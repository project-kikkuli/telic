"""Executing Swift counterexamples: the file is compiled with ``swiftc``
(debug build: overflow and bounds checks on) together with a generated
harness that reads the solver's values at run time, calls the function, and
checks its postconditions and its type's invariants; a trap is read from
the runtime's message. One binary per function serves every input (and is
cached), so replaying many inputs costs one compilation."""

from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
import subprocess
import tempfile
from fractions import Fraction
from typing import Any

from .. import ir

TIMEOUT_S = 10.0
COMPILE_TIMEOUT_S = 600.0

PRELUDE = r'''
#if canImport(Glibc)
import Glibc
#elseif canImport(Darwin)
import Darwin
#endif
let telicUnbuffered: Void = { setvbuf(stdout, nil, _IONBF, 0); return () }()
indirect enum TelicJ { case list([TelicJ]); case atom(String) }
func telicParse(_ text: String) -> TelicJ {
    let c = Array(text.utf8)
    var i = 0
    func value() -> TelicJ {
        if c[i] == UInt8(ascii: "[") {
            i += 1
            var items: [TelicJ] = []
            if c[i] == UInt8(ascii: "]") { i += 1; return .list(items) }
            while true {
                items.append(value())
                if c[i] == UInt8(ascii: ",") { i += 1; continue }
                i += 1
                return .list(items)
            }
        }
        let start = i
        while i < c.count && c[i] != UInt8(ascii: ",") && c[i] != UInt8(ascii: "]") { i += 1 }
        return .atom(String(decoding: c[start..<i], as: UTF8.self))
    }
    return value()
}
func telicList(_ j: TelicJ) -> [TelicJ] { if case .list(let xs) = j { return xs }; fatalError("telic harness: a list was expected") }
func telicAtom(_ j: TelicJ) -> String { if case .atom(let s) = j { return String(s.dropFirst()) }; fatalError("telic harness: a value was expected") }
func telicNull(_ j: TelicJ) -> Bool { if case .atom(let s) = j { return s == "n" }; return false }
func telicInt<T: FixedWidthInteger>(_ j: TelicJ) -> T { T(telicAtom(j))! }
func telicDouble(_ j: TelicJ) -> Double { let p = telicAtom(j).split(separator: "/"); return Double(String(p[0]))! / Double(String(p[1]))! }
func telicBool(_ j: TelicJ) -> Bool { telicAtom(j) == "t" }
func telicString(_ j: TelicJ) -> String {
    let h = Array(telicAtom(j).utf8)
    var bytes: [UInt8] = []
    var k = 0
    while k + 1 < h.count { bytes.append(UInt8(String(decoding: h[k...k + 1], as: UTF8.self), radix: 16)!); k += 2 }
    return String(decoding: bytes, as: UTF8.self)
}
func telicQuote(_ s: String) -> String {
    var o = "\""
    for u in s.unicodeScalars {
        switch u {
        case "\"": o += "\\\""
        case "\\": o += "\\\\"
        case "\n": o += "\\n"
        default:
            if u.value < 0x20 { let h = String(u.value, radix: 16); o += "\\u" + String(repeating: "0", count: 4 - h.count) + h } else { o.unicodeScalars.append(u) }
        }
    }
    return o + "\""
}
func telicDoubleJSON(_ d: Double) -> String { d.isNaN ? "NaN" : d.isInfinite ? (d > 0 ? "Infinity" : "-Infinity") : "\(d)" }
var telicObjects: [String: AnyObject] = [:]
'''

IMPLIES = "func implies(_ a: Bool, _ b: @autoclosure () -> Bool) -> Bool { !a || b() }\n"


class NotReplayable(Exception):
    pass


class Harness:
    """The generated Swift for calling one function on runtime values."""

    def __init__(self, pj: Any, info: Any, fn: ir.Function, source: str, path: str):
        self.pj = pj
        self.info = info
        self.fn = fn
        self.source = source
        self.path = path
        self.decls: list[str] = []
        self.decoders: dict[str, str] = {}
        self.encoders: dict[str, str] = {}
        self.inits: dict[str, str] = {}  # type -> its generated '__telic' initializer
        self.injections: list[tuple[int, str]] = []  # (byte offset, text) inserted into the source
        self.n = 0

    # -- types ------------------------------------------------------------

    def _tinfo(self, tn: Any) -> tuple[str, Any]:
        """(category, detail) of a Swift type node."""
        from .swift import INT_KINDS, REAL_TYPES, _base_name, _generic_args
        from .swift_syntax import text

        k = tn.type
        if k in ("array_type",):
            inner = tn.child_by_field_name("element") or next(c for c in tn.children if c.is_named)
            return "list", inner
        if k == "dictionary_type":
            kids = [c for c in tn.children if c.is_named]
            return "dict", (kids[0], kids[1])
        if k == "optional_type":
            inner = tn.child_by_field_name("wrapped") or next(c for c in tn.children if c.is_named)
            return "opt", inner
        if k == "user_type":
            name = _base_name(text(tn))
            args = _generic_args(tn)
            if name in self.free_generics():
                # an unconstrained type parameter: the function cannot look
                # inside its values, so any value of any type is a real input
                return "param", None
            if name in INT_KINDS:
                return "int", name
            if name in REAL_TYPES:
                return "real", name
            if name == "Bool":
                return "bool", None
            if name in ("String", "Character"):
                return "str", name
            if name == "Array" and len(args) == 1:
                return "list", args[0]
            if name == "Optional" and len(args) == 1:
                return "opt", args[0]
            if name == "Dictionary" and len(args) == 2:
                return "dict", (args[0], args[1])
            t = self.pj.types.get(name)
            if t is not None and not t.generics:
                if t.kind == "enum":
                    return ("payload" if t.payload else "enum"), t
                if t.kind in ("struct", "class") and isinstance(t.ir_type, ir.TClass) and not t.superclass:
                    return t.kind, t
        raise NotReplayable(f"cannot build a value of type {text(tn)}")

    def free_generics(self) -> set[str]:
        """Type parameters of the function with no constraint."""
        out: set[str] = set()
        for ch in self.info.node.children:
            if ch.type == "type_parameters":
                for tp in ch.children:
                    if tp.type == "type_parameter" and len([c for c in tp.children if c.is_named]) == 1:
                        out.add(tp.text.decode().strip())
        if any(ch.type == "type_constraints" for ch in self.info.node.children):
            return set()
        return out

    def ty_text(self, tn: Any) -> str:
        from .swift_syntax import text

        t = text(tn)
        for g in self.free_generics():
            t = re.sub(rf"\b{re.escape(g)}\b", "Int", t)
        return t

    def decoder(self, tn: Any) -> str:
        """The name of a function (TelicJ) -> T for the type node."""
        from .swift_syntax import text

        key = re.sub(r"\s+", "", text(tn))
        if key in self.decoders:
            return self.decoders[key]
        self.n += 1
        name = f"telicD{self.n}"
        self.decoders[key] = name
        cat, d = self._tinfo(tn)
        T = self.ty_text(tn)
        if cat in ("int", "param"):
            body = "telicInt(j)"
        elif cat == "real":
            body = "telicDouble(j)" if d == "Double" else f"{d}(telicDouble(j))"
        elif cat == "bool":
            body = "telicBool(j)"
        elif cat == "str":
            body = "telicString(j)" if d == "String" else "Character(telicString(j))"
        elif cat == "list":
            body = f"telicList(j).map({self.decoder(d)})"
        elif cat == "opt":
            body = f"telicNull(j) ? nil : {self.decoder(d)}(telicList(j)[0])"
        elif cat == "dict":
            kd, vd = self.decoder(d[0]), self.decoder(d[1])
            body = f"Dictionary(telicList(j).map {{ p in let q = telicList(p); return ({kd}(q[0]), {vd}(q[1])) }}, uniquingKeysWith: {{ a, _ in a }})"
        elif cat == "enum":
            cases = ", ".join(f"{d.name}.`{c.name}`" for c in d.cases)
            body = f"[{cases}][Int(telicAtom(j))!]"
        elif cat == "payload":
            arms = []
            for i, c in enumerate(d.cases):
                if c.params:
                    vals = ", ".join((f"{lbl}: " if lbl else "") + f"{self.decoder(tn2)}(q[{k + 1}])" for k, (lbl, tn2) in enumerate(c.params))
                    arms.append(f"case {i}: return .`{c.name}`({vals})")
                else:
                    arms.append(f"case {i}: return .`{c.name}`")
            arms.append("default: fatalError(\"telic harness: bad case\")")
            self.decls.append(f"func {name}(_ j: TelicJ) -> {T} {{ let q = telicList(j); switch Int(telicAtom(q[0]))! {{ {'; '.join(arms)} }} }}")
            return name
        elif cat in ("struct", "class"):
            fields = self._settable(d)
            init = self._init(d, fields)
            args = ", ".join(f"{self.decoder(fi.tnode)}(q[{k + (1 if cat == 'class' else 0)}])" for k, fi in enumerate(fields))
            call = f"{d.name}(__telic: ()" + (", " + args if args else "") + ")"
            del init
            if cat == "struct":
                body = f"{{ let q = telicList(j); return {call} }}()"
            else:
                body = f"{{ let q = telicList(j); let r = telicAtom(q[0]); if let o = telicObjects[r] {{ return o as! {T} }}; if q.count == 1 {{ fatalError(\"telic harness: an object without its fields\") }}; let o = {call}; telicObjects[r] = o; return o }}()"
        else:
            raise NotReplayable(f"cannot build a value of type {T}")
        self.decls.append(f"func {name}(_ j: TelicJ) -> {T} {{ {body} }}")
        return name

    def _settable(self, t: Any) -> list[Any]:
        out = []
        for fi in t.fields:
            if fi.tnode is None:
                raise NotReplayable(f"{t.name}.{fi.name} has no type annotation")
            if fi.is_let and fi.default is not None:
                continue
            out.append(fi)
        return out

    def _init(self, t: Any, fields: list[Any]) -> str:
        """An initializer that sets every stored property (the solver's
        values bypass the type's own initializers)."""
        if t.name in self.inits:
            return self.inits[t.name]
        params = ", ".join(["__telic: ()"] + [f"_ f{k}: {self.ty_text(fi.tnode)}" for k, fi in enumerate(fields)])
        sets = "; ".join(f"self.{fi.name} = f{k}" for k, fi in enumerate(fields))
        text_ = f"init({params}) {{ {sets} }}"
        self.inits[t.name] = text_
        if t.kind == "struct":
            self.decls.append(f"extension {t.name} {{ {text_} }}")
        else:
            body = t.node.child_by_field_name("body")
            if body is None or not self.path_is(t.path):
                raise NotReplayable(f"cannot build a {t.name}")
            extra = text_
            if not t.has_explicit_init and all(f.default is not None for f in t.fields):
                extra += " init() {}"  # keep the default initializer the source relies on
            self.injections.append((body.start_byte + 1, " " + extra + " "))
        return text_

    def path_is(self, p: str) -> bool:
        return os.path.normpath(p) == os.path.normpath(self.path)

    def encoder(self, tn: Any | None) -> str:
        """The name of a function T -> String (JSON)."""
        from .swift_syntax import text

        if tn is None:
            return "telicVoid"
        key = re.sub(r"\s+", "", text(tn))
        if key in self.encoders:
            return self.encoders[key]
        self.n += 1
        name = f"telicE{self.n}"
        self.encoders[key] = name
        T = self.ty_text(tn)
        try:
            cat, d = self._tinfo(tn)
        except NotReplayable:
            cat, d = "other", None
        if cat == "int":
            body = "String(v)"
        elif cat == "real":
            body = "telicDoubleJSON(Double(v))"
        elif cat == "bool":
            body = 'v ? "true" : "false"'
        elif cat == "str":
            body = "telicQuote(String(v))"
        elif cat == "list":
            body = f'"[" + v.map({self.encoder(d)}).joined(separator: ",") + "]"'
        elif cat == "opt":
            body = f'v.map({self.encoder(d)}) ?? "null"'
        elif cat in ("struct", "class"):
            parts = " + \",\" + ".join(f'"\\"{fi.name}\\":" + {self.encoder(fi.tnode)}(v.{fi.name})' for fi in d.fields if fi.tnode is not None)
            body = '"{" + ' + (parts or '""') + ' + "}"'
        else:
            body = 'telicQuote(String(describing: v))'
        self.decls.append(f"func {name}(_ v: {T}) -> String {{ {body} }}")
        return name

    # -- the call -------------------------------------------------------------

    def params(self) -> list[tuple[str, Any, bool]]:
        """(internal name, type node, inout) for each declared parameter."""
        out = []
        for p in self.info.node.children:
            if p.type != "parameter":
                continue
            from .swift_syntax import text

            pn = p.child_by_field_name("name")
            tnode = [c for c in p.children if c.is_named and c.type not in ("simple_identifier", "parameter_modifiers")]
            mods = next((c for c in p.children if c.type == "parameter_modifiers"), None)
            if not tnode:
                raise NotReplayable("a parameter without a type")
            out.append((text(pn), tnode[-1], mods is not None and "inout" in text(mods)))
        return out

    def invariants(self) -> list[str]:
        owner = self.pj.types.get(self.info.owner) if self.info.owner else None
        if owner is None or owner.kind not in ("struct", "class"):
            return []
        return [" ".join(cl.payload.split()) for cl in self.pj.invariant_lines(owner)]

    def return_node(self) -> Any:
        from .swift import _return_type

        info = self.info
        if info.kind in ("getter",):
            ann = next((c for c in info.node.children if c.type == "type_annotation"), None)
            return (ann.child_by_field_name("name") or next(c for c in ann.children if c.is_named)) if ann is not None else None
        if info.kind == "init":
            return None
        return _return_type(info.node)

    def build(self, checks: bool) -> str:
        from .swift_syntax import text

        info = self.info
        fn = self.fn
        if info.kind in ("requirement", "field-getter") or info.alias_of:
            raise NotReplayable("not callable on its own")
        if any(isinstance(t, ir.TClass) for t in info.generics.values()):
            raise NotReplayable("a generic function constrained by a protocol")
        owner = self.pj.types.get(info.owner) if info.owner else None
        if owner is not None and owner.generics:
            raise NotReplayable("a method of a generic type")
        ps = self.params()
        lines: list[str] = []
        args_code: list[str] = []
        idx = 0
        recv = None
        if info.owner and not info.static and info.kind != "init":
            if owner is None or owner.kind not in ("struct", "class", "enum"):
                raise NotReplayable("a method of a protocol")
            recv_dec = self.decoder(_TypeName(owner.name, owner.node))
            lines.append(f"var __self = {recv_dec}(q[{idx}])")
            idx += 1
            recv = "__self"
        for (pname, tn, inout), label in zip(ps, info.labels):
            dec = self.decoder(tn)
            lines.append(f"var {pname}: {self.ty_text(tn)} = {dec}(q[{idx}])")
            idx += 1
            args_code.append((f"{label}: " if label else "") + ("&" if inout else "") + pname)
        name = info.name
        if info.kind == "init":
            call = f"{owner.name}({', '.join(args_code)})"  # type: ignore[union-attr]
        elif info.kind == "getter":
            call = f"{recv}.{name}" if recv else f"{info.owner}.{name}"
        elif recv:
            call = f"{recv}.{name}({', '.join(args_code)})"
        elif info.owner:
            call = f"{info.owner}.{name}({', '.join(args_code)})"
        else:
            call = f"{name}({', '.join(args_code)})"
        if info.throws:
            call = "try " + call
        ret_n = self.return_node()
        is_void = info.kind != "init" and (ret_n is None or text(ret_n).replace(" ", "") in ("Void", "()"))
        # contracts, evaluated where their names mean what they mean in the source
        host = owner.name if owner is not None else None
        plist = ", ".join(f"_ {pn}: {self.ty_text(tn)}" for pn, tn, _ in ps)
        pargs = ", ".join(pn for pn, _, _ in ps)
        checks_code: list[str] = []
        throw_checks: list[str] = []
        pre_code: list[str] = []
        if checks:
            reqs = [c.text for c in fn.requires if "old(" not in c.text]
            if reqs:
                cond = " && ".join(f"({r})" for r in reqs)
                if host and not info.static and info.kind != "init":
                    self.decls.append(f"extension {host} {{ func __telicReq({plist}) -> Bool {{ {cond} }} }}")
                    pre_code.append(f"if !__self.__telicReq({pargs}) {{ print(\"TELIC_REJECTED\"); return }}")
                elif host:
                    self.decls.append(f"extension {host} {{ static func __telicReq({plist}) -> Bool {{ {cond} }} }}")
                    pre_code.append(f"if !{host}.__telicReq({pargs}) {{ print(\"TELIC_REJECTED\"); return }}")
                else:
                    self.decls.append(f"func __telicReq({plist}) -> Bool {{ {cond} }}")
                    pre_code.append(f"if !__telicReq({pargs}) {{ print(\"TELIC_REJECTED\"); return }}")
            ret_t = self.ty_text(ret_n) if ret_n is not None and not is_void else None
            for i, c in enumerate(fn.ensures):
                if "old(" in c.text:
                    continue
                body = re.sub(r"\bresult\b", "__v", c.text)
                vparam = f"_ __v: {ret_t}" if ret_t else ""
                allp = ", ".join(x for x in (vparam, plist) if x)
                vargs = ", ".join(x for x in ("__v" if ret_t else "", pargs) if x)
                if info.kind == "init":
                    self.decls.append(f"extension {host} {{ func __telicEns{i}({plist}) -> Bool {{ {c.text} }} }}")
                    checks_code.append(f"if !__v.__telicEns{i}({pargs}) {{ print(\"TELIC_VIOLATION ensures {i}\") }}")
                elif host and not info.static:
                    self.decls.append(f"extension {host} {{ func __telicEns{i}({allp}) -> Bool {{ {body} }} }}")
                    checks_code.append(f"if !__self.__telicEns{i}({vargs}) {{ print(\"TELIC_VIOLATION ensures {i}\") }}")
                elif host:
                    self.decls.append(f"extension {host} {{ static func __telicEns{i}({allp}) -> Bool {{ {body} }} }}")
                    checks_code.append(f"if !{host}.__telicEns{i}({vargs}) {{ print(\"TELIC_VIOLATION ensures {i}\") }}")
                else:
                    self.decls.append(f"func __telicEns{i}({allp}) -> Bool {{ {body} }}")
                    checks_code.append(f"if !__telicEns{i}({vargs}) {{ print(\"TELIC_VIOLATION ensures {i}\") }}")
            invs = self.invariants()
            if invs and (recv or info.kind == "init"):
                target = "__self" if recv else "__v"
                for i, inv in enumerate(invs):
                    self.decls.append(f"extension {host} {{ func __telicInv{i}() -> Bool {{ {inv} }} }}")
                    checks_code.append(f"if !{target}.__telicInv{i}() {{ print(\"TELIC_VIOLATION class.inv {i}\") }}")
                    if recv:  # (the error carries the receiver to whoever catches it)
                        throw_checks.append(f"if !__self.__telicInv{i}() {{ print(\"TELIC_VIOLATION class.inv {i}\") }}")
        if info.kind == "init" and info.failable:
            checks_code = [f"if let __v = __v {{ {' '.join(checks_code)} }}"] if checks_code else []
        enc = self.encoder(ret_n) if not is_void and info.kind != "init" else ("telicVoid" if is_void else "telicInitE")
        if info.kind == "init":
            self.decls.append("func telicInitE(_ v: Any) -> String { telicQuote(String(describing: v)) }")
        self.decls.append("func telicVoid(_ v: Void) -> String { \"null\" }")
        call_line = f"let __v = {call}" if not is_void else f"{call}; let __v: Void = ()"
        body = "\n    ".join(lines + pre_code)
        inner = "\n        ".join([call_line] + checks_code + [f'print("TELIC_RETURNED " + {enc}(__v))'])
        if info.throws:
            run = f"do {{\n        {inner}\n    }} catch {{ {''.join(c + '; ' for c in throw_checks)}print(\"TELIC_THROW \\(error)\") }}"
        else:
            run = inner
        main = f"""
func telicCase(_ j: TelicJ) {{
    let q = telicList(j)
    {body}
    {run}
}}
let telicCases = telicList(telicParse(CommandLine.arguments[1]))
let telicFrom = Int(CommandLine.arguments[2])!
_ = telicUnbuffered
for i in telicFrom..<telicCases.count {{ print("TELIC_CASE \\(i)"); telicCase(telicCases[i]) }}
"""
        src = self.source.encode("utf8")
        for off, txt in sorted(self.injections, reverse=True):
            src = src[:off] + txt.encode("utf8") + src[off:]
        user = re.sub(r"@main\b", "     ", src.decode("utf8"))
        implies = IMPLIES if not re.search(r"\bfunc\s+implies\b", self.source) else ""
        return user + "\n" + PRELUDE + implies + "\n".join(dict.fromkeys(self.decls)) + main


class _TypeName:
    """A type node for a named type (the receiver of a method)."""

    def __init__(self, name: str, at: Any):
        self.type = "user_type"
        self._name = name
        self.text = name.encode("utf8")
        self.children: list[Any] = []
        self.named_children: list[Any] = []
        self.start_point = at.start_point
        self.end_point = at.end_point

    def child_by_field_name(self, f: str) -> Any:
        return None


# ---------------------------------------------------------------------------
# Values on the wire


def _hex(s: str) -> str:
    return "s" + s.encode("utf8").hex()


def wire(v: Any, tn: Any, h: Harness, seen: set) -> str:
    """The solver's value (as replay.encode_value normalizes it) in the
    harness's input format."""
    cat, d = h._tinfo(tn)
    if cat == "param":
        return "i0"
    if isinstance(v, dict) and "__opaque__" in v:
        # a value telic does not model: no stand-in is made up for it
        raise NotReplayable("a value telic does not model")
    if cat == "int":
        if isinstance(v, bool) or not isinstance(v, (int, Fraction)):
            v = 0
        return f"i{int(v)}"
    if cat == "real":
        if isinstance(v, dict) and "__real__" in v:
            n, den = v["__real__"]
        elif isinstance(v, Fraction):
            n, den = v.numerator, v.denominator
        else:
            n, den = int(v or 0), 1
        return f"r{n}/{den}"
    if cat == "bool":
        return "bt" if v else "bf"
    if cat == "str":
        s = v if isinstance(v, str) else ""
        if d == "Character" and len(s) != 1:
            raise NotReplayable("a Character that is not one character")
        return _hex(s)
    if cat == "list":
        return "[" + ",".join(wire(x, d, h, seen) for x in (v or [])) + "]"
    if cat == "opt":
        return "n" if v is None else "[" + wire(v, d, h, seen) + "]"
    if cat == "dict":
        items = v["__dict__"] if isinstance(v, dict) and "__dict__" in v else list((v or {}).items())
        return "[" + ",".join("[" + wire(k, d[0], h, seen) + "," + wire(x, d[1], h, seen) + "]" for k, x in items) + "]"
    if cat == "enum":
        names = [c.name for c in d.cases]
        if isinstance(v, dict) and "__enum__" in v:
            return f"i{names.index(v['member']) if v['member'] in names else 0}"
        return f"i{int(v) if isinstance(v, int) and 0 <= v < len(names) else 0}"
    if cat == "payload":
        fields = v.get("fields", v) if isinstance(v, dict) else {}
        tag = fields.get("case")
        if isinstance(tag, dict) and "__enum__" in tag:
            i = [c.name for c in d.cases].index(tag["member"])
        else:
            i = tag if isinstance(tag, int) and 0 <= tag < len(d.cases) else 0
        c = d.cases[i]
        vals = [wire(fields.get(slot), tn2, h, seen) for (_, slot, _, _), (_, tn2) in zip(d.payload.get(c.name, []), c.params)]
        return "[" + ",".join([f"i{i}"] + vals) + "]"
    if cat in ("struct", "class"):
        if not isinstance(v, dict) or "__object__" not in v:
            raise NotReplayable(f"no value for a {d.name}")
        ref = v.get("ref")
        if cat == "class" and ref in seen:
            return f"[i{ref}]"
        if v.get("fields") is None:
            raise NotReplayable(f"the solver's {d.name} is deeper than it shows")
        seen.add(ref)
        vals = [wire(v["fields"].get(fi.name), fi.tnode, h, seen) for fi in h._settable(d)]
        return "[" + ",".join(([f"i{ref}"] if cat == "class" else []) + vals) + "]"
    raise NotReplayable("unsupported value")


def case_wire(h: Harness, fn: ir.Function, model: dict[str, Any]) -> str:
    from ..replay import encode_value

    seen: set = set()
    parts = []
    params = list(fn.params)
    ps = h.params()
    owner = h.pj.types.get(h.info.owner) if h.info.owner else None
    if params and params[0].name == "self" and owner is not None:
        parts.append(wire(encode_value(model.get("self"), params[0].ty), _TypeName(owner.name, owner.node), h, seen))
        params = params[1:]
    for p, (_, tn, _) in zip(params, ps):
        parts.append(wire(encode_value(model.get(p.name), p.ty), tn, h, seen))
    return "[" + ",".join(parts) + "]"


# ---------------------------------------------------------------------------
# Compiling and running


def _project(path: str) -> Any:
    from .swift import Project

    source = open(path, encoding="utf8").read()
    pj = Project([(path, source)])
    pj.declare()
    return pj, source


def compile_harness(path: str, fn: ir.Function) -> tuple[str | None, Any, str]:
    """(executable, harness, error): the binary for calling ``fn``."""
    swiftc = shutil.which("swiftc")
    if swiftc is None:
        return None, None, "swiftc is not installed"
    pj, source = _project(path)
    info = pj.fns.get(ir.source_name(fn.name))
    if info is None:
        return None, None, "the function is not in the file"
    err = ""
    for checks in (True, False):
        h = Harness(pj, info, fn, source, path)
        try:
            prog = h.build(checks)
        except NotReplayable as e:
            return None, None, str(e)
        key = hashlib.sha256(prog.encode()).hexdigest()[:16]
        work = os.path.join(tempfile.gettempdir(), f"telic-swift-{key}")
        exe = os.path.join(work, "main")
        if os.path.exists(exe):
            return exe, h, ""
        os.makedirs(work, exist_ok=True)
        src = os.path.join(work, "main.swift")
        with open(src, "w", encoding="utf8") as fh:
            fh.write(prog)
        try:
            c = subprocess.run([swiftc, "-Onone", "-o", exe + ".tmp", src], capture_output=True, text=True, timeout=COMPILE_TIMEOUT_S, cwd=work)
        except subprocess.TimeoutExpired:
            return None, None, "swiftc timed out"
        if c.returncode == 0:
            os.replace(exe + ".tmp", exe)
            return exe, h, ""
        err = next((ln for ln in c.stderr.splitlines() if "error:" in ln), "compile error")
    return None, None, f"swiftc could not build the counterexample: {err.split('error:', 1)[-1].strip()}"


def run_cases(exe: str, cases: list[str], n_lines: int) -> list[dict[str, Any]]:
    """Run every case; a trap ends the process, which restarts after it."""
    results: list[dict[str, Any]] = []
    payload = "[" + ",".join(cases) + "]"
    start = 0
    while start < len(cases):
        try:
            r = subprocess.run([exe, payload, str(start)], capture_output=True, text=True, timeout=TIMEOUT_S)
        except subprocess.TimeoutExpired:
            results.append({"timeout": True})
            start += 1
            while len(results) < start:
                results.append({"timeout": True})
            continue
        chunks = _split_cases(r.stdout)
        done = sorted(chunks)
        for i in done:
            if i < start:
                continue
            while len(results) < i:
                results.append({"harness_error": "no output"})
            out = _parse_case(chunks[i])
            if out is None and i == done[-1] and r.returncode != 0:
                out = _crash(r.stderr, r.returncode, n_lines)
            results.append(out or {"harness_error": "the counterexample program printed nothing"})
        if r.returncode != 0 and (not done or _parse_case(chunks[done[-1]]) is not None):
            # it died before announcing the next case
            results.append(_crash(r.stderr, r.returncode, n_lines))
        start = len(results)
        if not done and r.returncode == 0:
            break
    return results[: len(cases)]


def _split_cases(out: str) -> dict[int, list[str]]:
    chunks: dict[int, list[str]] = {}
    cur = None
    for line in out.splitlines():
        m = re.match(r"^TELIC_CASE (\d+)$", line)
        if m:
            cur = int(m.group(1))
            chunks[cur] = []
        elif cur is not None:
            chunks[cur].append(line)
    return chunks


def _parse_case(lines: list[str]) -> dict[str, Any] | None:
    out: dict[str, Any] = {}
    for line in lines:
        if line == "TELIC_REJECTED":
            return {"rejected": True}
        if line.startswith("TELIC_VIOLATION ") and "violation" not in out:
            _, kind, i = line.split()
            out.update({"violation": kind, "index": int(i)})
        elif line.startswith("TELIC_THROW "):
            if "violation" in out:
                return {**out, "detail": "raised"}
            return {"crash": "throw", "msg": line[len("TELIC_THROW "):]}
        elif line.startswith("TELIC_RETURNED "):
            text = line[len("TELIC_RETURNED "):]
            out["returned_repr"] = text
            try:
                out["value"] = json.loads(text)
            except ValueError:
                out["value"] = text
            return out
    return out or None


def _crash(stderr: str, rc: int, n_lines: int) -> dict[str, Any]:
    msg = ""
    line = None
    for ln in stderr.splitlines():
        m = re.match(r"^(.*?):(\d+): (Fatal error|Precondition failed|Assertion failed)(?:: (.*))?$", ln.strip())
        if m:
            where, num, what, text = m.groups()
            msg = f"{what}: {text}" if text else what
            if where.endswith("main.swift") and int(num) <= n_lines:
                line = int(num)
            break
    crash = "trap"
    if "Index out of range" in msg or "index out of range" in msg.lower():
        crash = "IndexError"
    elif "Unexpectedly found nil" in msg:
        crash = "unwrap on None"
    elif "Division by zero" in msg or "Remainder of or division by zero" in msg:
        crash = "ZeroDivisionError"
    elif "overflow" in msg.lower() or "Not enough bits" in msg or "cannot be converted" in msg:
        crash = "overflow"
    elif msg.startswith(("Precondition failed", "Assertion failed")):
        crash = "AssertionError"
    elif msg.startswith("Fatal error"):
        crash = "fatal"
    return {"crash": crash, "msg": msg or f"trapped (exit status {rc})", "line": line}


def run_swift(path: str, fn: ir.Function, model: dict[str, Any]) -> dict[str, Any] | None:
    """Replay one counterexample; None when it cannot be run here."""
    if shutil.which("swiftc") is None:
        return None
    exe, h, err = compile_harness(path, fn)
    if exe is None:
        if err.startswith(("cannot build", "not callable", "a method of", "no value", "the solver's", "a parameter", "unsupported", "a Character")):
            return None
        return {"harness_error": err}
    try:
        case = case_wire(h, fn, model)
    except NotReplayable:
        return None
    (out,) = run_cases(exe, [case], len(h.source.splitlines()))
    return describe(out, fn, h)


def describe(out: dict[str, Any], fn: ir.Function, h: Harness) -> dict[str, Any]:
    if out.get("violation") == "ensures":
        c = fn.ensures[out["index"]]
        return {"violation": "ensures", "func": ir.source_name(fn.name), "text": c.text, "detail": f"returned {out.get('returned_repr', '')}".strip(), "returned_repr": out.get("returned_repr")}
    if out.get("violation") == "class.inv":
        seen = {k: out[k] for k in ("returned_repr", "detail") if k in out}
        return {"violation": "class.inv", "func": ir.source_name(fn.name), "text": h.invariants()[out["index"]], **seen}
    return out


def run_swift_batch(path: str, fn: ir.Function, batch_models: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """Run ``fn`` on many inputs (for @mirrors): one compilation."""
    exe, h, err = compile_harness(path, fn)
    if exe is None:
        return [{"harness_error": err}] * len(batch_models)
    cases = []
    idx = []
    for i, m in enumerate(batch_models):
        try:
            cases.append(case_wire(h, fn, m))
            idx.append(i)
        except NotReplayable as e:
            del e
    outs = run_cases(exe, cases, len(h.source.splitlines())) if cases else []
    res: list[dict[str, Any]] = [{"harness_error": "cannot build this input"}] * len(batch_models)
    for i, o in zip(idx, outs):
        res[i] = o
    return res
