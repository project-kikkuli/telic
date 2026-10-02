"""Swift frontend: lowers Swift source (parsed with tree-sitter) to the IR.

All Swift files of a run are lowered together, as one Swift module: a file
sees every other file's declarations without imports, and a protocol's
conformers are known wherever they are declared.

What Swift makes checkable, telic checks: integer arithmetic must not
overflow (it traps), indexing must be in bounds, ``!`` must see a value,
``fatalError``/``precondition``/``assert`` must be unreachable or hold, and
``throw`` must happen only where ``@raises`` says. Values of an integer type
lie in its range (a fact, not an assumption).

The model of values follows Swift's:

* a class is an object on the heap (references alias);
* a struct is an object too, but every place a struct value is stored
  (a binding, a field, an element, an argument path through another object)
  gets its own copy, so no two places share one and mutation stays local,
  as value semantics require;
* an enum without payloads is a finite enum; one with payloads is a record
  (the case, and a slot for each payload);
* a protocol is a base class of its conformers: a call through it is
  checked against the requirement's contract, which every conformer is
  checked against. A protocol telic cannot see every conformer of (a public
  one, or one a type it does not model conforms to) is opaque;
* a generic parameter is opaque, or the protocol that constrains it;
* ``String`` equality is Unicode canonical equivalence, which telic does
  not decide: it is modelled as equality of an uninterpreted normal form.

Contracts are ``//@`` comments whose payload is a Swift expression; in them
arithmetic is mathematical (no overflow), ``result`` is the return value,
``old(e)`` is ``e`` at entry, ``implies(a, b)`` is implication, and
quantifiers are written as Swift: ``(0..<n).allSatisfy { i in ... }``,
``xs.allSatisfy { $0 >= 0 }``, ``xs.contains { ... }``.
"""

from __future__ import annotations

import os
import re
from dataclasses import dataclass, field
from typing import Any

from .. import ir
from ..contracts import (
    ContractLine,
    ContractSyntaxError,
    parse_aim_directive,
    parse_comment_lines,
)
from .swift_syntax import Unsupported, named, parser, text

SWIFT_ASSUMPTIONS = [
    "Double and Float use IEEE 754 binary64 and binary32 semantics; Float80 is opaque",
    "Int and UInt are 64 bits wide",
    "String equality (Unicode canonical equivalence) and other String operations are uninterpreted functions",
    "assert and precondition are checked (debug build semantics)",
    "print and logging have no effect on program state",
]

INT_KINDS = {
    "Int": (True, 64), "Int8": (True, 8), "Int16": (True, 16), "Int32": (True, 32), "Int64": (True, 64),
    "UInt": (False, 64), "UInt8": (False, 8), "UInt16": (False, 16), "UInt32": (False, 32), "UInt64": (False, 64),
}
REAL_TYPES = {"Double", "Float", "Float32", "Float64", "CGFloat", "Float80"}
STR_TYPES = {"String", "Character"}
LOGGING = {"print", "debugPrint", "NSLog", "dump"}


def int_range(kind: str) -> tuple[int, int]:
    signed, bits = INT_KINDS[kind]
    return (-(1 << (bits - 1)), (1 << (bits - 1)) - 1) if signed else (0, (1 << bits) - 1)


class LowerError(Exception):
    def __init__(self, msg: str, line: int = 0):
        super().__init__(msg)
        self.line = line


def _line(n: Any) -> int:
    return n.start_point[0] + 1 if n is not None else 0


def _kw(n: Any) -> str:
    """struct / class / enum / extension / actor, for a class_declaration."""
    for c in n.children:
        if n.field_name_for_child(list(n.children).index(c)) == "declaration_kind":
            return text(c)
    for c in n.children:
        if c.type in ("struct", "class", "enum", "extension", "actor"):
            return c.type
    return "class"


def _modifiers(n: Any) -> set[str]:
    out: set[str] = set()
    for c in n.children:
        if c.type == "modifiers":
            out.update(text(m).split("(")[0].strip() for m in c.children if m.is_named)
    return out


def _attributes(n: Any) -> list[str]:
    return [text(m) for c in n.children if c.type == "modifiers" for m in c.children if m.type == "attribute"]


def _base_name(t: str) -> str:
    """'Stack<Int>' -> 'Stack'; 'Swift.Int' -> 'Int'."""
    t = t.strip()
    depth = 0
    out = ""
    for ch in t:
        if ch == "<":
            depth += 1
        elif ch == ">":
            depth -= 1
        elif depth == 0:
            out += ch
    return out.split(".")[-1].strip()


def _generic_args(tn: Any) -> list[Any]:
    ta = next((c for c in tn.children if c.type == "type_arguments"), None)
    return [c for c in ta.children if c.is_named] if ta is not None else []


@dataclass
class FieldInfo:
    name: str
    tnode: Any  # type annotation's type node, or None
    is_let: bool
    default: Any  # tree-sitter node of the initial value, or None
    node: Any


@dataclass
class CaseInfo:
    name: str
    params: list[tuple[str | None, Any]]  # (label, type node)
    raw: Any  # raw value node


@dataclass
class TypeInfo:
    name: str
    kind: str  # struct | class | enum | protocol | actor
    node: Any
    path: str
    access: set[str]
    fields: list[FieldInfo] = field(default_factory=list)
    members: list[tuple[Any, str, bool]] = field(default_factory=list)  # (decl node, path, from an extension)
    conforms: list[str] = field(default_factory=list)
    superclass: str | None = None
    cases: list[CaseInfo] = field(default_factory=list)
    generics: list[str] = field(default_factory=list)
    raw_type: str | None = None
    indirect: bool = False
    requirements: dict[str, Any] = field(default_factory=dict)  # protocol: name -> decl node
    mutating_reqs: set[str] = field(default_factory=set)
    open_why: str | None = None  # protocol: why calls through it are unchecked
    conformers: list[str] = field(default_factory=list)
    ir_type: Any = None
    payload: dict[str, list[tuple[str, str, ir.Type, str | None]]] = field(default_factory=dict)  # enum case -> [(label, slot, type, kind)]
    field_kinds: dict[str, str] = field(default_factory=dict)
    has_explicit_init: bool = False
    custom_eq: bool = False
    equatable: bool = False


@dataclass
class FnInfo:
    key: str
    name: str
    node: Any
    path: str
    owner: str | None
    static: bool
    mutating: bool
    params: list[ir.Param]
    labels: list[str | None]
    defaults: list[Any]
    ret: ir.Type
    ret_kind: str | None
    param_kinds: dict[str, str]
    elem_kinds: dict[str, str]
    inout: set[str]
    throws: bool
    kind: str = "func"  # func | init | getter | field-getter | requirement
    failable: bool = False
    body: Any = None  # statements node (or None for a declaration)
    exported: bool = True
    generics: dict[str, ir.Type] = field(default_factory=dict)
    inherit: "FnInfo | None" = None  # the requirement whose contract this implementation takes
    field_name: str | None = None  # field-getter: the stored property it reads
    contract_lines: list[ContractLine] = field(default_factory=list)
    fn: ir.Function | None = None  # the lowered function (contracts first, body later)
    problems: list[tuple[str, int]] = field(default_factory=list)
    alias_of: str | None = None  # a default implementation: the requirement it provides


@dataclass
class FileInfo:
    path: str
    source: str
    lines: list[str]
    tree: Any
    module: ir.Module
    contracts: list[ContractLine] = field(default_factory=list)


class Project:
    """Every Swift file of the run, lowered as one module."""

    def __init__(self, files: list[tuple[str, str]]):
        self.files: dict[str, FileInfo] = {}
        for path, source in files:
            m = ir.Module(path=path, language="swift", source=source)
            m.assumptions = list(SWIFT_ASSUMPTIONS)
            self.files[path] = FileInfo(path, source, source.splitlines(), None, m)
        self.types: dict[str, TypeInfo] = {}
        self.fns: dict[str, FnInfo] = {}
        self.by_name: dict[str, list[FnInfo]] = {}  # "Owner.name" / "name" -> overloads
        self.consts: dict[str, tuple[Any, str]] = {}  # global constant -> (literal node, path)
        self.globals: set[str] = set()  # global variables: unchecked shared state
        self.extensions: list[tuple[Any, str]] = []
        self.aliases: dict[str, str] = {}  # typealias name -> what it names
        self.nested_aliases: dict[str, str] = {}
        self.stray: list[tuple[str, list[str], str, int]] = []  # unmodelled types: (name, what they inherit, path, line)
        self.partial: list[tuple[str, str]] = []  # (protocol, type) conformances telic does not model

    # -- entry ----------------------------------------------------------

    def run(self) -> dict[str, ir.Module]:
        self.declare()
        from .swift_lower import FunctionLowerer

        for info in list(self.fns.values()):
            info.fn = FunctionLowerer(self, info).contracts()
        for t in self.types.values():
            self._invariants(t)
        for info in list(self.fns.values()):
            f = self.files[info.path]
            try:
                fn = FunctionLowerer(self, info).lower()
            except LowerError as e:
                fn = self._stub(info, str(e), e.line)
            except Unsupported as e:
                fn = self._stub(info, str(e), _line(e.node))
            except Exception as e:  # noqa: BLE001 - a telic bug leaves one function unchecked, with the reason
                fn = self._stub(info, f"telic could not model this function ({type(e).__name__}: {e}); please report it", _line(info.node))
            f.module.functions[info.key] = fn
        for f in self.files.values():
            self._leftover_contracts(f)
            for other in self.files.values():
                if other is f:
                    continue
                for key in other.module.functions:
                    f.module.imports.setdefault(key, (other.path, key))
        return {p: f.module for p, f in self.files.items()}

    def declare(self) -> None:
        """Parse every file and collect declarations, types and signatures."""
        for f in self.files.values():
            f.tree = parser().parse(f.source.encode("utf8"))
            root = f.tree.root_node
            if root.has_error:
                bad = _first_error(root)
                f.module.problems.append(("syntax error (or Swift syntax telic's parser does not know)", ir.Loc(_line(bad) if bad is not None else 1)))
            comments: list[tuple[int, int, str]] = []
            _collect_comments(root, comments)
            try:
                f.contracts = parse_comment_lines(comments, "//")
            except ContractSyntaxError as e:
                f.module.problems.append((str(e), ir.Loc(e.line, e.col)))
                f.contracts = []
        for f in self.files.values():
            self._scan(f.tree.root_node, f.path, top=True)
        for f in self.files.values():
            self._collect(f.tree.root_node, f.path)
        for node, path in self.extensions:
            self._extension(node, path)
        self._model_types()
        for t in self.types.values():
            self._members(t)
        for f in self.files.values():
            for c in named(f.tree.root_node):
                if c.type == "function_declaration":
                    self._signature(c, f.path, None, False)
        self._keys()
        self._protocols()

    def _stub(self, info: FnInfo, msg: str, line: int) -> ir.Function:
        base = info.fn
        n = info.node
        fn = ir.Function(info.key, ir.Loc(_line(n), n.start_point[1]), n.end_point[0] + 1, info.params, info.ret, source=text(n))
        if base is not None:
            fn.requires, fn.ensures, fn.raises, fn.aims, fn.mirrors, fn.decreases = base.requires, base.ensures, base.raises, base.aims, base.mirrors, base.decreases
        fn.unsupported.append((msg, ir.Loc(line or _line(n))))
        return fn

    def _leftover_contracts(self, f: FileInfo) -> None:
        for cl in f.contracts:
            if cl.consumed:
                continue
            if cl.keyword == "aim":
                try:
                    ids, txt = parse_aim_directive(cl)
                except ContractSyntaxError as e:
                    f.module.problems.append((str(e), ir.Loc(e.line, e.col)))
                    continue
                if txt is not None:
                    f.module.aims.append(ir.AimDecl(ids[0], txt, ir.Loc(cl.line, cl.col)))
                else:
                    f.module.problems.append((f"'@aim {', '.join(ids)}' outside a function links nothing", ir.Loc(cl.line, cl.col)))
                continue
            f.module.problems.append((f"'@{cl.keyword}' is not attached to anything telic checks", ir.Loc(cl.line, cl.col)))

    # -- declarations ---------------------------------------------------

    def _scan(self, n: Any, path: str, top: bool) -> None:
        """Type aliases, and the conformances of types telic does not model
        (nested in a type or declared in a function): a protocol or class
        they extend has a conformer or subclass telic never sees."""
        for c in n.children:
            if c.type == "typealias_declaration":
                names = [x for x in c.children_by_field_name("name")]
                if len(names) == 2:
                    # (a nested alias only widens what conformance clauses may mean)
                    (self.aliases if top else self.nested_aliases).setdefault(_base_name(text(names[0])), text(names[1]))
            elif c.type in ("class_declaration", "protocol_declaration") and not top:
                inherits = [text(ch) for ch in c.children if ch.type == "inheritance_specifier"]
                if inherits:
                    self.stray.append((_base_name(text(c.child_by_field_name("name"))), inherits, path, _line(c)))
            self._scan(c, path, False)

    def names(self, inherits: str) -> list[str]:
        """The type names an inheritance clause entry means: 'A & B' is two,
        and a type alias is what it names."""
        out: list[str] = []
        todo = [inherits]
        seen: set[str] = set()
        while todo:
            t = todo.pop()
            for part in t.split("&"):
                name = _base_name(part)
                if name in self.aliases and name not in seen:
                    seen.add(name)
                    todo.append(self.aliases[name])
                elif name:
                    out.append(name)
                    if name in self.nested_aliases and name not in seen:
                        seen.add(name)
                        todo.append(self.nested_aliases[name])
        return out

    def _collect(self, container: Any, path: str) -> None:
        for c in named(container):
            if c.type == "class_declaration":
                kw = _kw(c)
                if kw == "extension":
                    self.extensions.append((c, path))
                    continue
                self._type(c, path, kw)
            elif c.type == "protocol_declaration":
                self._protocol_decl(c, path)
            elif c.type == "property_declaration":
                self._global(c, path)

    def _global(self, c: Any, path: str) -> None:
        pat = c.child_by_field_name("name")
        name = text(pat.child_by_field_name("bound_identifier")) if pat is not None and pat.child_by_field_name("bound_identifier") is not None else None
        if name is None:
            return
        is_let = any(ch.type == "value_binding_pattern" and "let" in text(ch) for ch in c.children)
        val = c.child_by_field_name("value")
        if is_let and val is not None and val.type in ("integer_literal", "real_literal", "boolean_literal", "line_string_literal", "hex_literal", "bin_literal", "oct_literal") or is_let and val is not None and val.type == "prefix_expression" and text(val).startswith("-") and val.child_by_field_name("target") is not None and val.child_by_field_name("target").type in ("integer_literal", "real_literal"):
            ann = next((ch for ch in c.children if ch.type == "type_annotation"), None)
            self.consts[name] = (val, text(ann).lstrip(":").strip() if ann is not None else "")
        else:
            self.globals.add(name)

    def _type(self, c: Any, path: str, kw: str) -> None:
        name_n = c.child_by_field_name("name")
        name = _base_name(text(name_n))
        body = c.child_by_field_name("body")
        t = TypeInfo(name, "struct" if kw == "struct" else "enum" if kw == "enum" else "class", c, path, _modifiers(c))
        t.indirect = any(ch.type == "indirect" for ch in c.children) or "indirect" in t.access
        t.generics = [text(tp.children[0]) for ch in c.children if ch.type == "type_parameters" for tp in ch.children if tp.type == "type_parameter"]
        for ch in c.children:
            if ch.type == "inheritance_specifier":
                t.conforms.extend(self.names(text(ch)))
        if name in self.types:
            self.files[path].module.problems.append((f"type {name} is declared twice; telic checks neither", ir.Loc(_line(c))))
            self.types[name].open_why = f"{name} is declared twice"
            return
        self.types[name] = t
        if kw == "actor":
            t.open_why = "actors are not modelled"
        if body is None:
            return
        for m in named(body):
            self._member(t, m, path, False)

    def _protocol_decl(self, c: Any, path: str) -> None:
        name = _base_name(text(c.child_by_field_name("name")))
        t = TypeInfo(name, "protocol", c, path, _modifiers(c))
        for ch in c.children:
            if ch.type == "inheritance_specifier":
                t.conforms.extend(self.names(text(ch)))
        body = c.child_by_field_name("body")
        self.types[name] = t
        for m in named(body) if body is not None else []:
            if m.type == "protocol_function_declaration":
                nm = m.child_by_field_name("name")
                t.requirements[text(nm) if nm is not None else "?"] = m
                if "mutating" in _modifiers(m):
                    t.mutating_reqs.add(text(nm))
            elif m.type == "protocol_property_declaration":
                pat = m.child_by_field_name("name")
                bid = pat.child_by_field_name("bound_identifier") if pat is not None else None
                if bid is not None:
                    t.requirements[text(bid)] = m
                    reqs = next((ch for ch in m.children if ch.type == "protocol_property_requirements"), None)
                    if reqs is not None and "set" in text(reqs):
                        t.mutating_reqs.add(text(bid))
            elif m.type in ("associatedtype_declaration",):
                t.open_why = f"protocol {name} has associated types, which telic does not model"
            elif m.type != "comment":
                t.requirements[f"?{m.type}"] = m
                t.open_why = f"protocol {name} has a requirement telic does not model ({m.type.replace('_', ' ')})"

    def _member(self, t: TypeInfo, m: Any, path: str, ext: bool) -> None:
        if m.type == "property_declaration":
            mods = _modifiers(m)
            pat = m.child_by_field_name("name")
            bid = pat.child_by_field_name("bound_identifier") if pat is not None else None
            if bid is None:
                t.open_why = t.open_why or f"{t.name} has a stored property pattern telic does not model"
                return
            ann = next((ch for ch in m.children if ch.type == "type_annotation"), None)
            tnode = ann.child_by_field_name("name") if ann is not None else None
            if tnode is None and ann is not None:
                tnode = next((ch for ch in ann.children if ch.is_named), None)
            computed = m.child_by_field_name("computed_value")
            if computed is not None or any(ch.type == "computed_property" for ch in m.children):
                t.members.append((m, path, ext))
                return
            if "static" in mods or "class" in mods:
                t.members.append((m, path, ext))
                return
            if ext:
                return  # extensions cannot add stored properties
            if "lazy" in mods or any(ch.type == "property_behavior_modifier" or ch.type == "willset_didset_block" for ch in m.children) or any(a.startswith("@") for a in _attributes(m)):
                t.open_why = t.open_why or f"{t.name}.{text(bid)} has observers or a property wrapper, which telic does not model"
            is_let = any(ch.type == "value_binding_pattern" and "let" in text(ch) for ch in m.children)
            t.fields.append(FieldInfo(text(bid), tnode, is_let, m.child_by_field_name("value"), m))
            return
        if m.type == "enum_entry":
            names = m.children_by_field_name("name")
            datas = m.children_by_field_name("data_contents")
            raws = m.children_by_field_name("raw_value")
            # the entries of one 'case a, b(x: Int)' line: pair each name with what follows it
            items: list[CaseInfo] = []
            for ch in m.children:
                if ch.type == "simple_identifier" and ch in names:
                    items.append(CaseInfo(text(ch), [], None))
                elif ch.type == "enum_type_parameters" and items:
                    items[-1].params = _case_params(ch)
                elif items and ch in raws:
                    items[-1].raw = ch
            del datas
            t.cases.extend(items)
            return
        if m.type in ("function_declaration", "init_declaration", "subscript_declaration", "deinit_declaration", "typealias_declaration", "class_declaration", "protocol_declaration"):
            if m.type == "init_declaration" and not ext:
                t.has_explicit_init = True
            if m.type == "class_declaration" or m.type == "protocol_declaration":
                self.files[path].module.notes.append((f"nested type in {t.name} is not modelled", ir.Loc(_line(m))))
                return
            t.members.append((m, path, ext))
            return

    def _extension(self, c: Any, path: str) -> None:
        names = self.names(text(c.child_by_field_name("name")))
        name = names[0] if len(names) == 1 else text(c.child_by_field_name("name"))
        t = self.types.get(name)
        conforms = [n for ch in c.children if ch.type == "inheritance_specifier" for n in self.names(text(ch))]
        if t is None:
            # an extension of a type telic does not model: what it conforms to is open
            self.partial += [(p, name) for p in conforms]
            self.files[path].module.notes.append((f"extension of {name}, a type telic does not model: its members are unchecked", ir.Loc(_line(c))))
            return
        if any(ch.type == "type_constraints" or ch.type == "where_clause" for ch in c.children):
            self.partial += [(p, f"{name} (where ...)") for p in conforms]
            self.files[path].module.notes.append((f"constrained extension of {name} is not modelled: its members are unchecked", ir.Loc(_line(c))))
            return
        t.conforms.extend(conforms)
        body = c.child_by_field_name("body")
        for m in named(body) if body is not None else []:
            self._member(t, m, path, True)

    # -- the model of each type -------------------------------------------

    def _model_types(self) -> None:
        for k in [k for k, v in self.types.items() if v is None]:
            del self.types[k]
        for t in self.types.values():
            if t.kind == "protocol":
                continue
            if t.kind == "enum":
                continue
            t.superclass = next((c for c in t.conforms if c in self.types and self.types[c].kind == "class"), None) if t.kind == "class" else None
        # protocols: which are closed (every conformer is modelled as an object and known)
        for t in self.types.values():
            if t.kind != "protocol":
                continue
            if "public" in t.access or "open" in t.access:
                t.open_why = t.open_why or f"protocol {t.name} is public, so conformers outside these files may exist"
        for proto, typ in self.partial:
            p = self.types.get(proto)
            if p is not None and p.kind == "protocol":
                p.open_why = p.open_why or f"{typ} conforms to {proto}, and telic does not model {typ}"
        for sub, inherits, path, line in self.stray:
            for n in (x for i in inherits for x in self.names(i)):
                b = self.types.get(n)
                if b is not None and b.kind == "protocol":
                    b.open_why = b.open_why or f"{sub} ({path}:{line}) conforms to {n}, and telic does not model a type declared inside another declaration"
                elif b is not None and b.kind == "class":
                    self.files[path].module.opaque_subclasses.append((sub, n, ir.Loc(line)))
        changed = True
        while changed:  # conformance is transitive through protocol inheritance
            changed = False
            for t in self.types.values():
                for c in list(t.conforms):
                    p = self.types.get(c)
                    if p is not None and p.kind == "protocol":
                        for q in p.conforms:
                            if q not in t.conforms:
                                t.conforms.append(q)
                                changed = True
        for t in self.types.values():
            for c in t.conforms:
                p = self.types.get(c)
                if p is None or p.kind != "protocol" or t.kind == "protocol":
                    continue
                p.conformers.append(t.name)
                if t.kind == "enum":
                    p.open_why = p.open_why or f"enum {t.name} conforms to {p.name}, and telic models protocol values as objects"
                elif t.open_why:
                    p.open_why = p.open_why or f"{t.name} conforms to {p.name}, and {t.open_why}"
        for t in self.types.values():
            if t.kind == "protocol":
                t.ir_type = ir.TClass(t.name) if not t.open_why else ir.TOpaque(t.name)
            elif t.kind in ("struct", "class"):
                t.ir_type = ir.TClass(t.name) if not t.open_why else ir.TOpaque(t.name)
                t.equatable = any(c in ("Equatable", "Hashable", "Comparable") for c in t.conforms)
            elif t.kind == "enum":
                self._model_enum(t)
        for t in self.types.values():
            if t.kind in ("struct", "class") and not t.open_why:
                self._declare_class(t)
            elif t.kind == "protocol" and not t.open_why:
                # a protocol is a base class of its conformers, with no fields
                self.files[t.path].module.classes[t.name] = ir.ClassDecl(t.name, [], [], ir.Loc(_line(t.node), t.node.start_point[1]))
                for f in self.files.values():
                    if f.path != t.path:
                        f.module.class_origin[t.name] = t.path

    def _model_enum(self, t: TypeInfo) -> None:
        raw = next((c for c in t.conforms if c in INT_KINDS or c in STR_TYPES), None)
        t.raw_type = raw
        if not any(c.params for c in t.cases):
            values: list[object] = []
            nxt = 0
            for c in t.cases:
                if raw in INT_KINDS:
                    if c.raw is not None:
                        try:
                            nxt = int(text(c.raw).replace("_", ""), 0)
                        except ValueError:
                            t.ir_type = ir.TOpaque(t.name)
                            return
                    values.append(nxt)
                    nxt += 1
                elif raw in STR_TYPES:
                    values.append(_str_literal(c.raw) if c.raw is not None else c.name)
                else:
                    values.append(c.name)
            if raw in STR_TYPES and any(v is None for v in values):
                t.ir_type = ir.TOpaque(t.name)
                return
            t.ir_type = ir.TEnum(t.name, tuple(c.name for c in t.cases), tuple(values))
            return
        if t.indirect or t.generics:
            t.ir_type = ir.TOpaque(t.name)
            return
        tag = ir.TEnum(f"{t.name}.Case", tuple(c.name for c in t.cases), tuple(c.name for c in t.cases))
        slots: list[tuple[str, ir.Type]] = [("case", tag)]
        for c in t.cases:
            t.payload[c.name] = []
            for i, (label, tn) in enumerate(c.params):
                ty, kind = self.stype(tn, None, {})
                if isinstance(ty, (ir.TList, ir.TDict, ir.TOpaque, ir.TNone)) or isinstance(ty, ir.TOption) and not isinstance(ty.inner, (ir.TInt, ir.TReal, ir.TBool, ir.TStr, ir.TEnum)):
                    t.ir_type = ir.TOpaque(t.name)
                    return
                if isinstance(ty, ir.TRecord) and ty.name == t.name:
                    t.ir_type = ir.TOpaque(t.name)
                    return
                slot = f"{c.name}_{i}"
                t.payload[c.name].append((label, slot, ty, kind))
                slots.append((slot, ty))
        t.ir_type = ir.TRecord(t.name, tuple(slots))
        # every file sees the record
        for f in self.files.values():
            f.module.records[t.name] = t.ir_type

    def _declare_class(self, t: TypeInfo) -> None:
        fields: list[tuple[str, ir.Type]] = []
        for fi in t.fields:
            if fi.tnode is None:
                ty, kind = self._infer_field(fi, t)
            else:
                ty, kind = self.stype(fi.tnode, t.name, {g: ir.TOpaque(g) for g in t.generics})
            if kind:
                t.field_kinds[fi.name] = kind
            fields.append((fi.name, ty))
        bases = [c for c in t.conforms if c in self.types and self.types[c].kind == "protocol" and not self.types[c].open_why]
        decl = ir.ClassDecl(t.name, fields, [], ir.Loc(_line(t.node), t.node.start_point[1]), bases=bases)
        self.files[t.path].module.classes[t.name] = decl
        for f in self.files.values():
            if f.path != t.path:
                f.module.class_origin[t.name] = t.path
        if t.superclass:
            self.files[t.path].module.opaque_subclasses.append((t.name, t.superclass, ir.Loc(_line(t.node))))
            t.open_why = t.open_why or None

    def _infer_field(self, fi: FieldInfo, t: TypeInfo) -> tuple[ir.Type, str | None]:
        v = fi.default
        if v is None:
            return ir.TOpaque(""), None
        k = v.type
        if k in ("integer_literal", "hex_literal", "oct_literal", "bin_literal"):
            return ir.INT, "Int"
        if k == "real_literal":
            return ir.REAL, None
        if k == "boolean_literal":
            return ir.BOOL, None
        if k == "line_string_literal":
            return ir.STR, None
        if k == "prefix_expression" and text(v).startswith("-") and v.child_by_field_name("target") is not None:
            tk = v.child_by_field_name("target").type
            if tk == "integer_literal":
                return ir.INT, "Int"
            if tk == "real_literal":
                return ir.REAL, None
        if k == "call_expression":
            callee = text(named(v)[0]) if named(v) else ""
            if callee in self.types and self.types[callee].ir_type is not None:
                return self.types[callee].ir_type, None
        return ir.TOpaque(""), None

    def stype(self, tn: Any, self_ty: str | None, generics: dict[str, ir.Type]) -> tuple[ir.Type, str | None]:
        """IR type and integer kind of a Swift type node."""
        if tn is None:
            return ir.NONE, None
        k = tn.type
        if k == "user_type":
            name = _base_name(text(tn))
            args = _generic_args(tn)
            if name in self.aliases and not args:
                resolved = self.names(name)
                if len(resolved) != 1:
                    return ir.TOpaque(text(tn)), None
                name = resolved[0]
            if len(tn.named_children) > 1 and "." in text(tn).split("<")[0]:
                pass  # a qualified name: Swift.Int, Foo.Bar
            if name == "Self" and self_ty:
                name = self_ty
            if name in generics:
                return generics[name], None
            if name in INT_KINDS:
                return ir.INT, name
            if name in REAL_TYPES:
                if name in {"Float", "Float32"}:
                    return ir.FLOAT32, None
                if name == "Float80":
                    return ir.TOpaque("Swift Float80 is not IEEE binary32 or binary64"), None
                return ir.REAL, None
            if name == "Bool":
                return ir.BOOL, None
            if name in STR_TYPES:
                return ir.STR, None
            if name == "Void":
                return ir.NONE, None
            if name == "Array" and len(args) == 1:
                return self._list(self.stype(args[0], self_ty, generics), text(tn))
            if name == "Optional" and len(args) == 1:
                return self._opt(self.stype(args[0], self_ty, generics), text(tn))
            if name == "Dictionary" and len(args) == 2:
                return self._dict(self.stype(args[0], self_ty, generics), self.stype(args[1], self_ty, generics), text(tn))
            t = self.types.get(name)
            if t is not None and t.ir_type is not None:
                return t.ir_type, None
            return ir.TOpaque(text(tn)), None
        if k == "array_type":
            inner = tn.child_by_field_name("element") or next((c for c in tn.children if c.is_named), None)
            return self._list(self.stype(inner, self_ty, generics), text(tn))
        if k == "dictionary_type":
            kids = [c for c in tn.children if c.is_named]
            if len(kids) != 2:
                return ir.TOpaque(text(tn)), None
            return self._dict(self.stype(kids[0], self_ty, generics), self.stype(kids[1], self_ty, generics), text(tn))
        if k == "optional_type":
            inner = tn.child_by_field_name("wrapped") or next((c for c in tn.children if c.is_named), None)
            return self._opt(self.stype(inner, self_ty, generics), text(tn))
        if k in ("opaque_type", "existential_type"):
            inner = next((c for c in tn.children if c.is_named), None)
            return self.stype(inner, self_ty, generics)
        if k == "tuple_type" and not any(c.is_named for c in tn.children):
            return ir.NONE, None
        if k == "tuple_type":
            kids = [c for c in tn.children if c.is_named]
            if len(kids) == 1 and kids[0].type == "tuple_type_item":
                inner = [c for c in kids[0].children if c.is_named]
                if len(inner) == 1:
                    return self.stype(inner[0], self_ty, generics)
        return ir.TOpaque(text(tn)), None

    def _list(self, et: tuple[ir.Type, str | None], txt: str) -> tuple[ir.Type, str | None]:
        t, k = et
        if isinstance(t, (ir.TList, ir.TDict, ir.TOption, ir.TNone)):
            return ir.TOpaque(txt), None
        return ir.TList(t), k

    def _opt(self, it: tuple[ir.Type, str | None], txt: str) -> tuple[ir.Type, str | None]:
        t, k = it
        if isinstance(t, (ir.TList, ir.TDict, ir.TOption, ir.TNone, ir.TOpaque)):
            return ir.TOpaque(txt), None
        return ir.TOption(t), k

    def _dict(self, kt: tuple[ir.Type, str | None], vt: tuple[ir.Type, str | None], txt: str) -> tuple[ir.Type, str | None]:
        if isinstance(vt[0], (ir.TList, ir.TDict, ir.TOption, ir.TNone)) or not isinstance(kt[0], (ir.TInt, ir.TStr, ir.TBool, ir.TEnum)):
            return ir.TOpaque(txt), None
        return ir.TDict(kt[0], vt[0]), vt[1]

    # -- members and signatures -------------------------------------------

    def _members(self, t: TypeInfo) -> None:
        if t.kind == "protocol":
            if t.open_why:
                return
            for name, m in t.requirements.items():
                if name.startswith("?"):
                    continue
                if m.type == "protocol_function_declaration":
                    self._signature(m, t.path, t.name, False, kind="requirement")
                else:
                    self._property_requirement(t, name, m)
            for m, path, _ in t.members:
                self._member_fn(t, m, path)
            return
        if t.ir_type is None or isinstance(t.ir_type, ir.TOpaque):
            for m, path, _ in t.members:
                if m.type in ("function_declaration", "init_declaration"):
                    self.files[path].module.notes.append((f"{t.name} is not modelled ({t.open_why or 'unsupported type'}): its members are unchecked", ir.Loc(_line(m))))
                    break
            return
        for m, path, _ in t.members:
            self._member_fn(t, m, path)
        # a stored property that satisfies a protocol requirement: a getter checked against it
        for c in t.conforms:
            p = self.types.get(c)
            if p is None or p.kind != "protocol" or p.open_why:
                continue
            for req, m in p.requirements.items():
                if m.type == "protocol_property_declaration" and any(fi.name == req for fi in t.fields):
                    fi = next(fi for fi in t.fields if fi.name == req)
                    self._field_getter(t, fi)

    def _member_fn(self, t: TypeInfo, m: Any, path: str) -> None:
        if m.type == "function_declaration":
            mods = _modifiers(m)
            if t.kind == "struct" or t.kind == "class" or t.kind == "protocol" or t.kind == "enum":
                if "==" == _fn_name(m) and ("static" in mods):
                    t.custom_eq = True
                self._signature(m, path, t.name, "static" in mods or "class" in mods)
        elif m.type == "init_declaration":
            self._signature(m, path, t.name, True, kind="init")
        elif m.type == "property_declaration":
            self._computed(t, m, path)
        elif m.type == "subscript_declaration":
            self.files[path].module.notes.append((f"subscripts of {t.name} are not modelled: uses are unchecked", ir.Loc(_line(m))))

    def _computed(self, t: TypeInfo, m: Any, path: str) -> None:
        mods = _modifiers(m)
        pat = m.child_by_field_name("name")
        bid = pat.child_by_field_name("bound_identifier") if pat is not None else None
        if bid is None:
            return
        ann = next((ch for ch in m.children if ch.type == "type_annotation"), None)
        tnode = ann.child_by_field_name("name") if ann is not None else None
        computed = m.child_by_field_name("computed_value") or next((ch for ch in m.children if ch.type == "computed_property"), None)
        static = "static" in mods or "class" in mods
        if computed is None:
            if static:
                val = m.child_by_field_name("value")
                is_let = any(ch.type == "value_binding_pattern" and "let" in text(ch) for ch in m.children)
                if is_let and val is not None and val.type in ("integer_literal", "real_literal", "boolean_literal", "line_string_literal"):
                    self.consts[f"{t.name}.{text(bid)}"] = (val, text(tnode) if tnode is not None else "")
                else:
                    self.globals.add(f"{t.name}.{text(bid)}")
            return
        getter = next((ch for ch in computed.children if ch.type == "computed_getter"), None)
        setter = next((ch for ch in computed.children if ch.type in ("computed_setter", "computed_modify")), None)
        body = next((ch for ch in (getter or computed).children if ch.type == "statements"), None)
        if tnode is None:
            return
        generics = {g: ir.TOpaque(g) for g in t.generics}
        ret, rk = self.stype(tnode, t.name, generics)
        params = [] if static else [ir.Param("self", self.self_type(t))]
        key = f"{t.name}.{text(bid)}"
        info = FnInfo(key, text(bid), m, path, t.name, static, False, params, [], [], ret, rk if ret == ir.INT or isinstance(ret, ir.TOption) else None, {}, {}, set(), False, kind="getter", body=body, exported=_exported(m), generics=generics)
        if body is None and getter is None and not any(ch.type == "statements" for ch in computed.children):
            info.body = None
        self._add(info)
        if setter is not None:
            self.files[path].module.notes.append((f"the setter of {key} is not modelled: assignments to it are unchecked", ir.Loc(_line(setter))))

    def _property_requirement(self, t: TypeInfo, name: str, m: Any) -> None:
        ann = next((ch for ch in m.children if ch.type == "type_annotation"), None)
        tnode = ann.child_by_field_name("name") if ann is not None else None
        if tnode is None and ann is not None:
            tnode = next((ch for ch in ann.children if ch.is_named), None)
        ret, rk = self.stype(tnode, t.name, {})
        static = "static" in _modifiers(m)
        params = [] if static else [ir.Param("self", ir.TClass(t.name))]
        info = FnInfo(f"{t.name}.{name}", name, m, t.path, t.name, static, False, params, [], [], ret, rk if ret == ir.INT or isinstance(ret, ir.TOption) else None, {}, {}, set(), False, kind="requirement", exported=True)
        self._add(info)

    def _field_getter(self, t: TypeInfo, fi: FieldInfo) -> None:
        key = f"{t.name}.{fi.name}"
        if key in self.by_name:
            return
        ty = dict(self.files[t.path].module.classes[t.name].fields)[fi.name] if t.name in self.files[t.path].module.classes else ir.TOpaque("")
        k = t.field_kinds.get(fi.name)
        info = FnInfo(key, fi.name, fi.node, t.path, t.name, False, False, [ir.Param("self", self.self_type(t))], [], [], ty, k if ty == ir.INT or isinstance(ty, ir.TOption) else None, {}, {}, set(), False, kind="field-getter", exported=_exported(fi.node))
        info.field_name = fi.name
        self._add(info)

    def self_type(self, t: TypeInfo) -> ir.Type:
        return t.ir_type if t.ir_type is not None else ir.TOpaque(t.name)

    def _signature(self, f: Any, path: str, owner: str | None, static: bool, kind: str | None = None) -> None:
        t = self.types.get(owner) if owner else None
        is_init = f.type == "init_declaration"
        kind = kind or ("init" if is_init else "func")
        name = "init" if is_init else _fn_name(f)
        if name is None:
            return
        mods = _modifiers(f)
        generics: dict[str, ir.Type] = {g: ir.TOpaque(g) for g in (t.generics if t else [])}
        for tp in (c for ch in f.children if ch.type == "type_parameters" for c in ch.children if c.type == "type_parameter"):
            gname = text(tp.children[0])
            cons = [c for c in tp.children[1:] if c.is_named]
            gt: ir.Type = ir.TOpaque(gname)
            if len(cons) == 1:
                p = self.types.get(_base_name(text(cons[0])))
                if p is not None and p.kind == "protocol" and not p.open_why:
                    gt = ir.TClass(p.name)
            generics[gname] = gt
        if any(ch.type == "type_constraints" for ch in f.children):
            generics = {g: ir.TOpaque(g) for g in generics}  # 'where' clauses: stay opaque
        params: list[ir.Param] = []
        labels: list[str | None] = []
        defaults: list[Any] = []
        kinds: dict[str, str] = {}
        ekinds: dict[str, str] = {}
        inout: set[str] = set()
        mutating = "mutating" in mods
        if owner and not static and kind != "init":
            if t is not None and t.kind == "enum" and mutating:
                self.files[path].module.notes.append((f"mutating methods of enum {owner} are not modelled", ir.Loc(_line(f))))
                return
            params.append(ir.Param("self", self.self_type(t) if t else ir.TOpaque(owner)))
        problems: list[tuple[str, int]] = []
        children = list(f.children)
        for i, p in enumerate(children):
            if p.type != "parameter":
                continue
            ext = p.child_by_field_name("external_name")
            pn = p.child_by_field_name("name")
            if pn is None:
                continue
            pname = text(pn)
            label = text(ext) if ext is not None else pname
            tnode = [c for c in p.children if c.is_named and c.type not in ("simple_identifier", "parameter_modifiers")]
            mods_p = next((c for c in p.children if c.type == "parameter_modifiers"), None)
            is_inout = mods_p is not None and "inout" in text(mods_p)
            ty, k = self.stype(tnode[-1] if tnode else None, owner, generics)
            if any(c.type == "..." for c in p.children) or text(p).rstrip().endswith("..."):
                ty, k = ir.TOpaque("variadic"), None
            if is_inout:
                inout.add(pname)
                if not isinstance(ty, (ir.TList, ir.TDict, ir.TClass, ir.TOpaque)):
                    problems.append((f"inout parameter '{pname}' of type {ty} is not modelled", _line(p)))
                    ty, k = ir.TOpaque(f"inout {ty}"), None
                elif isinstance(ty, ir.TClass) and self.types.get(ty.name) is not None and self.types[ty.name].kind == "protocol":
                    problems.append((f"inout parameter '{pname}' of protocol type is not modelled", _line(p)))
            if k and ty == ir.INT:
                kinds[pname] = k
            elif k and isinstance(ty, (ir.TList, ir.TDict)):
                ekinds[pname] = k
            elif k and isinstance(ty, ir.TOption):
                kinds[pname] = k
            nxt = children[i + 2] if i + 2 < len(children) and i + 1 < len(children) and children[i + 1].type == "=" else None
            defaults.append(nxt)
            labels.append(None if label == "_" or not re.fullmatch(r"\w+", name) else label)  # operators take no labels
            params.append(ir.Param(pname, ty))
        throws = any(c.type == "throws" or text(c) in ("throws", "rethrows") for c in f.children if c.type in ("throws", "rethrows") or not c.is_named and text(c) in ("throws", "rethrows"))
        body_n = f.child_by_field_name("body")
        body = next((c for c in body_n.children if c.type == "statements"), None) if body_n is not None else None
        failable = False
        if kind == "init":
            failable = any(c.type == "?" or text(c) == "?" for c in f.children[:3] if not c.is_named) or text(f).lstrip().startswith(("init?", "public init?", "convenience init?"))
            if t is None:
                return
            ret: ir.Type = self.self_type(t)
            if failable and not isinstance(ret, ir.TOpaque):
                ret = ir.TOption(ret)
            rk = None
        else:
            rt = _return_type(f)
            ret, rk = self.stype(rt, owner, generics) if rt is not None else (ir.NONE, None)
        info = FnInfo("", name, f, path, owner, static, mutating, params, labels, defaults, ret, rk if ret == ir.INT or isinstance(ret, ir.TOption) else None, kinds, ekinds, inout, throws, kind=kind, failable=failable, body=body, exported=_exported(f), generics=generics)
        info.problems = problems
        if body_n is not None and body is None:
            info.body = body_n  # an empty body
        self._add(info)

    def _add(self, info: FnInfo) -> None:
        base = f"{info.owner}.{info.name}" if info.owner else info.name
        info.key = base
        self.by_name.setdefault(base, []).append(info)

    def _keys(self) -> None:
        """Function keys: 'Type.name', or with argument labels when overloaded.
        A default implementation of a protocol requirement is the
        requirement's key with '$default'."""
        for base, all_infos in self.by_name.items():
            reqs = [i for i in all_infos if i.kind == "requirement"]
            defaults = [i for i in all_infos if i.kind != "requirement" and any(r.labels == i.labels for r in reqs)]
            infos = [i for i in all_infos if i not in defaults]
            if len(infos) == 1:
                infos[0].key = base
            else:
                seen: dict[str, int] = {}
                for i in infos:
                    k = base + "(" + "".join(f"{lbl or '_'}:" for lbl in i.labels) + ")"
                    if k in seen:
                        seen[k] += 1
                        k = f"{k}#{seen[k]}"
                    else:
                        seen[k] = 1
                    i.key = k
            for d in defaults:
                req = next(r for r in reqs if r.labels == d.labels)
                d.key = f"{req.key}$default"
                d.alias_of = req.key
                d.inherit = req
            for i in all_infos:
                self.fns[i.key] = i

    def _protocols(self) -> None:
        """A conformer's implementation of a requirement is checked against the
        requirement's contract. A default implementation (in a protocol
        extension) that a conformer replaces is not what every call through
        the protocol runs: calls through the protocol use the requirement."""
        for t in self.types.values():
            if t.kind == "protocol" or t.ir_type is None or isinstance(t.ir_type, ir.TOpaque):
                continue
            for c in t.conforms:
                p = self.types.get(c)
                if p is None or p.kind != "protocol" or p.open_why:
                    continue
                for req in p.requirements:
                    reqs = [i for i in self.by_name.get(f"{p.name}.{req}", []) if i.kind == "requirement"]
                    if not reqs:
                        continue
                    for impl in self.by_name.get(f"{t.name}.{req}", []):
                        if impl.labels == reqs[0].labels or impl.kind in ("getter", "field-getter"):
                            impl.inherit = reqs[0]

    def invariant_lines(self, t: TypeInfo) -> list[ContractLine]:
        """The '@invariant' lines in a type's body (outside its members)."""
        f = self.files[t.path]
        body = t.node.child_by_field_name("body")
        if body is None:
            return []
        lo, hi = _line(body), body.end_point[0] + 1
        inside = [(_line(m), m.end_point[0] + 1) for m in named(body) if m.type in ("function_declaration", "init_declaration", "property_declaration", "subscript_declaration")]
        return [cl for cl in f.contracts if cl.keyword == "invariant" and lo <= cl.line <= hi and not any(a <= cl.line <= b for a, b in inside)]

    def _invariants(self, t: TypeInfo) -> None:
        if t.kind not in ("struct", "class") or t.ir_type is None or not isinstance(t.ir_type, ir.TClass):
            return
        f = self.files[t.path]
        decl = f.module.classes[t.name]
        from .swift_lower import FunctionLowerer

        for cl in self.invariant_lines(t):
            if cl.consumed:
                continue
            cl.consumed = True
            info = FnInfo(f"{t.name}.invariant", "invariant", t.node, t.path, t.name, False, False, [ir.Param("self", ir.TClass(t.name))], [], [], ir.BOOL, None, {}, {}, set(), False)
            try:
                c = FunctionLowerer(self, info).invariant(cl)
            except (LowerError, ContractSyntaxError) as e:
                f.module.problems.append((f"invariant: {e}", ir.Loc(getattr(e, "line", cl.line) or cl.line)))
                continue
            except Unsupported as e:
                f.module.problems.append((f"invariant: {e}", ir.Loc(cl.line)))
                continue
            decl.invariants.append(c)

    # -- lookups used by the lowering -------------------------------------

    def lookup_fn(self, base: str, labels: list[str | None]) -> FnInfo | None:
        infos = self.by_name.get(base)
        if not infos:
            return None
        fits = [i for i in infos if _labels_fit(i, labels)]
        if len(fits) == 1:
            return fits[0]
        return None

    def member_fn(self, tname: str, meth: str, labels: list[str | None]) -> FnInfo | None:
        """A method of a type: its own, else a protocol's (a default
        implementation or the requirement)."""
        seen: set[str] = set()
        todo = [tname]
        while todo:
            n = todo.pop(0)
            if n in seen:
                continue
            seen.add(n)
            infos = [i for i in self.by_name.get(f"{n}.{meth}", []) if i.kind != "init"]
            fits = [i for i in infos if _labels_fit(i, labels)]
            if fits:
                own = [i for i in fits if i.kind != "requirement"]
                if n == tname or self.types.get(tname) is None or self.types[tname].kind == "protocol":
                    pick = [i for i in fits if i.kind == "requirement"] or own
                    if self.types.get(n) is not None and self.types[n].kind != "protocol":
                        pick = own or fits
                    return pick[0] if len(pick) == 1 else None
                return (own[0] if len(own) == 1 else None) if own else fits[0]
            t = self.types.get(n)
            if t is not None:
                todo.extend(c for c in t.conforms if c in self.types)
        return None


def _labels_fit(info: FnInfo, labels: list[str | None]) -> bool:
    """Do call-site labels match the parameters (skipping defaulted ones)?"""
    i = 0
    for want, dflt in zip(info.labels, info.defaults):
        if i < len(labels) and labels[i] == want:
            i += 1
            continue
        if dflt is not None:
            continue
        return False
    return i == len(labels)


def _fn_name(f: Any) -> str | None:
    n = f.child_by_field_name("name")
    if n is None:
        return None
    if n.type in ("simple_identifier",):
        return text(n)
    t = text(n)
    return t if re.fullmatch(r"[^\s(]+", t) else None


def _return_type(f: Any) -> Any:
    """The node after '->' in a function declaration."""
    kids = list(f.children)
    for i, c in enumerate(kids):
        if c.type == "->" and i + 1 < len(kids):
            return kids[i + 1]
    return None


def _case_params(n: Any) -> list[tuple[str | None, Any]]:
    out: list[tuple[str | None, Any]] = []
    label = None
    for c in n.children:
        if c.type == "simple_identifier":
            label = text(c)
        elif c.is_named and c.type not in ("simple_identifier",):
            out.append((label, c))
            label = None
    return out


def _str_literal(n: Any) -> str | None:
    if n is None or n.type != "line_string_literal":
        return None
    parts = [text(c) for c in n.children if c.type == "line_str_text"]
    if any(c.type not in ("line_str_text", '"') for c in n.children):
        return None
    return "".join(parts)


def _exported(n: Any) -> bool:
    mods = _modifiers(n)
    return bool(mods & {"public", "open"})


def _first_error(n: Any) -> Any:
    if n.type == "ERROR" or n.is_missing:
        return n
    for c in n.children:
        if c.has_error:
            e = _first_error(c)
            if e is not None:
                return e
    return None


def _collect_comments(n: Any, out: list) -> None:
    if n.type == "comment":
        out.append((n.start_point[0] + 1, n.start_point[1], text(n).rstrip("\n")))
        return
    for c in n.children:
        _collect_comments(c, out)


def lower_swift_files(paths: list[str], root: str) -> dict[str, ir.Module]:
    """Lower every Swift file of a run together (one Swift module)."""
    files = []
    for p in paths:
        with open(p, encoding="utf8") as fh:
            files.append((os.path.relpath(p, root), fh.read()))
    mods = Project(files).run()
    return {p: mods[os.path.relpath(p, root)] for p in paths}


def lower_swift(path: str, source: str) -> ir.Module:
    return Project([(path, source)]).run()[path]
