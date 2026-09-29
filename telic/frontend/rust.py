"""Rust frontend: lowers Rust source (parsed with tree-sitter) to the IR.

What Rust makes checkable, telic checks: every arithmetic operation on a
fixed-width integer must not overflow (debug builds panic), indexing must be
in bounds, ``unwrap``/``expect`` must see ``Some``, and ``panic!``,
``unreachable!`` and ``assert!`` must be unreachable or hold. Values of an
integer type are known to lie in its range (the type system guarantees it,
so this is a fact, not an assumption).

Ownership keeps the model simple: a ``Vec`` is a list value, a non-``Copy``
struct is an object (a move copies the reference, and the moved-from name is
dead, so no alias survives), a ``Copy`` struct of scalars is a record value.
``&mut`` to a local list is an alias the frontend resolves to the list
itself. What is not modelled becomes an unchecked value or call, with the
reason, never a silent guess.

Contracts are ``//@`` comments whose payload is a Rust expression; in them
arithmetic is mathematical (no overflow), ``result`` is the return value,
``old(e)`` is ``e`` at entry, and quantifiers are written as Rust iterators:
``(0..n).all(|i| ...)``, ``xs.iter().any(|x| ...)``.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from fractions import Fraction
from typing import Any, Callable

from .. import ir
from ..contracts import (
    FUNCTION_KEYWORDS,
    LOOP_KEYWORDS,
    STATEMENT_KEYWORDS,
    ContractLine,
    ContractSyntaxError,
    parse_comment_lines,
    parse_intent_directive,
)

RUST_ASSUMPTIONS = [
    "f32/f64 are modelled as exact rational arithmetic (rounding, NaN and infinities ignored)",
    "integer overflow panics (debug build semantics); release builds wrap instead",
    "println!/eprintln!/dbg! and logging have no effect on program state",
]

INT_KINDS = {
    "i8": (True, 8), "i16": (True, 16), "i32": (True, 32), "i64": (True, 64), "i128": (True, 128), "isize": (True, 64),
    "u8": (False, 8), "u16": (False, 16), "u32": (False, 32), "u64": (False, 64), "u128": (False, 128), "usize": (False, 64),
}


def int_range(kind: str) -> tuple[int, int]:
    signed, bits = INT_KINDS[kind]
    return (-(1 << (bits - 1)), (1 << (bits - 1)) - 1) if signed else (0, (1 << bits) - 1)


class LowerError(Exception):
    def __init__(self, msg: str, line: int = 0):
        super().__init__(msg)
        self.line = line


class RustUnavailable(Exception):
    pass


_PARSER: Any = None


def parser() -> Any:
    global _PARSER
    if _PARSER is None:
        try:
            import tree_sitter
            import tree_sitter_rust
        except ImportError as e:  # pragma: no cover - depends on the install
            raise RustUnavailable("Rust support needs the 'tree-sitter' and 'tree-sitter-rust' packages (pip install 'telic[rust]')") from e
        _PARSER = tree_sitter.Parser(tree_sitter.Language(tree_sitter_rust.language()))
    return _PARSER


def _named(n: Any) -> list[Any]:
    return [c for c in n.children if c.is_named and c.type not in ("line_comment", "block_comment")]


def _text(n: Any) -> str:
    return n.text.decode("utf8")


@dataclass
class StructInfo:
    name: str
    fields: list[tuple[str, str, Any]]  # (name, rust type text, type node)
    copy: bool
    node: Any
    record: bool = False  # a Copy struct of scalars: a value
    kinds: dict[str, str] = field(default_factory=dict)  # field -> integer kind


@dataclass
class FnInfo:
    key: str  # "name" or "Type.name"
    node: Any
    params: list[ir.Param]
    ret: ir.Type
    ret_kind: str | None
    param_kinds: dict[str, str]  # integer parameters -> kind
    self_mode: str | None  # None | "ref" | "mut" | "value"
    owner: str | None
    mut_params: set[str]
    elem_kinds: dict[str, str] = field(default_factory=dict)  # Vec/slice parameters -> element kind


class RustFrontend:
    def __init__(self, path: str, source: str):
        self.path = path
        self.source = source
        self.lines = source.splitlines()
        self.module = ir.Module(path=path, language="rust", source=source)
        self.module.assumptions = list(RUST_ASSUMPTIONS)
        self.structs: dict[str, StructInfo] = {}
        self.enums: dict[str, ir.TEnum] = {}
        self.consts: dict[str, tuple[Any, str | None]] = {}  # name -> (literal node, int kind)
        self.fns: dict[str, FnInfo] = {}
        self.contract_lines: list[ContractLine] = []

    # -- entry ----------------------------------------------------------

    def run(self) -> ir.Module:
        tree = parser().parse(self.source.encode("utf8"))
        root = tree.root_node
        if root.has_error:
            bad = _first_error(root)
            self.module.problems.append(("syntax error (or Rust syntax telic's parser does not know)", ir.Loc(bad.start_point[0] + 1 if bad else 1)))
        comments = []
        self._collect_comments(root, comments)
        try:
            self.contract_lines = parse_comment_lines(comments, "//")
        except ContractSyntaxError as e:
            self.module.problems.append((str(e), ir.Loc(e.line, e.col)))
            return self.module
        items = self._items(root)
        # types first, then signatures, then bodies: calls may be forward
        for it, attrs in items:
            if it.type == "struct_item":
                self._struct(it, attrs)
            elif it.type == "enum_item":
                self._enum(it)
            elif it.type == "const_item":
                self._const(it)
        mutating_impls: set[str] = set()
        for it, _ in items:
            if it.type == "impl_item":
                owner = self._impl_owner(it)
                for f in self._impl_fns(it):
                    sp = f.child_by_field_name("parameters")
                    if sp is not None and any(c.type == "self_parameter" and "mut" in _text(c) and "&" in _text(c) for c in sp.children):
                        mutating_impls.add(owner or "")
        for s in self.structs.values():
            scalar = all(self.rtype(tn, s.name)[0] in (ir.INT, ir.REAL, ir.BOOL, ir.STR) or isinstance(self.rtype(tn, s.name)[0], ir.TEnum) for _, _, tn in s.fields)
            s.record = s.copy and scalar and s.name not in mutating_impls
        for s in self.structs.values():
            self._declare_struct(s)
        for it, _ in items:
            if it.type == "function_item":
                self._signature(it, None)
            elif it.type == "impl_item":
                owner = self._impl_owner(it)
                if owner is None:
                    self.module.notes.append(("impl of a type telic does not model: its methods are unchecked", ir.Loc(it.start_point[0] + 1)))
                    continue
                for f in self._impl_fns(it):
                    self._signature(f, owner)
        for key, info in self.fns.items():
            try:
                fn = FunctionLowerer(self, info).lower()
            except LowerError as e:
                fn = self._stub(info, str(e), e.line)
            except Exception as e:  # noqa: BLE001 - a telic bug leaves one function unchecked, with the reason
                fn = self._stub(info, f"telic could not model this function ({type(e).__name__}: {e}); please report it", info.node.start_point[0] + 1)
            self.module.functions[key] = fn
        for cl in self.contract_lines:
            if cl.consumed:
                continue
            if cl.keyword == "intent":
                try:
                    ids, text = parse_intent_directive(cl)
                except ContractSyntaxError as e:
                    self.module.problems.append((str(e), ir.Loc(e.line, e.col)))
                    continue
                if text is not None:
                    self.module.intents.append(ir.IntentDecl(ids[0], text, ir.Loc(cl.line, cl.col)))
                else:
                    self.module.problems.append((f"'@intent {', '.join(ids)}' outside a function links nothing", ir.Loc(cl.line, cl.col)))
                continue
            self.module.problems.append((f"'@{cl.keyword}' is not attached to anything telic checks", ir.Loc(cl.line, cl.col)))
        return self.module

    def _stub(self, info: FnInfo, msg: str, line: int) -> ir.Function:
        n = info.node
        fn = ir.Function(info.key, ir.Loc(n.start_point[0] + 1, n.start_point[1]), n.end_point[0] + 1, info.params, info.ret, source=_text(n))
        fn.unsupported.append((msg, ir.Loc(line or n.start_point[0] + 1)))
        return fn

    def _collect_comments(self, n: Any, out: list) -> None:
        if n.type == "line_comment":
            out.append((n.start_point[0] + 1, n.start_point[1], _text(n).rstrip("\n")))
            return
        for c in n.children:
            self._collect_comments(c, out)

    def _items(self, root: Any) -> list[tuple[Any, list[str]]]:
        """Top-level items (also inside inline 'mod m { ... }'), with their attributes."""
        out: list[tuple[Any, list[str]]] = []

        def walk(container: Any) -> None:
            attrs: list[str] = []
            for c in container.children:
                if c.type == "attribute_item":
                    attrs.append(_text(c))
                    continue
                if c.type == "mod_item":
                    body = c.child_by_field_name("body")
                    if body is not None:
                        walk(body)
                    attrs = []
                    continue
                if c.type in ("line_comment", "block_comment"):
                    continue
                if c.is_named:
                    if not any("cfg(test)" in a for a in attrs):
                        out.append((c, attrs))
                    attrs = []

        walk(root)
        return out

    def _impl_owner(self, it: Any) -> str | None:
        t = it.child_by_field_name("type")
        name = _text(t).split("<")[0].strip() if t is not None else ""
        return name if name in self.structs else None

    def _impl_fns(self, it: Any) -> list[Any]:
        body = it.child_by_field_name("body")
        return [c for c in body.children if c.type == "function_item"] if body is not None else []

    # -- declarations ---------------------------------------------------

    def _struct(self, it: Any, attrs: list[str]) -> None:
        name = _text(it.child_by_field_name("name"))
        body = it.child_by_field_name("body")
        copy = any(re.search(r"\bCopy\b", a) for a in attrs if "derive" in a)
        fields: list[tuple[str, str, Any]] = []
        if body is None or body.type != "field_declaration_list":
            if body is not None:
                self.module.notes.append((f"struct {name}: tuple structs are not modelled yet; its values are unchecked", ir.Loc(it.start_point[0] + 1)))
                return
        else:
            for fd in body.children:
                if fd.type == "field_declaration":
                    fields.append((_text(fd.child_by_field_name("name")), _text(fd.child_by_field_name("type")), fd.child_by_field_name("type")))
        self.structs[name] = StructInfo(name, fields, copy, it)

    def _declare_struct(self, s: StructInfo) -> None:
        typed = []
        for fname, _, tn in s.fields:
            t, kind = self.rtype(tn, s.name)
            if kind:
                s.kinds[fname] = kind
            typed.append((fname, t))
        if s.record:
            self.module.records[s.name] = ir.TRecord(s.name, tuple(typed))
        else:
            self.module.classes[s.name] = ir.ClassDecl(s.name, [(f, t) for f, t in typed], [], ir.Loc(s.node.start_point[0] + 1, s.node.start_point[1]))

    def _enum(self, it: Any) -> None:
        name = _text(it.child_by_field_name("name"))
        body = it.child_by_field_name("body")
        members = []
        for v in body.children if body is not None else []:
            if v.type == "enum_variant":
                if v.child_by_field_name("body") is not None:
                    self.module.notes.append((f"enum {name}: variants with data are not modelled yet; its values are unchecked", ir.Loc(it.start_point[0] + 1)))
                    return
                members.append(_text(v.child_by_field_name("name")))
        self.enums[name] = ir.TEnum(name, tuple(members), tuple(members))

    def _const(self, it: Any) -> None:
        name = _text(it.child_by_field_name("name"))
        val = it.child_by_field_name("value")
        t = it.child_by_field_name("type")
        kind = _text(t) if t is not None and _text(t) in INT_KINDS else None
        if val is not None and val.type in ("integer_literal", "float_literal", "boolean_literal", "string_literal"):
            self.consts[name] = (val, kind)

    def rtype(self, tn: Any, self_ty: str | None = None) -> tuple[ir.Type, str | None]:
        """IR type and integer kind of a Rust type node."""
        if tn is None:
            return ir.NONE, None
        k = tn.type
        txt = _text(tn)
        if k == "primitive_type":
            if txt in INT_KINDS:
                return ir.INT, txt
            if txt in ("f32", "f64"):
                return ir.REAL, None
            if txt == "bool":
                return ir.BOOL, None
            if txt in ("str", "char"):
                return ir.STR, None
            return ir.TOpaque(txt), None
        if k == "unit_type":
            return ir.NONE, None
        if k == "reference_type":
            return self.rtype(tn.child_by_field_name("type"), self_ty)
        if k in ("type_identifier", "scoped_type_identifier"):
            name = txt.split("::")[-1]
            if name == "Self" and self_ty:
                name = self_ty
            if name == "String":
                return ir.STR, None
            if name in self.structs:
                s = self.structs[name]
                return (ir.TRecord(name, ()) if s.record else ir.TClass(name)), None  # records are completed by _resolve_record
            if name in self.enums:
                return self.enums[name], None
            return ir.TOpaque(txt), None
        if k == "generic_type":
            base = _text(tn.child_by_field_name("type")).split("::")[-1]
            targs = [c for c in tn.child_by_field_name("type_arguments").children if c.is_named] if tn.child_by_field_name("type_arguments") is not None else []
            if base in ("Vec", "VecDeque") and len(targs) == 1:
                et, ek = self.rtype(targs[0], self_ty)
                if isinstance(et, (ir.TList, ir.TDict, ir.TOption, ir.TNone)):
                    return ir.TOpaque(txt), None
                return ir.TList(self._resolve_record(et)), ek
            if base == "Option" and len(targs) == 1:
                it, ik = self.rtype(targs[0], self_ty)
                if isinstance(it, (ir.TList, ir.TDict, ir.TOption, ir.TNone)):
                    return ir.TOpaque(txt), None
                return ir.TOption(self._resolve_record(it)), ik
            if base in ("HashMap", "BTreeMap") and len(targs) == 2:
                kt, _ = self.rtype(targs[0], self_ty)
                vt, vk = self.rtype(targs[1], self_ty)
                if isinstance(vt, (ir.TList, ir.TDict, ir.TOption)) or not isinstance(kt, (ir.TInt, ir.TStr, ir.TBool, ir.TEnum)):
                    return ir.TOpaque(txt), None
                return ir.TDict(kt, self._resolve_record(vt)), vk  # (the kind of a map is its values')
            if base in ("Box", "Rc", "Arc", "Cow") and len(targs) == 1:
                return self.rtype(targs[0], self_ty)
            return ir.TOpaque(txt), None
        if k in ("array_type", "slice_type"):
            et, ek = self.rtype(tn.child_by_field_name("element"), self_ty)
            if isinstance(et, (ir.TList, ir.TDict, ir.TOption, ir.TNone)):
                return ir.TOpaque(txt), None
            return ir.TList(self._resolve_record(et)), ek
        return ir.TOpaque(txt), None

    def _resolve_record(self, t: ir.Type) -> ir.Type:
        if isinstance(t, ir.TRecord) and not t.fields and t.name in self.module.records:
            return self.module.records[t.name]
        return t

    def ty(self, tn: Any, self_ty: str | None = None) -> tuple[ir.Type, str | None]:
        t, k = self.rtype(tn, self_ty)
        return self._resolve_record(t), k

    def _signature(self, f: Any, owner: str | None) -> None:
        name = _text(f.child_by_field_name("name"))
        key = f"{owner}.{name}" if owner else name
        params: list[ir.Param] = []
        kinds: dict[str, str] = {}
        ekinds: dict[str, str] = {}
        mut_params: set[str] = set()
        self_mode = None
        ps = f.child_by_field_name("parameters")
        for p in ps.children if ps is not None else []:
            if p.type == "self_parameter":
                t = _text(p)
                self_mode = "mut" if "&" in t and "mut" in t else "ref" if "&" in t else "value"
                assert owner is not None
                params.append(ir.Param("self", self._resolve_record(ir.TRecord(owner, ()) if self.structs[owner].record else ir.TClass(owner))))
                if self_mode == "mut":
                    mut_params.add("self")
            elif p.type == "parameter":
                pat = p.child_by_field_name("pattern")
                pname = _text(pat).replace("mut ", "").strip()
                if not re.fullmatch(r"[A-Za-z_]\w*", pname):
                    pname = f"arg${len(params)}"
                tn = p.child_by_field_name("type")
                t, k = self.ty(tn, owner)
                if tn is not None and tn.type == "reference_type" and "mut" in _text(tn).split(">")[0]:
                    mut_params.add(pname)
                    if not isinstance(t, (ir.TList, ir.TDict, ir.TClass, ir.TOpaque)):
                        t, k = ir.TOpaque(f"&mut {_text(tn.child_by_field_name('type'))}"), None  # a mutable reference to a scalar: not modelled
                if k and t == ir.INT:
                    kinds[pname] = k
                elif k and isinstance(t, (ir.TList, ir.TDict)):
                    ekinds[pname] = k
                params.append(ir.Param(pname, t))
        rt = f.child_by_field_name("return_type")
        ret, rk = self.ty(rt, owner) if rt is not None else (ir.NONE, None)
        self.fns[key] = FnInfo(key, f, params, ret, rk if ret == ir.INT or isinstance(ret, ir.TOption) else None, kinds, self_mode, owner, mut_params, ekinds)


def _first_error(n: Any) -> Any:
    if n.type == "ERROR" or n.is_missing:
        return n
    for c in n.children:
        if c.has_error:
            e = _first_error(c)
            if e is not None:
                return e
    return None


# ---------------------------------------------------------------------------
# Functions


class FunctionLowerer:
    def __init__(self, fe: RustFrontend, info: FnInfo):
        self.fe = fe
        self.info = info
        self.node = info.node
        self.env: dict[str, ir.Type] = {p.name: p.ty for p in info.params}
        self.kinds: dict[str, str] = dict(info.param_kinds)  # integer (and Option<integer>) variables -> kind
        self.elem_kinds: dict[str, str] = dict(info.elem_kinds)  # list variables -> element kind
        self.aliases: dict[str, str] = {}  # let r = &mut v  ->  r means v
        self.scopes: list[dict[str, str]] = [{p.name: p.name for p in info.params}]  # source name -> IR name
        self.used: set[str] = {p.name for p in info.params}
        self.tmp = 0
        self.intents: list[str] = []
        lo, hi = self.node.start_point[0] + 1, self.node.end_point[0] + 1
        self.local_contracts = [cl for cl in fe.contract_lines if lo <= cl.line <= hi]
        self.loop_value: list[str | None] = []  # target of 'break value' per enclosing loop
        self.range_after: list[ir.Stmt] = []
        self.escaped: set[str] = set()

    # -- entry ----------------------------------------------------------

    def lower(self) -> ir.Function:
        n = self.node
        info = self.info
        body = n.child_by_field_name("body")
        self.fn = ir.Function(
            info.key,
            ir.Loc(n.start_point[0] + 1, n.start_point[1]),
            n.end_point[0] + 1,
            info.params,
            info.ret,
            source=_text(n),
            exported=_text(n).lstrip().startswith("pub"),
        )
        for cl in self._header_contracts(body):
            cl.consumed = True
            try:
                self._function_contract(cl)
            except (LowerError, ContractSyntaxError) as e:
                self.fn.unsupported.append((f"contract: {e}", ir.Loc(getattr(e, "line", cl.line) or cl.line)))
        if body is None:
            self.fn.trusted = True  # a declaration without a body (trait/extern): its contract is what callers use
            return self.fn
        stmts: list[ir.Stmt] = []
        for p in info.params:
            k = self.kinds.get(p.name)
            if k:
                stmts.append(ir.ExprStmt(self.fn.loc, self.in_range(ir.Var(ir.INT, self.fn.loc, p.name), k)))
        out = self.block_value(body, stmts, info.ret, info.ret_kind)
        if out is not None and info.ret != ir.NONE:
            stmts.append(ir.Return(out.loc, self.coerce(out, info.ret)))
        elif out is not None:
            stmts.append(ir.ExprStmt(out.loc, out))
        self.fn.body = stmts
        self.fn.locals = dict(self.env)
        self.fn.escaped = set(self.escaped)
        self.fn.intents = self.intents + [i for i in self.fn.intents if i not in self.intents]
        return self.fn

    def err(self, msg: str, node: Any) -> LowerError:
        return LowerError(msg, node.start_point[0] + 1 if node is not None else 0)

    def loc(self, n: Any) -> ir.Loc:
        (l1, c1), (l2, c2) = n.start_point, n.end_point
        return ir.Loc(l1 + 1, c1, c2 if l1 == l2 else 0)

    def fresh(self, base: str, ty: ir.Type) -> str:
        self.tmp += 1
        name = f"{base}${self.tmp}"
        self.env[name] = ty
        return name

    # -- contracts ------------------------------------------------------

    def _header_contracts(self, body: Any) -> list[ContractLine]:
        start = self.node.start_point[0] + 1
        by_line = {l: cl for cl in self.fe.contract_lines for l in cl.raw_lines}
        above: list[ContractLine] = []
        ln = start - 1
        while ln >= 1:
            t = self.fe.lines[ln - 1].strip()
            if not (t.startswith("//") or t.startswith("#[")):
                break
            cl = by_line.get(ln)
            if cl is not None and cl.keyword in FUNCTION_KEYWORDS and not cl.consumed and cl not in above:
                above.append(cl)
            ln -= 1
        above.reverse()
        if body is not None:
            first = next((c for c in body.children if c.is_named and c.type not in ("line_comment", "block_comment")), None)
            limit = first.start_point[0] + 1 if first is not None else body.end_point[0] + 1
            above += [cl for cl in self.local_contracts if body.start_point[0] + 1 <= cl.line < limit and cl.keyword in FUNCTION_KEYWORDS and not cl.consumed and cl not in above]
        return above

    def _function_contract(self, cl: ContractLine) -> None:
        kw = cl.keyword
        if kw == "intent":
            ids, text = parse_intent_directive(cl)
            if text is not None:
                self.fe.module.intents.append(ir.IntentDecl(ids[0], text, ir.Loc(cl.line, cl.col)))
            for i in ids:
                if i not in self.intents:
                    self.intents.append(i)
            self.current_intents = ids
            return
        if kw == "mirrors":
            self.fn.mirrors.append((cl.payload.strip(), ir.Loc(cl.line, cl.col)))
            return
        if kw == "trusted":
            self.fn.trusted = True
            return
        if kw == "pure":
            return
        tags = tuple(cl.tags) or tuple(getattr(self, "current_intents", ()))
        for t in tags:
            if t not in self.intents:
                self.intents.append(t)
        if kw == "requires":
            self.fn.requires.append(self.clause(cl, "requires", tags))
        elif kw == "ensures":
            self.fn.ensures.append(self.clause(cl, "ensures", tags))
        elif kw == "decreases":
            self.fn.decreases = self.clause(cl, "decreases", tags, expect=ir.INT)
        elif kw == "raises":
            self.fn.raises.append(self.clause(cl, "raises", tags))

    def clause(self, cl: ContractLine, kind: str, tags: tuple[str, ...] = (), expect: ir.Type = ir.BOOL) -> ir.Clause:
        text = cl.payload
        if not text:
            raise LowerError(f"empty '@{kind}'", cl.line)
        src = "fn __telic() {\n(" + text + "\n);\n}"
        tree = parser().parse(src.encode("utf8"))
        if tree.root_node.has_error:
            raise LowerError(f"cannot parse '@{kind}' as a Rust expression", cl.line)
        fn = tree.root_node.children[0]
        body = fn.child_by_field_name("body")
        stmt = next(c for c in body.children if c.is_named)
        node = stmt.children[0] if stmt.type == "expression_statement" else stmt
        el = ExprLowerer(self, spec=True, line_offset=cl.line - 2, col_offset=cl.payload_col, allow_old=kind in ("ensures", "invariant"))
        e = el.expr(node, expect)
        if el.pre:
            raise LowerError(f"'@{kind}' must be a pure expression", cl.line)
        if expect == ir.BOOL and e.ty != ir.BOOL:
            raise LowerError(f"'@{kind}' must be a boolean expression", cl.line)
        if expect == ir.INT and e.ty != ir.INT:
            raise LowerError(f"'@{kind}' must be an integer expression", cl.line)
        loc = ir.Loc(cl.line, cl.payload_col, cl.payload_col + len(text) if "\n" not in text else 0)
        return ir.Clause(kind, e, loc, " ".join(text.split()), tags)

    def _loop_contracts(self, loop: Any, body: Any) -> list[ContractLine]:
        out: list[ContractLine] = []
        by_line = {l: cl for cl in self.local_contracts for l in cl.raw_lines}
        ln = loop.start_point[0]
        while ln >= 1:
            t = self.fe.lines[ln - 1].strip()
            if not t.startswith("//"):
                break
            cl = by_line.get(ln)
            if cl is not None and cl.keyword in LOOP_KEYWORDS and not cl.consumed and cl not in out:
                out.append(cl)
            ln -= 1
        out.reverse()
        first = next((c for c in body.children if c.is_named and c.type not in ("line_comment", "block_comment")), None)
        limit = first.start_point[0] + 1 if first is not None else body.end_point[0] + 1
        out += [cl for cl in self.local_contracts if body.start_point[0] + 1 <= cl.line < limit and cl.keyword in LOOP_KEYWORDS and not cl.consumed and cl not in out]
        for cl in out:
            cl.consumed = True
        return out

    def _loop_clauses(self, cls: list[ContractLine]) -> tuple[tuple[ir.Clause, ...], ir.Clause | None]:
        invs, dec = [], None
        for cl in cls:
            if cl.keyword == "invariant":
                invs.append(self.clause(cl, "invariant", tuple(cl.tags)))
            elif cl.keyword == "decreases":
                dec = self.clause(cl, "decreases", tuple(cl.tags), expect=ir.INT)
            else:
                raise LowerError(f"'@{cl.keyword}' is not supported on Rust loops", cl.line)
        return tuple(invs), dec

    def _stmt_contracts(self, lo: int, hi: int, out: list[ir.Stmt]) -> None:
        for cl in self.local_contracts:
            if not cl.consumed and lo < cl.line <= hi and cl.keyword in STATEMENT_KEYWORDS:
                cl.consumed = True
                try:
                    c = self.clause(cl, cl.keyword, tuple(cl.tags))
                except LowerError as e:
                    self.fn.unsupported.append((str(e), ir.Loc(e.line)))
                    out.append(ir.Unsupported(ir.Loc(cl.line), str(e)))
                    continue
                out.append(ir.AssertStmt(c.loc, c) if cl.keyword == "assert" else ir.AssumeStmt(c.loc, c))

    # -- blocks and statements ----------------------------------------------

    def block_value(self, block: Any, out: list[ir.Stmt], expect: ir.Type | None = None, kind: str | None = None) -> ir.Expr | None:
        """Lower a block's statements into ``out``; return its tail value."""
        self.push_scope()
        try:
            return self._block_value(block, out, expect, kind)
        finally:
            self.pop_scope()

    def _block_value(self, block: Any, out: list[ir.Stmt], expect: ir.Type | None = None, kind: str | None = None) -> ir.Expr | None:
        items = [c for c in block.children if c.is_named and c.type not in ("line_comment", "block_comment")]
        prev = block.start_point[0] + 1
        tail = None
        if items and items[-1].type not in ("expression_statement", "let_declaration", "empty_statement") and not items[-1].type.endswith("_item"):
            tail = items.pop()
        elif items and items[-1].type == "expression_statement" and not _text(items[-1]).rstrip().endswith(";") and items[-1].named_child_count == 1:
            tail = items.pop().named_children[0]  # a block-like expression in tail position (if/match/loop)
        for s in items:
            self._stmt_contracts(prev, s.start_point[0], out)
            self.stmt(s, out)
            prev = s.end_point[0] + 1
        value = None
        if tail is not None:
            self._stmt_contracts(prev, tail.start_point[0], out)
            el = ExprLowerer(self)
            value = el.expr(tail, expect, kind)
            out.extend(el.pre)
            prev = tail.end_point[0] + 1
        self._stmt_contracts(prev, block.end_point[0] + 1, out)
        if value is not None and value.ty == ir.NONE and isinstance(value, ir.Lit):
            return None
        return value

    def stmt(self, s: Any, out: list[ir.Stmt]) -> None:
        try:
            self._stmt(s, out)
        except LowerError as e:
            self.fn.unsupported.append((str(e), ir.Loc(e.line or s.start_point[0] + 1)))
            out.append(ir.Unsupported(self.loc(s), str(e)))

    def _stmt(self, s: Any, out: list[ir.Stmt]) -> None:
        loc = self.loc(s)
        k = s.type
        if k == "empty_statement" or k.endswith("_item") or k == "attribute_item":
            if k == "function_item":
                raise self.err("nested functions are not supported", s)
            return
        if k == "let_declaration":
            pat = s.child_by_field_name("pattern")
            tn = s.child_by_field_name("type")
            val = s.child_by_field_name("value")
            ann, akind = self.fe.ty(tn, self.info.owner) if tn is not None else (None, None)
            if s.child_by_field_name("alternative") is not None:
                raise self.err("let-else is not supported yet", s)
            if pat.type in ("identifier", "mut_pattern") or (pat.type == "identifier"):
                name = _text(pat).replace("mut", "", 1).strip() if pat.type == "mut_pattern" else _text(pat)
                if val is None:
                    if ann is None:
                        raise self.err(f"'let {name};' needs a type", s)
                    irn = self.declare(name, ann, s)
                    if akind:
                        (self.elem_kinds if isinstance(ann, (ir.TList, ir.TDict)) else self.kinds)[irn] = akind
                    return
                if val.type == "reference_expression" and _is_mut_ref(val) and ann is None:
                    target = _deref_target(val.named_children[-1])
                    if target.type == "identifier" and isinstance(self.lookup_ty(_text(target), target), (ir.TList, ir.TDict)):
                        irn = self.declare(name, self.lookup_ty(_text(target), target), s)
                        self.aliases[irn] = self.resolve(_text(target))  # r = &mut v: r is v
                        return
                el = ExprLowerer(self)
                v = el.copy_value(el.expr(val, ann, akind))
                out.extend(el.pre)
                ty = ann or v.ty
                if v.ty == ir.NONE and ann is None and not (isinstance(v, ir.Lit) and v.value is None):
                    raise self.err(f"'{name}' would hold ()", s)
                v = self.coerce(v, ty)
                irn = self.declare(name, ty, s)
                if isinstance(ty, (ir.TList, ir.TDict)):
                    k2 = akind or el.kind_of_elems(v)
                    if k2:
                        self.elem_kinds[irn] = k2
                else:
                    k2 = akind or el.kind_of(v) or ("i32" if ty == ir.INT and isinstance(v, ir.Lit) else None)  # Rust's default for a bare literal
                    if k2:
                        self.kinds[irn] = k2
                out.append(ir.Assign(loc, irn, v))
                return
            if pat.type == "tuple_pattern" and val is not None:
                el = ExprLowerer(self)
                v = el.expr(val)
                out.extend(el.pre)
                t = self.fresh("tuple", v.ty)
                out.append(ir.Assign(loc, t, v))
                for i, sub in enumerate(pat.named_children):
                    if sub.type != "identifier":
                        raise self.err("nested patterns in let are not supported", s)
                    item = ir.Builtin(ir.TOpaque(""), loc, "opaque_op", (ir.Lit(ir.STR, loc, f"item{i}"), ir.Var(v.ty, loc, t)))
                    irn = self.declare(_text(sub), item.ty, s)
                    out.append(ir.Assign(loc, irn, item))
                return
            if pat.type == "_" or _text(pat) == "_":
                if val is not None:
                    el = ExprLowerer(self)
                    v = el.expr(val)
                    out.extend(el.pre)
                    out.append(ir.ExprStmt(loc, v))
                return
            raise self.err(f"unsupported pattern in let: {_text(pat)}", s)
        if k == "expression_statement":
            e = s.named_children[0] if s.named_children else None
            if e is None:
                return
            if e.type in ("while_expression", "loop_expression", "for_expression"):
                self.loop(e, out, None)
                return
            el = ExprLowerer(self)
            v = el.expr(e, None)
            out.extend(el.pre)
            if not (isinstance(v, ir.Lit) or isinstance(v, ir.Var)):
                out.append(ir.ExprStmt(loc, v))
            return
        if k in ("while_expression", "loop_expression", "for_expression"):
            self.loop(s, out, None)
            return
        el = ExprLowerer(self)
        v = el.expr(s, None)
        out.extend(el.pre)
        if not isinstance(v, (ir.Lit, ir.Var)):
            out.append(ir.ExprStmt(loc, v))

    def declare(self, name: str, ty: ir.Type, node: Any) -> str:
        """Bind ``name`` in the current scope; returns its IR name. A binding
        that shadows another (Rust's 'let x = x.trim();', or a name reused in
        an inner block) gets a name of its own, so the outer one is intact."""
        if name in self.env or name in self.used:
            self.tmp += 1
            ir_name = f"{name}${self.tmp}"
        else:
            ir_name = name
        self.used.add(ir_name)
        self.scopes[-1][name] = ir_name
        self.env[ir_name] = ty
        return ir_name

    def resolve(self, name: str) -> str:
        for sc in reversed(self.scopes):
            if name in sc:
                name = sc[name]
                break
        while name in self.aliases:
            name = self.aliases[name]
        return name

    def push_scope(self) -> None:
        self.scopes.append({})

    def pop_scope(self) -> None:
        self.scopes.pop()

    def lookup_ty(self, name: str, node: Any) -> ir.Type:
        name = self.resolve(name)
        if name in self.env:
            return self.env[name]
        raise self.err(f"unknown variable '{name}'", node)

    def coerce(self, e: ir.Expr, ty: ir.Type) -> ir.Expr:
        if e.ty == ty:
            return e
        if isinstance(ty, ir.TOption) and e.ty == ir.NONE:
            return ir.Lit(ty, e.loc, None)
        if isinstance(ty, ir.TOption) and not isinstance(e.ty, ir.TOption) and e.ty == ty.inner:
            return ir.Builtin(ty, e.loc, "some", (e,))
        if isinstance(ty, ir.TList) and isinstance(e, ir.ListLit) and not e.elems:
            return ir.ListLit(ty, e.loc, ())
        if isinstance(ty, ir.TDict) and isinstance(e, ir.Builtin) and e.name == "dict_lit" and not e.args:
            return ir.Builtin(ty, e.loc, "dict_lit", ())
        if isinstance(e.ty, ir.TOpaque) and not isinstance(ty, ir.TOpaque) and ty != ir.NONE:
            return ir.Builtin(ty, e.loc, "from_opaque", (e,))
        if isinstance(ty, ir.TOpaque) and not isinstance(e.ty, ir.TOpaque):
            return ir.Builtin(ty, e.loc, "to_opaque", (e,) if e.ty != ir.NONE else (ir.Lit(ir.INT, e.loc, 0),))
        return e

    def in_range(self, e: ir.Expr, kind: str) -> ir.Expr:
        lo, hi = int_range(kind)
        return ir.Builtin(ir.INT, e.loc, "in_range", (e, ir.Lit(ir.INT, e.loc, lo), ir.Lit(ir.INT, e.loc, hi)))

    # -- loops ----------------------------------------------------------

    def loop(self, s: Any, out: list[ir.Stmt], value_target: str | None) -> None:
        loc = self.loc(s)
        k = s.type
        body = s.child_by_field_name("body")
        if s.child_by_field_name("label") is not None or any(c.type == "label" for c in s.children):
            raise self.err("loop labels are not supported yet", s)
        cls = self._loop_contracts(s, body)
        invs, dec = self._loop_clauses(cls) if k != "for_expression" else ((), None)
        self.loop_value.append(value_target)
        saved, self.range_after = self.range_after, []
        try:
            if k == "loop_expression":
                b: list[ir.Stmt] = []
                self._loop_body(body, b)
                out.append(ir.While(loc, ir.Lit(ir.BOOL, loc, True), invs, dec, tuple(b)))
                return
            if k == "while_expression":
                cond = s.child_by_field_name("condition")
                if cond.type == "let_condition":
                    b = []
                    self._while_let(cond, body, b, loc)
                    out.append(ir.While(loc, ir.Lit(ir.BOOL, loc, True), invs, dec, tuple(b)))
                    return
                el = ExprLowerer(self)
                c = el.expr(cond, ir.BOOL)
                b = []
                if el.pre:  # the condition does work: re-run it every iteration
                    b.extend(el.pre)
                    b.append(ir.If(loc, ir.Unary(ir.BOOL, loc, "not", c), (ir.Break(loc),), ()))
                    self._loop_body(body, b)
                    out.append(ir.While(loc, ir.Lit(ir.BOOL, loc, True), invs, dec, tuple(b)))
                    return
                self._loop_body(body, b)
                out.append(ir.While(loc, c, invs, dec, tuple(b)))
                return
            # for PAT in ITER
            pat = s.child_by_field_name("pattern")
            it = s.child_by_field_name("value")
            self._for(pat, it, body, out, loc, cls)
        finally:
            self.loop_value.pop()
            out.extend(self.range_after)  # ... and after the loop
            self.range_after = saved

    def _loop_body(self, body: Any, out: list[ir.Stmt]) -> None:
        start = len(out)
        before = set(self.env)
        v = self.block_value(body, out)
        if v is not None and not isinstance(v, (ir.Lit, ir.Var)):
            out.append(ir.ExprStmt(v.loc, v))
        # integers the loop changes keep their type's range (a fact, not an invariant to prove)
        loc = self.loc(body)
        facts = [ir.ExprStmt(loc, self.in_range(ir.Var(ir.INT, loc, n), self.kinds[n])) for n in sorted(ir.assigned_names(out[start:])) if n in before and n in self.kinds and self.env.get(n) == ir.INT]
        out[start:start] = facts
        self.range_after.extend(facts)

    def _while_let(self, cond: Any, body: Any, out: list[ir.Stmt], loc: ir.Loc) -> None:
        pat = cond.child_by_field_name("pattern")
        val = cond.child_by_field_name("value")
        el = ExprLowerer(self)
        v = el.expr(val)
        out.extend(el.pre)
        binds = self._option_pattern(pat)
        if binds is None or not isinstance(v.ty, ir.TOption):
            raise self.err("only 'while let Some(x) = ...' is supported", cond)
        t = self.fresh("opt", v.ty)
        out.append(ir.Assign(loc, t, v))
        tv = ir.Var(v.ty, loc, t)
        out.append(ir.If(loc, ir.Builtin(ir.BOOL, loc, "is_none", (tv,)), (ir.Break(loc),), ()))
        self.push_scope()
        try:
            if binds:
                irn = self.declare(binds, v.ty.inner, pat)
                out.append(ir.Assign(loc, irn, ir.Builtin(v.ty.inner, loc, "unwrap", (tv,))))
            self._loop_body(body, out)
        finally:
            self.pop_scope()

    def _option_pattern(self, pat: Any) -> str | None:
        """'Some(x)' -> 'x', 'Some(_)' -> ''; anything else None."""
        if pat.type == "tuple_struct_pattern" and _text(pat.child_by_field_name("type")) == "Some":
            args = pat.named_children[1:]
            if len(args) == 1 and args[0].type == "identifier":
                return _text(args[0])
            if len(args) == 1 and _text(args[0]) == "_":
                return ""
        return None

    def _for_clauses(self, cls: list[ContractLine], node: Any) -> tuple[ir.Clause, ...]:
        invs, dec = self._loop_clauses(cls)
        if dec is not None:
            raise self.err("a for loop terminates by construction; remove '@decreases'", node)
        return invs

    def _for(self, pat: Any, it: Any, body: Any, out: list[ir.Stmt], loc: ir.Loc, cls: list[ContractLine]) -> None:
        # for i in a..b / a..=b
        if it.type == "range_expression":
            kids = it.named_children
            if len(kids) != 2 or pat.type != "identifier":
                raise self.err("for loops over ranges need 'for i in a..b'", it)
            el = ExprLowerer(self)
            lo = el.expr(kids[0], ir.INT)
            hi = el.expr(kids[1], ir.INT)
            kind = el.kind_of(lo) or el.kind_of(hi)
            out.extend(el.pre)
            if lo.ty != ir.INT or hi.ty != ir.INT:
                raise self.err("range bounds must be integers", it)
            if "..=" in _text(it):
                hi = ir.Binary(ir.INT, hi.loc, "add", hi, ir.Lit(ir.INT, hi.loc, 1))
            self.push_scope()
            try:
                v = self.declare(_text(pat), ir.INT, pat)
                if kind:
                    self.kinds[v] = kind
                invs = self._for_clauses(cls, it)
                b: list[ir.Stmt] = []
                self._loop_body(body, b)
            finally:
                self.pop_scope()
            out.append(ir.ForRange(loc, v, lo, hi, invs, tuple(b)))
            return
        # for x in (a..b).rev(): a counted loop downwards
        seq_node, enum_idx = it, None
        if it.type == "call_expression" and it.child_by_field_name("function").type == "field_expression":
            f = it.child_by_field_name("function")
            meth = _text(f.child_by_field_name("field"))
            recv = f.child_by_field_name("value")
            if meth in ("iter", "into_iter", "iter_mut") and not it.child_by_field_name("arguments").named_children:
                seq_node = recv
            elif meth == "enumerate":
                inner = recv
                if inner.type == "call_expression" and inner.child_by_field_name("function").type == "field_expression" and _text(inner.child_by_field_name("function").child_by_field_name("field")) in ("iter", "into_iter", "iter_mut"):
                    seq_node = inner.child_by_field_name("function").child_by_field_name("value")
                    enum_idx = True
            elif meth == "rev" and recv.type == "parenthesized_expression" and recv.named_children[0].type == "range_expression" and pat.type == "identifier":
                rng = recv.named_children[0]
                kids = rng.named_children
                el = ExprLowerer(self)
                lo = el.expr(kids[0], ir.INT)
                hi = el.expr(kids[1], ir.INT)
                out.extend(el.pre)
                if "..=" in _text(rng):
                    hi = ir.Binary(ir.INT, hi.loc, "add", hi, ir.Lit(ir.INT, hi.loc, 1))
                self.push_scope()
                v = self.declare(_text(pat), ir.INT, pat)
                kind = el.kind_of(lo) or el.kind_of(hi)
                if kind:
                    self.kinds[v] = kind
                invs = self._for_clauses(cls, it)
                k = self.fresh("k", ir.INT)
                out.append(ir.Assign(loc, k, hi))
                b = [ir.Assign(loc, k, ir.Binary(ir.INT, loc, "sub", ir.Var(ir.INT, loc, k), ir.Lit(ir.INT, loc, 1))), ir.Assign(loc, v, ir.Var(ir.INT, loc, k))]
                try:
                    self._loop_body(body, b)
                finally:
                    self.pop_scope()
                dec = ir.Clause("decreases", ir.Binary(ir.INT, loc, "sub", ir.Var(ir.INT, loc, k), lo), loc, "k - lo", inferred=True)
                out.append(ir.While(loc, ir.Binary(ir.BOOL, loc, "lt", lo, ir.Var(ir.INT, loc, k)), invs, dec, tuple(b)))
                return
        if seq_node.type == "reference_expression":
            seq_node = seq_node.named_children[-1]
        el = ExprLowerer(self)
        seq = el.expr(seq_node)
        out.extend(el.pre)
        if isinstance(seq.ty, ir.TOpaque):
            seq = ir.Builtin(ir.TList(ir.TOpaque("")), seq.loc, "from_opaque", (seq,))
        if not isinstance(seq.ty, ir.TList):
            raise self.err(f"for loops need a Vec, slice or range here, not {seq.ty}", it)
        ekind = el.kind_of_elems(seq)
        self.push_scope()
        try:
            self._for_each(pat, seq, body, out, loc, cls, it, enum_idx, ekind)
        finally:
            self.pop_scope()

    def _for_each(self, pat: Any, seq: ir.Expr, body: Any, out: list[ir.Stmt], loc: ir.Loc, cls: list[ContractLine], it: Any, enum_idx: Any, ekind: str | None) -> None:
        assert isinstance(seq.ty, ir.TList)
        if enum_idx:
            if pat.type != "tuple_pattern" or len(pat.named_children) != 2:
                raise self.err("use 'for (i, x) in xs.iter().enumerate()'", pat)
            iname = self.declare(_text(pat.named_children[0]), ir.INT, pat)
            ename_src = _text(pat.named_children[1]).lstrip("&")
            self.kinds[iname] = "usize"
            idx, visible = iname, True
        else:
            if pat.type not in ("identifier", "reference_pattern"):
                raise self.err("for-loop patterns must be a name here", pat)
            ename_src = _text(pat).lstrip("&").strip()
            idx, visible = self.fresh("i", ir.INT), False
        ename = self.declare(ename_src, seq.ty.elem, pat)
        if ekind:
            self.kinds[ename] = ekind
        invs = self._for_clauses(cls, it)
        b = []
        if ekind:
            b.append(ir.ExprStmt(loc, self.in_range(ir.Var(ir.INT, loc, ename), ekind)))
        self._loop_body(body, b)
        out.append(ir.ForEach(loc, ename, idx, seq, invs, tuple(b), idx_visible=visible))


# ---------------------------------------------------------------------------
# Expressions


BINOPS = {"+": "add", "-": "sub", "*": "mul", "<": "lt", "<=": "le", ">": "gt", ">=": "ge", "==": "eq", "!=": "ne"}


class ExprLowerer:
    """Lowers one expression. Statements it needs first (a hoisted call's
    control flow, an if/match used as a value, '?') go to ``pre``, in
    evaluation order; code that must not run unconditionally (the right of
    '&&', an if-branch) is lowered into its own lowerer and guarded."""

    def __init__(self, fl: FunctionLowerer, spec: bool = False, line_offset: int = 0, col_offset: int = 0, allow_old: bool = False):
        self.fl = fl
        self.fe = fl.fe
        self.spec = spec
        self.pre: list[ir.Stmt] = []
        self.kinds: dict[int, str] = {}
        self.keep: list[ir.Expr] = []
        self.bound: dict[str, ir.Type] = {}
        self.line_offset = line_offset
        self.col_offset = col_offset
        self.allow_old = allow_old

    def sub(self) -> "ExprLowerer":
        e = ExprLowerer(self.fl, self.spec, self.line_offset, self.col_offset, self.allow_old)
        e.bound = dict(self.bound)
        e.kinds = self.kinds
        e.keep = self.keep
        return e

    def loc(self, n: Any) -> ir.Loc:
        (l1, c1), (l2, c2) = n.start_point, n.end_point
        if self.spec:
            return ir.Loc(l1 + 1 + self.line_offset, c1 + self.col_offset, 0)
        return ir.Loc(l1 + 1, c1, c2 if l1 == l2 else 0)

    def err(self, msg: str, n: Any) -> LowerError:
        return LowerError(msg, n.start_point[0] + 1 + (self.line_offset if self.spec else 0))

    def kinded(self, e: ir.Expr, kind: str | None) -> ir.Expr:
        if kind:
            self.kinds[id(e)] = kind
            self.keep.append(e)
        return e

    def kind_of(self, e: ir.Expr) -> str | None:
        k = self.kinds.get(id(e))
        if k:
            return k
        if isinstance(e, ir.Var):
            return self.fl.kinds.get(e.name)
        return None

    def kind_of_elems(self, seq: ir.Expr) -> str | None:
        return self.kinds.get(id(seq) * 7 + 1) or (self.fl.elem_kinds.get(seq.name) if isinstance(seq, ir.Var) else None)

    def elems_kinded(self, e: ir.Expr, kind: str | None) -> ir.Expr:
        if kind:
            self.kinds[id(e) * 7 + 1] = kind
            self.keep.append(e)
        return e

    def checked(self, e: ir.Expr, kind: str | None) -> ir.Expr:
        """Fixed-width arithmetic: the result must fit (in code, not in specs)."""
        if not kind or self.spec:
            return self.kinded(e, kind)
        lo, hi = int_range(kind)
        return self.kinded(ir.Builtin(ir.INT, e.loc, "checked", (e, ir.Lit(ir.INT, e.loc, lo), ir.Lit(ir.INT, e.loc, hi), ir.Lit(ir.STR, e.loc, kind))), kind)

    def ranged(self, e: ir.Expr, kind: str | None) -> ir.Expr:
        if not kind or self.spec:
            return self.kinded(e, kind)
        return self.kinded(self.fl.in_range(e, kind), kind)

    def copy_value(self, e: ir.Expr) -> ir.Expr:
        """A Copy struct modelled as an object (it has &mut self methods) is
        copied when used by value, not aliased."""
        if self.spec or not isinstance(e.ty, ir.TClass) or isinstance(e, ir.New):
            return e
        st = self.fe.structs.get(e.ty.name)
        if st is None or not st.copy:
            return e
        src = self.hoist(e) if not isinstance(e, ir.Var) else e
        decl = self.fe.module.classes[e.ty.name]
        return self.hoist(ir.New(e.ty, e.loc, e.ty.name, tuple(ir.Field(t, e.loc, src, f) for f, t in decl.fields)))

    def hoist(self, e: ir.Expr) -> ir.Expr:
        """Evaluate an effectful expression now, into a temporary."""
        if self.spec or e.ty == ir.NONE:
            return e
        t = self.fl.fresh("t", e.ty)
        self.pre.append(ir.Assign(e.loc, t, e))
        v = ir.Var(e.ty, e.loc, t)
        k = self.kind_of(e)
        if k:
            self.fl.kinds[t] = k
        if id(e) * 7 + 1 in self.kinds:
            self.fl.elem_kinds[t] = self.kinds[id(e) * 7 + 1]
        return v

    # -- dispatch ---------------------------------------------------------

    def expr(self, n: Any, expect: ir.Type | None = None, kind: str | None = None) -> ir.Expr:
        m = getattr(self, "x_" + n.type, None)
        if m is None:
            raise self.err(f"unsupported expression: {n.type.replace('_', ' ')}", n)
        return m(n, expect, kind)

    def x_parenthesized_expression(self, n: Any, expect: Any, kind: Any) -> ir.Expr:
        return self.expr(n.named_children[0], expect, kind)

    def x_integer_literal(self, n: Any, expect: Any, kind: Any) -> ir.Expr:
        t = _text(n).replace("_", "")
        m = re.match(r"^(0x[0-9a-fA-F]+|0o[0-7]+|0b[01]+|\d+)([iu](?:8|16|32|64|128|size))?$", t)
        if not m:
            raise self.err(f"unsupported integer literal {t}", n)
        v = int(m.group(1), 0)
        k = m.group(2) or kind
        if expect == ir.REAL:
            return ir.Lit(ir.REAL, self.loc(n), Fraction(v))
        return self.kinded(ir.Lit(ir.INT, self.loc(n), v), k)

    def x_float_literal(self, n: Any, expect: Any, kind: Any) -> ir.Expr:
        t = re.sub(r"f(32|64)$", "", _text(n).replace("_", ""))
        return ir.Lit(ir.REAL, self.loc(n), Fraction(t))

    def x_boolean_literal(self, n: Any, expect: Any, kind: Any) -> ir.Expr:
        return ir.Lit(ir.BOOL, self.loc(n), _text(n) == "true")

    def x_string_literal(self, n: Any, expect: Any, kind: Any) -> ir.Expr:
        raw = _text(n)
        if raw.startswith("r") or raw.startswith("b"):
            return self.opaque_str(n)
        body = raw[1:-1]
        if "\\" in body:
            try:
                body = bytes(body, "utf8").decode("unicode_escape")
            except UnicodeDecodeError:
                return self.opaque_str(n)
        return ir.Lit(ir.STR, self.loc(n), body)

    def opaque_str(self, n: Any) -> ir.Expr:
        return ir.Builtin(ir.STR, self.loc(n), "str_fn", (ir.Lit(ir.STR, self.loc(n), "literal"), ir.Lit(ir.STR, self.loc(n), _text(n))))

    def x_char_literal(self, n: Any, expect: Any, kind: Any) -> ir.Expr:
        body = _text(n)[1:-1]
        if body.startswith("\\"):
            return self.opaque_str(n)
        return ir.Lit(ir.STR, self.loc(n), body)

    def x_identifier(self, n: Any, expect: Any, kind: Any) -> ir.Expr:
        name = _text(n)
        loc = self.loc(n)
        if name in self.bound:
            return self.ranged(ir.Var(self.bound[name], loc, name), self.fl.kinds.get(name)) if self.bound[name] == ir.INT else ir.Var(self.bound[name], loc, name)
        if self.spec and name == "result":
            return self.kinded(ir.Result(self.fl.info.ret, loc), self.fl.info.ret_kind)
        if name == "None":
            return ir.Lit(expect if isinstance(expect, ir.TOption) else ir.NONE, loc, None)
        r = self.fl.resolve(name)
        if r in self.fl.env:
            return self.kinded(ir.Var(self.fl.env[r], loc, r), self.fl.kinds.get(r))
        if name in self.fe.consts:
            lit, k = self.fe.consts[name]
            return self.expr(lit, expect, k)
        raise self.err(f"unknown name '{name}'", n)

    def x_self(self, n: Any, expect: Any, kind: Any) -> ir.Expr:
        if "self" not in self.fl.env:
            raise self.err("'self' outside a method", n)
        return ir.Var(self.fl.env["self"], self.loc(n), "self")

    def x_scoped_identifier(self, n: Any, expect: Any, kind: Any) -> ir.Expr:
        txt = _text(n)
        parts = txt.split("::")
        loc = self.loc(n)
        if len(parts) == 2 and parts[0] in self.fe.enums:
            et = self.fe.enums[parts[0]]
            if parts[1] in et.members:
                return self._enum_lit(et, parts[1], loc)
        if len(parts) == 2 and parts[0] in INT_KINDS and parts[1] in ("MAX", "MIN"):
            lo, hi = int_range(parts[0])
            return self.kinded(ir.Lit(ir.INT, loc, hi if parts[1] == "MAX" else lo), parts[0])
        if len(parts) >= 2 and parts[-2] in ("f32", "f64") and parts[-1] in ("EPSILON",):
            return ir.Lit(ir.REAL, loc, Fraction(2) ** -52 if parts[-2] == "f64" else Fraction(2) ** -23)
        if self.spec:
            raise self.err(f"'{txt}' is not supported in specifications", n)
        return ir.Extern(ir.TOpaque(txt), loc, txt, ())

    def _enum_lit(self, et: ir.TEnum, member: str, loc: ir.Loc) -> ir.Expr:
        # an enum member literal: compare against by index (members are distinct)
        return ir.Lit(et, loc, et.members.index(member))

    def x_unary_expression(self, n: Any, expect: Any, kind: Any) -> ir.Expr:
        op = _text(n.children[0])
        arg = n.named_children[0]
        loc = self.loc(n)
        if op == "-":
            if arg.type == "integer_literal":
                lit = self.expr(arg, expect, kind)
                return self.kinded(ir.Lit(lit.ty, loc, -lit.value), self.kind_of(lit))  # type: ignore[operator]
            a = self.expr(arg, expect, kind)
            if a.ty == ir.REAL:
                return ir.Unary(ir.REAL, loc, "neg", a)
            if a.ty != ir.INT:
                raise self.err(f"cannot negate {a.ty}", n)
            return self.checked(ir.Unary(ir.INT, loc, "neg", a), self.kind_of(a))
        if op == "!":
            a = self.expr(arg, expect)
            if a.ty == ir.BOOL:
                return ir.Unary(ir.BOOL, loc, "not", a)
            if a.ty == ir.INT:
                k = self.kind_of(a)
                return self.ranged(self.opaque("bitnot", [a], ir.INT, loc), k)
            raise self.err(f"'!' on {a.ty}", n)
        if op == "*":
            return self.expr(arg, expect, kind)
        raise self.err(f"unsupported unary operator {op}", n)

    def x_reference_expression(self, n: Any, expect: Any, kind: Any) -> ir.Expr:
        return self.expr(n.named_children[-1], expect, kind)

    def x_type_cast_expression(self, n: Any, expect: Any, kind: Any) -> ir.Expr:
        v = self.expr(n.child_by_field_name("value"))
        tt = _text(n.child_by_field_name("type"))
        loc = self.loc(n)
        if tt in INT_KINDS:
            if v.ty == ir.INT:
                src = self.kind_of(v)
                if src and int_range(src)[0] >= int_range(tt)[0] and int_range(src)[1] <= int_range(tt)[1]:
                    return self.kinded(v, tt)  # widening: the value is unchanged
                signed, bits = INT_KINDS[tt]
                m = ir.Lit(ir.INT, loc, 1 << bits)
                if not signed:
                    return self.kinded(ir.Binary(ir.INT, loc, "fmod", v, m), tt)  # truncation to the low bits
                h = ir.Lit(ir.INT, loc, 1 << (bits - 1))
                return self.kinded(ir.Binary(ir.INT, loc, "sub", ir.Binary(ir.INT, loc, "fmod", ir.Binary(ir.INT, loc, "add", v, h), m), h), tt)
            if v.ty == ir.REAL:
                lo, hi = int_range(tt)
                t = ir.Builtin(ir.INT, loc, "trunc", (v,))
                return self.kinded(ir.Builtin(ir.INT, loc, "min", (ir.Builtin(ir.INT, loc, "max", (t, ir.Lit(ir.INT, loc, lo))), ir.Lit(ir.INT, loc, hi))), tt)  # saturating
            if v.ty == ir.BOOL:
                return self.kinded(ir.Ite(ir.INT, loc, v, ir.Lit(ir.INT, loc, 1), ir.Lit(ir.INT, loc, 0)), tt)
            if isinstance(v.ty, ir.TEnum):
                return self.kinded(self.opaque("enum_discriminant", [v], ir.INT, loc), tt)
        if tt in ("f32", "f64"):
            if v.ty == ir.INT:
                return ir.Builtin(ir.REAL, loc, "to_real", (v,))
            if v.ty == ir.REAL:
                return v
        raise self.err(f"unsupported cast from {v.ty} to {tt}", n)

    def x_binary_expression(self, n: Any, expect: Any, kind: Any) -> ir.Expr:
        op = _text(n.child_by_field_name("operator"))
        ln, rn = n.child_by_field_name("left"), n.child_by_field_name("right")
        loc = self.loc(n)
        if op in ("&&", "||"):
            a = self.expr(ln, ir.BOOL)
            s = self.sub()
            b = s.expr(rn, ir.BOOL)
            if a.ty != ir.BOOL or b.ty != ir.BOOL:
                raise self.err(f"'{op}' needs booleans", n)
            if not s.pre:
                return ir.Binary(ir.BOOL, loc, "and" if op == "&&" else "or", a, b)
            # the right side does work: only when it runs
            t = self.fl.fresh("sc", ir.BOOL)
            self.pre.append(ir.Assign(loc, t, a))
            tv = ir.Var(ir.BOOL, loc, t)
            guard = tv if op == "&&" else ir.Unary(ir.BOOL, loc, "not", tv)
            self.pre.append(ir.If(loc, guard, tuple(s.pre) + (ir.Assign(loc, t, b),), ()))
            return tv
        a = self.expr(ln, None, kind)
        b = self.expr(rn, a.ty if a.ty in (ir.INT, ir.REAL) else None, self.kind_of(a) or kind)
        if a.ty == ir.INT and b.ty == ir.INT and not self.kind_of(a) and self.kind_of(b):
            self.kinded(a, self.kind_of(b))
        k = self.kind_of(a) or self.kind_of(b)
        if a.ty == ir.REAL and b.ty == ir.INT and isinstance(b, ir.Lit):
            b = ir.Lit(ir.REAL, b.loc, Fraction(b.value))  # type: ignore[arg-type]
        if b.ty == ir.REAL and a.ty == ir.INT and isinstance(a, ir.Lit):
            a = ir.Lit(ir.REAL, a.loc, Fraction(a.value))  # type: ignore[arg-type]
        if op in ("==", "!="):
            a, b = self._same(a, b, n)
            return ir.Binary(ir.BOOL, loc, BINOPS[op], a, b)
        if op in ("<", "<=", ">", ">="):
            if not (a.ty == b.ty and a.ty in (ir.INT, ir.REAL, ir.STR)):
                raise self.err(f"cannot compare {a.ty} and {b.ty}", n)
            if a.ty == ir.STR:
                return ir.Builtin(ir.BOOL, loc, "str_lt" if op in ("<", ">") else "str_le", (a, b) if op in ("<", "<=") else (b, a))
            return ir.Binary(ir.BOOL, loc, BINOPS[op], a, b)
        if op in ("+", "-", "*", "/", "%"):
            if a.ty == ir.STR and op == "+":
                return ir.Builtin(ir.STR, loc, "str_concat", (a, b))
            if a.ty != b.ty or a.ty not in (ir.INT, ir.REAL):
                raise self.err(f"'{op}' on {a.ty} and {b.ty}", n)
            if a.ty == ir.REAL:
                if op == "/":  # float division by zero is inf/NaN, not a panic
                    nz = ir.Binary(ir.BOOL, loc, "ne", b, ir.Lit(ir.REAL, loc, Fraction(0)))
                    return ir.Ite(ir.REAL, loc, nz, ir.Binary(ir.REAL, loc, "rdiv", a, b), self.opaque("fdiv", [a, b], ir.REAL, loc))
                if op == "%":
                    return self.opaque("fmod", [a, b], ir.REAL, loc)
                return ir.Binary(ir.REAL, loc, BINOPS[op], a, b)
            name = {"+": "add", "-": "sub", "*": "mul", "/": "tdiv", "%": "tmod"}[op]
            # an integer whose type nothing fixes is an i32 in Rust
            return self.checked(ir.Binary(ir.INT, loc, name, a, b), k or kind or "i32")
        if op in ("&", "|", "^", "<<", ">>"):
            if a.ty == ir.BOOL and b.ty == ir.BOOL and op in ("&", "|", "^"):
                return ir.Binary(ir.BOOL, loc, {"&": "and", "|": "or", "^": "ne"}[op], a, b)  # non-short-circuit on bools
            if a.ty == ir.INT and b.ty == ir.INT:
                return self.ranged(self.opaque(f"bit{op}", [a, b], ir.INT, loc), self.kind_of(a))
        raise self.err(f"unsupported operator {op} on {a.ty}", n)

    def _same(self, a: ir.Expr, b: ir.Expr, n: Any) -> tuple[ir.Expr, ir.Expr]:
        if a.ty == b.ty:
            return a, b
        if isinstance(a.ty, ir.TOption) and b.ty == ir.NONE:
            return a, ir.Lit(a.ty, b.loc, None)
        if isinstance(b.ty, ir.TOption) and a.ty == ir.NONE:
            return ir.Lit(b.ty, a.loc, None), b
        if isinstance(a.ty, ir.TOption) and a.ty.inner == b.ty:
            return a, ir.Builtin(a.ty, b.loc, "some", (b,))
        if isinstance(b.ty, ir.TOption) and b.ty.inner == a.ty:
            return ir.Builtin(b.ty, a.loc, "some", (a,)), b
        if isinstance(a, ir.ListLit) and not a.elems and isinstance(b.ty, ir.TList):
            return ir.ListLit(b.ty, a.loc, ()), b
        if isinstance(b, ir.ListLit) and not b.elems and isinstance(a.ty, ir.TList):
            return a, ir.ListLit(a.ty, b.loc, ())
        raise self.err(f"cannot compare {a.ty} and {b.ty}", n)

    def x_compound_assignment_expr(self, n: Any, expect: Any, kind: Any) -> ir.Expr:
        op = _text(n.child_by_field_name("operator"))[:-1]
        left, right = n.child_by_field_name("left"), n.child_by_field_name("right")
        fake = _Synthetic("binary_expression", n, {"left": left, "right": right, "operator": op})
        value = self.x_binary_expression(fake, None, None)  # type: ignore[arg-type]
        self._store(left, value, n)
        return ir.Lit(ir.NONE, self.loc(n), None)

    def x_assignment_expression(self, n: Any, expect: Any, kind: Any) -> ir.Expr:
        left, right = n.child_by_field_name("left"), n.child_by_field_name("right")
        target_ty = self._target_type(left)
        k = self._target_kind(left)
        value = self.copy_value(self.expr(right, target_ty, k))
        self._store(left, value, n)
        return ir.Lit(ir.NONE, self.loc(n), None)

    def _target_type(self, left: Any) -> ir.Type | None:
        try:
            s = self.sub()
            return s.expr(left).ty
        except LowerError:
            return None

    def _target_kind(self, left: Any) -> str | None:
        if left.type == "identifier":
            return self.fl.kinds.get(self.fl.resolve(_text(left)))
        if left.type == "field_expression":
            try:
                obj = self.sub().expr(left.child_by_field_name("value"))
            except LowerError:
                return None
            name = getattr(obj.ty, "name", None)
            s = self.fe.structs.get(name) if name else None
            return s.kinds.get(_text(left.child_by_field_name("field"))) if s else None
        if left.type == "index_expression":
            try:
                seq = self.sub().expr(left.named_children[0])
            except LowerError:
                return None
            return self.kind_of_elems(seq)
        return None

    def _store(self, left: Any, value: ir.Expr, n: Any) -> None:
        if self.spec:
            raise self.err("assignment in a specification", n)
        loc = self.loc(n)
        if left.type == "identifier":
            name = self.fl.resolve(_text(left))
            if name not in self.fl.env:
                raise self.err(f"unknown variable '{name}'", left)
            ty = self.fl.env[name]
            value = self.fl.coerce(value, ty)
            if isinstance(ty, ir.TList) and ty.elem == ir.NONE and isinstance(value.ty, ir.TList):
                self.fl.env[name] = ty = value.ty
            if value.ty != ty:
                raise self.err(f"cannot assign {value.ty} to '{name}' of type {ty}", n)
            self.pre.append(ir.Assign(loc, name, value))
            return
        if left.type == "field_expression":
            obj = self.expr(left.child_by_field_name("value"))
            fname = _text(left.child_by_field_name("field"))
            if isinstance(obj.ty, ir.TClass):
                decl = self.fe.module.classes[obj.ty.name]
                ft = decl.field_type(fname)
                if ft is None:
                    raise self.err(f"{obj.ty.name} has no field '{fname}'", left)
                self.pre.append(ir.FieldAssign(loc, obj, obj.ty.name, fname, self.fl.coerce(value, ft)))
                return
            if isinstance(obj.ty, ir.TRecord) and isinstance(obj, ir.Var):
                # a Copy struct is a value: rebuild it with the field replaced
                fields = tuple((f, self.fl.coerce(value, t) if f == fname else ir.Field(t, loc, obj, f)) for f, t in obj.ty.fields)
                if fname not in dict(obj.ty.fields):
                    raise self.err(f"{obj.ty.name} has no field '{fname}'", left)
                self.pre.append(ir.Assign(loc, obj.name, ir.RecordLit(obj.ty, loc, fields)))
                return
            raise self.err(f"cannot assign a field of {obj.ty}", left)
        if left.type == "index_expression":
            seq_n, idx_n = left.named_children[0], left.named_children[1]
            seq = self.expr(seq_n)
            idx = self.expr(idx_n, ir.INT)
            if isinstance(seq.ty, ir.TList) and isinstance(seq, ir.Var):
                self.pre.append(ir.IndexAssign(loc, seq.name, idx, self.fl.coerce(value, seq.ty.elem), wrap=False))
                return
            if isinstance(seq.ty, ir.TDict) and isinstance(seq, ir.Var):
                # map[k] = v panics when k is missing (IndexMut is not implemented for HashMap)
                raise self.err("HashMap has no IndexMut; use insert", left)
            if isinstance(seq.ty, ir.TList) and isinstance(seq, ir.Field) and isinstance(seq.obj.ty, ir.TClass):
                self.pre.append(ir.FieldAssign(loc, seq.obj, seq.obj.ty.name, seq.name, ir.Builtin(seq.ty, loc, "list_set", (seq, idx, self.fl.coerce(value, seq.ty.elem)))))
                return
            raise self.err("assignment through an index needs a Vec variable or field", left)
        if left.type == "unary_expression" and _text(left.children[0]) == "*":
            return self._store(left.named_children[0], value, n)
        raise self.err(f"unsupported assignment target: {_text(left)}", left)

    def x_field_expression(self, n: Any, expect: Any, kind: Any) -> ir.Expr:
        obj = self.expr(n.child_by_field_name("value"))
        f = _text(n.child_by_field_name("field"))
        loc = self.loc(n)
        if isinstance(obj.ty, ir.TOption) and not self.spec:
            raise self.err("field of an Option: unwrap it first", n)
        if isinstance(obj.ty, (ir.TClass, ir.TRecord)):
            s = self.fe.structs[obj.ty.name]
            ft = dict(obj.ty.fields).get(f) if isinstance(obj.ty, ir.TRecord) else self.fe.module.classes[obj.ty.name].field_type(f)
            if ft is None:
                raise self.err(f"{obj.ty.name} has no field '{f}'", n)
            v = ir.Field(ft, loc, obj, f)
            k = s.kinds.get(f)
            if isinstance(ft, ir.TList):
                return self.elems_kinded(v, k)
            return self.ranged(v, k) if ft == ir.INT else v
        if isinstance(obj.ty, ir.TOpaque):
            if self.spec:
                raise self.err(f"field '{f}' of an unchecked value in a specification", n)
            return self.opaque(f"field.{f}", [obj], ir.TOpaque(""), loc)
        raise self.err(f"field '{f}' of {obj.ty}", n)

    def x_index_expression(self, n: Any, expect: Any, kind: Any) -> ir.Expr:
        seq = self.expr(n.named_children[0])
        idx_n = n.named_children[1]
        loc = self.loc(n)
        if idx_n.type == "range_expression":
            return self._slice(seq, idx_n, loc)
        if isinstance(seq.ty, ir.TList):
            i = self.expr(idx_n, ir.INT, "usize")
            v = ir.Index(seq.ty.elem, loc, seq, i, wrap=False)
            k = self.kind_of_elems(seq)
            return self.ranged(v, k) if seq.ty.elem == ir.INT else v
        if isinstance(seq.ty, ir.TDict):
            key = self.expr(idx_n, seq.ty.key)
            v = ir.Index(seq.ty.val, loc, seq, key, wrap=False)
            k = self.kind_of_elems(seq)
            return self.ranged(v, k) if seq.ty.val == ir.INT else v
        if isinstance(seq.ty, ir.TOpaque):
            if self.spec:
                raise self.err("indexing an unchecked value in a specification", n)
            return self.opaque("index", [seq, self.expr(idx_n)], ir.TOpaque(""), loc)
        raise self.err(f"indexing {seq.ty}", n)

    def _slice(self, seq: ir.Expr, rng: Any, loc: ir.Loc) -> ir.Expr:
        if not isinstance(seq.ty, ir.TList):
            raise self.err(f"slicing {seq.ty}", rng)
        txt = _text(rng)
        kids = rng.named_children
        lo = hi = None
        if txt.startswith(".."):
            hi = self.expr(kids[0], ir.INT) if kids else None
        else:
            lo = self.expr(kids[0], ir.INT)
            hi = self.expr(kids[1], ir.INT) if len(kids) > 1 else None
        if hi is not None and "..=" in txt:
            hi = ir.Binary(ir.INT, loc, "add", hi, ir.Lit(ir.INT, loc, 1))
        n = ir.Builtin(ir.INT, loc, "len", (seq,))
        lo_e = lo if lo is not None else ir.Lit(ir.INT, loc, 0)
        hi_e = hi if hi is not None else n
        if not self.spec:  # Rust panics instead of clamping
            ok = ir.Binary(ir.BOOL, loc, "and", ir.Binary(ir.BOOL, loc, "le", ir.Lit(ir.INT, loc, 0), lo_e), ir.Binary(ir.BOOL, loc, "and", ir.Binary(ir.BOOL, loc, "le", lo_e, hi_e), ir.Binary(ir.BOOL, loc, "le", hi_e, n)))
            self.pre.append(ir.AssertStmt(loc, ir.Clause("assert", ok, loc, "slice range is within bounds"), native=True))
        return self.elems_kinded(ir.Builtin(seq.ty, loc, "slice", (seq, lo_e, hi_e)), self.kind_of_elems(seq))

    def x_array_expression(self, n: Any, expect: Any, kind: Any) -> ir.Expr:
        loc = self.loc(n)
        if any(_text(c) == ";" for c in n.children):  # [v; n]
            return self._repeat(n.named_children[0], n.named_children[1], expect, loc)
        ek = None
        elem_expect = expect.elem if isinstance(expect, ir.TList) else None
        elems = [self.expr(c, elem_expect) for c in n.named_children]
        for e in elems:
            ek = ek or self.kind_of(e)
        if not elems:
            return ir.ListLit(expect if isinstance(expect, ir.TList) else ir.TList(ir.NONE), loc, ())
        t = elems[0].ty
        if any(e.ty != t for e in elems):
            raise self.err("array elements must have one type", n)
        return self.elems_kinded(ir.ListLit(ir.TList(t), loc, tuple(elems)), ek)

    def _repeat(self, vn: Any, cn: Any, expect: Any, loc: ir.Loc) -> ir.Expr:
        if self.spec:
            raise self.err("vec![v; n] in a specification", vn)
        v = self.hoist(self.expr(vn, expect.elem if isinstance(expect, ir.TList) else None))
        cnt = self.expr(cn, ir.INT, "usize")
        t = self.fl.fresh("rep", ir.TList(v.ty))
        i = self.fl.fresh("i", ir.INT)
        self.pre.append(ir.Assign(loc, t, ir.ListLit(ir.TList(v.ty), loc, ())))
        inv = ir.Clause("invariant", ir.Binary(ir.BOOL, loc, "eq", ir.Builtin(ir.INT, loc, "len", (ir.Var(ir.TList(v.ty), loc, t),)), ir.Var(ir.INT, loc, i)), loc, f"len({t}) == {i}", inferred=True)
        self.pre.append(ir.ForRange(loc, i, ir.Lit(ir.INT, loc, 0), cnt, (inv,), (ir.Append(loc, t, v),)))
        k = self.kind_of(v)
        if k:
            self.fl.elem_kinds[t] = k
        return ir.Var(ir.TList(v.ty), loc, t)

    def x_struct_expression(self, n: Any, expect: Any, kind: Any) -> ir.Expr:
        name = _text(n.child_by_field_name("name")).split("::")[-1]
        if name == "Self" and self.fl.info.owner:
            name = self.fl.info.owner
        loc = self.loc(n)
        if name not in self.fe.structs:
            if self.spec:
                raise self.err(f"struct {name} is not modelled", n)
            return ir.Extern(ir.TOpaque(name), loc, name, tuple(self.hoist(self.expr(c)) for c in n.child_by_field_name("body").named_children if c.type != "base_field_initializer"))
        s = self.fe.structs[name]
        body = n.child_by_field_name("body")
        vals: dict[str, ir.Expr] = {}
        base = None
        types = dict((f, t) for f, t in (self.fe.module.records[name].fields if s.record else self.fe.module.classes[name].fields))
        for c in body.named_children:
            if c.type == "shorthand_field_initializer":
                f = _text(c)
                vals[f] = self.x_identifier(c.named_children[0] if c.named_children else c, types.get(f), s.kinds.get(f))
            elif c.type == "field_initializer":
                f = _text(c.child_by_field_name("field"))
                vals[f] = self.copy_value(self.expr(c.child_by_field_name("value"), types.get(f), s.kinds.get(f)))
            elif c.type == "base_field_initializer":
                base = self.hoist(self.expr(c.named_children[0]))
        args = []
        for f, t in types.items():
            if f in vals:
                args.append(self.fl.coerce(vals[f], t))
            elif base is not None:
                args.append(ir.Field(t, loc, base, f))
            else:
                raise self.err(f"{name} literal is missing field '{f}'", n)
        if s.record:
            return ir.RecordLit(self.fe.module.records[name], loc, tuple(zip(types, args)))
        if self.spec:
            raise self.err("specifications cannot create objects", n)
        return self.hoist(ir.New(ir.TClass(name), loc, name, tuple(args)))

    def x_if_expression(self, n: Any, expect: Any, kind: Any) -> ir.Expr:
        loc = self.loc(n)
        cond_n = n.child_by_field_name("condition")
        cons = n.child_by_field_name("consequence")
        alt = n.child_by_field_name("alternative")
        alt_body = alt.named_children[0] if alt is not None else None
        if cond_n.type == "let_condition":
            return self._if_let(cond_n, cons, alt_body, expect, kind, loc)
        c = self.expr(cond_n, ir.BOOL)
        if c.ty != ir.BOOL:
            raise self.err("if condition must be a bool", cond_n)
        then_pre: list[ir.Stmt] = []
        tv = self.fl.block_value(cons, then_pre, expect, kind) if cons.type == "block" else None
        else_pre: list[ir.Stmt] = []
        ev = None
        if alt_body is not None:
            if alt_body.type == "block":
                ev = self.fl.block_value(alt_body, else_pre, expect, kind)
            else:  # else if
                s = self.sub()
                ev = s.expr(alt_body, expect, kind)
                else_pre = s.pre
        return self._join(c, then_pre, tv, else_pre, ev, expect, loc)

    def _join(self, c: ir.Expr, then_pre: list, tv: ir.Expr | None, else_pre: list, ev: ir.Expr | None, expect: Any, loc: ir.Loc) -> ir.Expr:
        if tv is None or ev is None or tv.ty == ir.NONE or ev.ty == ir.NONE:
            # a statement: both branches for their effects
            if tv is not None and not isinstance(tv, (ir.Lit, ir.Var)):
                then_pre.append(ir.ExprStmt(loc, tv))
            if ev is not None and not isinstance(ev, (ir.Lit, ir.Var)):
                else_pre.append(ir.ExprStmt(loc, ev))
            self.pre.append(ir.If(loc, c, tuple(then_pre), tuple(else_pre)))
            return ir.Lit(ir.NONE, loc, None)
        if self.spec and (then_pre or else_pre):
            raise self.err("blocks with statements in a specification", None)
        ty = expect if expect is not None and expect != ir.NONE else tv.ty
        tv, ev = self.fl.coerce(tv, ty), self.fl.coerce(ev, ty)
        if tv.ty != ev.ty:
            tv, ev = self._same(tv, ev, None)
        k = self.kind_of(tv) or self.kind_of(ev)
        if not then_pre and not else_pre:
            return self.kinded(ir.Ite(tv.ty, loc, c, tv, ev), k)
        t = self.fl.fresh("if", tv.ty)
        self.pre.append(ir.If(loc, c, tuple(then_pre) + (ir.Assign(loc, t, tv),), tuple(else_pre) + (ir.Assign(loc, t, ev),)))
        if k:
            self.fl.kinds[t] = k
        return ir.Var(tv.ty, loc, t)

    def _if_let(self, cond: Any, cons: Any, alt: Any, expect: Any, kind: Any, loc: ir.Loc) -> ir.Expr:
        pat = cond.child_by_field_name("pattern")
        v = self.expr(cond.child_by_field_name("value"))
        binds = self.fl._option_pattern(pat)
        if binds is None or not isinstance(v.ty, ir.TOption):
            raise self.err("only 'if let Some(x) = ...' is supported", cond)
        if self.spec:
            raise self.err("if let in a specification", cond)
        t = self.hoist(v) if not isinstance(v, ir.Var) else v
        then_pre: list[ir.Stmt] = []
        self.fl.push_scope()
        try:
            if binds:
                irn = self.fl.declare(binds, v.ty.inner, pat)
                then_pre.append(ir.Assign(loc, irn, ir.Builtin(v.ty.inner, loc, "unwrap", (t,))))
            tv = self.fl.block_value(cons, then_pre, expect, kind)
        finally:
            self.fl.pop_scope()
        else_pre: list[ir.Stmt] = []
        ev = None
        if alt is not None:
            if alt.type == "block":
                ev = self.fl.block_value(alt, else_pre, expect, kind)
            else:
                s = self.sub()
                ev = s.expr(alt, expect, kind)
                else_pre = s.pre
        c = ir.Unary(ir.BOOL, loc, "not", ir.Builtin(ir.BOOL, loc, "is_none", (t,)))
        return self._join(c, then_pre, tv, else_pre, ev, expect, loc)

    def x_match_expression(self, n: Any, expect: Any, kind: Any) -> ir.Expr:
        loc = self.loc(n)
        if self.spec:
            raise self.err("match in a specification", n)
        scrut = self.hoist(self.expr(n.child_by_field_name("value")))
        arms = [c for c in n.child_by_field_name("body").named_children if c.type == "match_arm"]
        # build an if-chain from the last arm up
        result: tuple[list[ir.Stmt], ir.Expr | None] | None = None
        conds = []
        for arm in arms:
            pat = arm.child_by_field_name("pattern")
            val = arm.child_by_field_name("value")
            cond, binds = self._pattern(pat, scrut)
            guard = pat.child_by_field_name("condition") if pat.type == "match_pattern" else None
            conds.append((cond, binds, guard, val))
        out_var = None
        chain: list[ir.Stmt] = []
        results = []
        for cond, binds, guard, val in conds:
            self.fl.push_scope()
            pre: list[ir.Stmt] = []
            for b, e in binds:
                pre.append(ir.Assign(loc, self.fl.declare(b, e.ty, val), e))
            if guard is not None:
                g = self.sub()
                gc = g.expr(guard, ir.BOOL)
                if g.pre:
                    raise self.err("match guards with side effects are not supported", guard)
                cond = ir.Binary(ir.BOOL, loc, "and", cond, gc) if not (isinstance(cond, ir.Lit) and cond.value is True) else gc
                if binds:
                    raise self.err("match guards on patterns that bind names are not supported", guard)
            if val.type == "block":
                v = self.fl.block_value(val, pre, expect, kind)
            else:
                s = self.sub()
                v = s.expr(val, expect, kind)
                pre = pre + s.pre
            self.fl.pop_scope()
            results.append((cond, pre, v))
        valued = all(v is not None and v.ty != ir.NONE for _, _, v in results) and not (expect == ir.NONE)
        ty = None
        if valued:
            ty = expect if expect is not None else next((v.ty for _, _, v in results if not (isinstance(v, ir.Lit) and v.value is None and v.ty == ir.NONE)), results[0][2].ty)  # type: ignore[union-attr]
            out_var = self.fl.fresh("match", ty)
        # rustc checks exhaustiveness: when no earlier arm matched, the last one does
        results[-1] = (ir.Lit(ir.BOOL, loc, True), results[-1][1], results[-1][2])
        tail: tuple[ir.Stmt, ...] = ()
        k = None
        for cond, pre, v in reversed(results):
            body = list(pre)
            if out_var is not None and v is not None:
                v2 = self.fl.coerce(v, ty)  # type: ignore[arg-type]
                k = k or self.kind_of(v)
                body.append(ir.Assign(loc, out_var, v2))
            elif v is not None and not isinstance(v, (ir.Lit, ir.Var)):
                body.append(ir.ExprStmt(loc, v))
            if isinstance(cond, ir.Lit) and cond.value is True:
                tail = tuple(body)
            else:
                tail = (ir.If(loc, cond, tuple(body), tail),)
        self.pre.extend(tail)
        if out_var is None:
            return ir.Lit(ir.NONE, loc, None)
        if k:
            self.fl.kinds[out_var] = k
        return ir.Var(ty, loc, out_var)  # type: ignore[arg-type]

    def _pattern(self, pat: Any, scrut: ir.Expr) -> tuple[ir.Expr, list[tuple[str, ir.Expr]]]:
        """(condition, bindings) for a match arm pattern."""
        loc = self.loc(pat)
        if pat.type == "match_pattern":
            inner = pat.named_children[0]
            return self._pattern(inner, scrut)
        txt = _text(pat)
        true = ir.Lit(ir.BOOL, loc, True)
        if txt == "_":
            return true, []
        if pat.type == "identifier" and txt not in ("None",):
            if isinstance(scrut.ty, ir.TEnum) and txt in scrut.ty.members:
                return ir.Binary(ir.BOOL, loc, "eq", scrut, self._enum_lit(scrut.ty, txt, loc)), []
            return true, [(txt, scrut)]
        if txt == "None" and isinstance(scrut.ty, ir.TOption):
            return ir.Builtin(ir.BOOL, loc, "is_none", (scrut,)), []
        if pat.type == "tuple_struct_pattern" and isinstance(scrut.ty, ir.TOption):
            b = self.fl._option_pattern(pat)
            if b is None:
                raise self.err(f"unsupported pattern {txt}", pat)
            present = ir.Unary(ir.BOOL, loc, "not", ir.Builtin(ir.BOOL, loc, "is_none", (scrut,)))
            return present, ([(b, ir.Builtin(scrut.ty.inner, loc, "unwrap", (scrut,)))] if b else [])
        if pat.type == "scoped_identifier" and isinstance(scrut.ty, ir.TEnum):
            member = txt.split("::")[-1]
            if member not in scrut.ty.members:
                raise self.err(f"{scrut.ty.name} has no variant {member}", pat)
            return ir.Binary(ir.BOOL, loc, "eq", scrut, self._enum_lit(scrut.ty, member, loc)), []
        if pat.type == "or_pattern":
            parts = [self._pattern(c, scrut) for c in pat.named_children]
            if any(b for _, b in parts):
                raise self.err("or-patterns that bind names are not supported", pat)
            out = parts[0][0]
            for c, _ in parts[1:]:
                out = ir.Binary(ir.BOOL, loc, "or", out, c)
            return out, []
        if pat.type == "range_pattern" and scrut.ty == ir.INT:
            kids = pat.named_children
            lo = self.expr(kids[0], ir.INT) if kids else None
            hi = self.expr(kids[-1], ir.INT) if len(kids) > 1 else None
            conds = []
            if lo is not None:
                conds.append(ir.Binary(ir.BOOL, loc, "le", lo, scrut))
            if hi is not None:
                conds.append(ir.Binary(ir.BOOL, loc, "le" if "..=" in txt else "lt", scrut, hi))
            out = conds[0]
            for c in conds[1:]:
                out = ir.Binary(ir.BOOL, loc, "and", out, c)
            return out, []
        if pat.type in ("integer_literal", "string_literal", "boolean_literal", "char_literal", "negative_literal"):
            lit = self.expr(pat if pat.type != "negative_literal" else pat, scrut.ty) if pat.type != "negative_literal" else ir.Lit(ir.INT, loc, int(txt.replace("_", "")))
            a, b = self._same(scrut, lit, pat)
            return ir.Binary(ir.BOOL, loc, "eq", a, b), []
        raise self.err(f"unsupported pattern {txt}", pat)

    def x_block(self, n: Any, expect: Any, kind: Any) -> ir.Expr:
        pre: list[ir.Stmt] = []
        v = self.fl.block_value(n, pre, expect, kind)
        if self.spec and pre:
            raise self.err("blocks in a specification", n)
        self.pre.extend(pre)
        return v if v is not None else ir.Lit(ir.NONE, self.loc(n), None)

    def x_unsafe_block(self, n: Any, expect: Any, kind: Any) -> ir.Expr:
        raise self.err("unsafe blocks are not checked", n)

    def x_loop_expression(self, n: Any, expect: Any, kind: Any) -> ir.Expr:
        if self.spec:
            raise self.err("loops in a specification", n)
        target = self.fl.fresh("loop", expect) if expect is not None and expect != ir.NONE else None
        self.fl.loop(n, self.pre, target)
        if target is None:
            return ir.Lit(ir.NONE, self.loc(n), None)
        return ir.Var(self.fl.env[target], self.loc(n), target)

    x_while_expression = x_loop_expression
    x_for_expression = x_loop_expression

    def x_break_expression(self, n: Any, expect: Any, kind: Any) -> ir.Expr:
        loc = self.loc(n)
        vals = [c for c in n.named_children if c.type != "label"]
        if any(c.type == "label" for c in n.named_children):
            raise self.err("labelled break is not supported yet", n)
        if vals:
            target = self.fl.loop_value[-1] if self.fl.loop_value else None
            v = self.expr(vals[0], self.fl.env.get(target) if target else None)
            if target is None:
                target = self.fl.fresh("loop", v.ty)
                self.fl.loop_value[-1] = target
            self.pre.append(ir.Assign(loc, target, self.fl.coerce(v, self.fl.env[target])))
        self.pre.append(ir.Break(loc))
        return ir.Lit(expect if expect is not None else ir.NONE, loc, None) if expect is None or expect == ir.NONE else self._never(expect, loc)

    def x_continue_expression(self, n: Any, expect: Any, kind: Any) -> ir.Expr:
        self.pre.append(ir.Continue(self.loc(n)))
        return self._never(expect, self.loc(n))

    def x_return_expression(self, n: Any, expect: Any, kind: Any) -> ir.Expr:
        loc = self.loc(n)
        if self.spec:
            raise self.err("return in a specification", n)
        vals = n.named_children
        ret = self.fl.info.ret
        if vals:
            v = self.expr(vals[0], ret, self.fl.info.ret_kind)
            self.pre.append(ir.Return(loc, self.fl.coerce(v, ret)))
        else:
            self.pre.append(ir.Return(loc, None))
        return self._never(expect, loc)

    def _never(self, expect: Any, loc: ir.Loc) -> ir.Expr:
        """The value of a diverging expression (never used: control left)."""
        if expect is None or expect == ir.NONE:
            return ir.Lit(ir.NONE, loc, None)
        if isinstance(expect, ir.TOption):
            return ir.Lit(expect, loc, None)
        return ir.Builtin(expect, loc, "from_opaque", (ir.Builtin(ir.TOpaque(""), loc, "opaque_op", (ir.Lit(ir.STR, loc, "never"),)),))

    def x_try_expression(self, n: Any, expect: Any, kind: Any) -> ir.Expr:
        """e?: return early on None / Err."""
        loc = self.loc(n)
        if self.spec:
            raise self.err("'?' in a specification", n)
        v = self.hoist(self.expr(n.named_children[0]))
        ret = self.fl.info.ret
        if isinstance(v.ty, ir.TOption):
            self.pre.append(ir.If(loc, ir.Builtin(ir.BOOL, loc, "is_none", (v,)), (ir.Return(loc, self.fl.coerce(ir.Lit(ir.NONE, loc, None), ret) if ret != ir.NONE else None),), ()))
            return ir.Builtin(v.ty.inner, loc, "unwrap", (v,))
        # Result (unchecked): Err returns early, Ok gives some value
        is_err = self.opaque("is_err", [v], ir.BOOL, loc)
        early = self.opaque("err", [v], ir.TOpaque(""), loc)
        self.pre.append(ir.If(loc, is_err, (ir.Return(loc, self.fl.coerce(early, ret) if ret != ir.NONE else None),), ()))
        return self.opaque("ok", [v], ir.TOpaque(""), loc)

    def x_closure_expression(self, n: Any, expect: Any, kind: Any) -> ir.Expr:
        if self.spec:
            raise self.err("closures in specifications appear only in .all(), .any()", n)
        # what it captures may change whenever unchecked code (which may call it) runs
        def names(x: Any) -> None:
            if x.type == "identifier":
                r = self.fl.resolve(_text(x))
                if r in self.fl.env:
                    self.fl.escaped.add(r)
            for c in x.children:
                names(c)
        body = n.child_by_field_name("body")
        if body is not None:
            names(body)
        return self.opaque("closure", [ir.Lit(ir.STR, self.loc(n), _text(n)[:40])], ir.TOpaque("closure"), self.loc(n))

    def x_tuple_expression(self, n: Any, expect: Any, kind: Any) -> ir.Expr:
        parts = [self.expr(c) for c in n.named_children]
        return self.opaque("tuple", [p if isinstance(p.ty, ir.TOpaque) else self.fl.coerce(p, ir.TOpaque("")) for p in parts], ir.TOpaque("tuple"), self.loc(n))

    def x_unit_expression(self, n: Any, expect: Any, kind: Any) -> ir.Expr:
        return ir.Lit(ir.NONE, self.loc(n), None)

    # -- calls -------------------------------------------------------------

    def opaque(self, op: str, parts: list[ir.Expr], ty: ir.Type, loc: ir.Loc) -> ir.Expr:
        return ir.Builtin(ty, loc, "opaque_op", (ir.Lit(ir.STR, loc, op), *parts))

    def args(self, n: Any) -> list[Any]:
        a = n.child_by_field_name("arguments")
        return [c for c in a.named_children if c.type not in ("line_comment", "block_comment")] if a is not None else []

    def x_call_expression(self, n: Any, expect: Any, kind: Any) -> ir.Expr:
        f = n.child_by_field_name("function")
        loc = self.loc(n)
        argn = self.args(n)
        if f.type == "field_expression":
            return self.method(f.child_by_field_name("value"), _text(f.child_by_field_name("field")), argn, n, expect, kind)
        if f.type == "generic_function":
            f = f.child_by_field_name("function")
            if f.type == "field_expression":
                return self.method(f.child_by_field_name("value"), _text(f.child_by_field_name("field")), argn, n, expect, kind)
        name = _text(f)
        if name == "Some":
            v = self.expr(argn[0], expect.inner if isinstance(expect, ir.TOption) else None, kind)
            if isinstance(v.ty, (ir.TList, ir.TDict, ir.TOption, ir.TOpaque)):
                raise self.err(f"Option<{v.ty}> is not modelled", n)
            return self.kinded(ir.Builtin(ir.TOption(v.ty), loc, "some", (v,)), self.kind_of(v))
        if name in ("Ok", "Err"):
            if self.spec:
                raise self.err("Result in a specification", n)
            v = self.expr(argn[0]) if argn else ir.Lit(ir.NONE, loc, None)
            return self.opaque(name.lower(), [self.fl.coerce(v, ir.TOpaque("")) if not isinstance(v.ty, ir.TOpaque) else v], ir.TOpaque("Result"), loc)
        if self.spec and name == "old":
            if not self.allow_old:
                raise self.err("old(...) is only meaningful in '@ensures' and invariants", n)
            e = self.expr(argn[0], expect, kind)
            return self.kinded(ir.Old(e.ty, loc, e), self.kind_of(e))
        if self.spec and name == "implies":
            a, b = self.expr(argn[0], ir.BOOL), self.expr(argn[1], ir.BOOL)
            return ir.Binary(ir.BOOL, loc, "implies", a, b)
        key = name.replace("::", ".") if "::" in name else name
        if key.startswith("Self.") and self.fl.info.owner:
            key = self.fl.info.owner + key[4:]
        info = self.fe.fns.get(key)
        if info is None:
            if key.endswith(".new") or key.endswith(".from") or key.endswith(".default"):
                owner = key.rsplit(".", 1)[0]
                if owner == "String":
                    return self.expr(argn[0], ir.STR) if argn else ir.Lit(ir.STR, loc, "")
                if owner in ("Vec", "HashMap", "BTreeMap", "VecDeque") and not argn:
                    if owner in ("HashMap", "BTreeMap"):
                        return ir.Builtin(expect if isinstance(expect, ir.TDict) else ir.TDict(ir.NONE, ir.NONE), loc, "dict_lit", ())
                    return ir.ListLit(expect if isinstance(expect, ir.TList) else ir.TList(ir.NONE), loc, ())
            if self.spec:
                raise self.err(f"'{name}' is not a checked function", n)
            args = [self.hoist(self.expr(a)) for a in argn]
            return self.hoist(ir.Extern(expect if expect is not None and expect != ir.NONE else ir.TOpaque(f"result of {name}"), loc, name, tuple(args)))
        return self.call(info, None, argn, n, expect)

    def call(self, info: FnInfo, recv: ir.Expr | None, argn: list[Any], n: Any, expect: Any) -> ir.Expr:
        loc = self.loc(n)
        params = info.params
        args: list[ir.Expr] = []
        if recv is not None:
            args.append(recv)
            params = params[1:]
        if len(argn) != len(params):
            raise self.err(f"'{info.key}' takes {len(params)} arguments", n)
        written: list[ir.Var] = []
        for p, a in zip(params, argn):
            if a.type == "reference_expression" and _is_mut_ref(a) and _deref_target(a.named_children[-1]).type == "identifier":
                v = self.expr(_deref_target(a.named_children[-1]))  # &mut v: the callee may change v
                if isinstance(v, ir.Var) and not isinstance(v.ty, (ir.TList, ir.TDict, ir.TClass)):
                    written.append(v)  # a scalar behind &mut: whatever the callee stored
            else:
                v = self.expr(a, p.ty, info.param_kinds.get(p.name))
                if a.type != "reference_expression":
                    v = self.copy_value(v)
            v = self.fl.coerce(v, p.ty)
            if v.ty != p.ty and not (isinstance(p.ty, ir.TList) and isinstance(v.ty, ir.TList) and v.ty.elem == ir.NONE):
                raise self.err(f"argument '{p.name}' of '{info.key}' expects {p.ty}, got {v.ty}", a)
            args.append(v)
        e = ir.Call(info.ret, loc, info.key, tuple(args))
        if self.spec:
            return self.kinded(e, info.ret_kind)
        if info.ret == ir.NONE:
            self.pre.append(ir.ExprStmt(loc, e))
            out: ir.Expr = ir.Lit(ir.NONE, loc, None)
        else:
            out = self.hoist(self.ranged(e, info.ret_kind) if info.ret_kind else e)
        for w in written:
            self.havoc_scalar(w, loc)
        return out

    def havoc_scalar(self, v: ir.Var, loc: ir.Loc) -> None:
        """A value written through &mut by code telic does not model here."""
        val = ir.Extern(v.ty, loc, "write through &mut", ())
        k = self.fl.kinds.get(v.name)
        self.pre.append(ir.Assign(loc, v.name, self.fl.in_range(val, k) if k and v.ty == ir.INT else val))

    def x_macro_invocation(self, n: Any, expect: Any, kind: Any) -> ir.Expr:
        name = _text(n.child_by_field_name("macro")).rstrip("!")
        loc = self.loc(n)
        tt = next((c for c in n.children if c.type == "token_tree"), None)
        body = _text(tt)[1:-1] if tt is not None else ""
        if name == "vec":
            if len(_top_level_split(body, ";")) == 2:
                v, c = _top_level_split(body, ";")
                vn, cn = self._parse_exprs(f"{v.strip()}, {c.strip()}", n)
                return self._repeat(vn, cn, expect, loc)
            nodes = self._parse_exprs(body, n) if body.strip() else []
            ek = None
            elem_expect = expect.elem if isinstance(expect, ir.TList) else None
            elems = [self.expr(c, elem_expect) for c in nodes]
            for e in elems:
                ek = ek or self.kind_of(e)
            if not elems:
                return ir.ListLit(expect if isinstance(expect, ir.TList) else ir.TList(ir.NONE), loc, ())
            if any(e.ty != elems[0].ty for e in elems):
                raise self.err("vec! elements must have one type", n)
            return self.elems_kinded(ir.ListLit(ir.TList(elems[0].ty), loc, tuple(elems)), ek)
        if self.spec:
            raise self.err(f"{name}! in a specification", n)
        if name in ("panic", "unreachable", "todo", "unimplemented"):
            # a panic is a crash, not error handling (Result is): it must be unreachable
            self.pre.append(ir.AssertStmt(loc, ir.Clause("assert", ir.Lit(ir.BOOL, loc, False), loc, f"{name}! is unreachable"), native=True))
            return self._never(expect, loc)
        if name in ("assert", "debug_assert"):
            args = self._parse_exprs(body, n)
            c = self.expr(args[0], ir.BOOL)
            text = " ".join(_text(args[0]).split())
            self.pre.append(ir.AssertStmt(loc, ir.Clause("assert", c, loc, text), native=True))
            return ir.Lit(ir.NONE, loc, None)
        if name in ("assert_eq", "assert_ne", "debug_assert_eq", "debug_assert_ne"):
            args = self._parse_exprs(body, n)
            a = self.expr(args[0])
            b = self.expr(args[1], a.ty)
            a, b = self._same(a, b, n)
            op = "eq" if name.endswith("eq") else "ne"
            text = f"{' '.join(_text(args[0]).split())} {'==' if op == 'eq' else '!='} {' '.join(_text(args[1]).split())}"
            self.pre.append(ir.AssertStmt(loc, ir.Clause("assert", ir.Binary(ir.BOOL, loc, op, a, b), loc, text), native=True))
            return ir.Lit(ir.NONE, loc, None)
        if name in ("println", "print", "eprintln", "eprint", "dbg", "trace", "debug", "info", "warn", "error", "log"):
            return ir.Lit(ir.NONE, loc, None)
        if name == "format":
            return ir.Builtin(ir.STR, loc, "str_fn", (ir.Lit(ir.STR, loc, "format"), ir.Lit(ir.STR, loc, body)))
        if name == "matches":
            parts = _top_level_split(body, ",")
            if len(parts) != 2:
                raise self.err("matches!(e, pattern)", n)
            (en,) = self._parse_exprs(parts[0], n)
            scrut = self.hoist(self.expr(en))
            pat = self._parse_pattern(parts[1], n)
            cond, binds = self._pattern(pat, scrut)
            if binds:
                raise self.err("matches! with bindings is not supported", n)
            return cond
        return self.hoist(ir.Extern(expect if expect is not None and expect != ir.NONE else ir.TOpaque(f"{name}!"), loc, f"{name}!", ()))

    def _parse_exprs(self, text: str, n: Any) -> list[Any]:
        src = f"fn __m() {{ __f({text}); }}"
        tree = parser().parse(src.encode("utf8"))
        if tree.root_node.has_error:
            raise self.err("cannot parse the macro's arguments", n)
        call = tree.root_node.children[0].child_by_field_name("body").named_children[0].named_children[0]
        nodes = [c for c in call.child_by_field_name("arguments").named_children]
        return [_Shifted(c, n) for c in nodes]  # type: ignore[misc]

    def _parse_pattern(self, text: str, n: Any) -> Any:
        src = f"fn __m() {{ match 0 {{ {text} => () }} }}"
        tree = parser().parse(src.encode("utf8"))
        if tree.root_node.has_error:
            raise self.err("cannot parse the pattern", n)
        arm = tree.root_node.children[0].child_by_field_name("body").named_children[0].named_children[0].child_by_field_name("body").named_children[0]
        return _Shifted(arm.child_by_field_name("pattern"), n)

    # -- methods -------------------------------------------------------------

    def method(self, recv_n: Any, m: str, argn: list[Any], n: Any, expect: Any, kind: Any) -> ir.Expr:
        loc = self.loc(n)
        chain = self.iter_chain(recv_n, m, argn, n, expect)
        if chain is not None:
            return chain
        recv = self.expr(recv_n)
        t = recv.ty
        # checked methods of a struct
        if isinstance(t, (ir.TClass, ir.TRecord)):
            info = self.fe.fns.get(f"{t.name}.{m}")
            if info is not None:
                return self.call(info, recv, argn, n, expect)
            if m == "clone":
                if isinstance(t, ir.TRecord):
                    return recv
                if self.spec:
                    raise self.err("clone() in a specification", n)
                decl = self.fe.module.classes[t.name]
                return self.hoist(ir.New(t, loc, t.name, tuple(ir.Field(ft, loc, recv, f) for f, ft in decl.fields)))
        k = self.kind_of(recv)
        if t == ir.INT:
            return self.int_method(recv, m, argn, n, k)
        if t == ir.REAL:
            if m in ("abs", "floor", "ceil", "sqrt", "round", "trunc", "min", "max", "powi", "powf") and not self.spec:
                args = [self.expr(a, ir.REAL) for a in argn]
                if m == "abs":
                    return ir.Builtin(ir.REAL, loc, "abs", (recv,))
                if m in ("min", "max"):
                    return ir.Builtin(ir.REAL, loc, m, (recv, args[0]))
                return self.opaque(f"f64.{m}", [recv, *args], ir.REAL, loc)
        if isinstance(t, ir.TOption):
            return self.option_method(recv, m, argn, n, expect)
        if isinstance(t, ir.TList):
            return self.vec_method(recv, recv_n, m, argn, n, expect)
        if isinstance(t, ir.TDict):
            return self.map_method(recv, recv_n, m, argn, n, expect)
        if t == ir.STR:
            return self.str_method(recv, m, argn, n, expect)
        if self.spec:
            raise self.err(f".{m}() is not supported in specifications here", n)
        if isinstance(t, ir.TOpaque) and m in ("unwrap", "expect"):
            return self.opaque(f"unwrap", [recv], ir.TOpaque(""), loc)  # a Result from unchecked code
        args = [self.hoist(self.expr(a)) for a in argn]
        return self.hoist(ir.Extern(expect if expect is not None and expect != ir.NONE else ir.TOpaque(f"result of .{m}()"), loc, f"{t}.{m}", (recv, *args)))

    def int_method(self, recv: ir.Expr, m: str, argn: list[Any], n: Any, k: str | None) -> ir.Expr:
        loc = self.loc(n)
        args = [self.expr(a, ir.INT, k) for a in argn]
        if m == "abs":
            return self.checked(ir.Builtin(ir.INT, loc, "abs", (recv,)), k)
        if m in ("min", "max"):
            return self.kinded(ir.Builtin(ir.INT, loc, m, (recv, args[0])), k)
        if m == "pow" and argn and argn[0].type == "integer_literal":
            p = int(_text(argn[0]).rstrip("u32").replace("_", ""))
            out: ir.Expr = ir.Lit(ir.INT, loc, 1)
            for _ in range(p):
                out = ir.Binary(ir.INT, loc, "mul", out, recv)
            return self.checked(out, k)
        if k and m in ("saturating_add", "saturating_sub", "saturating_mul"):
            lo, hi = int_range(k)
            op = {"saturating_add": "add", "saturating_sub": "sub", "saturating_mul": "mul"}[m]
            raw = ir.Binary(ir.INT, loc, op, recv, args[0])
            return self.kinded(ir.Builtin(ir.INT, loc, "min", (ir.Builtin(ir.INT, loc, "max", (raw, ir.Lit(ir.INT, loc, lo))), ir.Lit(ir.INT, loc, hi))), k)
        if k and m in ("checked_add", "checked_sub", "checked_mul", "checked_div"):
            lo, hi = int_range(k)
            op = {"checked_add": "add", "checked_sub": "sub", "checked_mul": "mul", "checked_div": "tdiv"}[m]
            if op == "tdiv":
                ok = ir.Binary(ir.BOOL, loc, "ne", args[0], ir.Lit(ir.INT, loc, 0))
                raw = ir.Ite(ir.INT, loc, ok, ir.Binary(ir.INT, loc, "tdiv", recv, args[0]), ir.Lit(ir.INT, loc, 0))
            else:
                raw = ir.Binary(ir.INT, loc, op, recv, args[0])
                ok = ir.Lit(ir.BOOL, loc, True)
            fits = ir.Binary(ir.BOOL, loc, "and", ok, ir.Binary(ir.BOOL, loc, "and", ir.Binary(ir.BOOL, loc, "le", ir.Lit(ir.INT, loc, lo), raw), ir.Binary(ir.BOOL, loc, "le", raw, ir.Lit(ir.INT, loc, hi))))
            return self.kinded(ir.Ite(ir.TOption(ir.INT), loc, fits, ir.Builtin(ir.TOption(ir.INT), loc, "some", (raw,)), ir.Lit(ir.TOption(ir.INT), loc, None)), k)
        if k and m in ("wrapping_add", "wrapping_sub", "wrapping_mul"):
            signed, bits = INT_KINDS[k]
            op = {"wrapping_add": "add", "wrapping_sub": "sub", "wrapping_mul": "mul"}[m]
            raw = ir.Binary(ir.INT, loc, op, recv, args[0])
            mod = ir.Lit(ir.INT, loc, 1 << bits)
            if not signed:
                return self.kinded(ir.Binary(ir.INT, loc, "fmod", raw, mod), k)
            h = ir.Lit(ir.INT, loc, 1 << (bits - 1))
            return self.kinded(ir.Binary(ir.INT, loc, "sub", ir.Binary(ir.INT, loc, "fmod", ir.Binary(ir.INT, loc, "add", raw, h), mod), h), k)
        if m in ("to_string",):
            return ir.Builtin(ir.STR, loc, "str_of_int", (recv,))
        if m == "clone":
            return recv
        if m in ("is_positive", "is_negative"):
            return ir.Binary(ir.BOOL, loc, "gt" if m == "is_positive" else "lt", recv, ir.Lit(ir.INT, loc, 0))
        if m == "signum":
            return self.kinded(ir.Ite(ir.INT, loc, ir.Binary(ir.BOOL, loc, "gt", recv, ir.Lit(ir.INT, loc, 0)), ir.Lit(ir.INT, loc, 1), ir.Ite(ir.INT, loc, ir.Binary(ir.BOOL, loc, "lt", recv, ir.Lit(ir.INT, loc, 0)), ir.Lit(ir.INT, loc, -1), ir.Lit(ir.INT, loc, 0))), k)
        if self.spec:
            raise self.err(f"integer method .{m}() in a specification", n)
        return self.ranged(self.opaque(f"int.{m}", [recv, *args], ir.INT, loc), k)

    def option_method(self, recv: ir.Expr, m: str, argn: list[Any], n: Any, expect: Any) -> ir.Expr:
        loc = self.loc(n)
        t = recv.ty
        assert isinstance(t, ir.TOption)
        k = self.kind_of(recv)
        if m in ("unwrap", "expect"):
            u = ir.Builtin(t.inner, loc, "unwrap", (recv,))
            return self.ranged(u, k) if t.inner == ir.INT else self.kinded(u, k)
        if m == "is_some":
            return ir.Unary(ir.BOOL, loc, "not", ir.Builtin(ir.BOOL, loc, "is_none", (recv,)))
        if m == "is_none":
            return ir.Builtin(ir.BOOL, loc, "is_none", (recv,))
        if m in ("unwrap_or", "unwrap_or_default"):
            d = self.expr(argn[0], t.inner, k) if argn else _default(t.inner, loc)
            if d is None:
                raise self.err(f"no default for {t.inner}", n)
            v = ir.Ite(t.inner, loc, ir.Builtin(ir.BOOL, loc, "is_none", (recv,)), self.fl.coerce(d, t.inner), ir.Builtin(t.inner, loc, "unwrap", (recv,)))
            return self.ranged(v, k) if t.inner == ir.INT else self.kinded(v, k)
        if m in ("clone", "copied", "cloned", "as_ref"):
            return recv
        if self.spec:
            raise self.err(f"Option method .{m}() in a specification", n)
        return self.hoist(ir.Extern(expect if expect is not None and expect != ir.NONE else ir.TOpaque(""), loc, f"Option.{m}", (recv,)))

    def vec_method(self, recv: ir.Expr, recv_n: Any, m: str, argn: list[Any], n: Any, expect: Any) -> ir.Expr:
        loc = self.loc(n)
        t = recv.ty
        assert isinstance(t, ir.TList)
        ek = self.kind_of_elems(recv)
        length = ir.Builtin(ir.INT, loc, "len", (recv,))
        if m == "len":
            if self.spec:
                return self.kinded(length, "usize")
            # a Vec never holds more than isize::MAX elements
            return self.kinded(ir.Builtin(ir.INT, loc, "in_range", (length, ir.Lit(ir.INT, loc, 0), ir.Lit(ir.INT, loc, (1 << 63) - 1))), "usize")
        if m == "is_empty":
            return ir.Binary(ir.BOOL, loc, "eq", length, ir.Lit(ir.INT, loc, 0))
        if m == "contains":
            v = self.expr(argn[0], t.elem, ek)
            return ir.Builtin(ir.BOOL, loc, "contains", (recv, self.fl.coerce(v, t.elem)))
        if m in ("first", "last", "get"):
            if isinstance(t.elem, (ir.TList, ir.TDict)):
                raise self.err("Option of a container is not modelled", n)
            i = self.expr(argn[0], ir.INT, "usize") if m == "get" else (ir.Lit(ir.INT, loc, 0) if m == "first" else ir.Binary(ir.INT, loc, "sub", length, ir.Lit(ir.INT, loc, 1)))
            inb = ir.Binary(ir.BOOL, loc, "and", ir.Binary(ir.BOOL, loc, "le", ir.Lit(ir.INT, loc, 0), i), ir.Binary(ir.BOOL, loc, "lt", i, length))
            ot = ir.TOption(t.elem)
            return self.kinded(ir.Ite(ot, loc, inb, ir.Builtin(ot, loc, "some", (ir.Index(t.elem, loc, recv, i, wrap=False),)), ir.Lit(ot, loc, None)), ek)
        if m in ("clone", "to_vec", "iter", "into_iter", "as_slice", "to_owned"):
            return recv
        if self.spec:
            raise self.err(f"Vec method .{m}() in a specification", n)
        if m == "push":
            v = self.fl.coerce(self.expr(argn[0], t.elem if t.elem != ir.NONE else None, ek), t.elem) if t.elem != ir.NONE else self.expr(argn[0])
            if isinstance(recv, ir.Var):
                if t.elem == ir.NONE:
                    self.fl.env[recv.name] = ir.TList(v.ty)
                    k2 = self.kind_of(v)
                    if k2:
                        self.fl.elem_kinds[recv.name] = k2
                self.pre.append(ir.Append(loc, recv.name, v))
                return ir.Lit(ir.NONE, loc, None)
            if isinstance(recv, ir.Field) and isinstance(recv.obj.ty, ir.TClass):
                self.pre.append(ir.FieldAssign(loc, recv.obj, recv.obj.ty.name, recv.name, ir.Builtin(t, loc, "list_append", (recv, v))))
                return ir.Lit(ir.NONE, loc, None)
            raise self.err("push needs a Vec variable or field", n)
        if m == "pop" and isinstance(recv, ir.Var):
            ot = ir.TOption(t.elem)
            tv = self.fl.fresh("pop", ot)
            last = ir.Binary(ir.INT, loc, "sub", length, ir.Lit(ir.INT, loc, 1))
            self.pre.append(ir.If(loc, ir.Binary(ir.BOOL, loc, "gt", length, ir.Lit(ir.INT, loc, 0)), (ir.Assign(loc, tv, ir.Builtin(ot, loc, "some", (ir.Index(t.elem, loc, recv, last, wrap=False),))), ir.Assign(loc, recv.name, ir.Builtin(t, loc, "slice", (recv, ir.Lit(ir.INT, loc, 0), last)))), (ir.Assign(loc, tv, ir.Lit(ot, loc, None)),)))
            if ek:
                self.fl.kinds[tv] = ek
            return ir.Var(ot, loc, tv)
        if m == "extend_from_slice" or m == "extend" and isinstance(recv, ir.Var):
            ys = self.expr(argn[0], t)
            if isinstance(ys.ty, ir.TList) and isinstance(recv, ir.Var):
                self.pre.append(ir.Assign(loc, recv.name, ir.Builtin(t, loc, "list_concat", (recv, self.fl.coerce(ys, t)))))
                return ir.Lit(ir.NONE, loc, None)
        if m == "swap" and isinstance(recv, ir.Var) and len(argn) == 2:
            i, j = self.hoist(self.expr(argn[0], ir.INT, "usize")), self.hoist(self.expr(argn[1], ir.INT, "usize"))
            a = self.hoist(ir.Index(t.elem, loc, recv, i, wrap=False))
            b = self.hoist(ir.Index(t.elem, loc, recv, j, wrap=False))
            self.pre.append(ir.IndexAssign(loc, recv.name, i, b, wrap=False))
            self.pre.append(ir.IndexAssign(loc, recv.name, j, a, wrap=False))
            return ir.Lit(ir.NONE, loc, None)
        if m == "clear" and isinstance(recv, ir.Var):
            self.pre.append(ir.Assign(loc, recv.name, ir.ListLit(t, loc, ())))
            return ir.Lit(ir.NONE, loc, None)
        if m == "truncate" and isinstance(recv, ir.Var):
            k = self.expr(argn[0], ir.INT, "usize")
            self.pre.append(ir.Assign(loc, recv.name, ir.Builtin(t, loc, "slice", (recv, ir.Lit(ir.INT, loc, 0), ir.Builtin(ir.INT, loc, "min", (k, length))))))
            return ir.Lit(ir.NONE, loc, None)
        mutating = m in ("sort", "sort_unstable", "reverse", "dedup", "retain", "insert", "remove", "sort_by", "sort_by_key", "drain", "iter_mut", "resize")
        args = [self.hoist(self.expr(a)) for a in argn]
        if mutating and isinstance(recv, ir.Var):
            # the list changes in a way telic does not track: an unchecked call that may change it
            call = ir.Extern(ir.NONE if m not in ("remove", "drain") else ir.TOpaque(""), loc, f"Vec.{m}", (recv, *args))
            if m in ("sort", "sort_unstable", "reverse", "sort_by", "sort_by_key"):
                # same length, same elements in some order
                before = self.hoist(length)
                self.pre.append(ir.ExprStmt(loc, call))
                self.pre.append(ir.AssumeStmt(loc, ir.Clause("assume", ir.Binary(ir.BOOL, loc, "eq", length, before), loc, f"{m} keeps the length")))
                return ir.Lit(ir.NONE, loc, None)
            return self.hoist(call) if call.ty != ir.NONE else (self.pre.append(ir.ExprStmt(loc, call)) or ir.Lit(ir.NONE, loc, None))  # type: ignore[func-returns-value]
        pure_recv = self.fl.coerce(recv, ir.TOpaque("")) if isinstance(recv, ir.Var) else recv
        return self.hoist(ir.Extern(expect if expect is not None and expect != ir.NONE else ir.TOpaque(f"result of .{m}()"), loc, f"Vec.{m}", (pure_recv, *args)))

    def map_method(self, recv: ir.Expr, recv_n: Any, m: str, argn: list[Any], n: Any, expect: Any) -> ir.Expr:
        loc = self.loc(n)
        t = recv.ty
        assert isinstance(t, ir.TDict)
        if m == "contains_key":
            return ir.Builtin(ir.BOOL, loc, "dict_has", (recv, self.expr(argn[0], t.key)))
        if m == "get":
            if isinstance(t.val, (ir.TList, ir.TDict)):
                raise self.err("Option of a container is not modelled", n)
            return self.kinded(ir.Builtin(ir.TOption(t.val), loc, "dict_get_opt", (recv, self.expr(argn[0], t.key))), self.kind_of_elems(recv))
        if m in ("clone",):
            return recv
        if self.spec:
            raise self.err(f"map method .{m}() in a specification", n)
        if m == "insert" and isinstance(recv, ir.Var):
            k = self.hoist(self.expr(argn[0], t.key))
            v = self.fl.coerce(self.expr(argn[1], t.val, self.kind_of_elems(recv)), t.val)
            old = self.hoist(ir.Builtin(ir.TOption(t.val), loc, "dict_get_opt", (recv, k))) if not isinstance(t.val, (ir.TList, ir.TDict)) else None
            self.pre.append(ir.IndexAssign(loc, recv.name, k, v, wrap=False))
            return old if old is not None else ir.Lit(ir.NONE, loc, None)
        if m == "remove" and isinstance(recv, ir.Var):
            k = self.hoist(self.expr(argn[0], t.key))
            old = self.hoist(ir.Builtin(ir.TOption(t.val), loc, "dict_get_opt", (recv, k))) if not isinstance(t.val, (ir.TList, ir.TDict)) else None
            self.pre.append(ir.DictDel(loc, recv.name, k, strict=False))
            return old if old is not None else ir.Lit(ir.NONE, loc, None)
        if m == "len":
            return self.hoist(ir.Extern(ir.INT, loc, "HashMap.len", (self.fl.coerce(recv, ir.TOpaque("")),)))
        args = [self.hoist(self.expr(a)) for a in argn]
        return self.hoist(ir.Extern(expect if expect is not None and expect != ir.NONE else ir.TOpaque(""), loc, f"HashMap.{m}", (recv, *args)))

    def str_method(self, recv: ir.Expr, m: str, argn: list[Any], n: Any, expect: Any) -> ir.Expr:
        loc = self.loc(n)
        if m in ("to_string", "to_owned", "clone", "as_str", "into", "trim_end_matches") and not argn:
            return recv
        if m == "is_empty":
            return ir.Binary(ir.BOOL, loc, "eq", recv, ir.Lit(ir.STR, loc, ""))
        if m in ("starts_with", "ends_with", "contains") and len(argn) == 1:
            a = self.expr(argn[0], ir.STR)
            if a.ty == ir.STR:
                return ir.Builtin(ir.BOOL, loc, {"starts_with": "str_startswith", "ends_with": "str_endswith", "contains": "str_contains"}[m], (recv, a))
        if m == "len":
            # bytes of UTF-8, not characters: unknown here, but a usize
            return self.ranged(self.opaque("str.len_bytes", [recv], ir.INT, loc), "usize")
        if self.spec:
            raise self.err(f"string method .{m}() in a specification", n)
        args = [self.expr(a) for a in argn]
        if m in ("trim", "to_lowercase", "to_uppercase", "replace", "trim_start", "trim_end", "repeat"):
            return ir.Builtin(ir.STR, loc, "str_fn", (ir.Lit(ir.STR, loc, m), recv, *[a if not isinstance(a.ty, (ir.TList, ir.TDict)) else self.fl.coerce(a, ir.TOpaque("")) for a in args]))
        return self.hoist(ir.Extern(expect if expect is not None and expect != ir.NONE else ir.TOpaque(""), loc, f"str.{m}", (recv, *[self.hoist(a) for a in args])))

    # -- iterator chains ---------------------------------------------------

    def iter_chain(self, recv_n: Any, m: str, argn: list[Any], n: Any, expect: Any) -> ir.Expr | None:
        """xs.iter()[.map(f)][.filter(p)].{sum,count,all,any,collect,max,min}()
        and (a..b).all(|i| ...): comprehensions and quantifiers."""
        if m not in ("sum", "count", "all", "any", "collect", "product", "max", "min"):
            return None
        stages: list[tuple[str, Any]] = []
        cur = recv_n
        while cur.type == "call_expression":
            f = cur.child_by_field_name("function")
            if f.type == "generic_function":
                f = f.child_by_field_name("function")
            if f.type != "field_expression":
                break
            name = _text(f.child_by_field_name("field"))
            if name in ("map", "filter"):
                stages.append((name, self.args(cur)[0] if self.args(cur) else None))
                cur = f.child_by_field_name("value")
                continue
            if name in ("iter", "into_iter", "copied", "cloned"):
                cur = f.child_by_field_name("value")
                continue
            break
        stages.reverse()
        loc = self.loc(n)
        base = cur
        while base.type == "parenthesized_expression":
            base = base.named_children[0]
        rng = None
        if base.type == "range_expression":
            kids = base.named_children
            if len(kids) != 2:
                return None
            lo, hi = self.expr(kids[0], ir.INT), self.expr(kids[1], ir.INT)
            if "..=" in _text(base):
                hi = ir.Binary(ir.INT, loc, "add", hi, ir.Lit(ir.INT, loc, 1))
            rng = (lo, hi)
            seq = None
        else:
            if base is recv_n and m in ("max", "min") and not stages:
                return None  # a.max(b) on numbers
            try:
                seq = self.expr(base)
            except LowerError:
                return None
            if not isinstance(seq.ty, ir.TList):
                return None
        # quantifiers
        if m in ("all", "any") and len(argn) == 1 and argn[0].type == "closure_expression" and not stages:
            name, body_n = self._closure(argn[0])
            kind = "forall" if m == "all" else "exists"
            idx = f"{name}$q{self.fl.tmp}"
            self.fl.tmp += 1
            s = self.sub()
            if rng is not None:
                s.bound[name] = ir.INT
                body = s.expr(body_n, ir.BOOL)
                if s.pre:
                    raise self.err("the predicate of .all()/.any() must not have effects", n)
                body = _rename(body, name, idx)
                return ir.Quant(ir.BOOL, loc, kind, idx, rng[0], rng[1], body)
            assert seq is not None
            s.bound[name] = seq.ty.elem
            body = s.expr(body_n, ir.BOOL)
            if s.pre:
                raise self.err("the predicate of .all()/.any() must not have effects", n)
            return ir.Quant(ir.BOOL, loc, kind, idx, ir.Lit(ir.INT, loc, 0), ir.Builtin(ir.INT, loc, "len", (seq,)), body, elem=name, seq=seq)
        if rng is not None:
            return None
        assert seq is not None
        cur_seq = seq
        ek = self.kind_of_elems(seq)
        for st, clo in stages:
            if clo is None or clo.type != "closure_expression":
                return None
            name, body_n = self._closure(clo)
            s = self.sub()
            s.bound[name] = cur_seq.ty.elem  # type: ignore[union-attr]
            if ek:
                self.fl.kinds[name] = ek
            body = s.expr(body_n, ir.BOOL if st == "filter" else None, ek)
            if s.pre:
                return None  # effects in the closure: leave it to an unchecked call
            if st == "map":
                if isinstance(body.ty, (ir.TList, ir.TDict, ir.TNone)):
                    return None
                ek = s.kind_of(body)
                cur_seq = ir.Builtin(ir.TList(body.ty), loc, "comp", (cur_seq, ir.Lit(ir.STR, loc, name), body))
            else:
                cur_seq = ir.Builtin(cur_seq.ty, loc, "comp", (cur_seq, ir.Lit(ir.STR, loc, name), ir.Var(cur_seq.ty.elem, loc, name), body))  # type: ignore[union-attr]
        if m == "count":
            return self.kinded(ir.Builtin(ir.INT, loc, "len", (cur_seq,)), "usize")
        if m == "sum":
            elem = cur_seq.ty.elem  # type: ignore[union-attr]
            if elem not in (ir.INT, ir.REAL):
                return None
            total = ir.Builtin(elem, loc, "sum", (cur_seq,))
            return self.checked(total, ek) if elem == ir.INT else total
        if m == "collect":
            return self.elems_kinded(cur_seq, ek)
        return None

    def _closure(self, c: Any) -> tuple[str, Any]:
        ps = c.child_by_field_name("parameters")
        names = [_text(p).lstrip("&").strip() for p in ps.named_children] if ps is not None else []
        if len(names) != 1 or not re.fullmatch(r"[A-Za-z_]\w*", names[0].split(":")[0].strip()):
            raise self.err("closures here take one simple parameter", c)
        return names[0].split(":")[0].strip(), c.child_by_field_name("body")


def _rename(e: ir.Expr, old: str, new: str) -> ir.Expr:
    """Rename a bound variable (the quantified index) throughout an expression."""
    import dataclasses

    if isinstance(e, ir.Var) and e.name == old:
        return ir.Var(e.ty, e.loc, new)
    changes = {}
    for f in dataclasses.fields(e):
        v = getattr(e, f.name)
        if isinstance(v, ir.Expr):
            changes[f.name] = _rename(v, old, new)
        elif isinstance(v, tuple) and v and all(isinstance(x, ir.Expr) for x in v):
            changes[f.name] = tuple(_rename(x, old, new) for x in v)
    return dataclasses.replace(e, **changes) if changes else e


def _is_mut_ref(n: Any) -> bool:
    return re.match(r"^&\s*mut\b", _text(n)) is not None


def _deref_target(n: Any) -> Any:
    """&mut *v -> v"""
    while n.type == "unary_expression" and _text(n.children[0]) == "*":
        n = n.named_children[0]
    return n


def _default(t: ir.Type, loc: ir.Loc) -> ir.Expr | None:
    if t == ir.INT:
        return ir.Lit(ir.INT, loc, 0)
    if t == ir.REAL:
        return ir.Lit(ir.REAL, loc, Fraction(0))
    if t == ir.BOOL:
        return ir.Lit(ir.BOOL, loc, False)
    if t == ir.STR:
        return ir.Lit(ir.STR, loc, "")
    return None


def _top_level_split(text: str, sep: str) -> list[str]:
    parts, depth, cur, instr = [], 0, "", False
    for ch in text:
        if ch == '"':
            instr = not instr
        if not instr:
            if ch in "([{":
                depth += 1
            elif ch in ")]}":
                depth -= 1
            elif ch == sep and depth == 0:
                parts.append(cur)
                cur = ""
                continue
        cur += ch
    parts.append(cur)
    return parts


class _Shifted:
    """A node parsed from a macro's text, located at the macro in the file."""

    def __init__(self, node: Any, anchor: Any):
        self._n = node
        self._a = anchor

    def __getattr__(self, name: str) -> Any:
        v = getattr(self._n, name)
        if name in ("children", "named_children"):
            return [_Shifted(c, self._a) for c in v]
        if name in ("start_point", "end_point"):
            return self._a.start_point if name == "start_point" else self._a.end_point
        return v

    def child_by_field_name(self, f: str) -> Any:
        c = self._n.child_by_field_name(f)
        return _Shifted(c, self._a) if c is not None else None

    @property
    def text(self) -> bytes:
        return self._n.text


class _Synthetic:
    """A binary_expression built from a compound assignment."""

    def __init__(self, type_: str, at: Any, fields: dict[str, Any]):
        self.type = type_
        self._at = at
        self._f = fields
        self.start_point, self.end_point = at.start_point, at.end_point

    def child_by_field_name(self, f: str) -> Any:
        v = self._f.get(f)
        if isinstance(v, str):
            return _Text(v)
        return v


class _Text:
    def __init__(self, s: str):
        self.text = s.encode()


def lower_rust(path: str, source: str) -> ir.Module:
    return RustFrontend(path, source).run()
