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

import dataclasses
import os
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
    parse_aim_directive,
)
from ..lifecycle import LifecycleError
from ..lifecycle import build as build_lifecycle
from .rust_crate import ModPath, Res

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
    name: str  # IR name: the Rust name, qualified when several modules define one
    fields: list[tuple[str, str, Any]]  # (name, rust type text, type node); a tuple struct's are _0, _1, ...
    copy: bool
    node: Any
    record: bool = False  # a Copy struct of scalars: a value
    kinds: dict[str, str] = field(default_factory=dict)  # field -> integer kind
    mod: ModPath = ()
    tuple: bool = False
    eq: str = ""  # what '==' runs: "derive", "impl" (its PartialEq::eq), "" (none known)
    src: str = ""  # the Rust name
    generics: dict[str, list[str]] = field(default_factory=dict)


@dataclass
class EnumInfo:
    """An enum whose variants carry data, modelled as a record of a tag and
    every variant's fields (those of the other variants hold defaults)."""

    name: str
    src: str
    mod: ModPath
    node: Any
    variants: list[tuple[str, str, list[tuple[str, str, Any]]]]  # (variant, unit|tuple|struct, [(field, rust type, node)])
    copy: bool
    eq: str = ""
    record: ir.TRecord | None = None
    why: str = ""  # why it is not modelled (record is None)
    kinds: dict[str, str] = field(default_factory=dict)  # record slot -> integer kind
    generics: dict[str, list[str]] = field(default_factory=dict)

    def variant(self, name: str) -> tuple[str, str, list[tuple[str, str, Any]]] | None:
        return next((v for v in self.variants if v[0] == name), None)


@dataclass
class TraitInfo:
    name: str
    src: str
    mod: ModPath
    node: Any
    file: str
    methods: dict[str, Any] = field(default_factory=dict)  # name -> signature or default-bodied fn


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
    mod: ModPath = ()
    file: str = ""
    generics: dict[str, list[str]] = field(default_factory=dict)  # type parameter -> trait bounds
    trait_method: str | None = None  # key of the trait method this implements: its contract applies
    decl: bool = False  # a trait's method declaration: callers through the trait use its contract
    lens: dict[str, int] = field(default_factory=dict)  # [T; N] parameters -> N


RESULT_TAG = ir.TEnum("Result$tag", ("Ok", "Err"))


def _slot(variant: str, fname: str) -> str:
    return f"{variant}_{fname}"


def _tag_of(t: ir.Type) -> str:
    return re.sub(r"\W", "_", str(t))


def _derives(attrs: list[str], trait: str) -> bool:
    return any(re.search(rf"\b{trait}\b", a) for a in attrs if "derive" in a)


class RustFrontend:
    def __init__(self, path: str, source: str, abs_path: str | None = None, root: str | None = None):
        self.path = path
        self.source = source
        self.lines = source.splitlines()
        self.abs = os.path.normpath(os.path.abspath(abs_path or path))
        self.root = os.path.normpath(os.path.abspath(root)) if root else os.getcwd()
        self.module = ir.Module(path=path, language="rust", source=source)
        self.module.assumptions = list(RUST_ASSUMPTIONS)
        self.structs: dict[str, StructInfo] = {}
        self.enums: dict[str, ir.TEnum] = {}  # enums without data
        self.data_enums: dict[str, EnumInfo] = {}
        self.traits: dict[str, TraitInfo] = {}
        self.classes: dict[str, ir.ClassDecl] = {}  # every class of the crate; module.classes holds this file's
        self.records: dict[str, ir.TRecord] = {}
        self.aliases: dict[tuple[ModPath, str], Any] = {}  # type aliases -> their item
        self.consts: dict[tuple[ModPath, str], tuple[Any, str | None]] = {}  # -> (literal node, int kind)
        self.const_types: dict[tuple[ModPath, str], Any] = {}  # other constants and statics -> their type
        self.fns: dict[str, FnInfo] = {}  # by "file\0key": keys are unique per file only
        self.file_keys: dict[str, set[str]] = {}
        self.fn_keys: dict[int, str] = {}  # id(fn node) -> uid in fns
        self.methods: dict[tuple[str, str], str] = {}  # (type or trait, method) -> uid; ("default:" + m) for a trait's default body
        self.impls_of: dict[str, list[str]] = {}  # type -> traits it implements
        self.ir_names: dict[int, str] = {}  # id(type item node) -> IR name
        self.contract_lines: list[ContractLine] = []
        self.other_contracts: dict[str, tuple[list[str], list[ContractLine]]] = {}
        self.cur_mod: ModPath = ()
        self.cur_generics: dict[str, list[str]] = {}
        self.cur_self: str | None = None
        self.cur_subst: dict[str, ir.Type] = {}
        self._alias_stack: list[int] = []
        self._enum_stack: list[str] = []
        self.call_names: dict[str, str] = {}
        self.result_kinds: dict[str, dict[str, str]] = {}  # Result record -> slot -> integer kind

    # -- entry ----------------------------------------------------------

    def run(self) -> ir.Module:
        from .rust_crate import crate_for

        self.crate = crate_for(self.abs, self.source)
        tree = self.crate.trees.get(self.abs) or parser().parse(self.source.encode("utf8"))
        root = tree.root_node
        if root.has_error:
            bad = _first_error(root)
            self.module.problems.append(("syntax error (or Rust syntax telic's parser does not know)", ir.Loc(bad.start_point[0] + 1 if bad else 1)))
        for f, msg, line in self.crate.problems:
            if f == self.abs:
                self.module.notes.append((msg, ir.Loc(line)))
        comments: list = []
        _collect_comments(root, comments)
        try:
            self.contract_lines = parse_comment_lines(comments, "//")
        except ContractSyntaxError as e:
            self.module.problems.append((str(e), ir.Loc(e.line, e.col)))
            return self.module
        self.other_contracts[self.abs] = (self.lines, self.contract_lines)
        self._declare()
        self._signatures()
        mine = set(self.crate.modules_in(self.abs))
        for info in self.fns.values():
            key = info.key
            if info.file != self.abs or info.mod not in mine:
                continue
            self._enter(info)
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
            if cl.keyword == "aim":
                try:
                    ids, text = parse_aim_directive(cl)
                except ContractSyntaxError as e:
                    self.module.problems.append((str(e), ir.Loc(e.line, e.col)))
                    continue
                if text is not None:
                    self.module.aims.append(ir.AimDecl(ids[0], text, ir.Loc(cl.line, cl.col)))
                else:
                    self.module.problems.append((f"'@aim {', '.join(ids)}' outside a function links nothing", ir.Loc(cl.line, cl.col)))
                continue
            self.module.problems.append((f"'@{cl.keyword}' is not attached to anything telic checks", ir.Loc(cl.line, cl.col)))
        self.module.records.update(self.records)
        return self.module

    def _enter(self, info: FnInfo) -> None:
        self.cur_mod, self.cur_generics, self.cur_self, self.cur_subst = info.mod, info.generics, info.owner, {}

    def _stub(self, info: FnInfo, msg: str, line: int) -> ir.Function:
        n = info.node
        fn = ir.Function(info.key, ir.Loc(n.start_point[0] + 1, n.start_point[1]), n.end_point[0] + 1, info.params, info.ret, source=_text(n))
        fn.unsupported.append((msg, ir.Loc(line or n.start_point[0] + 1)))
        return fn

    def rel(self, file: str) -> str:
        return os.path.relpath(file, self.root)

    def call_name(self, info: FnInfo) -> str:
        """How this module's IR names a call to ``info`` (imported when it
        lives in another file)."""
        if info.file == self.abs:
            return info.key
        name = self.call_names.get(info.key + "\0" + info.file)
        if name is None:
            name = info.key
            local = self.file_keys.get(self.abs, set())
            while name in local or name in self.module.imports and self.module.imports[name] != (self.rel(info.file), info.key):
                name += "@" + (re.sub(r"\W", "_", "_".join(info.mod)) or "crate")
            self.module.imports[name] = (self.rel(info.file), info.key)
            self.call_names[info.key + "\0" + info.file] = name
        return name

    def contracts_of(self, file: str) -> tuple[list[str], list[ContractLine]]:
        """Source lines and contract lines of a file of the crate."""
        if file not in self.other_contracts:
            src = self.crate.sources.get(file, "")
            comments: list = []
            tree = self.crate.trees.get(file)
            if tree is not None:
                _collect_comments(tree.root_node, comments)
            try:
                cls = parse_comment_lines(comments, "//")
            except ContractSyntaxError:
                cls = []
            self.other_contracts[file] = (src.splitlines(), cls)
        return self.other_contracts[file]

    # -- declarations ---------------------------------------------------

    def _declare(self) -> None:
        items = self.crate.all_items()
        counts: dict[str, int] = {}
        for it in items:
            if it.kind in ("struct", "enum", "trait", "union", "type"):
                counts[it.name] = counts.get(it.name, 0) + 1
        for it in items:
            if it.kind in ("struct", "enum", "trait", "union", "type"):
                self.ir_names[id(it.node)] = it.name if counts[it.name] <= 1 else f"{it.name}@{'_'.join(it.mod) or 'crate'}"
        firsts = [its[0] for m in self.crate.mods.values() for its in m.items.values()]
        for it in firsts:
            self.cur_mod, self.cur_generics, self.cur_self = it.mod, {}, None
            if it.kind == "struct":
                self._struct(it)
            elif it.kind == "enum":
                self._enum(it)
            elif it.kind == "trait":
                self._trait(it)
            elif it.kind == "const" or it.kind == "static":
                self._const(it)
            elif it.kind == "type":
                self.aliases[(it.mod, it.name)] = it
        mutated: set[str] = set()
        for m in self.crate.mods.values():
            for imp in m.impls:
                self.cur_mod = imp.mod
                owner = self._impl_owner(imp.node)
                trait = imp.node.child_by_field_name("trait")
                if owner is not None and trait is not None and _text(trait).split("<")[0].split("::")[-1] == "PartialEq":
                    for info in (self.structs.get(owner), self.data_enums.get(owner)):
                        if info is not None:
                            info.eq = "impl"
                for f in self._impl_fns(imp.node):
                    sp = f.child_by_field_name("parameters")
                    if sp is not None and any(c.type == "self_parameter" and "mut" in _text(c) and "&" in _text(c) for c in sp.children):
                        mutated.add(owner or "")
        for s in self.structs.values():
            self._in(s.mod, s.generics)
            types = [self.rtype(tn, s.name)[0] for _, _, tn in s.fields]
            scalar = all(t in (ir.INT, ir.REAL, ir.BOOL, ir.STR) or isinstance(t, ir.TEnum) for t in types)
            s.record = s.copy and scalar and s.name not in mutated
        for s in self.structs.values():
            self._in(s.mod, s.generics)
            self._declare_struct(s)
        for s in self.structs.values():
            if next((i.file for i in self.crate.mods[s.mod].items.get(s.src, [])), "") == self.abs:
                self._in(s.mod, s.generics, s.name)
                self._lifecycles(s)
        for e in self.data_enums.values():
            self._enum_record(e)

    def _in(self, mod: ModPath, generics: dict[str, list[str]], owner: str | None = None) -> None:
        self.cur_mod, self.cur_generics, self.cur_self, self.cur_subst = mod, generics, owner, {}

    def _generics(self, node: Any, outer: dict[str, list[str]] | None = None) -> dict[str, list[str]]:
        """Type parameters and their trait bounds (inline and in where clauses)."""
        out = {k: list(v) for k, v in (outer or {}).items()}
        tps = node.child_by_field_name("type_parameters")
        for p in tps.named_children if tps is not None else []:
            if p.type in ("type_parameter", "constrained_type_parameter", "optional_type_parameter"):
                nm = p.child_by_field_name("name") or p.child_by_field_name("left") or (p.named_children[0] if p.named_children else None)
                if nm is None:
                    continue
                b = p.child_by_field_name("bounds")
                out[_text(nm)] = out.get(_text(nm), []) + (self._bounds(b) if b is not None else [])
            elif p.type == "type_identifier":
                out.setdefault(_text(p), [])
        for c in node.children:
            if c.type == "where_clause":
                for wp in c.named_children:
                    if wp.type != "where_predicate":
                        continue
                    left, b = wp.child_by_field_name("left"), wp.child_by_field_name("bounds")
                    if left is not None and _text(left) in out and b is not None:
                        out[_text(left)] += self._bounds(b)
        return out

    def _bounds(self, b: Any) -> list[str]:
        out = []
        for t in b.named_children:
            if t.type == "lifetime":
                continue
            txt = _text(t).split("<")[0].strip().lstrip("?")
            full = " ".join(_text(t).split()).lstrip("?")
            out.append(self._trait_named(txt) or full.split("<")[0].split("::")[-1] + full[len(full.split("<")[0]) :])
        return out

    def _trait_named(self, path: str) -> str | None:
        r = self.crate.resolve(self.cur_mod, path.split("::"))
        if r is not None and r.kind == "item" and r.item is not None and r.item.kind == "trait":
            return self.ir_names.get(id(r.item.node))
        return None

    def _struct(self, it: Any) -> None:
        name = self.ir_names[id(it.node)]
        body = it.node.child_by_field_name("body")
        copy = _derives(it.attrs, "Copy")
        fields: list[tuple[str, str, Any]] = []
        tup = False
        if body is not None and body.type == "ordered_field_declaration_list":
            tup = True
            for i, tn in enumerate(c for c in body.children if c.is_named and c.type not in ("visibility_modifier", "attribute_item", "line_comment", "block_comment")):
                fields.append((f"_{i}", _text(tn), tn))
        elif body is not None:
            for fd in body.children:
                if fd.type == "field_declaration":
                    fields.append((_text(fd.child_by_field_name("name")), _text(fd.child_by_field_name("type")), fd.child_by_field_name("type")))
        eq = "derive" if _derives(it.attrs, "PartialEq") else ""
        self.structs[name] = StructInfo(name, fields, copy, it.node, mod=it.mod, tuple=tup, eq=eq, src=it.name, generics=self._generics(it.node))

    def _declare_struct(self, s: StructInfo) -> None:
        typed = []
        for fname, _, tn in s.fields:
            t, kind = self.rtype(tn, s.name)
            if kind:
                s.kinds[fname] = kind
            typed.append((fname, t))
        if s.record:
            self.records[s.name] = ir.TRecord(s.name, tuple(typed))
        else:
            decl = ir.ClassDecl(s.name, [(f, t) for f, t in typed], [], ir.Loc(s.node.start_point[0] + 1, s.node.start_point[1]))
            self.classes[s.name] = decl
            it_file = next((i.file for i in self.crate.mods[s.mod].items.get(s.src, [])), "")
            if it_file == self.abs:
                self.module.classes[s.name] = decl
            else:
                self.module.class_origin[s.name] = self.rel(it_file)

    def _lifecycles(self, s: StructInfo) -> None:
        """Lifecycle lines inside a struct's braces or in the comments right above it."""
        lo, hi = s.node.start_point[0] + 1, s.node.end_point[0] + 1
        while lo > 1 and self.lines[lo - 2].strip().startswith(("//", "#[")):
            lo -= 1
        mine = [cl for cl in self.contract_lines if not cl.consumed and cl.keyword == "lifecycle" and lo <= cl.line <= hi]
        if not mine:
            return
        decl = self.module.classes.get(s.name)
        info = FnInfo(f"{s.name}.<lifecycle>", s.node, [ir.Param("self", ir.TClass(s.name))], ir.NONE, None, {}, "mut", s.name, set())
        info.mod, info.file = s.mod, self.abs
        for cl in mine:
            cl.consumed = True
            if decl is None:
                self.module.problems.append((f"struct {s.name}: lifecycle: a Copy struct of scalars is a value, so it has no lifecycle; give it a '&mut self' method or drop Copy", ir.Loc(cl.line, cl.col)))
                continue
            fl = FunctionLowerer(self, info)

            def lower(text: str, two_state: bool, cl: ContractLine = cl) -> ir.Expr:
                line = ContractLine(cl.keyword, text, cl.line, cl.col, cl.payload_col, cl.tags)
                return fl.clause(line, "lifecycle" if two_state else "lifecycle.new").expr

            loc = ir.Loc(cl.line, cl.payload_col, cl.payload_col + len(cl.payload) if "\n" not in cl.payload else 0)
            try:
                decl.lifecycles.append(build_lifecycle(cl.payload, loc, tuple(cl.tags), "rust", lower))
            except (LowerError, ContractSyntaxError, LifecycleError) as e:
                self.module.problems.append((f"struct {s.name}: lifecycle: {e}", ir.Loc(cl.line, cl.col)))

    def _enum(self, it: Any) -> None:
        name = self.ir_names[id(it.node)]
        body = it.node.child_by_field_name("body")
        variants: list[tuple[str, str, list[tuple[str, str, Any]]]] = []
        for v in body.children if body is not None else []:
            if v.type != "enum_variant":
                continue
            vn = _text(v.child_by_field_name("name"))
            vb = v.child_by_field_name("body")
            if vb is None:
                variants.append((vn, "unit", []))
            elif vb.type == "ordered_field_declaration_list":
                tns = [c for c in vb.children if c.is_named and c.type not in ("visibility_modifier", "attribute_item", "line_comment", "block_comment")]
                variants.append((vn, "tuple", [(str(i), _text(tn), tn) for i, tn in enumerate(tns)]))
            else:
                variants.append((vn, "struct", [(_text(fd.child_by_field_name("name")), _text(fd.child_by_field_name("type")), fd.child_by_field_name("type")) for fd in vb.children if fd.type == "field_declaration"]))
        if all(k == "unit" for _, k, _ in variants):
            members = tuple(v for v, _, _ in variants)
            self.enums[name] = ir.TEnum(name, members, members)
            return
        eq = "derive" if _derives(it.attrs, "PartialEq") else ""
        self.data_enums[name] = EnumInfo(name, it.name, it.mod, it.node, variants, _derives(it.attrs, "Copy"), eq, generics=self._generics(it.node))

    def _enum_record(self, e: EnumInfo) -> ir.TRecord | None:
        """The record modelling ``e``, or None (with ``e.why``) when a variant
        holds what a record cannot: a list, a map, an object, or ``e`` itself."""
        if e.record is not None or e.why:
            return e.record
        if e.name in self._enum_stack:
            e.why = f"enum {e.src} is recursive"
            return None
        self._enum_stack.append(e.name)
        saved = (self.cur_mod, self.cur_generics, self.cur_self, self.cur_subst)
        self._in(e.mod, e.generics, e.name)
        try:
            tag = ir.TEnum(f"{e.name}$tag", tuple(v for v, _, _ in e.variants), tuple(v for v, _, _ in e.variants))
            fields: list[tuple[str, ir.Type]] = [("tag", tag)]
            for vn, _, fs in e.variants:
                for fname, rt, tn in fs:
                    t, k = self.ty(tn, e.name)
                    if e.name in self._enum_stack[:-1] or e.why:
                        return None
                    bad = self._record_field_problem(t)
                    if bad:
                        e.why = f"variant {vn} holds {rt} ({bad})"
                        return None
                    if t == ir.NONE:
                        continue
                    fields.append((_slot(vn, fname), t))
                    if k:
                        e.kinds[_slot(vn, fname)] = k
            if len({f for f, _ in fields}) != len(fields):
                e.why = "two variants' field names collide in telic's model"
                return None
            e.record = ir.TRecord(e.name, tuple(fields))
            self.records[e.name] = e.record
            return e.record
        finally:
            self._enum_stack.pop()
            self.cur_mod, self.cur_generics, self.cur_self, self.cur_subst = saved

    def _record_field_problem(self, t: ir.Type) -> str:
        if isinstance(t, (ir.TList, ir.TDict)):
            return "a collection"
        if isinstance(t, ir.TClass):
            return "an object"
        if isinstance(t, ir.TOption) and not (t.inner in (ir.INT, ir.REAL, ir.BOOL, ir.STR) or isinstance(t.inner, (ir.TEnum, ir.TOpaque))):
            return "an Option of a compound value"
        if isinstance(t, ir.TRecord) and not t.fields:
            return "a type telic has not resolved"
        return ""

    def _trait(self, it: Any) -> None:
        name = self.ir_names[id(it.node)]
        info = TraitInfo(name, it.name, it.mod, it.node, it.file)
        body = it.node.child_by_field_name("body")
        for c in body.named_children if body is not None else []:
            if c.type in ("function_signature_item", "function_item"):
                info.methods[_text(c.child_by_field_name("name"))] = c
        self.traits[name] = info

    def _const(self, it: Any) -> None:
        val = it.node.child_by_field_name("value")
        t = it.node.child_by_field_name("type")
        kind = _text(t) if t is not None and _text(t) in INT_KINDS else None
        if val is not None and val.type in ("integer_literal", "float_literal", "boolean_literal", "string_literal") and it.kind == "const":
            self.consts[(it.mod, it.name)] = (val, kind)
        elif t is not None:
            self.const_types[(it.mod, it.name)] = t
        elif val is not None and val.type == "unary_expression" and _text(val).startswith("-") and val.named_children and val.named_children[0].type == "integer_literal" and it.kind == "const":
            self.consts[(it.mod, it.name)] = (val, kind)

    def _impl_owner(self, it: Any) -> str | None:
        t = it.child_by_field_name("type")
        if t is None:
            return None
        base = t.child_by_field_name("type") if t.type == "generic_type" else t
        txt = _text(base)
        if txt == "Self" and self.cur_self:
            return self.cur_self
        r = self.crate.resolve(self.cur_mod, txt.split("::"))
        if r is None or r.kind != "item" or r.item is None or r.item.kind not in ("struct", "enum"):
            return None
        return self.ir_names.get(id(r.item.node))

    def _impl_fns(self, it: Any) -> list[Any]:
        body = it.child_by_field_name("body")
        return [c for c in body.children if c.type == "function_item"] if body is not None else []

    def owner_type(self, owner: str) -> ir.Type:
        if owner in self.structs:
            return self._resolve_record(ir.TRecord(owner, ()) if self.structs[owner].record else ir.TClass(owner))
        if owner in self.enums:
            return self.enums[owner]
        if owner in self.data_enums:
            r = self._enum_record(self.data_enums[owner])
            return r if r is not None else ir.TOpaque(self.data_enums[owner].src)
        if owner in self.traits:
            return ir.TOpaque(f"generic:{owner}")
        return ir.TOpaque(owner)

    def class_decl(self, name: str) -> ir.ClassDecl:
        return self.classes[name]

    # -- types ------------------------------------------------------------

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
        if k in ("dynamic_type", "abstract_type"):
            tr = tn.child_by_field_name("trait")
            names = [self._trait_named(_text(x).split("<")[0]) for x in ([tr] if tr is not None and tr.type != "trait_bounds" else (tr.named_children if tr is not None else []))]
            return ir.TOpaque("generic:" + "|".join(n for n in names if n)), None
        if k in ("type_identifier", "scoped_type_identifier"):
            if txt in self.cur_subst:
                return self.cur_subst[txt], None
            if txt in self.cur_generics:
                return ir.TOpaque("generic:" + "|".join(self.cur_generics[txt])), None
            name = txt.split("::")[-1]
            if name == "Self" and (self_ty or self.cur_self):
                return self.owner_type(self_ty or self.cur_self), None  # type: ignore[arg-type]
            if name == "String" and self._std(txt):
                return ir.STR, None
            if name == "Result" and self._std(txt):
                return self.result_type(ir.NONE, ir.TOpaque("Error")), None
            return self._named_type(txt, [])
        if k == "generic_type":
            base_n = tn.child_by_field_name("type")
            base_txt = _text(base_n)
            base = base_txt.split("::")[-1]
            targs = [c for c in tn.child_by_field_name("type_arguments").children if c.is_named and c.type not in ("lifetime", "type_binding")] if tn.child_by_field_name("type_arguments") is not None else []
            if not self._std(base_txt):
                return self._named_type(base_txt, targs)
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
            if base == "Result" and len(targs) in (1, 2):
                t, tk = self.ty(targs[0], self_ty)
                e, ek = self.ty(targs[1], self_ty) if len(targs) == 2 else (ir.TOpaque("Error"), None)
                return self.result_type(t, e, tk, ek), tk
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

    def _std(self, path: str) -> bool:
        """Does this type path name something outside the crate (std)?"""
        return self.crate.resolve(self.cur_mod, path.split("::")) is None

    def _named_type(self, path: str, targs: list[Any]) -> tuple[ir.Type, str | None]:
        r = self.crate.resolve(self.cur_mod, path.split("::"))
        if r is None or r.kind != "item" or r.item is None:
            return ir.TOpaque(path), None
        it = r.item
        name = self.ir_names.get(id(it.node), it.name)
        if it.kind == "struct" and name in self.structs:
            s = self.structs[name]
            return (ir.TRecord(name, ()) if s.record else ir.TClass(name)), None  # records are completed by _resolve_record
        if it.kind == "enum":
            if name in self.enums:
                return self.enums[name], None
            e = self.data_enums.get(name)
            rec = self._enum_record(e) if e is not None else None
            return (rec if rec is not None else ir.TOpaque(path)), None
        if it.kind == "type":
            if id(it.node) in self._alias_stack:
                return ir.TOpaque(path), None
            params = self._generics(it.node)
            args = [self.ty(a)[0] for a in targs]
            saved = (self.cur_mod, self.cur_generics, self.cur_self, self.cur_subst)
            self._alias_stack.append(id(it.node))
            try:
                self.cur_mod, self.cur_generics = it.mod, {}
                self.cur_subst = dict(zip(params, args))
                return self.ty(it.node.child_by_field_name("type"))
            finally:
                self._alias_stack.pop()
                self.cur_mod, self.cur_generics, self.cur_self, self.cur_subst = saved
        return ir.TOpaque(path), None

    def type_of_text(self, text: str) -> tuple[ir.Type, str | None]:
        """The type a piece of Rust type syntax names, here."""
        tree = parser().parse(f"type __T = {text};".encode("utf8"))
        item = tree.root_node.named_children[0] if tree.root_node.named_children else None
        tn = item.child_by_field_name("type") if item is not None and not tree.root_node.has_error else None
        if tn is None:
            return ir.TOpaque(text), None
        return self.ty(tn)

    def result_type(self, t: ir.Type, e: ir.Type, tk: str | None = None, ek: str | None = None) -> ir.Type:
        """``Result<T, E>``: a record of a tag and both payloads (named by
        their types and integer kinds, so one name means one model)."""
        fields: list[tuple[str, ir.Type]] = [("tag", RESULT_TAG)]
        for slot, x in (("Ok_0", t), ("Err_0", e)):
            if self._record_field_problem(x):
                return ir.TOpaque(f"Result<{t}, {e}>")
            if x != ir.NONE:
                fields.append((slot, x))
        rec = ir.TRecord(f"Result_{tk or _tag_of(t)}_{ek or _tag_of(e)}", tuple(fields))
        self.records[rec.name] = rec
        self.result_kinds[rec.name] = {s: k for s, k in (("Ok_0", tk), ("Err_0", ek)) if k}
        return rec

    def _resolve_record(self, t: ir.Type) -> ir.Type:
        if isinstance(t, ir.TRecord) and not t.fields and t.name in self.records:
            return self.records[t.name]
        return t

    def ty(self, tn: Any, self_ty: str | None = None) -> tuple[ir.Type, str | None]:
        t, k = self.rtype(tn, self_ty)
        return self._resolve_record(t), k

    # -- signatures ---------------------------------------------------------

    def _signatures(self) -> None:
        for m in self.crate.mods.values():
            for its in m.items.values():
                it = its[0]
                if it.kind == "fn" and it.node.type == "function_item":
                    self._in(it.mod, self._generics(it.node))
                    self._signature(it.node, None, it.mod, it.file)
        for tr in self.traits.values():
            for mname, node in tr.methods.items():
                self._in(tr.mod, self._generics(node, self._generics(tr.node)), tr.name)
                self._signature(node, tr.name, tr.mod, tr.file, key=f"{tr.name}.{mname}", decl=True)
                if node.type == "function_item":
                    self._signature(node, tr.name, tr.mod, tr.file, key=f"{tr.name}.{mname}@default", trait_method=f"{tr.name}.{mname}")
        for m in self.crate.mods.values():
            for imp in m.impls:
                self._in(imp.mod, self._generics(imp.node))
                owner = self._impl_owner(imp.node)
                tn = imp.node.child_by_field_name("trait")
                trait = self._trait_named(_text(tn).split("<")[0]) if tn is not None else None
                if owner is None:
                    if imp.file == self.abs:
                        self.module.notes.append(("impl of a type telic does not model: its methods are unchecked", ir.Loc(imp.node.start_point[0] + 1)))
                        if trait is not None:
                            self.module.assumptions.append(f"impl {_text(tn)} for {_text(imp.node.child_by_field_name('type'))} meets the trait's contracts (telic does not check it)")
                    continue
                if trait is not None:
                    self.impls_of.setdefault(owner, []).append(trait)
                for f in self._impl_fns(imp.node):
                    mname = _text(f.child_by_field_name("name"))
                    self._in(imp.mod, self._generics(f, self._generics(imp.node)), owner)
                    tm = f"{trait}.{mname}" if trait is not None and mname in self.traits[trait].methods else None
                    key = f"{owner}.{mname}"
                    if (owner, mname) in self.methods:
                        key += "@" + (re.sub(r"\W", "_", _text(tn)) if tn is not None else "impl")
                    self._signature(f, owner, imp.mod, imp.file, key=key, trait_method=tm)

    def _signature(self, f: Any, owner: str | None, mod: ModPath, file: str, key: str | None = None, decl: bool = False, trait_method: str | None = None) -> None:
        name = _text(f.child_by_field_name("name"))
        if key is None:
            key = name
            if key in self.file_keys.get(file, set()):
                key = f"{name}@{'_'.join(mod) or 'crate'}"
        params: list[ir.Param] = []
        kinds: dict[str, str] = {}
        ekinds: dict[str, str] = {}
        mut_params: set[str] = set()
        lens: dict[str, int] = {}
        self_mode = None
        ps = f.child_by_field_name("parameters")
        for p in ps.children if ps is not None else []:
            if p.type == "self_parameter":
                t = _text(p)
                self_mode = "mut" if "&" in t and "mut" in t else "ref" if "&" in t else "value"
                assert owner is not None
                params.append(ir.Param("self", self.owner_type(owner)))
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
                        t, k = ir.TOpaque(f"&mut {_text(tn.child_by_field_name('type'))}"), None  # a mutable reference to a value: not modelled
                if k and (t == ir.INT or isinstance(t, ir.TOption)):
                    kinds[pname] = k
                elif k and isinstance(t, (ir.TList, ir.TDict)):
                    ekinds[pname] = k
                size = _array_len(tn)
                if size is not None and isinstance(t, ir.TList):
                    lens[pname] = size
                params.append(ir.Param(pname, t))
        rt = f.child_by_field_name("return_type")
        ret, rk = self.ty(rt, owner) if rt is not None else (ir.NONE, None)
        info = FnInfo(key, f, params, ret, rk if ret == ir.INT or isinstance(ret, ir.TOption) or _is_result(ret) else None, kinds, self_mode, owner, mut_params, ekinds, mod, file, dict(self.cur_generics), trait_method, decl, lens)
        uid = f"{file}\0{key}"
        self.fns[uid] = info
        self.file_keys.setdefault(file, set()).add(key)
        if owner is None:
            self.fn_keys[id(f)] = uid
        elif decl:
            self.methods[(owner, name)] = uid
        elif key.endswith("@default"):
            self.methods[(owner, "default:" + name)] = uid
        else:
            self.methods.setdefault((owner, name), uid)

    def lookup(self, path: str) -> tuple | None:
        """What a path in an expression names, from the current module:
        ("fn", uid), ("type", name), ("variant", type, variant),
        ("assoc", type or trait, member), ("const", key), ("generic", T, member)
        or ("mod", path); None when it is outside the crate."""
        segs = [s.strip() for s in re.sub(r"<[^<>]*(?:<[^<>]*>[^<>]*)*>", "", path).split("::") if s.strip()]
        if not segs:
            return None
        if segs[0] == "Self" and self.cur_self:
            owner = self.cur_self
            if len(segs) == 1:
                return ("type", owner)
            if self._has_variant(owner, segs[1]):
                return ("variant", owner, segs[1])
            return ("assoc", owner, segs[1])
        if segs[0] in self.cur_generics and len(segs) == 2:
            return ("generic", segs[0], segs[1])
        r: Res | None = self.crate.resolve(self.cur_mod, segs)
        if r is None:
            return None
        if r.kind == "mod":
            return ("mod", r.mod)
        it = r.item
        assert it is not None
        if r.kind == "item":
            if it.kind == "fn":
                uid = self.fn_keys.get(id(it.node))
                return ("fn", uid) if uid is not None else None
            if it.kind in ("const", "static"):
                return ("const", (it.mod, it.name))
            return ("type", self.ir_names.get(id(it.node), it.name))
        owner = self.ir_names.get(id(it.node), it.name)
        return (r.kind, owner, r.member)

    def _has_variant(self, owner: str, name: str) -> bool:
        if owner in self.enums:
            return name in self.enums[owner].members
        return owner in self.data_enums and self.data_enums[owner].variant(name) is not None

    def method_of(self, owner: str, m: str) -> FnInfo | None:
        """``owner.m``: its own, or a default of a trait it implements (or,
        for a trait, its declaration or a supertrait's)."""
        uid = self.methods.get((owner, m))
        if uid is not None:
            return self.fns[uid]
        for tr in self.impls_of.get(owner, []):
            uid = self.methods.get((tr, "default:" + m))
            if uid is not None:
                return self.fns[uid]
        if owner in self.traits:
            for sup in self.supertraits(owner):
                uid = self.methods.get((sup, m))
                if uid is not None:
                    return self.fns[uid]
        return None

    def supertraits(self, trait: str) -> list[str]:
        out, todo = [], [trait]
        while todo:
            t = todo.pop()
            if t in out or t not in self.traits:
                continue
            out.append(t)
            tr = self.traits[t]
            b = tr.node.child_by_field_name("bounds")
            if b is not None:
                saved = self.cur_mod
                self.cur_mod = tr.mod
                todo += [x for x in self._bounds(b) if x in self.traits]
                self.cur_mod = saved
        return out

    def slot_kind(self, rec: str, slot: str) -> str | None:
        """The integer kind of a record field."""
        if rec in self.structs:
            return self.structs[rec].kinds.get(slot)
        if rec in self.data_enums:
            return self.data_enums[rec].kinds.get(slot)
        return self.result_kinds.get(rec, {}).get(slot)

    def default_value(self, t: ir.Type, loc: ir.Loc) -> ir.Expr:
        """The value an inactive variant's field holds in the model."""
        d = _default(t, loc)
        if d is not None:
            return d
        if isinstance(t, ir.TEnum):
            return ir.Lit(t, loc, 0)
        if isinstance(t, ir.TOption):
            return ir.Lit(t, loc, None)
        if isinstance(t, ir.TRecord):
            return ir.RecordLit(t, loc, tuple((f, self.default_value(ft, loc)) for f, ft in t.fields))
        return ir.Builtin(t, loc, "opaque_op", (ir.Lit(ir.STR, loc, "default"),))


def _int_literal(n: Any) -> int | None:
    """The value of an integer literal node (0x, 0o, 0b, _ and a type suffix allowed)."""
    if n.type != "integer_literal":
        return None
    m = re.match(r"^(0x[0-9a-fA-F]+|0o[0-7]+|0b[01]+|\d+)(?:[iu](?:8|16|32|64|128|size))?$", _text(n).replace("_", ""))
    return int(m.group(1), 0) if m else None


def _array_len(tn: Any) -> int | None:
    """N in [T; N] (behind references)."""
    while tn is not None and tn.type == "reference_type":
        tn = tn.child_by_field_name("type")
    if tn is None or tn.type != "array_type":
        return None
    n = tn.child_by_field_name("length")
    return _int_literal(n) if n is not None else None


def _is_result(t: ir.Type) -> bool:
    return isinstance(t, ir.TRecord) and t.fields[:1] == (("tag", RESULT_TAG),)


def _collect_comments(n: Any, out: list) -> None:
    if n.type == "line_comment":
        out.append((n.start_point[0] + 1, n.start_point[1], _text(n).rstrip("\n")))
        return
    for c in n.children:
        _collect_comments(c, out)


def _header_contracts(node: Any, lines: list[str], contract_lines: list[ContractLine], consumed_ok: bool = False) -> list[ContractLine]:
    """Function contract lines above a function (among its attributes and
    comments) and at the top of its body."""
    body = node.child_by_field_name("body")
    start = node.start_point[0] + 1
    by_line = {l: cl for cl in contract_lines for l in cl.raw_lines}
    above: list[ContractLine] = []
    ln = start - 1
    while ln >= 1:
        t = lines[ln - 1].strip()
        if not (t.startswith("//") or t.startswith("#[")):
            break
        cl = by_line.get(ln)
        if cl is not None and cl.keyword in FUNCTION_KEYWORDS and (consumed_ok or not cl.consumed) and cl not in above:
            above.append(cl)
        ln -= 1
    above.reverse()
    if body is not None:
        first = next((c for c in body.children if c.is_named and c.type not in ("line_comment", "block_comment")), None)
        limit = first.start_point[0] + 1 if first is not None else body.end_point[0] + 1
        above += [cl for cl in contract_lines if body.start_point[0] + 1 <= cl.line < limit and cl.keyword in FUNCTION_KEYWORDS and (consumed_ok or not cl.consumed) and cl not in above]
    return above


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
        self.aims: list[str] = []
        lo, hi = self.node.start_point[0] + 1, self.node.end_point[0] + 1
        self.local_contracts = [cl for cl in fe.contract_lines if lo <= cl.line <= hi]
        self.loop_value: list[str | None] = []  # target of 'break value' per enclosing loop
        self.range_after: list[ir.Stmt] = []
        self.escaped: set[str] = set()
        self.refmut: set[str] = set()  # names bound into a value matched through &mut

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
        for cl in _header_contracts(self.node, self.fe.lines, self.fe.contract_lines):
            cl.consumed = True
            try:
                self._function_contract(cl)
            except (LowerError, ContractSyntaxError) as e:
                self.fn.unsupported.append((f"contract: {e}", ir.Loc(getattr(e, "line", cl.line) or cl.line)))
        if info.trait_method is not None:
            self._inherit(info.trait_method)
        if body is None or info.decl:
            self.fn.trusted = True  # a declaration (trait/extern): its contract is what callers use
            return self.fn
        if info.self_mode == "mut" and isinstance(info.params[0].ty, (ir.TRecord, ir.TEnum)) and self.fn.ensures:
            self.fn.unsupported.append(("'@ensures' of a method that changes a value in place (&mut self on an enum or Copy value) is not modelled", self.fn.loc))
        stmts: list[ir.Stmt] = []
        for p in info.params:
            k = self.kinds.get(p.name)
            if k and p.ty == ir.INT:
                stmts.append(ir.ExprStmt(self.fn.loc, self.in_range(ir.Var(ir.INT, self.fn.loc, p.name), k)))
            elif k and isinstance(p.ty, ir.TOption) and p.ty.inner == ir.INT:
                pv = ir.Var(p.ty, self.fn.loc, p.name)
                present = ir.Unary(ir.BOOL, self.fn.loc, "not", ir.Builtin(ir.BOOL, self.fn.loc, "is_none", (pv,)))
                stmts.append(ir.If(self.fn.loc, present, (ir.ExprStmt(self.fn.loc, self.in_range(ir.Builtin(ir.INT, self.fn.loc, "unwrap", (pv,)), k)),), ()))
            stmts += _tag_ranges(ir.Var(p.ty, self.fn.loc, p.name), self.fn.loc)
            if p.name in info.lens:
                size = ir.Lit(ir.INT, self.fn.loc, info.lens[p.name])
                stmts.append(ir.ExprStmt(self.fn.loc, ir.Builtin(ir.INT, self.fn.loc, "in_range", (ir.Builtin(ir.INT, self.fn.loc, "len", (ir.Var(p.ty, self.fn.loc, p.name),)), size, size))))
        out = self.block_value(body, stmts, info.ret, info.ret_kind)
        if out is not None and info.ret != ir.NONE:
            stmts.append(ir.Return(out.loc, self.coerce(out, info.ret)))
        elif out is not None:
            stmts.append(ir.ExprStmt(out.loc, out))
        self.fn.body = stmts
        self.fn.locals = dict(self.env)
        self.fn.escaped = set(self.escaped)
        self.fn.aims = self.aims + [i for i in self.fn.aims if i not in self.aims]
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

    def _inherit(self, key: str) -> None:
        """A trait method's contract binds every implementation: callers
        through the trait rely on it, so each impl is checked against it."""
        uid = next((u for u, i in self.fe.fns.items() if i.key == key and i.decl), None)
        if uid is None:
            return
        decl = self.fe.fns[uid]
        if self.fn.requires and not self.info.decl and self.info.trait_method:
            self.fn.unsupported.append((f"an implementation of {ir.source_name(key)} cannot add '@requires' (callers through the trait do not know it); state it on the trait", self.fn.loc))
        lines, cls = self.fe.contracts_of(decl.file)
        own = [p.name for p in self.info.params]
        theirs = [p.name for p in decl.params]
        self.scopes.append({t: self.resolve(o) for t, o in zip(theirs, own)})
        try:
            for cl in _header_contracts(decl.node, lines, cls, consumed_ok=True):
                if cl.keyword not in ("requires", "ensures", "raises"):
                    continue
                try:
                    c = self.clause(cl, cl.keyword, tuple(cl.tags))
                except (LowerError, ContractSyntaxError) as e:
                    self.fn.unsupported.append((f"contract of {ir.source_name(key)}: {e}", self.fn.loc))
                    continue
                c = ir.Clause(c.kind, c.expr, self.fn.loc, c.text, c.aims)
                {"requires": self.fn.requires, "ensures": self.fn.ensures, "raises": self.fn.raises}[cl.keyword].append(c)
        finally:
            self.scopes.pop()

    def _function_contract(self, cl: ContractLine) -> None:
        kw = cl.keyword
        if kw == "aim":
            ids, text = parse_aim_directive(cl)
            if text is not None:
                self.fe.module.aims.append(ir.AimDecl(ids[0], text, ir.Loc(cl.line, cl.col)))
            for i in ids:
                if i not in self.aims:
                    self.aims.append(i)
            self.current_aims = ids
            return
        if kw == "mirrors":
            self.fn.mirrors.append((cl.payload.strip(), ir.Loc(cl.line, cl.col), tuple(cl.tags)))
            for t in cl.tags:
                if t not in self.fn.aims:
                    self.fn.aims.append(t)
            return
        if kw == "trusted":
            self.fn.trusted = True
            return
        if kw == "pure":
            return
        tags = tuple(cl.tags) or tuple(getattr(self, "current_aims", ()))
        for t in tags:
            if t not in self.aims:
                self.aims.append(t)
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
        el = ExprLowerer(self, spec=True, line_offset=cl.line - 2, col_offset=cl.payload_col, allow_old=kind in ("ensures", "invariant", "lifecycle"))
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
            if pat.type in ("tuple_struct_pattern", "struct_pattern") and val is not None:
                el = ExprLowerer(self)
                v = el.expr(val, ann, akind)
                v = el.hoist(v) if not isinstance(v, ir.Var) else v
                out.extend(el.pre)
                pl = ExprLowerer(self)
                _, binds = pl._pattern(pat, pl.kinded(v, el.kind_of(v)))  # irrefutable: rustc checks it
                if pl.pre:
                    raise self.err(f"unsupported pattern in let: {_text(pat)}", s)
                by_ref = self.mut_ref(val)
                for b, e in binds:
                    self.bind(b, e, pl, s, out, loc, by_ref)
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
        t = self.fresh("scrut", v.ty)
        out.append(ir.Assign(loc, t, v))
        tv = ir.Var(v.ty, loc, t)
        k = el.kind_of(v)
        if k:
            self.kinds[t] = k
        pl = ExprLowerer(self)
        c, binds = pl._pattern(pat, pl.kinded(tv, k))
        if pl.pre:
            raise self.err("this 'while let' pattern is not supported", cond)
        out.append(ir.If(loc, ir.Unary(ir.BOOL, loc, "not", c), (ir.Break(loc),), ()))
        by_ref = self.mut_ref(val)
        self.push_scope()
        try:
            for b, e in binds:
                self.bind(b, e, pl, pat, out, loc, by_ref)
            self._loop_body(body, out)
        finally:
            self.pop_scope()

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

    def bind(self, name: str, e: ir.Expr, el: "ExprLowerer", node: Any, out: list[ir.Stmt], loc: ir.Loc, by_ref: bool = False) -> str:
        """Bind a pattern's name to ``e`` (its integer kind follows it). A
        binding into a ``&mut`` scrutinee is a reference telic does not
        track, so writing through it is rejected."""
        irn = self.declare(name, e.ty, node)
        if isinstance(e.ty, (ir.TList, ir.TDict)):
            k = el.kind_of_elems(e)
            if k:
                self.elem_kinds[irn] = k
        else:
            k = el.kind_of(e)
            if k:
                self.kinds[irn] = k
        if by_ref and not isinstance(e.ty, ir.TClass):
            self.refmut.add(irn)
        out.append(ir.Assign(loc, irn, e))
        return irn

    def writable(self, name: str, node: Any) -> None:
        if name in self.refmut:
            raise self.err(f"'{name.split('$')[0]}' refers into a value matched through &mut; writing through it is not modelled", node)

    def mut_ref(self, n: Any) -> bool:
        """Is this scrutinee a ``&mut`` reference (so bindings borrow into it)?"""
        while n.type == "parenthesized_expression":
            n = n.named_children[0]
        if n.type == "reference_expression":
            return _is_mut_ref(n)
        if n.type == "self":
            return self.info.self_mode == "mut"
        if n.type == "identifier":
            r = self.resolve(_text(n))
            return r in self.info.mut_params or r in self.refmut
        if n.type == "call_expression":
            f = n.child_by_field_name("function")
            return f.type == "field_expression" and _text(f.child_by_field_name("field")) in ("as_mut", "get_mut", "iter_mut", "as_deref_mut", "last_mut", "first_mut")
        return False


# ---------------------------------------------------------------------------
# Expressions


VEC_MUTATORS = {"push", "pop", "clear", "truncate", "extend", "extend_from_slice", "append", "sort", "sort_unstable", "reverse", "dedup", "retain", "insert", "remove", "swap_remove", "sort_by", "sort_by_key", "sort_unstable_by", "sort_unstable_by_key", "drain", "iter_mut", "resize", "swap", "fill", "rotate_left", "rotate_right", "split_off", "as_mut_slice", "last_mut", "first_mut", "get_mut", "push_back", "push_front", "pop_back", "pop_front"}

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
        return self._copy_obj(e, e.loc, 0)

    def _copy_obj(self, e: ir.Expr, loc: ir.Loc, depth: int) -> ir.Expr:
        """A fresh object with ``e``'s fields, objects in them copied too
        (a derived Clone, or a Copy)."""
        assert isinstance(e.ty, ir.TClass)
        if depth > 3:
            raise LowerError("copying objects nested this deep is not modelled", loc.line)
        src = self.hoist(e) if not isinstance(e, ir.Var) else e
        decl = self.fe.classes[e.ty.name]
        fields = []
        for f, t in decl.fields:
            v: ir.Expr = ir.Field(t, loc, src, f)
            if isinstance(t, ir.TClass):
                v = self._copy_obj(v, loc, depth + 1)
            elif isinstance(t, ir.TList) and isinstance(t.elem, ir.TClass) or isinstance(t, ir.TDict) and isinstance(t.val, ir.TClass) or isinstance(t, ir.TOption) and isinstance(t.inner, ir.TClass):
                v = self.hoist(ir.Extern(t, loc, "clone of a collection of objects", ()))
            fields.append(v)
        return self.hoist(ir.New(e.ty, loc, e.ty.name, tuple(fields)))

    def hoist(self, e: ir.Expr) -> ir.Expr:
        """Evaluate an effectful expression now, into a temporary."""
        if self.spec or e.ty == ir.NONE:
            return e
        t = self.fl.fresh("t", e.ty)
        self.pre.append(ir.Assign(e.loc, t, e))
        v = ir.Var(e.ty, e.loc, t)
        if isinstance(e.ty, ir.TRecord) and not isinstance(e, ir.RecordLit):
            self.pre += _tag_ranges(v, e.loc)
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
        if raw.startswith('b"'):
            try:
                data = bytes(raw[2:-1], "utf8").decode("unicode_escape").encode("latin-1")
            except (UnicodeDecodeError, UnicodeEncodeError):
                return self.opaque_str(n)
            loc = self.loc(n)
            return self.elems_kinded(ir.ListLit(ir.TList(ir.INT), loc, tuple(ir.Lit(ir.INT, loc, x) for x in data)), "u8")
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
        hit = self.fe.lookup(name)
        if hit is not None:
            v = self._path_value(hit, name, n, expect, loc)
            if v is not None:
                return v
        if hit is None and name[:1].isupper() and not self.spec:
            return self.hoist(ir.Extern(ir.TOpaque(name), loc, name, ()))  # a unit struct or constant from outside the crate
        raise self.err(f"unknown name '{name}'", n)

    def x_self(self, n: Any, expect: Any, kind: Any) -> ir.Expr:
        if "self" not in self.fl.env:
            raise self.err("'self' outside a method", n)
        return ir.Var(self.fl.env["self"], self.loc(n), "self")

    def x_scoped_identifier(self, n: Any, expect: Any, kind: Any) -> ir.Expr:
        txt = _text(n)
        parts = txt.split("::")
        loc = self.loc(n)
        if len(parts) == 2 and parts[0] in INT_KINDS and parts[1] in ("MAX", "MIN"):
            lo, hi = int_range(parts[0])
            return self.kinded(ir.Lit(ir.INT, loc, hi if parts[1] == "MAX" else lo), parts[0])
        if len(parts) >= 2 and parts[-2] in ("f32", "f64") and parts[-1] in ("EPSILON",):
            return ir.Lit(ir.REAL, loc, Fraction(2) ** -52 if parts[-2] == "f64" else Fraction(2) ** -23)
        hit = self.fe.lookup(txt)
        if hit is not None:
            v = self._path_value(hit, txt, n, expect, loc)
            if v is not None:
                return v
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
        if tt == "char" and v.ty == ir.INT:
            return self.opaque("as_char", [v], ir.STR, loc)
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
        if op not in ("==", "!=") and not self.spec:
            # a value from unchecked code in arithmetic has the other operand's type
            if isinstance(a.ty, ir.TOpaque) and (b.ty == ir.REAL or b.ty == ir.INT and self.kind_of(b)):
                a = self._opaque_as(a, b.ty, self.kind_of(b))
            elif isinstance(b.ty, ir.TOpaque) and (a.ty == ir.REAL or a.ty == ir.INT and self.kind_of(a)):
                b = self._opaque_as(b, a.ty, self.kind_of(a))
        if a.ty == ir.INT and b.ty == ir.INT and not self.kind_of(a) and self.kind_of(b):
            self.kinded(a, self.kind_of(b))
        k = self.kind_of(a) or self.kind_of(b)
        if a.ty == ir.REAL and b.ty == ir.INT and isinstance(b, ir.Lit):
            b = ir.Lit(ir.REAL, b.loc, Fraction(b.value))  # type: ignore[arg-type]
        if b.ty == ir.REAL and a.ty == ir.INT and isinstance(a, ir.Lit):
            a = ir.Lit(ir.REAL, a.loc, Fraction(a.value))  # type: ignore[arg-type]
        if op in ("==", "!="):
            return self._eq(a, b, n, BINOPS[op])
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
            kk = k or kind or "i32"
            if op == "%" and INT_KINDS[kk][0] and not self.spec:
                # MIN % -1 overflows (the quotient does not fit) and panics
                a, b = self.hoist(a), self.hoist(b)
                self.pre.append(ir.ExprStmt(loc, self.checked(ir.Binary(ir.INT, loc, "tdiv", a, b), kk)))
            return self.checked(ir.Binary(ir.INT, loc, name, a, b), kk)
        if op in ("&", "|", "^", "<<", ">>"):
            if a.ty == ir.BOOL and b.ty == ir.BOOL and op in ("&", "|", "^"):
                return ir.Binary(ir.BOOL, loc, {"&": "and", "|": "or", "^": "ne"}[op], a, b)  # non-short-circuit on bools
            if a.ty == ir.INT and b.ty == ir.INT:
                return self._bitop(op, a, b, loc)
        raise self.err(f"unsupported operator {op} on {a.ty}", n)

    def _bitop(self, op: str, a: ir.Expr, b: ir.Expr, loc: ir.Loc) -> ir.Expr:
        """Shifts by a constant and masks of contiguous bits are arithmetic;
        other bit operations give some value of the type. A shift by the
        type's width or more panics."""
        if op == "&" and isinstance(a, ir.Lit) and not isinstance(b, ir.Lit):
            a, b = b, a
        k = self.kind_of(a) or (self.kind_of(b) if op in ("&", "|", "^") else None)
        lit = b.value if isinstance(b, ir.Lit) and isinstance(b.value, int) and not isinstance(b.value, bool) else None
        if not k:
            return self.ranged(self.opaque(f"bit{op}", [a, b], ir.INT, loc), k)
        signed, bits = INT_KINDS[k]
        if op in ("<<", ">>"):
            if not (lit is not None and 0 <= lit < bits):
                if not self.spec:
                    fits = ir.Binary(ir.BOOL, loc, "and", ir.Binary(ir.BOOL, loc, "le", ir.Lit(ir.INT, loc, 0), b), ir.Binary(ir.BOOL, loc, "lt", b, ir.Lit(ir.INT, loc, bits)))
                    self.pre.append(ir.AssertStmt(loc, ir.Clause("assert", fits, loc, f"the shift amount is below {bits}"), native=True))
                return self.ranged(self.opaque(f"bit{op}", [a, b], ir.INT, loc), k)
            p = ir.Lit(ir.INT, loc, 1 << lit)
            if op == ">>":
                return self.kinded(ir.Binary(ir.INT, loc, "floordiv", a, p), k)  # an arithmetic shift rounds down
            raw = ir.Binary(ir.INT, loc, "mul", a, p)
            mod = ir.Lit(ir.INT, loc, 1 << bits)
            if not signed:
                return self.kinded(ir.Binary(ir.INT, loc, "fmod", raw, mod), k)
            h = ir.Lit(ir.INT, loc, 1 << (bits - 1))
            return self.kinded(ir.Binary(ir.INT, loc, "sub", ir.Binary(ir.INT, loc, "fmod", ir.Binary(ir.INT, loc, "add", raw, h), mod), h), k)
        if op == "&" and not signed and lit is not None and 0 <= lit < (1 << bits):
            if lit & (lit + 1) == 0:
                return self.kinded(ir.Binary(ir.INT, loc, "fmod", a, ir.Lit(ir.INT, loc, lit + 1)), k)
            low = lit & -lit
            high = lit + low
            if high & (high - 1) == 0:  # one run of bits: a mod 2^hi - a mod 2^lo
                return self.kinded(ir.Binary(ir.INT, loc, "sub", ir.Binary(ir.INT, loc, "fmod", a, ir.Lit(ir.INT, loc, high)), ir.Binary(ir.INT, loc, "fmod", a, ir.Lit(ir.INT, loc, low))), k)
            return self.kinded(ir.Builtin(ir.INT, loc, "in_range", (self.opaque("bit&", [a, b], ir.INT, loc), ir.Lit(ir.INT, loc, 0), ir.Lit(ir.INT, loc, lit))), k)
        return self.ranged(self.opaque(f"bit{op}", [a, b], ir.INT, loc), k)

    def _opaque_as(self, e: ir.Expr, t: ir.Type, k: str | None) -> ir.Expr:
        v = self.hoist(ir.Builtin(t, e.loc, "from_opaque", (e,)))
        return self.ranged(v, k) if t == ir.INT else v

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
            self.fl.writable(name, left)
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
                decl = self.fe.classes[obj.ty.name]
                ft = decl.field_type(fname)
                if ft is None:
                    raise self.err(f"{obj.ty.name} has no field '{fname}'", left)
                self.pre.append(ir.FieldAssign(loc, obj, obj.ty.name, fname, self.fl.coerce(value, ft)))
                return
            if isinstance(obj.ty, ir.TRecord) and isinstance(obj, ir.Var):
                self.fl.writable(obj.name, left)
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
                self.fl.writable(seq.name, left)
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
            inner = left.named_children[0]
            obj = self.expr(inner) if inner.type in ("identifier", "self") else None
            if obj is not None and isinstance(obj.ty, ir.TClass):
                # the struct behind the reference is overwritten in place, field by field
                tmp = self.fl.fresh("whole", obj.ty)
                self.pre.append(ir.Assign(loc, tmp, self.fl.coerce(value, obj.ty)))
                src = ir.Var(obj.ty, loc, tmp)
                for f, t in self.fe.classes[obj.ty.name].fields:
                    self.pre.append(ir.FieldAssign(loc, obj, obj.ty.name, f, ir.Field(t, loc, src, f)))
                return
            if inner.type == "self":
                self.fl.writable("self", left)
                self.pre.append(ir.Assign(loc, "self", self.fl.coerce(value, self.fl.env["self"])))
                return
            return self._store(inner, value, n)
        raise self.err(f"unsupported assignment target: {_text(left)}", left)

    def x_field_expression(self, n: Any, expect: Any, kind: Any) -> ir.Expr:
        obj = self.expr(n.child_by_field_name("value"))
        f = _text(n.child_by_field_name("field"))
        f = f"_{f}" if f.isdigit() else f
        loc = self.loc(n)
        if isinstance(obj.ty, ir.TOption) and not self.spec:
            raise self.err("field of an Option: unwrap it first", n)
        if isinstance(obj.ty, (ir.TClass, ir.TRecord)) and obj.ty.name in self.fe.structs:
            ft = dict(obj.ty.fields).get(f) if isinstance(obj.ty, ir.TRecord) else self.fe.classes[obj.ty.name].field_type(f)
            if ft is None:
                raise self.err(f"{obj.ty.name} has no field '{f}'", n)
            v = ir.Field(ft, loc, obj, f)
            k = self.fe.slot_kind(obj.ty.name, f)
            if isinstance(ft, ir.TList):
                return self.elems_kinded(v, k)
            return self.ranged(v, k) if ft == ir.INT else self.kinded(v, k)
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
        path = _text(n.child_by_field_name("name"))
        loc = self.loc(n)
        body = n.child_by_field_name("body")
        hit = self.fe.lookup(path)
        if hit is not None and hit[0] == "variant" and hit[1] in self.fe.data_enums:
            e = self.fe.data_enums[hit[1]]
            rec = self.fe._enum_record(e)
            if rec is not None:
                vals: dict[str, ir.Expr] = {}
                types = dict(rec.fields)
                for c in body.named_children:
                    if c.type == "shorthand_field_initializer":
                        slot = _slot(hit[2], _text(c))
                        vals[slot] = self.x_identifier(c.named_children[0] if c.named_children else c, types.get(slot), self.fe.slot_kind(rec.name, slot))
                    elif c.type == "field_initializer":
                        slot = _slot(hit[2], _text(c.child_by_field_name("field")))
                        vals[slot] = self.expr(c.child_by_field_name("value"), types.get(slot), self.fe.slot_kind(rec.name, slot))
                    elif c.type == "base_field_initializer":
                        raise self.err("'..base' in an enum variant", c)
                return self._variant(rec, hit[2], vals, loc)
        s = self.fe.structs.get(hit[1]) if hit is not None and hit[0] == "type" else None
        if s is None:
            if self.spec:
                raise self.err(f"struct {path} is not modelled", n)
            return ir.Extern(ir.TOpaque(path), loc, path, tuple(self.hoist(self.expr(c)) for c in body.named_children if c.type != "base_field_initializer"))
        vals = {}
        base = None
        types = self._struct_fields(s)
        for c in body.named_children:
            if c.type == "shorthand_field_initializer":
                f = _text(c)
                vals[f] = self.x_identifier(c.named_children[0] if c.named_children else c, types.get(f), s.kinds.get(f))
            elif c.type == "field_initializer":
                f = _text(c.child_by_field_name("field"))
                f = f"_{f}" if f.isdigit() else f
                vals[f] = self.copy_value(self.expr(c.child_by_field_name("value"), types.get(f), s.kinds.get(f)))
            elif c.type == "base_field_initializer":
                base = self.hoist(self.expr(c.named_children[0]))
        return self._build_struct(s, vals, base, loc, n)

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
        value_n = cond.child_by_field_name("value")
        if self.spec:
            raise self.err("if let in a specification", cond)
        v = self.expr(value_n)
        t = self.hoist(v) if not isinstance(v, ir.Var) else v
        c, binds = self._pattern(pat, t)
        by_ref = self.fl.mut_ref(value_n)
        then_pre: list[ir.Stmt] = []
        self.fl.push_scope()
        try:
            for b, e in binds:
                self.fl.bind(b, e, self, pat, then_pre, loc, by_ref)
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
        return self._join(c, then_pre, tv, else_pre, ev, expect, loc)

    def x_match_expression(self, n: Any, expect: Any, kind: Any) -> ir.Expr:
        loc = self.loc(n)
        if self.spec:
            raise self.err("match in a specification", n)
        value_n = n.child_by_field_name("value")
        scrut = self.hoist(self.expr(value_n))
        by_ref = self.fl.mut_ref(value_n)
        arms = [c for c in n.child_by_field_name("body").named_children if c.type == "match_arm"]
        conds = []
        for arm in arms:
            pat = arm.child_by_field_name("pattern")
            val = arm.child_by_field_name("value")
            cond, binds = self._pattern(pat, scrut)
            guard = pat.child_by_field_name("condition") if pat.type == "match_pattern" else None
            conds.append((cond, binds, guard, val))
        results = []
        for cond, binds, guard, val in conds:
            self.fl.push_scope()
            pre: list[ir.Stmt] = []
            for b, e in binds:
                self.fl.bind(b, e, self, val, pre, loc, by_ref)
            if guard is not None:
                gc = self._guard(guard, binds)
                cond = ir.Binary(ir.BOOL, loc, "and", cond, gc) if not (isinstance(cond, ir.Lit) and cond.value is True) else gc
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
        out_var = None
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
        """(condition, bindings) for a pattern matched against ``scrut``."""
        loc = self.loc(pat)
        t = pat.type
        if t == "match_pattern":
            return self._pattern(pat.children[0], scrut)
        txt = _text(pat)
        true = ir.Lit(ir.BOOL, loc, True)
        if txt == "_" or t == "remaining_field_pattern":
            return true, []
        if t in ("reference_pattern", "ref_pattern"):
            if txt.startswith("ref "):
                raise self.err("'ref' bindings are not supported", pat)
            return self._pattern(pat.named_children[0], scrut)
        if t == "mut_pattern":
            return self._pattern(pat.named_children[0], scrut)
        if t == "captured_pattern":
            name = _text(pat.named_children[0])
            c, b = self._pattern(pat.named_children[-1], scrut)
            return c, [(name, scrut)] + b
        if t == "identifier":
            if txt == "None" and isinstance(scrut.ty, ir.TOption):
                return ir.Builtin(ir.BOOL, loc, "is_none", (scrut,)), []
            hit = self.fe.lookup(txt)
            if hit is not None and hit[0] in ("variant", "const"):
                return self._path_pattern(hit, pat, scrut, loc)
            return true, [(txt, scrut)]
        if t == "scoped_identifier":
            hit = self.fe.lookup(txt)
            if hit is None:
                if txt.split("::")[-1] == "None" and isinstance(scrut.ty, ir.TOption):
                    return ir.Builtin(ir.BOOL, loc, "is_none", (scrut,)), []
                raise self.err(f"unsupported pattern {txt}", pat)
            return self._path_pattern(hit, pat, scrut, loc)
        if t in ("tuple_struct_pattern", "struct_pattern"):
            tname = _text(pat.child_by_field_name("type"))
            subs = self._subpatterns(pat)
            hit = self.fe.lookup(tname)
            short = tname.split("::")[-1]
            if hit is None and short == "Some" and isinstance(scrut.ty, ir.TOption):
                if len(subs) != 1:
                    raise self.err(f"unsupported pattern {txt}", pat)
                present = ir.Unary(ir.BOOL, loc, "not", ir.Builtin(ir.BOOL, loc, "is_none", (scrut,)))
                inner = ir.Builtin(scrut.ty.inner, loc, "unwrap", (scrut,))
                inner = self.ranged(inner, self.kind_of(scrut)) if scrut.ty.inner == ir.INT else self.kinded(inner, self.kind_of(scrut))
                return self._and_sub(present, subs[0][1], inner, loc)
            if hit is None and short in ("Ok", "Err") and _is_result(scrut.ty):
                return self._variant_pattern(scrut, short, subs, pat, loc)
            if hit is not None and hit[0] == "variant":
                if hit[1] in self.fe.enums:
                    return self._path_pattern(hit, pat, scrut, loc)
                if not (isinstance(scrut.ty, ir.TRecord) and scrut.ty.name == hit[1]):
                    raise self.err(f"pattern {tname} on {scrut.ty}", pat)
                return self._variant_pattern(scrut, hit[2], subs, pat, loc)
            if hit is not None and hit[0] == "type" and hit[1] in self.fe.structs:
                s = self.fe.structs[hit[1]]
                if not (isinstance(scrut.ty, (ir.TRecord, ir.TClass)) and scrut.ty.name == s.name):
                    raise self.err(f"pattern {tname} on {scrut.ty}", pat)
                types = self._struct_fields(s)
                cond: ir.Expr = true
                binds: list[tuple[str, ir.Expr]] = []
                for fname, sp in subs:
                    f = f"_{fname}" if fname.isdigit() else fname
                    if f not in types:
                        raise self.err(f"{s.src} has no field '{fname}'", pat)
                    k = s.kinds.get(f)
                    fv = ir.Field(types[f], loc, scrut, f)
                    fv = self.ranged(fv, k) if types[f] == ir.INT else self.kinded(fv, k)
                    if sp is None:
                        binds.append((fname, fv))
                        continue
                    c, b = self._pattern(sp, fv)
                    cond = c if isinstance(cond, ir.Lit) else (cond if isinstance(c, ir.Lit) and c.value is True else ir.Binary(ir.BOOL, loc, "and", cond, c))
                    binds += b
                return cond, binds
            raise self.err(f"unsupported pattern {txt}", pat)
        if t == "or_pattern":
            parts = [self._pattern(c, scrut) for c in pat.named_children]
            if any(b for _, b in parts):
                raise self.err("or-patterns that bind names are not supported", pat)
            out = parts[0][0]
            for c, _ in parts[1:]:
                out = ir.Binary(ir.BOOL, loc, "or", out, c)
            return out, []
        if t == "range_pattern" and scrut.ty == ir.INT:
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
        if t in ("integer_literal", "string_literal", "boolean_literal", "char_literal", "negative_literal"):
            lit = self.expr(pat, scrut.ty) if t != "negative_literal" else ir.Lit(ir.INT, loc, int(txt.replace("_", "")))
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
            u = ir.Builtin(v.ty.inner, loc, "unwrap", (v,))
            return self.ranged(u, self.kind_of(v)) if v.ty.inner == ir.INT else self.kinded(u, self.kind_of(v))
        if _is_result(v.ty):
            err = self._slot(v, "Err_0", loc)
            if _is_result(ret):
                ret_err = dict(ret.fields).get("Err_0")
                vals = {}
                if ret_err is not None:
                    vals["Err_0"] = self._convert_err(err, ret_err, loc) if err is not None else self.fe.default_value(ret_err, loc)
                early: ir.Expr | None = self._variant(ret, "Err", vals, loc)
            else:
                early = self.fl.coerce(self.opaque("err", [self.fl.coerce(err, ir.TOpaque("")) if err is not None else ir.Lit(ir.INT, loc, 0)], ir.TOpaque(""), loc), ret) if ret != ir.NONE else None
            self.pre.append(ir.If(loc, self._tag_is(v, "Err", loc), (ir.Return(loc, early),), ()))
            ok = self._slot(v, "Ok_0", loc)
            return ok if ok is not None else ir.Lit(ir.NONE, loc, None)
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
        hit = self.fe.lookup(name) if f.type in ("identifier", "scoped_identifier") else None
        short = name.split("::")[-1]
        if hit is None and short == "Some" and len(argn) == 1:
            v = self.expr(argn[0], expect.inner if isinstance(expect, ir.TOption) else None, kind)
            if isinstance(v.ty, (ir.TList, ir.TDict, ir.TOption, ir.TOpaque)):
                raise self.err(f"Option<{v.ty}> is not modelled", n)
            return self.kinded(ir.Builtin(ir.TOption(v.ty), loc, "some", (v,)), self.kind_of(v))
        if hit is None and short in ("Ok", "Err") and len(argn) <= 1:
            return self._result_ctor(short, argn, n, expect, loc)
        if self.spec and name == "old":
            if not self.allow_old:
                raise self.err("old(...) is only meaningful in '@ensures' and invariants", n)
            e = self.expr(argn[0], expect, kind)
            return self.kinded(ir.Old(e.ty, loc, e), self.kind_of(e))
        if self.spec and name == "implies":
            a, b = self.expr(argn[0], ir.BOOL), self.expr(argn[1], ir.BOOL)
            return ir.Binary(ir.BOOL, loc, "implies", a, b)
        if hit is not None and hit[0] == "fn":
            return self.call(self.fe.fns[hit[1]], None, argn, n, expect)
        if hit is not None and hit[0] == "type" and hit[1] in self.fe.structs and self.fe.structs[hit[1]].tuple:
            s = self.fe.structs[hit[1]]
            types = self._struct_fields(s)
            if len(argn) != len(types):
                raise self.err(f"{s.src} has {len(types)} fields", n)
            vals = {f: self.copy_value(self.expr(a, t, s.kinds.get(f))) for (f, t), a in zip(types.items(), argn)}
            return self._build_struct(s, vals, None, loc, n)
        if hit is not None and hit[0] == "variant" and hit[1] in self.fe.data_enums:
            e = self.fe.data_enums[hit[1]]
            rec = self.fe._enum_record(e)
            variant = e.variant(hit[2])
            if rec is not None and variant is not None:
                fields = variant[2]
                if len(argn) != len(fields):
                    raise self.err(f"{e.src}::{hit[2]} has {len(fields)} fields", n)
                types = dict(rec.fields)
                vals = {}
                for (fname, _, _), a in zip(fields, argn):
                    slot = _slot(hit[2], fname)
                    v = self.expr(a, types.get(slot), self.fe.slot_kind(rec.name, slot))
                    if slot in types:
                        vals[slot] = v
                    elif not self.spec and not isinstance(v, (ir.Lit, ir.Var)):
                        self.pre.append(ir.ExprStmt(loc, v))
                return self._variant(rec, hit[2], vals, loc)
            if self.spec:
                raise self.err(f"enum {e.src} is not modelled ({e.why})", n)
        if hit is not None and hit[0] == "assoc":
            info = self.fe.method_of(hit[1], hit[2])
            if info is not None:
                if info.self_mode is not None:  # Type::method(x, ...)
                    if not argn:
                        raise self.err(f"'{info.key}' needs a receiver", n)
                    recv = self.expr(argn[0], info.params[0].ty)
                    return self.call(info, recv, argn[1:], n, expect)
                return self.call(info, None, argn, n, expect)
        if hit is None and short in ("new", "from", "default") and "::" in name:
            owner = name.rsplit("::", 1)[0].split("::")[-1].split("<")[0]
            if owner == "String":
                return self.expr(argn[0], ir.STR) if argn else ir.Lit(ir.STR, loc, "")
            if owner in ("Vec", "HashMap", "BTreeMap", "VecDeque") and not argn:
                if owner in ("HashMap", "BTreeMap"):
                    return ir.Builtin(expect if isinstance(expect, ir.TDict) else ir.TDict(ir.NONE, ir.NONE), loc, "dict_lit", ())
                return ir.ListLit(expect if isinstance(expect, ir.TList) else ir.TList(ir.NONE), loc, ())
        if self.spec:
            raise self.err(f"'{name}' is not a checked function", n)
        args, writes = self.extern_args(argn)
        out = self.hoist(ir.Extern(expect if expect is not None and expect != ir.NONE else ir.TOpaque(f"result of {name}"), loc, name, tuple(args)))
        self.after_extern(writes)
        return out

    def extern_args(self, argn: list[Any]) -> tuple[list[ir.Expr], list[tuple[ir.Expr, Any]]]:
        """Arguments of a call into unchecked code, and the places it may
        write through ``&mut``."""
        args: list[ir.Expr] = []
        writes: list[tuple[ir.Expr, Any]] = []
        for a in argn:
            if a.type == "reference_expression" and _is_mut_ref(a):
                place = self.expr(_deref_target(a.named_children[-1]))
                writes.append((place, a))
                args.append(place if isinstance(place, ir.Var) and isinstance(place.ty, (ir.TList, ir.TDict)) else self.hoist(place))
            else:
                args.append(self.hoist(self.expr(a)))
        return args, writes

    def after_extern(self, writes: list[tuple[ir.Expr, Any]]) -> None:
        for place, node in writes:
            if isinstance(place.ty, ir.TClass) or isinstance(place, ir.Var) and isinstance(place.ty, (ir.TList, ir.TDict)):
                if isinstance(place, ir.Var):
                    self.fl.writable(place.name, node)
                continue  # (unchecked code passed a list variable or an object may change it: the VC generator havocs those)
            self.havoc_place(place, node)

    def call(self, info: FnInfo, recv: ir.Expr | None, argn: list[Any], n: Any, expect: Any) -> ir.Expr:
        loc = self.loc(n)
        params = info.params
        args: list[ir.Expr] = []
        changed = None
        if recv is not None:
            if info.self_mode == "mut" and not isinstance(recv.ty, (ir.TClass, ir.TList, ir.TDict, ir.TOpaque)) and not self.spec:
                changed = recv  # a value behind &mut self: whatever the method leaves in it
            r = self.fl.coerce(self.copy_value(recv) if info.self_mode == "value" else recv, params[0].ty)
            if r.ty != params[0].ty:
                raise self.err(f"'{info.key}' called on {recv.ty}", n)
            args.append(r)
            params = params[1:]
        if len(argn) != len(params):
            raise self.err(f"'{info.key}' takes {len(params)} arguments", n)
        written: list[ir.Var] = []
        for p, a in zip(params, argn):
            if a.type == "reference_expression" and _is_mut_ref(a) and _deref_target(a.named_children[-1]).type == "identifier":
                v = self.expr(_deref_target(a.named_children[-1]))  # &mut v: the callee may change v
                if isinstance(v, ir.Var):
                    self.fl.writable(v.name, a)
                    if not isinstance(v.ty, (ir.TList, ir.TDict, ir.TClass)):
                        written.append(v)  # a value behind &mut: whatever the callee stored
            else:
                v = self.expr(a, p.ty, info.param_kinds.get(p.name))
                if a.type != "reference_expression":
                    v = self.copy_value(v)
            v = self.fl.coerce(v, p.ty)
            if v.ty != p.ty and not (isinstance(p.ty, ir.TList) and isinstance(v.ty, ir.TList) and v.ty.elem == ir.NONE):
                raise self.err(f"argument '{p.name}' of '{info.key}' expects {p.ty}, got {v.ty}", a)
            args.append(v)
        e = ir.Call(info.ret, loc, self.fe.call_name(info), tuple(args))
        if self.spec:
            return self.kinded(e, info.ret_kind)
        if info.ret == ir.NONE:
            self.pre.append(ir.ExprStmt(loc, e))
            out: ir.Expr = ir.Lit(ir.NONE, loc, None)
        else:
            out = self.hoist(self.ranged(e, info.ret_kind) if info.ret_kind and info.ret == ir.INT else self.kinded(e, info.ret_kind))
        for w in written:
            self.havoc_scalar(w, loc)
        if changed is not None:
            self.havoc_place(changed, n)
        return out

    def havoc_scalar(self, v: ir.Var, loc: ir.Loc) -> None:
        """A value written through &mut by code telic does not model here."""
        val = ir.Extern(v.ty, loc, "write through &mut", ())
        k = self.fl.kinds.get(v.name)
        self.pre.append(ir.Assign(loc, v.name, self.fl.in_range(val, k) if k and v.ty == ir.INT else val))
        self.pre += _tag_ranges(ir.Var(v.ty, loc, v.name), loc)

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
            op = "eq" if name.endswith("eq") else "ne"
            text = f"{' '.join(_text(args[0]).split())} {'==' if op == 'eq' else '!='} {' '.join(_text(args[1]).split())}"
            self.pre.append(ir.AssertStmt(loc, ir.Clause("assert", self._eq(a, b, n, op), loc, text), native=True))
            return ir.Lit(ir.NONE, loc, None)
        if name in ("println", "print", "eprintln", "eprint", "dbg", "trace", "debug", "info", "warn", "error", "log"):
            return ir.Lit(ir.NONE, loc, None)
        if name == "format":
            return ir.Builtin(ir.STR, loc, "str_fn", (ir.Lit(ir.STR, loc, "format"), ir.Lit(ir.STR, loc, body)))
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
        owner = t.name if isinstance(t, (ir.TClass, ir.TRecord, ir.TEnum)) else None
        if owner is not None and (owner in self.fe.structs or owner in self.fe.enums or owner in self.fe.data_enums):
            info = self.fe.method_of(owner, m)
            if info is not None:
                return self.call(info, recv, argn, n, expect)
            if m == "clone" and not argn:
                if not isinstance(t, ir.TClass):
                    return recv
                if self.spec:
                    raise self.err("clone() in a specification", n)
                return self._copy_obj(recv, loc, 0)
        if _is_result(t):
            return self.result_method(recv, m, argn, n, expect)
        if isinstance(t, ir.TOpaque) and t.why.startswith("generic:"):
            bounds = [x for x in t.why[len("generic:") :].split("|") if x]
            for tr in bounds:
                for sup in self.fe.supertraits(tr):
                    uid = self.fe.methods.get((sup, m))
                    if uid is not None:
                        return self.call(self.fe.fns[uid], recv, argn, n, expect)
            conv = self._conversion(recv, m, argn, bounds, loc)
            if conv is not None:
                return conv
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
        if isinstance(t, ir.TOpaque) and m in ("len", "count", "capacity") and not argn:
            v = self._opaque_as(self.hoist(ir.Extern(ir.TOpaque(""), loc, f"{t}.{m}", (recv,))), ir.INT, None)
            return self.kinded(ir.Builtin(ir.INT, loc, "in_range", (v, ir.Lit(ir.INT, loc, 0), ir.Lit(ir.INT, loc, (1 << 64) - 1))), "usize")
        if isinstance(t, ir.TOpaque) and m in ("unwrap", "expect"):
            return self.opaque("unwrap", [recv], ir.TOpaque(""), loc)  # a Result from unchecked code
        args, writes = self.extern_args(argn)
        out = self.hoist(ir.Extern(expect if expect is not None and expect != ir.NONE else ir.TOpaque(f"result of .{m}()"), loc, f"{t}.{m}", (recv, *args)))
        self.after_extern(writes)
        return out

    def _conversion(self, recv: ir.Expr, m: str, argn: list[Any], bounds: list[str], loc: ir.Loc) -> ir.Expr | None:
        """x.as_ref() / x.into() / x.borrow() on a generic bounded by
        AsRef<U> / Into<U> / Borrow<U>: some value of type U."""
        want = {"as_ref": "AsRef", "into": "Into", "borrow": "Borrow", "as_mut": "AsMut"}.get(m)
        if want is None or argn or self.spec:
            return None
        for b in bounds:
            base, _, arg = b.partition("<")
            if base.strip() != want or not arg.endswith(">"):
                continue
            t, k = self.fe.type_of_text(arg[:-1])
            if isinstance(t, (ir.TOpaque, ir.TNone)):
                return None
            v = self.hoist(ir.Builtin(t, loc, "from_opaque", (self.hoist(ir.Extern(ir.TOpaque(""), loc, f"{want}::{m}", (recv,))),)))  # (each call may return something else)
            if isinstance(t, (ir.TList, ir.TDict)):
                return self.elems_kinded(v, k)
            return self.ranged(v, k) if t == ir.INT else v
        return None

    def int_method(self, recv: ir.Expr, m: str, argn: list[Any], n: Any, k: str | None) -> ir.Expr:
        loc = self.loc(n)
        args = [self.expr(a, ir.INT, k) for a in argn]
        if m == "abs":
            return self.checked(ir.Builtin(ir.INT, loc, "abs", (recv,)), k)
        if m in ("min", "max"):
            return self.kinded(ir.Builtin(ir.INT, loc, m, (recv, args[0])), k)
        exp = _int_literal(argn[0]) if argn else None
        if m == "pow" and exp is not None and 0 <= exp <= 128:
            p = exp
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
        unsigned = ("u" + k[1:]) if k and k.startswith("i") else k
        zero = ir.Lit(ir.INT, loc, 0)
        if m == "unsigned_abs" and not argn:
            return self.kinded(ir.Ite(ir.INT, loc, ir.Binary(ir.BOOL, loc, "lt", recv, zero), ir.Unary(ir.INT, loc, "neg", recv), recv), unsigned)
        if m == "abs_diff" and len(args) == 1:
            return self.kinded(ir.Ite(ir.INT, loc, ir.Binary(ir.BOOL, loc, "gt", recv, args[0]), ir.Binary(ir.INT, loc, "sub", recv, args[0]), ir.Binary(ir.INT, loc, "sub", args[0], recv)), unsigned)
        if m == "clamp" and len(args) == 2:
            if not self.spec:
                ok = ir.Binary(ir.BOOL, loc, "le", args[0], args[1])
                self.pre.append(ir.AssertStmt(loc, ir.Clause("assert", ok, loc, "clamp's min <= max"), native=True))
            return self.kinded(ir.Builtin(ir.INT, loc, "min", (ir.Builtin(ir.INT, loc, "max", (recv, args[0])), args[1])), k)
        if self.spec:
            raise self.err(f"integer method .{m}() in a specification", n)
        if m in ("count_ones", "count_zeros", "leading_zeros", "trailing_zeros", "leading_ones", "trailing_ones") and k:
            return self.kinded(ir.Builtin(ir.INT, loc, "in_range", (self.opaque(f"int.{m}", [recv], ir.INT, loc), zero, ir.Lit(ir.INT, loc, INT_KINDS[k][1]))), "u32")
        if m == "is_power_of_two":
            return self.opaque("int.is_power_of_two", [recv], ir.BOOL, loc)
        if m in ("rem_euclid", "div_euclid", "wrapping_div", "wrapping_rem") and len(args) == 1 and k:
            y = self.hoist(args[0])
            r = ir.Binary(ir.INT, loc, "tmod", recv, y)  # (dividing by zero panics)
            if m == "wrapping_rem":
                return self.kinded(ir.Ite(ir.INT, loc, ir.Binary(ir.BOOL, loc, "eq", y, ir.Lit(ir.INT, loc, -1)), zero, r), k)
            if m == "wrapping_div":
                q = ir.Binary(ir.INT, loc, "tdiv", recv, y)
                lo = ir.Lit(ir.INT, loc, int_range(k)[0])
                return self.kinded(ir.Ite(ir.INT, loc, ir.Binary(ir.BOOL, loc, "gt", q, ir.Lit(ir.INT, loc, int_range(k)[1])), lo, q), k)
            r = self.hoist(r)
            rem = ir.Ite(ir.INT, loc, ir.Binary(ir.BOOL, loc, "lt", r, zero), ir.Binary(ir.INT, loc, "add", r, ir.Builtin(ir.INT, loc, "abs", (y,))), r)
            if INT_KINDS[k][0]:  # MIN % -1 overflows
                self.pre.append(ir.ExprStmt(loc, self.checked(ir.Binary(ir.INT, loc, "tdiv", recv, y), k)))
            if m == "rem_euclid":
                return self.kinded(rem, k)
            return self.kinded(ir.Binary(ir.INT, loc, "tdiv", ir.Binary(ir.INT, loc, "sub", recv, rem), y), k)
        if m in ("pow", "next_power_of_two") and k:
            return self.checked(self.opaque(f"int.{m}", [recv, *args], ir.INT, loc), k)  # (it panics when the result does not fit)
        if m in ("isqrt", "ilog2", "ilog10", "ilog") and k:
            ok = ir.Binary(ir.BOOL, loc, "ge" if m == "isqrt" else "gt", recv, zero)
            self.pre.append(ir.AssertStmt(loc, ir.Clause("assert", ok, loc, f"{m} of a {'negative' if m == 'isqrt' else 'non-positive'} number panics"), native=True))
            return self.kinded(ir.Builtin(ir.INT, loc, "in_range", (self.opaque(f"int.{m}", [recv, *args], ir.INT, loc), zero, ir.Lit(ir.INT, loc, int_range(k)[1]))), k if m == "isqrt" else "u32")
        if m in ("wrapping_neg", "rotate_left", "rotate_right", "swap_bytes", "reverse_bits", "saturating_pow", "wrapping_pow", "to_be", "to_le", "from_be", "from_le"):
            return self.ranged(self.opaque(f"int.{m}", [recv, *args], ir.INT, loc), k)  # same type as the receiver
        return self.hoist(ir.Extern(ir.TOpaque(f"result of .{m}()"), loc, f"int.{m}", (self.fl.coerce(recv, ir.TOpaque("")), *[self.fl.coerce(a, ir.TOpaque("")) for a in args])))

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
        if m in ("take", "replace") and not self.spec and len(argn) == (1 if m == "replace" else 0):
            old = self.hoist(recv)
            new = self.fl.coerce(self.expr(argn[0], t.inner, k), t) if m == "replace" else ir.Lit(t, loc, None)
            if isinstance(recv, ir.Var):
                self.fl.writable(recv.name, n)
                self.pre.append(ir.Assign(loc, recv.name, new))
            elif isinstance(recv, ir.Field) and isinstance(recv.obj.ty, ir.TClass):
                self.pre.append(ir.FieldAssign(loc, recv.obj, recv.obj.ty.name, recv.name, new))
            else:
                raise self.err(f".{m}() on an Option that is not a variable or field", n)
            return self.kinded(old, k)
        if m == "ok_or" and len(argn) == 1:
            e = self.expr(argn[0])
            rt = expect if _is_result(expect) else self.fe.result_type(t.inner, e.ty, k, self.kind_of(e))
            if _is_result(rt):
                assert isinstance(rt, ir.TRecord)
                some = self._variant(rt, "Ok", {"Ok_0": ir.Builtin(t.inner, loc, "unwrap", (recv,))} if "Ok_0" in dict(rt.fields) else {}, loc)
                none = self._variant(rt, "Err", {"Err_0": e} if "Err_0" in dict(rt.fields) else {}, loc)
                return ir.Ite(rt, loc, ir.Builtin(ir.BOOL, loc, "is_none", (recv,)), none, some)
        if self.spec:
            raise self.err(f"Option method .{m}() in a specification", n)
        args, writes = self.extern_args(argn)
        out = self.hoist(ir.Extern(expect if expect is not None and expect != ir.NONE else ir.TOpaque(""), loc, f"Option.{m}", (recv, *args)))
        if m in ("insert", "get_or_insert", "get_or_insert_with", "as_mut", "iter_mut", "as_deref_mut", "take_if"):
            self.havoc_place(recv, n)
        self.after_extern(writes)
        return out

    def vec_method(self, recv: ir.Expr, recv_n: Any, m: str, argn: list[Any], n: Any, expect: Any) -> ir.Expr:
        loc = self.loc(n)
        t = recv.ty
        assert isinstance(t, ir.TList)
        ek = self.kind_of_elems(recv)
        length = ir.Builtin(ir.INT, loc, "len", (recv,))
        if m == "len":
            if self.spec:
                return self.kinded(length, "usize")
            # a Vec of non-zero-sized elements never holds more than isize::MAX of them
            zst = isinstance(t.elem, (ir.TRecord, ir.TClass)) and not (t.elem.fields if isinstance(t.elem, ir.TRecord) else self.fe.classes.get(t.elem.name, ir.ClassDecl("", [], [])).fields)
            return self.kinded(ir.Builtin(ir.INT, loc, "in_range", (length, ir.Lit(ir.INT, loc, 0), ir.Lit(ir.INT, loc, (1 << 64) - 1 if zst else (1 << 63) - 1))), "usize")
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
        if isinstance(recv, ir.Var) and m not in ("len", "iter", "get", "first", "last", "contains", "is_empty", "to_vec", "clone"):
            self.fl.writable(recv.name, n)
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
        args, writes = self.extern_args(argn)
        if m in ("remove", "swap_remove", "insert") and len(args) == (2 if m == "insert" else 1):
            i = args[0]
            bound = ir.Binary(ir.BOOL, loc, "le" if m == "insert" else "lt", i, length)
            self.pre.append(ir.AssertStmt(loc, ir.Clause("assert", ir.Binary(ir.BOOL, loc, "and", ir.Binary(ir.BOOL, loc, "le", ir.Lit(ir.INT, loc, 0), i), bound), loc, f"the {m} index is within bounds"), native=True))
        ret = expect if expect is not None and expect != ir.NONE else ir.TOpaque(f"result of .{m}()")
        if m in VEC_MUTATORS and not isinstance(recv, ir.Var):
            out = self.hoist(ir.Extern(ret, loc, f"Vec.{m}", (self.fl.coerce(recv, ir.TOpaque("")), *args)))
            self.havoc_place(recv, n)  # a list in a field, changed in a way telic does not track
            self.after_extern(writes)
            return out
        if m in VEC_MUTATORS:
            # the list changes in a way telic does not track: an unchecked call that may change it
            if m in ("sort", "sort_unstable", "reverse", "sort_by", "sort_by_key", "sort_unstable_by", "sort_unstable_by_key", "fill", "rotate_left", "rotate_right", "swap"):
                before = self.hoist(length)  # same length, elements rearranged or replaced
                self.pre.append(ir.ExprStmt(loc, ir.Extern(ir.NONE, loc, f"Vec.{m}", (recv, *args))))
                self.pre.append(ir.AssumeStmt(loc, ir.Clause("assume", ir.Binary(ir.BOOL, loc, "eq", length, before), loc, f"{m} keeps the length")))
                self.after_extern(writes)
                return ir.Lit(ir.NONE, loc, None)
            call = ir.Extern(ret if m in ("remove", "swap_remove", "drain", "split_off", "pop", "pop_back", "pop_front", "iter_mut", "last_mut", "first_mut", "get_mut", "as_mut_slice") else ir.NONE, loc, f"Vec.{m}", (recv, *args))
            out = self.hoist(call) if call.ty != ir.NONE else ir.Lit(ir.NONE, loc, None)
            if call.ty == ir.NONE:
                self.pre.append(ir.ExprStmt(loc, call))
            self.after_extern(writes)
            return out
        pure_recv = self.fl.coerce(recv, ir.TOpaque("")) if isinstance(recv, ir.Var) else recv
        out = self.hoist(ir.Extern(ret, loc, f"Vec.{m}", (pure_recv, *args)))
        self.after_extern(writes)
        return out

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
        if isinstance(recv, ir.Var) and m in ("insert", "remove", "clear", "retain", "entry", "get_mut", "extend", "drain"):
            self.fl.writable(recv.name, n)
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
        args, writes = self.extern_args(argn)
        out = self.hoist(ir.Extern(expect if expect is not None and expect != ir.NONE else ir.TOpaque(""), loc, f"HashMap.{m}", (recv, *args)))
        if not isinstance(recv, ir.Var) and m not in ("get", "contains_key", "is_empty", "keys", "values", "iter", "clone", "get_key_value"):
            self.havoc_place(recv, n)
        self.after_extern(writes)
        return out

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
        out = self.hoist(ir.Extern(expect if expect is not None and expect != ir.NONE else ir.TOpaque(""), loc, f"str.{m}", (recv, *[self.hoist(a) for a in args])))
        if m in ("push", "push_str", "pop", "clear", "insert", "insert_str", "remove", "retain", "truncate", "drain", "extend", "make_ascii_lowercase", "make_ascii_uppercase", "replace_range", "split_off", "as_mut_str", "reserve", "shrink_to_fit"):
            self.havoc_place(recv, n)  # a String changed in a way telic does not track
        return out

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

    def _path_value(self, hit: tuple, txt: str, n: Any, expect: Any, loc: ir.Loc) -> ir.Expr | None:
        """The value a path names: a constant, a unit variant, a unit struct."""
        if hit[0] == "const":
            c = self.fe.consts.get(hit[1])
            if c is not None:
                lit, k = c
                if lit.type == "unary_expression":
                    v = self.expr(lit.named_children[0], expect, k)
                    return self.kinded(ir.Lit(v.ty, loc, -v.value), k)  # type: ignore[operator]
                v = self.expr(lit, expect, k)
                return self.kinded(dataclasses.replace(v, loc=loc), self.kind_of(v))
            if self.spec:
                raise self.err(f"the value of '{txt}' is not known to telic", n)
            tn = self.fe.const_types.get(hit[1])
            if tn is not None:
                saved = self.fe.cur_mod, self.fe.cur_generics, self.fe.cur_self, self.fe.cur_subst
                self.fe._in(hit[1][0], {})
                try:
                    t, k = self.fe.ty(tn)
                finally:
                    self.fe.cur_mod, self.fe.cur_generics, self.fe.cur_self, self.fe.cur_subst = saved
                if not isinstance(t, (ir.TOpaque, ir.TNone)):
                    v = self.hoist(ir.Extern(t, loc, txt, ()))
                    size = _array_len(tn)
                    if size is not None:
                        self.pre.append(ir.ExprStmt(loc, ir.Builtin(ir.INT, loc, "in_range", (ir.Builtin(ir.INT, loc, "len", (v,)), ir.Lit(ir.INT, loc, size), ir.Lit(ir.INT, loc, size)))))
                    if isinstance(t, (ir.TList, ir.TDict)):
                        return self.elems_kinded(v, k)
                    return self.ranged(v, k) if t == ir.INT else v
            return self.hoist(ir.Extern(expect if expect is not None and expect != ir.NONE else ir.TOpaque(txt), loc, txt, ()))
        if hit[0] == "variant":
            owner, v = hit[1], hit[2]
            if owner in self.fe.enums:
                return self._enum_lit(self.fe.enums[owner], v, loc)
            e = self.fe.data_enums.get(owner)
            if e is None:
                return None
            rec = self.fe._enum_record(e)
            variant = e.variant(v)
            if rec is None or variant is None or variant[1] != "unit":
                if self.spec:
                    raise self.err(f"enum {e.src} is not modelled ({e.why or 'a variant used as a function'})", n)
                return self.hoist(ir.Extern(ir.TOpaque(txt), loc, txt, ()))
            return self._variant(rec, v, {}, loc)
        if hit[0] == "type":
            s = self.fe.structs.get(hit[1])
            if s is not None and not s.fields:
                return self._build_struct(s, {}, None, loc, n)
        if hit[0] == "fn":
            if self.spec:
                raise self.err(f"function '{txt}' used as a value in a specification", n)
            return self.opaque("fn", [ir.Lit(ir.STR, loc, txt)], ir.TOpaque("fn"), loc)
        return None

    def _variant(self, rec: ir.TRecord, variant: str, vals: dict[str, ir.Expr], loc: ir.Loc) -> ir.Expr:
        """A value of a data-carrying enum (or Result): the tag, this
        variant's fields, and defaults in every other variant's."""
        tag = dict(rec.fields)["tag"]
        assert isinstance(tag, ir.TEnum)
        out = []
        for f, t in rec.fields:
            if f == "tag":
                out.append((f, ir.Lit(tag, loc, tag.members.index(variant))))
            elif f in vals:
                v = self.fl.coerce(vals[f], t)
                if v.ty != t:
                    raise LowerError(f"{variant} holds {t}, not {v.ty}", loc.line)
                out.append((f, v))
            else:
                out.append((f, self.fe.default_value(t, loc)))
        return ir.RecordLit(rec, loc, tuple(out))

    def _tag_is(self, scrut: ir.Expr, variant: str, loc: ir.Loc) -> ir.Expr:
        assert isinstance(scrut.ty, ir.TRecord)
        tag = dict(scrut.ty.fields)["tag"]
        assert isinstance(tag, ir.TEnum)
        return ir.Binary(ir.BOOL, loc, "eq", ir.Field(tag, loc, scrut, "tag"), ir.Lit(tag, loc, tag.members.index(variant)))

    def _slot(self, scrut: ir.Expr, slot: str, loc: ir.Loc) -> ir.Expr | None:
        assert isinstance(scrut.ty, ir.TRecord)
        ft = dict(scrut.ty.fields).get(slot)
        if ft is None:
            return None
        v = ir.Field(ft, loc, scrut, slot)
        k = self.fe.slot_kind(scrut.ty.name, slot)
        return self.ranged(v, k) if ft == ir.INT else self.kinded(v, k)

    def _struct_fields(self, s: StructInfo) -> dict[str, ir.Type]:
        return dict(self.fe.records[s.name].fields if s.record else self.fe.classes[s.name].fields)

    def _build_struct(self, s: StructInfo, vals: dict[str, ir.Expr], base: ir.Expr | None, loc: ir.Loc, n: Any) -> ir.Expr:
        types = self._struct_fields(s)
        args = []
        for f, t in types.items():
            if f in vals:
                args.append(self.fl.coerce(vals[f], t))
            elif base is not None:
                args.append(ir.Field(t, loc, base, f))
            else:
                raise self.err(f"{s.src} literal is missing field '{f}'", n)
        if s.record:
            return ir.RecordLit(self.fe.records[s.name], loc, tuple(zip(types, args)))
        if self.spec:
            raise self.err("specifications cannot create objects", n)
        return self.hoist(ir.New(ir.TClass(s.name), loc, s.name, tuple(args)))

    def _guard(self, guard: Any, binds: list[tuple[str, ir.Expr]]) -> ir.Expr:
        """A match guard, over the arm's bindings (substituted: they are
        bound only once the arm is taken)."""
        g = self.sub()
        saved = {}
        for b, e in binds:
            g.bound[b] = e.ty
            saved[b] = self.fl.kinds.get(b)
            k = self.kind_of(e)
            if k:
                self.fl.kinds[b] = k
        try:
            gc = g.expr(guard, ir.BOOL)
        finally:
            for b, k0 in saved.items():
                if k0 is None:
                    self.fl.kinds.pop(b, None)
                else:
                    self.fl.kinds[b] = k0
        if g.pre:
            raise self.err("match guards with side effects are not supported", guard)
        for b, e in binds:
            gc = _subst(gc, b, e)
        return gc

    def _subpatterns(self, pat: Any) -> list[tuple[str, Any]]:
        """(field, sub-pattern) of 'P(a, _)' (fields 0, 1, ...) or 'S { a, b: p, .. }'
        (a sub-pattern of None binds the field's own name)."""
        out: list[tuple[str, Any]] = []
        if pat.type == "tuple_struct_pattern":
            i = 0
            kids = [c for j, c in enumerate(pat.children) if pat.field_name_for_child(j) != "type" and c.type not in ("(", ")", ",", "line_comment", "block_comment")]
            for j, c in enumerate(kids):
                if c.type == "remaining_field_pattern":
                    if j != len(kids) - 1:
                        raise self.err("'..' before the last field of a pattern is not supported", pat)
                    break
                out.append((str(i), c))
                i += 1
            return out
        for c in pat.named_children:
            if c.type == "field_pattern":
                nm = c.child_by_field_name("name")
                sp = c.child_by_field_name("pattern")
                if _text(c).startswith("ref "):
                    raise self.err("'ref' bindings are not supported", c)
                out.append((_text(nm), sp))
            elif c.type == "shorthand_field_identifier":
                out.append((_text(c), None))
        return out

    def _and_sub(self, cond: ir.Expr, sp: Any, v: ir.Expr, loc: ir.Loc) -> tuple[ir.Expr, list[tuple[str, ir.Expr]]]:
        if sp is None:
            return cond, []
        c, b = self._pattern(sp, v)
        if isinstance(c, ir.Lit) and c.value is True:
            return cond, b
        return ir.Binary(ir.BOOL, loc, "and", cond, c), b

    def _variant_pattern(self, scrut: ir.Expr, variant: str, subs: list[tuple[str, Any]], pat: Any, loc: ir.Loc) -> tuple[ir.Expr, list[tuple[str, ir.Expr]]]:
        cond = self._tag_is(scrut, variant, loc)
        binds: list[tuple[str, ir.Expr]] = []
        for fname, sp in subs:
            fv = self._slot(scrut, _slot(variant, fname), loc)
            if fv is None:  # a () payload
                if sp is not None and _text(sp) not in ("_", "()"):
                    raise self.err(f"unsupported pattern {_text(sp)}", sp)
                continue
            if sp is None:
                binds.append((fname, fv))
                continue
            c, b = self._pattern(sp, fv)
            if not (isinstance(c, ir.Lit) and c.value is True):
                cond = ir.Binary(ir.BOOL, loc, "and", cond, c)
            binds += b
        return cond, binds

    def _path_pattern(self, hit: tuple, pat: Any, scrut: ir.Expr, loc: ir.Loc) -> tuple[ir.Expr, list[tuple[str, ir.Expr]]]:
        if hit[0] == "variant":
            if hit[1] in self.fe.enums:
                if not (isinstance(scrut.ty, ir.TEnum) and scrut.ty.name == hit[1]):
                    raise self.err(f"pattern {_text(pat)} on {scrut.ty}", pat)
                return ir.Binary(ir.BOOL, loc, "eq", scrut, self._enum_lit(scrut.ty, hit[2], loc)), []
            if isinstance(scrut.ty, ir.TRecord) and scrut.ty.name == hit[1]:
                return self._tag_is(scrut, hit[2], loc), []
        if hit[0] == "const":
            v = self._path_value(hit, _text(pat), pat, scrut.ty, loc)
            if v is not None and not isinstance(v, ir.Var):
                a, b = self._same(scrut, v, pat)
                return ir.Binary(ir.BOOL, loc, "eq", a, b), []
        raise self.err(f"unsupported pattern {_text(pat)}", pat)

    def _result_ctor(self, name: str, argn: list[Any], n: Any, expect: Any, loc: ir.Loc) -> ir.Expr:
        """Ok(v) / Err(e): a Result record when the context fixes its type."""
        if _is_result(expect):
            slot = f"{name}_0"
            ft = dict(expect.fields).get(slot)
            vals = {}
            if argn:
                v = self.expr(argn[0], ft, self.fe.slot_kind(expect.name, slot))
                if ft is not None:
                    vals[slot] = v
                elif not self.spec and not isinstance(v, (ir.Lit, ir.Var)):
                    self.pre.append(ir.ExprStmt(loc, v))
            return self._variant(expect, name, vals, loc)
        if self.spec:
            raise self.err("a Result whose type telic does not know, in a specification", n)
        v = self.expr(argn[0]) if argn else ir.Lit(ir.NONE, loc, None)
        return self.opaque(name.lower(), [self.fl.coerce(v, ir.TOpaque("")) if not isinstance(v.ty, ir.TOpaque) else v], ir.TOpaque("Result"), loc)

    def havoc_place(self, v: ir.Expr, n: Any) -> None:
        """A value a ``&mut self`` method changed: telic does not model what
        it leaves there."""
        loc = self.loc(n)
        if isinstance(v, ir.Var):
            self.fl.writable(v.name, n)
            self.havoc_scalar(v, loc)
            return
        if isinstance(v, ir.Field) and isinstance(v.obj.ty, ir.TClass):
            self.pre.append(ir.FieldAssign(loc, v.obj, v.obj.ty.name, v.name, ir.Extern(v.ty, loc, "write through &mut", ())))
            return
        if isinstance(v, ir.Field) and isinstance(v.obj.ty, ir.TRecord) and isinstance(v.obj, (ir.Var, ir.Field)):
            rec = v.obj.ty
            self.havoc_place_with(v.obj, ir.RecordLit(rec, loc, tuple((f, ir.Extern(ft, loc, "write through &mut", ()) if f == v.name else ir.Field(ft, loc, v.obj, f)) for f, ft in rec.fields)), n)
            return
        raise self.err("a value changed through &mut that is not a variable or field is not modelled", n)

    def havoc_place_with(self, place: ir.Expr, value: ir.Expr, n: Any) -> None:
        """Store ``value`` into a variable, or a field of one (records are values: rebuilt)."""
        loc = self.loc(n)
        if isinstance(place, ir.Var):
            self.fl.writable(place.name, n)
            self.pre.append(ir.Assign(loc, place.name, value))
            self.pre += _tag_ranges(ir.Var(place.ty, loc, place.name), loc)
            return
        if isinstance(place, ir.Field) and isinstance(place.obj.ty, ir.TClass):
            self.pre.append(ir.FieldAssign(loc, place.obj, place.obj.ty.name, place.name, value))
            return
        if isinstance(place, ir.Field) and isinstance(place.obj.ty, ir.TRecord):
            rec = place.obj.ty
            self.havoc_place_with(place.obj, ir.RecordLit(rec, loc, tuple((f, value if f == place.name else ir.Field(ft, loc, place.obj, f)) for f, ft in rec.fields)), n)
            return
        raise self.err("a value changed through &mut that is not a variable or field is not modelled", n)

    def _convert_err(self, err: ir.Expr, to: ir.Type, loc: ir.Loc) -> ir.Expr:
        """'?' converts the error with From::from: the identity, a checked
        'impl From<E> for F', or an unchecked conversion."""
        if err.ty == to:
            return err
        name = getattr(to, "name", None)
        if name is not None:
            for info in self.fe.fns.values():
                if info.owner == name and info.key.split("@")[0] == f"{name}.from" and len(info.params) == 1 and info.params[0].ty == err.ty:
                    e = ir.Call(info.ret, loc, self.fe.call_name(info), (err,))
                    return self.hoist(e) if info.ret == to else self.fl.coerce(self.fl.coerce(self.hoist(e), ir.TOpaque("")), to)
        return self.hoist(ir.Extern(to, loc, "From::from", (self.fl.coerce(err, ir.TOpaque("")) if not isinstance(err.ty, ir.TOpaque) else err,)))

    def result_method(self, recv: ir.Expr, m: str, argn: list[Any], n: Any, expect: Any) -> ir.Expr:
        loc = self.loc(n)
        t = recv.ty
        assert isinstance(t, ir.TRecord)
        ok = self._slot(recv, "Ok_0", loc)
        err = self._slot(recv, "Err_0", loc)
        is_ok = self._tag_is(recv, "Ok", loc)
        if m == "is_ok":
            return is_ok
        if m == "is_err":
            return ir.Unary(ir.BOOL, loc, "not", is_ok)
        if m in ("clone", "copied", "cloned", "as_ref", "as_deref"):
            return recv
        if m in ("unwrap", "expect", "unwrap_err", "expect_err"):
            want_ok = m in ("unwrap", "expect")
            cond = is_ok if want_ok else ir.Unary(ir.BOOL, loc, "not", is_ok)
            val = ok if want_ok else err
            if self.spec:
                if val is None:
                    return ir.Lit(ir.NONE, loc, None)
                return ir.Ite(val.ty, loc, cond, val, ir.Builtin(val.ty, loc, "from_opaque", (ir.Builtin(ir.TOpaque(""), loc, "opaque_op", (ir.Lit(ir.STR, loc, f"{m} of the other variant"), self.fl.coerce(recv, ir.TOpaque(""))),),)))
            text = f"called `Result::{m}()` on an `{'Err' if want_ok else 'Ok'}` value"
            self.pre.append(ir.AssertStmt(loc, ir.Clause("assert", cond, loc, text), native=True))
            return val if val is not None else ir.Lit(ir.NONE, loc, None)
        if m in ("unwrap_or", "unwrap_or_default") and ok is not None:
            d = self.expr(argn[0], ok.ty, self.kind_of(ok)) if argn else _default(ok.ty, loc)
            if d is None:
                raise self.err(f"no default for {ok.ty}", n)
            return self.kinded(ir.Ite(ok.ty, loc, is_ok, ok, self.fl.coerce(d, ok.ty)), self.kind_of(ok))
        if m in ("ok", "err"):
            val = ok if m == "ok" else err
            cond = is_ok if m == "ok" else ir.Unary(ir.BOOL, loc, "not", is_ok)
            if val is not None and not isinstance(val.ty, (ir.TOption, ir.TList, ir.TDict, ir.TOpaque)):
                ot = ir.TOption(val.ty)
                return self.kinded(ir.Ite(ot, loc, cond, ir.Builtin(ot, loc, "some", (val,)), ir.Lit(ot, loc, None)), self.kind_of(val))
        if self.spec:
            raise self.err(f"Result method .{m}() in a specification", n)
        args, writes = self.extern_args(argn)
        out = self.hoist(ir.Extern(expect if expect is not None and expect != ir.NONE else ir.TOpaque(""), loc, f"Result.{m}", (self.fl.coerce(recv, ir.TOpaque("")), *args)))
        if m in ("as_mut", "iter_mut", "insert", "get_or_insert_with"):
            self.havoc_place(recv, n)
        self.after_extern(writes)
        return out

    def _eq(self, a: ir.Expr, b: ir.Expr, n: Any, op: str) -> ir.Expr:
        """``a == b`` as Rust runs it: PartialEq::eq, derived (structural) or
        a checked impl; unknown for types telic does not model."""
        loc = self.loc(n)
        a, b = self._same(a, b, n)
        t = a.ty
        name = getattr(t, "name", None)
        custom = None
        if name in self.fe.structs:
            custom = self.fe.structs[name].eq
        elif name in self.fe.data_enums:
            custom = self.fe.data_enums[name].eq
        if custom == "impl" and not self.spec:
            info = self.fe.method_of(name, "eq")  # type: ignore[arg-type]
            if info is not None and len(info.params) == 2:
                r = self.hoist(ir.Call(ir.BOOL, loc, self.fe.call_name(info), (a, self.fl.coerce(b, info.params[1].ty))))
            else:
                r = self.hoist(ir.Extern(ir.BOOL, loc, "PartialEq::eq", (self.fl.coerce(a, ir.TOpaque("")), self.fl.coerce(b, ir.TOpaque("")))))
        elif isinstance(t, ir.TOpaque) and not self.spec:
            r = self.hoist(ir.Extern(ir.BOOL, loc, "PartialEq::eq", (a, b)))
        else:
            r = self._structural_eq(a, b, loc, 0) or (None if self.spec else self.hoist(ir.Extern(ir.BOOL, loc, "PartialEq::eq", (self.fl.coerce(a, ir.TOpaque("")), self.fl.coerce(b, ir.TOpaque(""))))))
            if r is None:
                r = ir.Binary(ir.BOOL, loc, "eq", a, b)
        return r if op == "eq" else ir.Unary(ir.BOOL, loc, "not", r)

    def _structural_eq(self, a: ir.Expr, b: ir.Expr, loc: ir.Loc, depth: int) -> ir.Expr | None:
        """Field-by-field equality (derived PartialEq); None when telic cannot
        compare these values that way."""
        t = a.ty
        if isinstance(t, ir.TRecord) and t.fields[:1] and t.fields[0][0] == "tag":
            if t.name in self.fe.data_enums and self.fe.data_enums[t.name].eq != "derive" and not self.spec:
                return None
            tag = t.fields[0][1]
            assert isinstance(tag, ir.TEnum)
            out: ir.Expr = ir.Binary(ir.BOOL, loc, "eq", ir.Field(tag, loc, a, "tag"), ir.Field(tag, loc, b, "tag"))
            for i, v in enumerate(tag.members):
                parts = []
                for f, ft in t.fields[1:]:
                    if f.startswith(v + "_"):
                        e = self._structural_eq(ir.Field(ft, loc, a, f), ir.Field(ft, loc, b, f), loc, depth + 1)
                        if e is None:
                            return None
                        parts.append(e)
                if parts:
                    body = parts[0]
                    for p in parts[1:]:
                        body = ir.Binary(ir.BOOL, loc, "and", body, p)
                    out = ir.Binary(ir.BOOL, loc, "and", out, ir.Binary(ir.BOOL, loc, "implies", ir.Binary(ir.BOOL, loc, "eq", ir.Field(tag, loc, a, "tag"), ir.Lit(tag, loc, i)), body))
            return out
        if isinstance(t, ir.TRecord):
            s = self.fe.structs.get(t.name)
            if s is not None and s.eq != "derive" and not self.spec:
                return None
            out = ir.Lit(ir.BOOL, loc, True)
            for f, ft in t.fields:
                e = self._structural_eq(ir.Field(ft, loc, a, f), ir.Field(ft, loc, b, f), loc, depth + 1)
                if e is None:
                    return None
                out = e if isinstance(out, ir.Lit) else ir.Binary(ir.BOOL, loc, "and", out, e)
            return out
        if isinstance(t, ir.TClass):
            if self.spec:
                return ir.Binary(ir.BOOL, loc, "eq", a, b)
            s = self.fe.structs.get(t.name)
            if s is None or s.eq != "derive" or depth > 2:
                return None
            decl = self.fe.classes[t.name]
            out = ir.Lit(ir.BOOL, loc, True)
            for f, ft in decl.fields:
                fa, fb = self.hoist(ir.Field(ft, loc, a, f)), self.hoist(ir.Field(ft, loc, b, f))
                e = self._structural_eq(fa, fb, loc, depth + 1)
                if e is None:
                    return None
                out = e if isinstance(out, ir.Lit) else ir.Binary(ir.BOOL, loc, "and", out, e)
            return out
        if isinstance(t, ir.TList) and isinstance(t.elem, ir.TRecord) and not self.spec:
            s = self.fe.structs.get(t.elem.name)
            return ir.Binary(ir.BOOL, loc, "eq", a, b) if s is not None and s.eq == "derive" else None  # (a tagged record's unused fields may differ)
        if isinstance(t, ir.TList) and isinstance(t.elem, (ir.TClass, ir.TOpaque)):
            return None if not self.spec else ir.Binary(ir.BOOL, loc, "eq", a, b)
        if isinstance(t, ir.TDict) and isinstance(t.val, (ir.TClass, ir.TOpaque, ir.TRecord)):
            return None if not self.spec else ir.Binary(ir.BOOL, loc, "eq", a, b)
        if isinstance(t, ir.TOpaque):
            return None if not self.spec else ir.Binary(ir.BOOL, loc, "eq", a, b)
        return ir.Binary(ir.BOOL, loc, "eq", a, b)


def _rename(e: ir.Expr, old: str, new: str) -> ir.Expr:
    """Rename a bound variable (the quantified index) throughout an expression."""
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


def _tag_ranges(v: ir.Expr, loc: ir.Loc, depth: int = 0) -> list[ir.Stmt]:
    """A value of a data-carrying enum is one of its variants (and so are
    such values held in its fields)."""
    t = v.ty
    if not isinstance(t, ir.TRecord) or depth > 3:
        return []
    out: list[ir.Stmt] = []
    for f, ft in t.fields:
        if f == "tag" and isinstance(ft, ir.TEnum):
            tag = ir.Field(ft, loc, v, "tag")
            out.append(ir.ExprStmt(loc, ir.Builtin(ir.INT, loc, "in_range", (tag, ir.Lit(ir.INT, loc, 0), ir.Lit(ir.INT, loc, len(ft.members) - 1)))))
        elif isinstance(ft, ir.TRecord):
            out += _tag_ranges(ir.Field(ft, loc, v, f), loc, depth + 1)
    return out


def _subst(e: ir.Expr, name: str, by: ir.Expr) -> ir.Expr:
    """Replace the variable ``name`` by the expression ``by`` (not where a
    quantifier or comprehension binds its own ``name``)."""
    if isinstance(e, ir.Var) and e.name == name:
        return by
    if isinstance(e, ir.Quant) and name in (e.elem, e.idx):
        return dataclasses.replace(e, lo=_subst(e.lo, name, by), hi=_subst(e.hi, name, by), seq=_subst(e.seq, name, by) if e.seq is not None else None)
    if isinstance(e, ir.Builtin) and e.name == "comp" and len(e.args) > 1 and isinstance(e.args[1], ir.Lit) and e.args[1].value == name:
        return dataclasses.replace(e, args=(_subst(e.args[0], name, by), *e.args[1:]))
    changes = {}
    for f in dataclasses.fields(e):
        v = getattr(e, f.name)
        if isinstance(v, ir.Expr):
            changes[f.name] = _subst(v, name, by)
        elif isinstance(v, tuple) and v and all(isinstance(x, ir.Expr) for x in v):
            changes[f.name] = tuple(_subst(x, name, by) for x in v)
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


def lower_rust(path: str, source: str, abs_path: str | None = None, root: str | None = None) -> ir.Module:
    """Lower one file. Its crate (found from ``abs_path``) gives the types,
    traits and functions other files declare; calls into them are imports."""
    return RustFrontend(path, source, abs_path, root).run()
