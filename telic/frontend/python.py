"""Python -> telic IR.

Supported: top-level functions over ``int``, ``float``, ``bool``, ``str``,
``list[T]`` and frozen dataclass records; ``if``/``while``/``for`` over
``range``/lists/``enumerate``; ``break``/``continue``; ``assert``; ``raise``;
calls to other functions in the program; the numeric builtins. Everything
else is reported as unsupported with a reason and a line -- telic never
guesses at semantics it does not model.
"""

from __future__ import annotations

import ast
import dataclasses
import sys
import io
import os
import tokenize
from fractions import Fraction
from pathlib import Path

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
from .python_code import code_graph
from .python_rewrites import rewrites
from ..lifecycle import build as build_lifecycle

PY_ASSUMPTIONS = [
    "a float argument annotated float is a binary64 value",
    "distinct list arguments do not alias each other",
    "print() and logging calls have no effect on program state",
]

IGNORED_CALLS = {"print"}
EXCEPTION_BASES = {"Exception", "BaseException", "ValueError", "KeyError", "RuntimeError", "TypeError", "LookupError", "ArithmeticError", "PermissionError", "HTTPException"}
IGNORED_ATTR_CALLS = {"debug", "info", "warning", "error", "exception", "critical"}


def _has_mutable_child(ty: ir.Type) -> bool:
    if isinstance(ty, (ir.TList, ir.TDict)):
        return True
    if isinstance(ty, ir.TOption):
        return _has_mutable_child(ty.inner)
    if isinstance(ty, ir.TRecord):
        return any(_has_mutable_child(field) for _, field in ty.fields)
    return False


class LowerError(Exception):
    def __init__(self, msg: str, node: ast.AST | None = None, line: int | None = None):
        super().__init__(msg)
        self.line = line if line is not None else getattr(node, "lineno", 0)


def _loc(node: ast.AST, line_offset: int = 0, col_offset: int = 0) -> ir.Loc:
    line = getattr(node, "lineno", 0)
    col = getattr(node, "col_offset", 0)
    end_col = getattr(node, "end_col_offset", col) or col
    end_line = getattr(node, "end_lineno", line)
    if line_offset:
        if line == 1:
            col += col_offset
        if end_line == 1:
            end_col += col_offset
        line += line_offset - 1
        end_line += line_offset - 1
    if end_line != line:
        end_col = 0
    return ir.Loc(line, col, end_col)


# ---------------------------------------------------------------------------


class PythonFrontend:
    def __init__(self, path: str, source: str):
        self.path = path
        self.source = source
        self.lines = source.splitlines()
        self.module = ir.Module(path=path, language="python", source=source)
        self.module.assumptions = list(PY_ASSUMPTIONS)
        self.contract_lines: list[ContractLine] = []
        self.signatures: dict[str, tuple[list[ir.Param], ir.Type]] = {}
        self.defaults: dict[str, dict[str, ast.expr]] = {}
        self.kwonly: dict[str, set[str]] = {}
        self.bound: set[str] = set()
        self.class_names: set[str] = set()
        self.properties: set[str] = set()  # 'C.name' for @property methods
        self.dataclass_defaults: dict[str, dict[str, ast.expr]] = {}
        self.dataclasses: set[str] = set()
        self.custom_eq: dict[str, bool] = {}
        self.custom_bool: dict[str, bool] = {}
        self.enums: dict[str, list[str]] = {}
        self.enum_types: dict[str, ir.TEnum] = {}
        self.constants: dict[str, ast.expr] = {}  # module-level literals never rebound
        self.modules: set[str] = set()  # names bound by 'import'
        self.ignored_classes: set[str] = set()
        self.wrapped: dict[str, str] = {}  # key -> an unknown decorator: calls go through a wrapper
        self.setters: set[str] = set()
        self.classmethods: set[str] = set()
        self.varargs: dict[str, tuple[str | None, str | None]] = {}
        self.foreign_classes: dict[str, ir.ClassDecl] = {}
        self.linked_classes: dict[str, "PythonFrontend"] = {}
        self.linked_functions: dict[str, tuple["PythonFrontend", str]] = {}
        self.nested_imports: dict[int, str] = {}  # id of an ImportFrom inside a function -> the checked module it names
        self.module_aliases: dict[str, "PythonFrontend"] = {}
        self.imports: list[tuple[str, int, str, str | None]] = []  # (module, level, name, asname)
        self.class_bases: dict[str, list[str]] = {}  # checked bases, also of foreign ancestors
        self.pydantic: set[str] = set()
        self._own: dict[str, tuple[bool, bool, dict[str, ast.expr], bool]] = {}  # cls -> (dataclass, has __init__, defaults, pydantic)
        self._flat: set[str] = set()
        self.generators: set[str] = set()  # functions containing yield: their body runs later, driven by the consumer
        self.handed: list[tuple[str, ir.Loc, str]] = []  # (function, where, by whom): a checked function used as a value
        # every checked class in the project (name -> owner), for types that
        # reach a module through fields without being imported there
        self.project: dict[str, "PythonFrontend"] = {}
        self.peers: list["PythonFrontend"] = [self]  # every module checked with this one

    def import_class_info(self, other: "PythonFrontend", cname: str) -> None:
        """Make a class from another checked module usable here: its
        constructor, methods and what calling them means."""
        for key, sig in other.signatures.items():
            if key.startswith(cname + "."):
                self.signatures[key] = sig
                for attr in ("defaults", "kwonly", "varargs", "wrapped"):
                    src = getattr(other, attr)
                    if key in src:
                        getattr(self, attr)[key] = src[key]
        prefix = cname + "."
        for attr in ("properties", "setters", "classmethods"):
            getattr(self, attr).update(k for k in getattr(other, attr) if k.startswith(prefix))
        for attr in ("custom_eq", "custom_bool"):
            if cname in getattr(other, attr):
                getattr(self, attr)[cname] = getattr(other, attr)[cname]
        if cname in other.dataclasses:
            self.dataclasses.add(cname)
        if cname in other.dataclass_defaults:
            self.dataclass_defaults[cname] = other.dataclass_defaults[cname]

    def structure_fields(self, text: str) -> frozenset[str] | None:
        """The fields a value annotated ``text`` can be read through when every
        class it can be is a frozen dataclass or NamedTuple: set once, to
        values that existed before the object was built. None otherwise."""
        try:
            node = ast.parse(text, mode="eval").body
        except SyntaxError:
            return None
        return self._structure(node, frozenset())

    def _structure(self, n: ast.expr, seen: frozenset[str]) -> frozenset[str] | None:
        if isinstance(n, ast.Constant) and n.value is None:
            return frozenset()
        if isinstance(n, ast.Constant) and isinstance(n.value, str):
            try:
                return self._structure(ast.parse(n.value, mode="eval").body, seen)
            except SyntaxError:
                return None
        if isinstance(n, ast.BinOp) and isinstance(n.op, ast.BitOr):
            parts: list[ast.expr] = [n.left, n.right]
        elif isinstance(n, ast.Subscript) and _decorator_name(n.value) in ("Union", "Optional"):
            parts = list(n.slice.elts) if isinstance(n.slice, ast.Tuple) else [n.slice]
        elif isinstance(n, ast.Attribute) and isinstance(n.value, ast.Name) and n.value.id in self.module_aliases:
            return self.module_aliases[n.value.id]._structure(ast.Name(n.attr), frozenset())
        elif isinstance(n, ast.Name):
            if n.id in seen:
                return frozenset()
            structs, aliases = self._structures()
            if n.id in structs:
                return structs[n.id]
            if n.id in aliases:
                return self._structure(aliases[n.id], seen | {n.id})
            if n.id in self.linked_functions:
                other, name = self.linked_functions[n.id]
                return other._structure(ast.Name(name), frozenset())
            return None
        else:
            return None
        out: frozenset[str] = frozenset()
        for x in parts:
            f = self._structure(x, seen)
            if f is None:
                return None
            out |= f
        return out

    def _structures(self) -> tuple[dict[str, frozenset[str]], dict[str, ast.expr]]:
        """Module-level frozen dataclasses and NamedTuples (name -> the fields
        an instance of it or of a subclass has) and type aliases. A class that
        runs code while it is built or read (``__post_init__``,
        ``__setattr__``, ...), or has a subclass here that is not one of
        them, does not count."""
        if hasattr(self, "_structs"):
            return self._structs
        body = self.tree.body if hasattr(self, "tree") else []
        aliases: dict[str, ast.expr] = {}
        for node in body:
            if isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
                aliases[node.targets[0].id] = node.value
            elif isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name) and node.value is not None and _decorator_name(node.annotation) == "TypeAlias":
                aliases[node.target.id] = node.value
            elif sys.version_info >= (3, 12) and isinstance(node, ast.TypeAlias):
                aliases[node.name.id] = node.value
        hooks = {"__init__", "__new__", "__post_init__", "__setattr__", "__getattr__", "__getattribute__", "__init_subclass__", "__set_name__", "__class_getitem__"}
        by_name = {c.name: c for c in body if isinstance(c, ast.ClassDef)}
        done: dict[str, tuple[frozenset[str], frozenset[str]] | None] = {}

        def attrs_of(name: str) -> tuple[frozenset[str], frozenset[str]] | None:
            """(fields, every other attribute), inherited ones included."""
            if name in done:
                return done[name]
            done[name] = None
            c = by_name[name]
            frozen = any(isinstance(d, ast.Call) and _decorator_name(d) == "dataclass" and any(k.arg == "frozen" and isinstance(k.value, ast.Constant) and k.value.value is True for k in d.keywords) for d in c.decorator_list)
            named_tuple = any(_decorator_name(b) == "NamedTuple" for b in c.bases)
            inherits = any(_decorator_name(b) in by_name for b in c.bases)
            if not (frozen or named_tuple or inherits) or c.keywords:
                return None
            if any(_decorator_name(d) not in ("dataclass", "final") for d in c.decorator_list):
                return None
            own: set[str] = set()
            other: set[str] = set()
            for st in c.body:
                if isinstance(st, ast.AnnAssign) and isinstance(st.target, ast.Name):
                    (other if "ClassVar" in ast.unparse(st.annotation) or not (frozen or named_tuple) else own).add(st.target.id)
                elif isinstance(st, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    if st.name in hooks:
                        return None
                    other.add(st.name)
                elif isinstance(st, ast.Assign):
                    other.update(t.id for t in st.targets if isinstance(t, ast.Name))
                elif isinstance(st, ast.ClassDef):
                    other.add(st.name)
            for b in c.bases:
                bn = _decorator_name(b)
                if bn in ("NamedTuple", "Generic", "object"):
                    continue
                if bn not in by_name or not isinstance(b, (ast.Name, ast.Subscript)):
                    return None
                inherited = attrs_of(bn)
                if inherited is None:
                    return None
                own |= inherited[0]
                other |= inherited[1]
            done[name] = (frozenset(own), frozenset(other))
            return done[name]

        subs: dict[str, set[str]] = {n: {n} for n in by_name}
        for n, c in by_name.items():
            for b in c.bases:
                if _decorator_name(b) in subs:
                    subs[_decorator_name(b)].add(n)
        changed = True
        while changed:  # every descendant, not only direct subclasses
            changed = False
            for n in subs:
                more = set().union(*(subs[d] for d in subs[n]))
                if more - subs[n]:
                    subs[n] |= more
                    changed = True
        structs: dict[str, frozenset[str]] = {}
        reopened = self._reopened(subs)
        if reopened is None:
            self._structs = (structs, aliases)
            return self._structs
        for n in by_name:
            if subs[n] & reopened:
                continue
            got = [attrs_of(d) for d in sorted(subs[n])]
            if all(g is not None for g in got):
                fields = frozenset().union(*(g[0] for g in got if g))
                others = frozenset().union(*(g[1] for g in got if g))
                structs[n] = fields - others
        self._structs = (structs, aliases)
        return self._structs

    def _reopened(self, subs: dict[str, set[str]]) -> set[str] | None:
        """Classes of this module (keys of ``subs``, each to its subclasses)
        whose objects checked code may rewrite or whose subclasses telic does
        not model (see ``python_rewrites``): the classes a site names and,
        for a rewrite, their subclasses. None when a site could reach any
        class."""
        written = {c.name: {_decorator_name(b) for b in c.bases} for c in getattr(self, "tree", ast.Module([], [])).body if isinstance(c, ast.ClassDef)}
        bases: dict[str, set[str]] = {n: set(written.get(n, ())) for n in subs}
        for n, below in subs.items():
            for d in below - {n}:
                bases[d] |= {n} | written.get(n, set())
        out: set[str] = set()
        for fe in self.peers:
            tree = getattr(fe, "tree", None)
            if tree is None:
                continue
            for kind, names in rewrites(tree, set(self.project), fe is not self):
                if names is None:
                    return None
                if kind == "sub":
                    out |= names & set(subs)
                else:
                    out |= {n for n in subs if names & ({n} | bases[n])}
        return out

    def import_function(self, other: "PythonFrontend", name: str) -> None:
        self.signatures[name] = other.signatures[name]
        for attr in ("defaults", "kwonly", "varargs", "wrapped"):
            src = getattr(other, attr)
            if name in src:
                getattr(self, attr)[name] = src[name]
        self.module.imports[name] = (other.path, name)

    @property
    def classes(self) -> dict[str, ir.ClassDecl]:
        """Classes usable here: this module's and those imported from other
        checked modules."""
        if not self.foreign_classes and not self.project:
            return self.module.classes
        reach = {n: o.module.classes[n] for n, o in self.project.items() if n in o.module.classes}
        return {**reach, **self.foreign_classes, **self.module.classes}

    # -- entry --------------------------------------------------------------

    def run(self) -> ir.Module:
        for _ in self.stages():
            pass
        return self.module

    def stages(self):
        """Lowering in three steps, so a project can link imports between
        them: yields "names" once classes, enums and records are known, and
        "signatures" once fields and signatures are."""
        try:
            tree = ast.parse(self.source, filename=self.path)
        except SyntaxError as e:
            v = f"{sys.version_info.major}.{sys.version_info.minor}"
            self.module.problems.append((f"syntax error: {e.msg} (telic parses with Python {v}; newer syntax needs telic running on a newer Python)", ir.Loc(e.lineno or 0)))
            return
        try:
            self.contract_lines = parse_comment_lines(self._comments(), "#")
        except ContractSyntaxError as e:
            self.module.problems.append((str(e), ir.Loc(e.line, e.col)))
            return
        self.tree = tree

        # Names bound at module level shadow builtins of the same name.
        assigned: dict[str, int] = {}
        for node in tree.body:
            if isinstance(node, (ast.Import, ast.ImportFrom)):
                for a in node.names:
                    self.bound.add((a.asname or a.name).split(".")[0])
                    if isinstance(node, ast.Import):
                        self.modules.add((a.asname or a.name).split(".")[0])
                        self.imports.append((a.name, 0, "", a.asname))
                    else:
                        self.imports.append((node.module or "", node.level, a.name, a.asname))
            if isinstance(node, (ast.Assign, ast.AnnAssign)):
                targets = node.targets if isinstance(node, ast.Assign) else [node.target]
                for t in targets:
                    if isinstance(t, ast.Name):
                        assigned[t.id] = assigned.get(t.id, 0) + 1
                        if node.value is not None and _simple_default(node.value):
                            self.constants[t.id] = node.value
        rebound = {n for f in ast.walk(tree) if isinstance(f, (ast.Global, ast.Nonlocal)) for n in f.names}
        for name in list(self.constants):
            if assigned.get(name, 0) != 1 or name in rebound:
                del self.constants[name]
        for node in tree.body:
            if isinstance(node, ast.ClassDef):
                self.bound.add(node.name)
                bases = {_decorator_name(b) for b in node.bases}
                if bases & {"Enum", "IntEnum", "StrEnum", "Flag", "IntFlag"}:
                    members, values = [], []
                    for st in node.body:
                        if isinstance(st, ast.Assign) and len(st.targets) == 1 and isinstance(st.targets[0], ast.Name) and not st.targets[0].id.startswith("_"):
                            members.append(st.targets[0].id)
                            values.append(st.value.value if isinstance(st.value, ast.Constant) else None)
                    mixed = bases & {"IntEnum", "StrEnum", "str", "int", "Flag", "IntFlag"}
                    if members and not mixed:
                        self.enums[node.name] = list(members)
                        self.enum_types[node.name] = ir.TEnum(node.name, tuple(members), tuple(values))
                    else:
                        self.ignored_classes.add(node.name)  # enum with behaviour: its values are opaque
                elif bases & EXCEPTION_BASES or (node.name.endswith(("Error", "Exception")) and bases and not bases & {"BaseModel"}):
                    self.ignored_classes.add(node.name)  # exceptions: only ever raised
            elif isinstance(node, (ast.Assign, ast.AnnAssign, ast.AugAssign)):
                targets = node.targets if isinstance(node, ast.Assign) else [node.target]
                for t in targets:
                    for n in ast.walk(t):
                        if isinstance(n, ast.Name):
                            self.bound.add(n.id)
            elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                self.bound.add(node.name)
        # Records and classes first, then signatures, then bodies: calls may be forward.
        classes: list[ast.ClassDef] = []
        for node in tree.body:
            if isinstance(node, ast.ClassDef) and node.name not in self.enums and node.name not in self.ignored_classes:
                self._record(node)
                if node.name not in self.module.records:
                    self.class_names.add(node.name)
                    classes.append(node)
        yield "names"
        for node in classes:
            try:
                self._class_fields(node)
            except NotModelled as e:
                self.class_names.discard(node.name)
                self.module.notes.append((f"class {node.name}: {e}", ir.Loc(e.line or node.lineno)))
            except LowerError as e:
                self.class_names.discard(node.name)
                self.module.problems.append((f"class {node.name}: {e}", ir.Loc(e.line or node.lineno)))
        yield "fields"
        for node in classes:
            if node.name in self.module.classes:
                self.flatten(node.name)
        classes = [c for c in classes if c.name in self.module.classes]
        methods: list[tuple[ast.FunctionDef, str]] = []
        for node in tree.body:
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                try:
                    self.signatures[node.name] = self._signature(node)
                except LowerError as e:
                    self.module.problems.append((f"{node.name}: {e}", ir.Loc(e.line)))
        for node in tree.body:
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and node.name in self.signatures and _is_generator(node):
                self.generators.add(node.name)
        for node in tree.body:
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and node.name in self.signatures:
                unknown = {_decorator_name(d) for d in node.decorator_list} - TRANSPARENT_DECORATORS
                if unknown and not all(_route_decorator(d) for d in node.decorator_list if _decorator_name(d) in unknown):
                    self.wrapped[node.name] = sorted(unknown)[0]
                elif node.name in self.generators:
                    self.wrapped[node.name] = "generator"  # calling it only creates the generator
        for c in classes:
            for sub in c.body:
                if not isinstance(sub, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    continue
                decos = {_decorator_name(d) for d in sub.decorator_list}
                key = f"{c.name}.{sub.name}"
                if "setter" in decos:
                    key += ".setter"
                    self.setters.add(f"{c.name}.{sub.name}")
                try:
                    self.signatures[key] = self._signature(sub, c.name, static="staticmethod" in decos, clsmethod="classmethod" in decos)
                    if decos & {"property", "cached_property"}:
                        self.properties.add(key)
                    if "classmethod" in decos:
                        self.classmethods.add(key)
                    unknown = decos - TRANSPARENT_DECORATORS
                    if unknown:
                        self.wrapped[key] = sorted(unknown)[0]
                    if _is_generator(sub):
                        self.generators.add(key)
                        self.wrapped.setdefault(key, "generator")
                    methods.append((sub, c.name, key))
                except LowerError as e:
                    self.module.problems.append((f"{key}: {e}", ir.Loc(e.line or sub.lineno)))
        yield "signatures"
        for c in classes:
            self._class_invariants(c)
        for node in tree.body:
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and node.name in self.signatures:
                fn = self._lower_safely(node, None, node.name)
                self.module.functions[fn.name] = fn
        for node, cname, key in methods:
            fn = self._lower_safely(node, cname, key)
            self.module.functions[fn.name] = fn
        imports = {local: (other.path, name) for local, (other, name) in self.linked_functions.items()}
        imports.update({f"{alias}.*": (other.path, "*") for alias, other in self.module_aliases.items()})
        self.module.code = code_graph(tree, set(self.module.functions) | set(self.signatures), set(self.wrapped), TRANSPARENT_DECORATORS | {"setter"}, imports, set(self.module_aliases), self.nested_imports)
        handed_on(self.module, self.handed)

        # Module-level aim declarations (anything not consumed by a function).
        for cl in self.contract_lines:
            if cl.consumed:
                continue
            if cl.keyword == "aim":
                try:
                    ids, text = parse_aim_directive(cl)
                except ContractSyntaxError as e:
                    self.module.problems.append((str(e), ir.Loc(e.line, e.col)))
                    cl.consumed = True
                    continue
                if text is None:
                    self.module.problems.append(
                        ("'@aim ID' outside a function links nothing; declare with '@aim ID: sentence'", ir.Loc(cl.line, cl.col))
                    )
                else:
                    self.module.aims.append(ir.AimDecl(ids[0], text, ir.Loc(cl.line, cl.col)))
                cl.consumed = True
        spans: list[tuple[int, int, str]] = []
        for node in ast.walk(tree):
            if isinstance(node, ast.ClassDef):
                for sub in node.body:
                    if isinstance(sub, (ast.FunctionDef, ast.AsyncFunctionDef)) and f"{node.name}.{sub.name}" not in self.signatures:
                        spans.append((min([sub.lineno] + [d.lineno for d in sub.decorator_list]) - 3, sub.end_lineno or sub.lineno, f"'{node.name}.{sub.name}' is not checked (see the problem reported for it or its class)"))
            elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and node not in tree.body and not any(node is m for m, _, _ in methods):
                spans.append((node.lineno - 3, node.end_lineno or node.lineno, f"nested functions are not checked yet ('{node.name}')"))
        reported: set[str] = set()
        for cl in self.contract_lines:
            if not cl.consumed:
                why = next((msg for lo, hi, msg in spans if lo <= cl.line <= hi), None)
                if why is not None:
                    if why not in reported:
                        self.module.problems.append((why, ir.Loc(cl.line, cl.col)))
                        reported.add(why)
                    continue
                self.module.problems.append(
                    (f"stray '@{cl.keyword}' is not attached to any function, loop, or statement", ir.Loc(cl.line, cl.col))
                )

    def _comments(self) -> list[tuple[int, int, str]]:
        out = []
        toks = tokenize.generate_tokens(io.StringIO(self.source).readline)
        try:
            for tok in toks:
                if tok.type == tokenize.COMMENT:
                    out.append((tok.start[0], tok.start[1], tok.string))
        except tokenize.TokenError:
            pass
        return out

    # -- declarations -------------------------------------------------------

    def _record(self, node: ast.ClassDef) -> None:
        def frozen_dataclass(d: ast.expr) -> bool:
            if not isinstance(d, ast.Call):
                return False
            f = d.func
            named = (isinstance(f, ast.Name) and f.id == "dataclass") or (isinstance(f, ast.Attribute) and f.attr == "dataclass")
            return named and any(k.arg == "frozen" and isinstance(k.value, ast.Constant) and k.value.value is True for k in d.keywords)

        is_dc = any(frozen_dataclass(d) for d in node.decorator_list)
        is_nt = any(isinstance(b, ast.Name) and b.id == "NamedTuple" for b in node.bases)
        if not (is_dc or is_nt):
            return  # mutable classes are not records
        if any(isinstance(st, (ast.FunctionDef, ast.AsyncFunctionDef)) and st.name.startswith("__") for st in node.body):
            return  # custom construction (__post_init__, __init__, ...) is not modelled
        fields: list[tuple[str, ir.Type]] = []
        for stmt in node.body:
            if isinstance(stmt, ast.AnnAssign) and isinstance(stmt.target, ast.Name):
                try:
                    t = self.type_of_annotation(stmt.annotation)
                except LowerError:
                    return
                if isinstance(t, ir.TList):
                    return  # records hold scalars / records only
                fields.append((stmt.target.id, t))
        self.module.records[node.name] = ir.TRecord(node.name, tuple(fields))

    def _class_fields(self, node: ast.ClassDef) -> None:
        """Fields of a mutable class: class-level annotations (dataclass
        style) plus 'self.x = ...' assignments in __init__."""
        bases = [_decorator_name(b) for b in node.bases]
        model_base = bool(set(bases) & MODEL_BASES)  # pydantic: a validated dataclass
        checked = [b for b in bases if b in self.class_names and b != node.name]
        library = [b for b in bases if b not in checked and b not in MODEL_BASES and b not in NEUTRAL_BASES]
        if library:
            raise NotModelled(f"subclass of {library[0]}, which telic does not check: its instances are treated as library values", node)
        if node.keywords and not (model_base or checked):
            raise NotModelled("class keywords (metaclass=...) are not modelled: its instances are treated as library values", node)
        self.class_bases[node.name] = checked
        decos = {_decorator_name(d) for d in node.decorator_list}
        if decos - {"dataclass"}:
            raise LowerError(f"class decorator @{sorted(decos - {'dataclass'})[0]} is not modelled", node)
        magic = {st.name for st in node.body if isinstance(st, (ast.FunctionDef, ast.AsyncFunctionDef))} & {"__setattr__", "__getattr__", "__getattribute__", "__delattr__", "__new__", "__init_subclass__", "__class_getitem__"}
        if magic:
            raise LowerError(f"{sorted(magic)[0]} changes what attribute access means; not modelled", node)
        if any(isinstance(st, ast.Assign) and any(isinstance(t, ast.Name) and t.id == "__slots__" for t in st.targets) for st in node.body):
            pass  # __slots__ only restricts attributes; fields are still fields
        fields: list[tuple[str, ir.Type]] = []
        defaults: dict[str, ast.expr] = {}
        for st in node.body:
            if isinstance(st, ast.AnnAssign) and isinstance(st.target, ast.Name):
                if isinstance(st.annotation, ast.Name) and st.annotation.id == "ClassVar" or (isinstance(st.annotation, ast.Subscript) and _decorator_name(st.annotation.value) == "ClassVar"):
                    continue
                fields.append((st.target.id, self.type_of_annotation(st.annotation)))
                if st.value is not None:
                    defaults[st.target.id] = st.value if _simple_default(st.value) else None  # type: ignore[assignment]
            elif isinstance(st, ast.Assign) and not (len(st.targets) == 1 and isinstance(st.targets[0], ast.Name) and st.targets[0].id in ("__slots__", "model_config", "Config")):
                raise LowerError("class attributes other than annotated fields are not modelled", st)
        init = next((st for st in node.body if isinstance(st, ast.FunctionDef) and st.name == "__init__"), None)
        methods = [init] if init is not None else []
        methods += [st for st in node.body if isinstance(st, (ast.FunctionDef, ast.AsyncFunctionDef)) and st is not init and st.args.args and not any(_decorator_name(d) == "staticmethod" for d in st.decorator_list)]
        known = {f for f, _ in fields}
        for meth in methods:
            ann = {a.arg: a.annotation for a in meth.args.args[1:]}
            me = meth.args.args[0].arg if meth.args.args else "self"
            for st in ast.walk(meth):
                tgt, tann, val = None, None, None
                if isinstance(st, ast.AnnAssign):
                    tgt, tann, val = st.target, st.annotation, st.value
                elif isinstance(st, ast.Assign) and len(st.targets) == 1:
                    tgt, val = st.targets[0], st.value
                if not (isinstance(tgt, ast.Attribute) and isinstance(tgt.value, ast.Name) and tgt.value.id == me):
                    continue
                if tgt.attr in known:
                    continue
                if tann is not None:
                    ty = self.type_of_annotation(tann)
                elif isinstance(val, ast.Name) and ann.get(val.id) is not None:
                    ty = self.type_of_annotation(ann[val.id])
                elif isinstance(val, ast.Constant) and type(val.value) in (int, float, str, bool):
                    ty = {int: ir.INT, float: ir.REAL, str: ir.STR, bool: ir.BOOL}[type(val.value)]
                elif isinstance(val, ast.UnaryOp) and isinstance(val.op, (ast.USub, ast.UAdd)) and isinstance(val.operand, ast.Constant) and type(val.operand.value) in (int, float):
                    ty = ir.INT if type(val.operand.value) is int else ir.REAL
                elif isinstance(val, ast.Attribute) and isinstance(val.value, ast.Name) and val.value.id in self.enum_types:
                    ty = self.enum_types[val.value.id]
                else:
                    ty = ir.TOpaque(f"field {tgt.attr}")  # annotate it to have it checked
                fields.append((tgt.attr, ty))
                known.add(tgt.attr)
        self.module.classes[node.name] = ir.ClassDecl(node.name, fields, [], ir.Loc(node.lineno, node.col_offset))
        dunders = {st.name for st in node.body if isinstance(st, (ast.FunctionDef, ast.AsyncFunctionDef))}
        self.custom_eq[node.name] = "__eq__" in dunders
        self.custom_bool[node.name] = bool(dunders & {"__bool__", "__len__"})
        self._own[node.name] = ("dataclass" in decos, init is not None, defaults, model_base)

    def flatten(self, cname: str) -> None:
        """Inherited fields (base fields first, as Python orders them), which
        class owns each field, and how instances are constructed."""
        if cname in self._flat:
            return
        self._flat.add(cname)
        decl = self.module.classes[cname]
        own_dc, own_init, own_defaults, pyd = self._own[cname]
        fields: list[tuple[str, ir.Type]] = []
        owner: dict[str, str] = {}
        base_defaults: dict[str, ast.expr] = {}
        dc_base = False
        for b in self.class_bases.get(cname, []):
            ofe = self if b in self.module.classes else self.linked_classes.get(b)
            if ofe is None or b not in ofe.module.classes:
                del self.module.classes[cname]
                self.class_names.discard(cname)
                self.module.notes.append((f"class {cname}: subclass of {b}, which telic could not model: its instances are treated as library values", decl.loc))
                return
            ofe.flatten(b)
            if b not in ofe.module.classes:  # dropped while flattening
                del self.module.classes[cname]
                self.class_names.discard(cname)
                self.module.notes.append((f"class {cname}: subclass of {b}, which telic could not model: its instances are treated as library values", decl.loc))
                return
            bdecl = ofe.module.classes[b]
            for f, t in bdecl.fields:
                if f not in owner:
                    fields.append((f, t))
                    owner[f] = bdecl.field_owner(f)
            pyd = pyd or b in ofe.pydantic
            dc_base = dc_base or b in ofe.dataclasses
            base_defaults.update(ofe.dataclass_defaults.get(b, {}))
            self.custom_eq[cname] = self.custom_eq.get(cname, False) or ofe.custom_eq.get(b, False)
            self.custom_bool[cname] = self.custom_bool.get(cname, False) or ofe.custom_bool.get(b, False)
        for f, t in decl.fields:
            if f in owner:
                fields = [(g, t if g == f else u) for g, u in fields]  # a redeclared field keeps its place
            else:
                fields.append((f, t))
                owner[f] = cname
        decl.fields = fields
        decl.owner = owner
        decl.bases = list(self.class_bases.get(cname, []))
        if pyd:
            self.pydantic.add(cname)
        if pyd or own_dc:
            self.dataclasses.add(cname)
            if not own_init:
                self.dataclass_defaults[cname] = {**base_defaults, **own_defaults}
        elif dc_base and not own_init:
            self.dataclasses.add(cname)
            if cname in self.dataclass_defaults or not any(owner[f] == cname for f, _ in fields):
                self.dataclass_defaults[cname] = dict(base_defaults)

    def mro(self, cls: str) -> list[str]:
        """Method resolution order over checked classes (left to right,
        depth first, each class once: C3 for the hierarchies telic models)."""
        out: list[str] = []

        def walk(c: str) -> None:
            if c in out:
                return
            out.append(c)
            bases = self.class_bases.get(c)
            if bases is None and c in self.project:
                bases = self.project[c].class_bases.get(c, [])
            for b in bases or []:
                walk(b)

        walk(cls)
        return out

    def library_derived(self, cls: str) -> bool:
        """Does ``cls`` get members from a library base (pydantic's BaseModel)?"""
        for c in self.mro(cls):
            owner = self if c in self.module.classes else self.project.get(c) or self.linked_classes.get(c)
            if owner is not None and c in owner.pydantic:
                return True
        return False

    def member(self, cls: str, attr: str) -> str:
        """The key of the method/property ``attr`` of ``cls``, inherited or its own."""
        for c in self.mro(cls):
            key = f"{c}.{attr}"
            if key in self.signatures or key in self.properties or key in self.setters:
                return key
            owner = self.project.get(c)
            if owner is not None and owner is not self and c not in self.module.classes and (key in owner.signatures or key in owner.properties):
                self.import_class_info(owner, c)  # a class reached through a field type
                return key
        return f"{cls}.{attr}"

    def _class_invariants(self, node: ast.ClassDef) -> None:
        decl = self.module.classes[node.name]
        methods = [(min([m.lineno] + [d.lineno for d in m.decorator_list]) - 1, m.end_lineno or m.lineno) for m in node.body if isinstance(m, (ast.FunctionDef, ast.AsyncFunctionDef))]
        lo, hi = node.lineno, node.end_lineno or node.lineno
        stub = _ClassScope(self, node.name)
        for cl in self.contract_lines:
            if cl.consumed or not (lo <= cl.line <= hi) or cl.keyword not in ("invariant", "lifecycle"):
                continue
            if any(a + 1 < cl.line <= b for a, b in methods):
                continue  # inside a method: a loop invariant
            cl.consumed = True
            try:
                if cl.keyword == "lifecycle":
                    decl.lifecycles.append(self._lifecycle(stub, cl))
                    continue
                c = stub.clause(cl, "invariant", tuple(cl.tags))
                _own_fields_only(c.expr, node.name, cl.line)
                decl.invariants.append(c)
            except (LowerError, ContractSyntaxError, LifecycleError) as e:
                self.module.problems.append((f"class {node.name}: {cl.keyword}: {e}", ir.Loc(cl.line, cl.col)))

    def _lifecycle(self, stub: "_ClassScope", cl: ContractLine) -> ir.Lifecycle:
        def lower(text: str, two_state: bool) -> ir.Expr:
            line = ContractLine(cl.keyword, text, cl.line, cl.col, cl.payload_col, cl.tags)
            return stub.clause(line, "lifecycle" if two_state else "lifecycle.new").expr

        loc = ir.Loc(cl.line, cl.payload_col, cl.payload_col + len(cl.payload) if "\n" not in cl.payload else 0)
        return build_lifecycle(cl.payload, loc, tuple(cl.tags), "python", lower)

    def _lower_safely(self, node: ast.FunctionDef, cname: str | None, key: str) -> ir.Function:
        #@ requires key in self.signatures
        """Lower one function; a bug in telic on one function leaves that
        function unchecked (with the reason) instead of stopping the run."""
        try:
            return FunctionLowerer(self, node, cname, key).lower() if cname else FunctionLowerer(self, node).lower()
        except Exception as e:  # noqa: BLE001 - reported on the function, never swallowed
            params, ret = self.signatures[key]
            fn = ir.Function(key, ir.Loc(node.lineno, node.col_offset), node.end_lineno or node.lineno, params, ret, source=ast.get_source_segment(self.source, node) or "")
            fn.unsupported.append((f"telic could not model this function ({type(e).__name__}: {e}); please report it", ir.Loc(node.lineno)))
            return fn

    def type_of_annotation(self, ann: ast.expr | None) -> ir.Type:
        if ann is None:
            raise LowerError("missing type annotation")
        if isinstance(ann, ast.Constant) and ann.value is None:
            return ir.NONE
        if isinstance(ann, ast.Constant) and isinstance(ann.value, str):
            return self.type_of_annotation(ast.parse(ann.value, mode="eval").body)
        if isinstance(ann, ast.Attribute):
            owner, name = self._annotation_origin(ann)
            if owner is not None:
                if name in owner.module.records:
                    return owner.module.records[name]
                if name in owner.enum_types:
                    return owner.enum_types[name]
                if name in owner.module.classes:
                    self.linked_classes.setdefault(name, owner)
                    return ir.TClass(name)
            return ir.TOpaque(ast.unparse(ann))  # e.g. datetime.date
        if isinstance(ann, ast.Name):
            simple = {"int": ir.INT, "float": ir.REAL, "bool": ir.BOOL, "str": ir.STR}
            if ann.id in simple:
                return simple[ann.id]
            if ann.id in self.module.records:
                return self.module.records[ann.id]
            if ann.id in self.class_names:
                return ir.TClass(ann.id)
            if ann.id in self.enum_types:
                return self.enum_types[ann.id]
            return ir.TOpaque(ann.id)  # Any, object, library types: unchecked
        if isinstance(ann, ast.BinOp) and isinstance(ann.op, ast.BitOr):
            parts = _union_parts(ann)
            return self._union([self.type_of_annotation(x) for x in parts], ann)
        if isinstance(ann, ast.Subscript):
            base = ann.value
            name = base.id if isinstance(base, ast.Name) else base.attr if isinstance(base, ast.Attribute) else None
            if name in {"list", "List", "Sequence"}:
                elem = self.type_of_annotation(ann.slice)
                if isinstance(elem, (ir.TList, ir.TDict)):
                    return ir.TOpaque(ast.unparse(ann))  # nested containers: unchecked
                return ir.TList(elem)
            if name == "Optional":
                return self._union([self.type_of_annotation(ann.slice), ir.NONE], ann)
            if name == "Union":
                elts = ann.slice.elts if isinstance(ann.slice, ast.Tuple) else [ann.slice]
                return self._union([self.type_of_annotation(x) for x in elts], ann)
            if name in {"dict", "Dict", "Mapping", "MutableMapping"}:
                if not (isinstance(ann.slice, ast.Tuple) and len(ann.slice.elts) == 2):
                    raise LowerError("dict types need a key and a value type", ann)
                k = self.type_of_annotation(ann.slice.elts[0])
                v = self.type_of_annotation(ann.slice.elts[1])
                if not isinstance(k, (ir.TInt, ir.TStr, ir.TBool)) or isinstance(v, (ir.TList, ir.TDict, ir.TOption)):
                    return ir.TOpaque(ast.unparse(ann))
                return ir.TDict(k, v)
            if name in {"tuple", "Tuple"} and isinstance(ann.slice, ast.Tuple):
                if any(isinstance(x, ast.Constant) and x.value is Ellipsis for x in ann.slice.elts):
                    return ir.TOpaque(ast.unparse(ann))
                fields = tuple((f"_{i}", self.type_of_annotation(x)) for i, x in enumerate(ann.slice.elts))
                if any(_has_mutable_child(t) for _, t in fields):
                    raise LowerError("tuples containing mutable containers need identity-preserving product storage", ann)
                return ir.TRecord("tuple", fields)
        return ir.TOpaque(ast.unparse(ann))

    def _annotation_origin(self, ann: ast.Attribute) -> tuple["PythonFrontend | None", str]:
        """Resolve a qualified annotation through a checked module import."""
        parts: list[str] = []
        node: ast.expr = ann
        while isinstance(node, ast.Attribute):
            parts.append(node.attr)
            node = node.value
        if not isinstance(node, ast.Name):
            return None, ann.attr
        parts.append(node.id)
        parts.reverse()
        owner = self.module_aliases.get(parts[0])
        if owner is None:
            return None, parts[-1]
        for part in parts[1:-1]:
            owner = owner.module_aliases.get(part)
            if owner is None:
                return None, parts[-1]
        return owner, parts[-1]

    def _union(self, ts: list[ir.Type], node: ast.AST) -> ir.Type:
        rest = [t for t in ts if t != ir.NONE]
        if len(rest) != 1:
            if all(ir.is_numeric(t) for t in rest):
                rest = [ir.REAL]  # int | float: a number
            else:
                return ir.TOpaque(ast.unparse(node))  # a real union: unchecked
        if len(rest) == len(ts):
            return rest[0]
        inner = rest[0]
        if isinstance(inner, ir.TOpaque):
            return inner  # an unknown value may as well be None
        return ir.TOption(inner)

    def _signature(self, node: ast.FunctionDef, cls: str | None = None, static: bool = False, clsmethod: bool = False) -> tuple[list[ir.Param], ir.Type]:
        a = node.args
        params = []
        args = list(a.posonlyargs) + list(a.args) + list(a.kwonlyargs)
        for i, arg in enumerate(args):
            if i == 0 and clsmethod:
                params.append(ir.Param(arg.arg, ir.TOpaque("cls")))
                continue
            if i == 0 and cls is not None and not static:
                if arg.annotation is not None and not (isinstance(arg.annotation, ast.Name) and arg.annotation.id in (cls, "Self")):
                    raise LowerError(f"'{arg.arg}' of a method of {cls} must be the instance", arg)
                params.append(ir.Param(arg.arg, ir.TClass(cls)))
                continue
            if arg.annotation is None:
                params.append(ir.Param(arg.arg, ir.TOpaque("unannotated")))
                continue
            params.append(ir.Param(arg.arg, self.type_of_annotation(arg.annotation)))
        # *args / **kwargs: unchecked collections of whatever is passed.
        key = f"{cls}.{node.name}" if cls else node.name
        if any(_decorator_name(d) == "setter" for d in node.decorator_list):
            key += ".setter"
        if a.vararg is not None:
            params.append(ir.Param(a.vararg.arg, ir.TOpaque("*args")))
        if a.kwarg is not None:
            params.append(ir.Param(a.kwarg.arg, ir.TOpaque("**kwargs")))
        self.varargs[key] = (a.vararg.arg if a.vararg else None, a.kwarg.arg if a.kwarg else None)
        # Default values, by parameter name: substituted at call sites.
        defaults: dict[str, ast.expr] = {}
        pos = list(a.posonlyargs) + list(a.args)
        for arg, d in zip(pos[len(pos) - len(a.defaults):], a.defaults):
            defaults[arg.arg] = d
        for arg, d in zip(a.kwonlyargs, a.kw_defaults):
            if d is not None:
                defaults[arg.arg] = d
        for name, d in list(defaults.items()):
            if not _simple_default(d):
                if isinstance(d, (ast.List, ast.Dict, ast.Set)):
                    raise LowerError(f"default of '{name}' is a mutable {type(d).__name__.lower()} shared by every call; use None and create it inside", d)
                defaults[name] = None  # type: ignore[assignment]  # computed default: unknown value
        self.defaults[key] = defaults
        self.kwonly[key] = {x.arg for x in a.kwonlyargs}
        if node.returns is not None:
            ret = self.type_of_annotation(node.returns)
        elif any(isinstance(r, ast.Return) and r.value is not None for r in _own_nodes(node)):
            ret = ir.TOpaque("unannotated return")
        else:
            ret = ir.NONE
        return params, ret


# ---------------------------------------------------------------------------


class FunctionLowerer:
    def __init__(self, fe: PythonFrontend, node: ast.FunctionDef, cls: str | None = None, key: str | None = None, unit: str = ""):
        self.fe = fe
        self.node = node
        self.cls = cls
        self.key = key or (f"{cls}.{node.name}" if cls else node.name)
        self.unit = unit  # a lambda checked on its own: the comments round it belong to its enclosing function
        self.env: dict[str, ir.Type] = {}
        self.fn: ir.Function
        self.tmp = 0
        # contract lines inside this function's line span, not yet consumed
        self.local_contracts = [
            cl for cl in fe.contract_lines if node.lineno <= cl.line <= (node.end_lineno or node.lineno)
        ] if not unit else []
        self.current_aims: list[str] = []
        self.try_depth = 0
        self.stored_names = {n.id for n in ast.walk(node) if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Store)} | {a.arg for a in node.args.args + node.args.kwonlyargs}

    # -- contract comment association ------------------------------------

    def _header_contracts(self) -> list[ContractLine]:
        node = self.node
        first_line = min([node.lineno] + [d.lineno for d in node.decorator_list])
        above: list[ContractLine] = []
        # Walk upward over contiguous comment lines.
        ln = first_line - 1
        by_line = {l: cl for cl in self.fe.contract_lines for l in cl.raw_lines}
        while ln >= 1:
            text = self.fe.lines[ln - 1].strip()
            if not text.startswith("#"):
                break
            cl = by_line.get(ln)
            if cl is not None and cl.keyword in FUNCTION_KEYWORDS and not cl.consumed:
                if cl not in above:
                    above.append(cl)
            ln -= 1
        above.reverse()
        # Lines between the header and the first real body statement.
        body = node.body
        first = body[0]
        if isinstance(first, ast.Expr) and isinstance(first.value, ast.Constant) and isinstance(first.value.value, str):
            limit = body[1].lineno if len(body) > 1 else (node.end_lineno or node.lineno) + 1
        else:
            limit = first.lineno
        inside = [
            cl
            for cl in self.fe.contract_lines
            if node.lineno < cl.line < limit and cl.keyword in FUNCTION_KEYWORDS and not cl.consumed
        ]
        return above + inside

    def lower(self) -> ir.Function:
        node = self.node
        params, ret = self.fe.signatures[self.key]
        seg = ast.get_source_segment(self.fe.source, node) or ""
        self.fn = ir.Function(
            name=self.key,
            loc=ir.Loc(node.lineno, node.col_offset),
            end_line=node.end_lineno or node.lineno,
            params=params,
            ret=ret,
            source=seg,
            exported=not node.name.startswith("_") or node.name == "__init__",
            is_async=isinstance(node, ast.AsyncFunctionDef),
        )
        for p in params:
            self.env[p.name] = p.ty
        self.fn.unit = self.unit
        if self.unit:
            self.fn.exported = False

        for cl in self._header_contracts() if not self.unit else []:
            cl.consumed = True
            try:
                self._function_contract(cl)
            except (LowerError, ContractSyntaxError) as e:
                self.fn.unsupported.append((f"contract: {e}", ir.Loc(getattr(e, "line", cl.line))))

        body = node.body
        if body and isinstance(body[0], ast.Expr) and isinstance(body[0].value, ast.Constant) and isinstance(body[0].value.value, str):
            body = body[1:]
        self._scan_closures(node)
        if self.key in self.fe.generators:
            self.fn.ret = ir.NONE  # the body is checked as a procedure; values leave through yield
            self.fe.wrapped.setdefault(self.key, "generator")
        self.fn.body = list(self.block(body, node))
        self.fn.locals = dict(self.env)
        self.fn.escaped = {n for n in self.escaped if isinstance(self.env.get(n), (ir.TList, ir.TDict, ir.TClass, ir.TOpaque))}
        return self.fn

    def _scan_closures(self, node: ast.AST) -> None:
        """Nested functions and lambdas capture the enclosing locals. If one
        escapes (is used other than by calling it), code telic cannot see may
        run it later, so what it captures may change at any unchecked call."""
        self.closures: dict[str, list[str]] = {}
        self.escaped: set[str] = set()
        called: set[int] = set()
        for n in _own_nodes(node):
            if isinstance(n, ast.Call) and isinstance(n.func, ast.Name):
                called.add(id(n.func))
        nested = {n.name: n for n in _own_nodes(node) if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))}
        for name, fnode in nested.items():
            if any(isinstance(x, (ast.Nonlocal, ast.Global)) for x in ast.walk(fnode)):
                self.fn.unsupported.append((f"nested function '{name}' rebinds outer variables (nonlocal/global); not modelled", ir.Loc(fnode.lineno)))
            self.closures[name] = sorted({x.id for x in ast.walk(fnode) if isinstance(x, ast.Name) and isinstance(x.ctx, ast.Load)} & self.stored_names)
        for n in _own_nodes(node):
            if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Load) and n.id in self.closures and id(n) not in called:
                self.escaped.update(self.closures[n.id])
            if isinstance(n, ast.Lambda) and any(isinstance(x, ast.Call) for x in ast.walk(n.body)):
                self.escaped.update({x.id for x in ast.walk(n.body) if isinstance(x, ast.Name)} & self.stored_names)

    def _function_contract(self, cl: ContractLine) -> None:
        kw = cl.keyword
        if kw == "aim":
            ids, text = parse_aim_directive(cl)
            if text is not None:
                self.fe.module.aims.append(ir.AimDecl(ids[0], text, ir.Loc(cl.line, cl.col)))
            for i in ids:
                if i not in self.fn.aims:
                    self.fn.aims.append(i)
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
        tags = tuple(cl.tags) or tuple(self.current_aims)
        for t in tags:
            if t not in self.fn.aims:
                self.fn.aims.append(t)
        if kw == "requires":
            self.fn.requires.append(self.clause(cl, "requires", tags))
        elif kw == "ensures":
            self.fn.ensures.append(self.clause(cl, "ensures", tags, result_ty=self.fn.ret))
        elif kw == "decreases":
            self.fn.decreases = self.clause(cl, "decreases", tags, expect=ir.INT)
        elif kw == "raises":
            self.fn.raises.append(self.clause(cl, "raises", tags))

    def clause(
        self,
        cl: ContractLine,
        kind: str,
        tags: tuple[str, ...] = (),
        result_ty: ir.Type | None = None,
        expect: ir.Type = ir.BOOL,
    ) -> ir.Clause:
        text = cl.payload
        if not text:
            raise LowerError(f"empty '@{kind}'", line=cl.line)
        try:
            tree = ast.parse("(" + text + "\n)", mode="eval")
        except SyntaxError as e:
            raise LowerError(f"cannot parse '@{kind}' as a Python expression: {e.msg}", line=cl.line)
        el = ExprLowerer(self, spec=True, result_ty=result_ty, line_offset=cl.line, col_offset=cl.payload_col - 1)
        el.allow_old = (kind == "invariant" and not isinstance(self, _ClassScope)) or kind == "lifecycle"
        if expect == ir.BOOL:
            e = el.cond(tree.body)
        else:
            e = el.expr(tree.body)
        if expect == ir.BOOL:
            pass
        elif not isinstance(e.ty, ir.TInt):
            raise LowerError(f"'@{kind}' must be an int expression", line=cl.line)
        loc = ir.Loc(cl.line, cl.payload_col, cl.payload_col + len(text) if "\n" not in text else 0)
        return ir.Clause(kind, e, loc, " ".join(text.split()), tags)

    # -- statements ------------------------------------------------------

    def _block_end(self, stmts: list[ast.stmt]) -> int:
        #@ requires len(stmts) > 0
        """Last line (inclusive) that belongs to this block, including trailing comments."""
        last = stmts[-1].end_lineno or stmts[-1].lineno
        col = stmts[0].col_offset
        ln = last + 1
        end = last
        while ln <= len(self.fe.lines):
            raw = self.fe.lines[ln - 1]
            s = raw.strip()
            if s == "":
                ln += 1
                continue
            indent = len(raw) - len(raw.lstrip())
            if s.startswith("#") and indent >= col:
                end = ln
                ln += 1
                continue
            break
        return end

    def _stmt_contracts(self, lo: int, hi: int, col: int) -> list[ContractLine]:
        return [
            cl
            for cl in self.local_contracts
            if not cl.consumed and lo < cl.line <= hi and cl.col == col and cl.keyword in STATEMENT_KEYWORDS
        ]

    def block(self, stmts: list[ast.stmt], parent: ast.AST):
        if not stmts:
            return
        col = stmts[0].col_offset
        prev_end = getattr(parent, "lineno", 0)
        for s in stmts:
            for cl in self._stmt_contracts(prev_end, s.lineno - 1, col):
                yield from self._stmt_contract(cl)
            yield from self.stmt(s)
            prev_end = s.end_lineno or s.lineno
        for cl in self._stmt_contracts(prev_end, self._block_end(stmts), col):
            yield from self._stmt_contract(cl)

    def _stmt_contract(self, cl: ContractLine):
        cl.consumed = True
        try:
            c = self.clause(cl, cl.keyword, tuple(cl.tags))
        except LowerError as e:
            self.fn.unsupported.append((str(e), ir.Loc(e.line)))
            yield ir.Unsupported(ir.Loc(cl.line), str(e))
            return
        if cl.keyword == "assert":
            yield ir.AssertStmt(c.loc, c)
        else:
            yield ir.AssumeStmt(c.loc, c)

    def stmt(self, s: ast.stmt):
        try:
            yield from self._stmt(s)
        except LowerError as e:
            self.fn.unsupported.append((str(e), ir.Loc(e.line or s.lineno)))
            yield ir.Unsupported(ir.Loc(s.lineno), str(e))

    def expr(self, e: ast.expr, expect: ir.Type | None = None) -> ir.Expr:
        return ExprLowerer(self).expr(e, expect)

    def cond(self, e: ast.expr) -> ir.Expr:
        return ExprLowerer(self).cond(e)

    def declare(self, name: str, ty: ir.Type, node: ast.AST) -> None:
        old = self.env.get(name)
        if old is None:
            self.env[name] = ty
        elif old != ty:
            if isinstance(old, ir.TOpaque) or isinstance(ty, ir.TOpaque):
                return  # mixing with unchecked values: converted on assignment
            if isinstance(old, ir.TOption) and ty in (old.inner, ir.NONE):
                return
            if old == ir.NONE and not isinstance(ty, (ir.TList, ir.TDict, ir.TOption)):
                self.env[name] = ir.TOption(ty)  # 'x = None' then 'x = 5'
                return
            if isinstance(old, ir.TReal) and isinstance(ty, ir.TInt):
                return  # int value stored in a float variable: promoted on assignment
            if isinstance(old, ir.TList) and isinstance(ty, ir.TList) and ty.elem == ir.NONE:
                return
            if isinstance(old, ir.TDict) and isinstance(ty, ir.TDict) and ty.key == ir.NONE:
                return
            raise LowerError(f"variable '{name}' changes type from {old} to {ty}; telic requires one type per variable", node)

    def coerce(self, e: ir.Expr, ty: ir.Type) -> ir.Expr:
        up = self._upcast(e.ty, ty)
        if up is not None:
            return dataclasses.replace(e, ty=up)  # a subclass object where its base is expected
        if e.ty != ty and not isinstance(e.ty, ir.TOpaque) and not isinstance(ty, ir.TOpaque) and (_has_opaque(e.ty) or _has_opaque(ty)) and e.ty != ir.NONE:
            return ir.Builtin(ty, e.loc, "from_opaque", (e,))  # e.g. list[opaque] used as list[str]
        if isinstance(e.ty, ir.TOpaque) and not isinstance(ty, ir.TOpaque) and ty != ir.NONE:
            if isinstance(e, ir.Extern):
                return ir.Extern(ty, e.loc, e.name, e.args)  # its result is simply unknown at this type
            return ir.Builtin(ty, e.loc, "from_opaque", (e,))
        if isinstance(ty, ir.TOpaque) and not isinstance(e.ty, ir.TOpaque):
            if e.ty == ir.NONE:
                return ir.Builtin(ty, e.loc, "to_opaque", (ir.Lit(ir.INT, e.loc, 0),))
            return ir.Builtin(ty, e.loc, "to_opaque", (e,))
        if isinstance(ty, ir.TOption):
            if e.ty == ir.NONE:
                return ir.Lit(ty, e.loc, None)
            if not isinstance(e.ty, ir.TOption):
                return ir.Builtin(ty, e.loc, "some", (self.coerce(e, ty.inner),))
            return e
        if isinstance(e.ty, ir.TOption) and ty != ir.NONE:
            # Using an optional where a value is needed: prove it is not None.
            return self.coerce(ir.Builtin(e.ty.inner, e.loc, "unwrap", (e,)), ty)
        if isinstance(ty, ir.TDict) and isinstance(e, ir.Builtin) and e.name == "dict_lit" and not e.args:
            return ir.Builtin(ty, e.loc, "dict_lit", ())
        if isinstance(ty, ir.TReal) and isinstance(e.ty, ir.TInt):
            return ir.Builtin(ir.REAL, e.loc, "to_real", (e,))
        if isinstance(ty, ir.TList) and isinstance(e, ir.ListLit) and not e.elems:
            return ir.ListLit(ty, e.loc, ())
        return e

    def _upcast(self, have: ir.Type, want: ir.Type) -> ir.Type | None:
        if isinstance(have, ir.TOption) and isinstance(want, ir.TOption):
            inner = self._upcast(have.inner, want.inner)
            return ir.TOption(inner) if inner is not None else None
        if isinstance(have, ir.TClass) and isinstance(want, ir.TClass) and have != want and want.name in self.fe.mro(have.name):
            return want
        return None

    def fresh(self, base: str) -> str:
        self.tmp += 1
        return f"{base}${self.tmp}"

    def _loop_contracts(self, s: ast.stmt) -> list[ContractLine]:
        """Invariants directly above the loop header or first in its body."""
        out: list[ContractLine] = []
        by_line = {l: cl for cl in self.local_contracts for l in cl.raw_lines}
        ln = s.lineno - 1
        while ln >= 1:
            text = self.fe.lines[ln - 1].strip()
            if not text.startswith("#"):
                break
            cl = by_line.get(ln)
            if cl is not None and cl.keyword in LOOP_KEYWORDS and not cl.consumed and cl not in out:
                out.append(cl)
            ln -= 1
        out.reverse()
        body_first = s.body[0].lineno
        for cl in self.local_contracts:
            if s.lineno < cl.line < body_first and cl.keyword in LOOP_KEYWORDS and not cl.consumed and cl not in out:
                out.append(cl)
        for cl in out:
            cl.consumed = True
        return out

    def _stmt(self, s: ast.stmt):
        loc = ir.Loc(s.lineno, s.col_offset)
        if isinstance(s, ast.Pass):
            return
        if isinstance(s, ast.Expr):
            v = s.value
            if isinstance(v, ast.Constant) and isinstance(v.value, str):
                return  # docstring / bare string
            if isinstance(v, ast.Call):
                f = v.func
                logging_call = (isinstance(f, ast.Name) and f.id in IGNORED_CALLS and f.id not in self.fe.bound) or (
                    isinstance(f, ast.Attribute) and f.attr in IGNORED_ATTR_CALLS and isinstance(f.value, ast.Name) and f.value.id in {"logger", "logging", "log"}
                )
                if logging_call:
                    # Output is ignored, but its arguments are still evaluated.
                    yield from self._effects_of(list(v.args) + [k.value for k in v.keywords], loc)
                    return
                if isinstance(f, ast.Attribute) and f.attr == "append" and isinstance(f.value, ast.Attribute):
                    fld = self.expr(f.value)
                    if isinstance(fld, ir.Field) and isinstance(fld.obj.ty, ir.TClass) and isinstance(fld.ty, ir.TList):
                        if len(v.args) != 1:
                            raise LowerError("append takes one argument", s)
                        val = self.coerce(self.expr(v.args[0], fld.ty.elem), fld.ty.elem)
                        yield ir.FieldAssign(loc, fld.obj, fld.obj.ty.name, fld.name, ir.Builtin(fld.ty, loc, "list_append", (fld, val)))
                        return
                if isinstance(f, ast.Attribute) and f.attr == "append" and isinstance(f.value, ast.Name):
                    name = f.value.id
                    t = self.env.get(name)
                    if not isinstance(t, ir.TList):
                        raise LowerError(f"'{name}.append' needs '{name}' to be a list", s)
                    if len(v.args) != 1:
                        raise LowerError("append takes one argument", s)
                    val = self.expr(v.args[0])
                    if t.elem == ir.NONE:
                        t = ir.TList(val.ty)
                        self.env[name] = t
                    yield ir.Append(loc, name, self.coerce(val, t.elem))
                    return
                yield ir.ExprStmt(loc, self.expr(v))
                return
            if isinstance(v, ast.Await):
                yield ir.ExprStmt(loc, self.expr(v))
                return
            if isinstance(v, (ast.Yield, ast.YieldFrom)):
                # a generator hands control (and the value) to its consumer: unchecked code
                args = (self.expr(v.value),) if v.value is not None else ()
                yield ir.ExprStmt(loc, ir.Extern(ir.NONE, loc, "yield", args))
                return
            if isinstance(v, (ast.Constant, ast.Name)):
                return  # a bare name / Ellipsis: no effect
            raise LowerError("expression statement has no effect", s)
        if isinstance(s, ast.AnnAssign) and isinstance(s.target, ast.Attribute):
            if s.value is None:
                return
            yield from self._assign(s.target, s.value, s, loc)
            return
        if isinstance(s, ast.AnnAssign):
            if not isinstance(s.target, ast.Name):
                raise LowerError("annotated assignment target must be a name", s)
            ty = self.fe.type_of_annotation(s.annotation)
            self.declare(s.target.id, ty, s)
            if s.value is None:
                return
            val = self.coerce(self.expr(s.value, ty), ty)
            self._no_alias(s.target.id, val, s)
            self._check_assignable(s.target.id, ty, val, s)
            yield ir.Assign(loc, s.target.id, val)
            return
        if isinstance(s, ast.Assign):
            if len(s.targets) != 1:
                raise LowerError("chained assignment is not supported", s)
            yield from self._assign(s.targets[0], s.value, s, loc)
            return
        if isinstance(s, ast.AugAssign):
            opnode = ast.BinOp(left=_as_load(s.target), op=s.op, right=s.value)
            ast.copy_location(opnode, s)
            opnode.end_lineno, opnode.end_col_offset = s.end_lineno, s.end_col_offset
            yield from self._assign(s.target, opnode, s, loc)
            return
        if isinstance(s, ast.If):
            c = self.cond(s.test)
            then = tuple(self.block(s.body, s))
            orelse = tuple(self.block(s.orelse, s.orelse[0])) if s.orelse else ()
            yield ir.If(loc, c, then, orelse)
            return
        if isinstance(s, ast.While):
            if s.orelse:
                raise LowerError("while/else is not supported", s)
            contracts = self._loop_contracts(s)
            c = self.cond(s.test)
            body = tuple(self.block(s.body, s))
            for cl in contracts:
                if cl.keyword == "index":
                    raise LowerError("'@index' only applies to for-each loops", line=cl.line)
            invs, dec = self._lower_loop_clauses(contracts)
            yield ir.While(loc, c, invs, dec, body)
            return
        if isinstance(s, ast.For):
            yield from self._for(s, loc)
            return
        if isinstance(s, ast.Return):
            if s.value is None:
                yield ir.Return(loc, None)
            else:
                val = self.coerce(self.expr(s.value, self.fn.ret), self.fn.ret)
                if self.fn.ret == ir.NONE:
                    raise LowerError("function returns a value but is annotated '-> None' (or has no return annotation)", s)
                if val.ty != self.fn.ret:
                    raise LowerError(f"returns {val.ty} but is annotated to return {self.fn.ret}", s)
                if isinstance(val.ty, (ir.TList, ir.TDict)) and not fresh_list(val):
                    if not (isinstance(val, ir.Var) and all(p.name != val.name for p in self.fn.params)):
                        raise LowerError("returning a list or dict parameter, or a field holding one, (or an alias of one) would let the caller alias it; return a copy (xs[:])", s)
                yield ir.Return(loc, val)
            return
        if isinstance(s, ast.Break):
            yield ir.Break(loc)
            return
        if isinstance(s, ast.Continue):
            yield ir.Continue(loc)
            return
        if isinstance(s, ast.Assert):
            c = self.cond(s.test)
            text = ast.get_source_segment(self.fe.source, s.test) or ast.unparse(s.test)
            clause = ir.Clause("assert", c, _loc(s.test), " ".join(text.split()))
            if _about_unchecked(c):
                # an assert about configuration / library data is a runtime
                # check of the environment: it raises AssertionError, which
                # (like any raise) needs a contract to be a claim
                yield ir.If(loc, ir.Unary(ir.BOOL, loc, "not", c), (ir.Raise(loc, f"AssertionError: {clause.text}", caught=self.try_depth > 0),), ())
                return
            yield ir.AssertStmt(loc, clause, native=True)
            return
        if isinstance(s, ast.Delete):
            for t in s.targets:
                if not (isinstance(t, ast.Subscript) and not isinstance(t.slice, ast.Slice)):
                    raise LowerError("only 'del d[k]' on a dict is supported", s)
                container = self.expr(t.value)
                if not isinstance(container.ty, ir.TDict):
                    raise LowerError("only 'del d[k]' on a dict is supported", s)
                k = self.coerce(self.expr(t.slice), container.ty.key)
                if isinstance(container, ir.Var):
                    yield ir.DictDel(loc, container.name, k)
                elif isinstance(container, ir.Field) and isinstance(container.obj.ty, ir.TClass):
                    yield ir.FieldAssign(loc, container.obj, container.obj.ty.name, container.name, ir.Builtin(container.ty, loc, "dict_del", (container, k)))
                else:
                    raise LowerError("'del' needs a dict variable or field", s)
            return
        if isinstance(s, ast.Raise):
            what = ast.unparse(s.exc) if s.exc is not None else "exception"
            yield ir.Raise(loc, what, caught=self.try_depth > 0)
            return
        if isinstance(s, (ast.Try, getattr(ast, "TryStar", ast.Try))):
            handlers = []
            self.try_depth += 1 if s.handlers else 0
            try:
                body = tuple(self.block(s.body, s))
            finally:
                self.try_depth -= 1 if s.handlers else 0
            for h in s.handlers:
                pre: tuple[ir.Stmt, ...] = ()
                if h.name:
                    self.declare(h.name, ir.TOpaque("exception"), h)
                    pre = (ir.Assign(loc, h.name, ir.Extern(ir.TOpaque("exception"), loc, "caught exception", ())),)
                handlers.append(pre + tuple(self.block(h.body, h)))
            orelse = tuple(self.block(s.orelse, s.orelse[0])) if s.orelse else ()
            final = tuple(self.block(s.finalbody, s.finalbody[0])) if s.finalbody else ()
            yield ir.Try(loc, body, tuple(handlers), orelse, final)
            return
        if isinstance(s, (ast.With, ast.AsyncWith)):
            # The context manager is unchecked code; assume it does not
            # swallow exceptions (listed as an assumption).
            for item in s.items:
                cm = self.expr(item.context_expr)
                enter = ir.Extern(ir.TOpaque("context"), loc, f"{_desc(item.context_expr)}.__enter__", (cm,) if isinstance(cm.ty, (ir.TOpaque, ir.TClass)) else ())
                if item.optional_vars is not None:
                    if not isinstance(item.optional_vars, ast.Name):
                        raise LowerError("'with ... as' target must be a name", s)
                    self.declare(item.optional_vars.id, ir.TOpaque("context"), s)
                    yield ir.Assign(loc, item.optional_vars.id, enter)
                else:
                    yield ir.ExprStmt(loc, enter)
            yield from self.block(s.body, s)
            return
        if isinstance(s, (ast.Import, ast.ImportFrom)):
            for a in s.names:
                nm = (a.asname or a.name).split(".")[0]
                self.fe.bound.add(nm)
                if isinstance(s, ast.Import):
                    self.fe.modules.add(nm)
            return
        if isinstance(s, (ast.Global, ast.Nonlocal)):
            raise LowerError("'global'/'nonlocal' state is not modelled", s)
        if isinstance(s, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            # A local function or class: an opaque value; calls to it are
            # unchecked and may change what it captures.
            self.declare(s.name, ir.TOpaque("closure"), s)
            yield ir.Assign(loc, s.name, ir.Builtin(ir.TOpaque("closure"), loc, "opaque_op", (ir.Lit(ir.STR, loc, "closure"), ir.Lit(ir.STR, loc, s.name))))
            return
        raise LowerError(f"unsupported statement: {type(s).__name__}", s)

    def _effects_of(self, args: list[ast.expr], loc: ir.Loc):
        """Evaluate the expressions inside logging arguments (f-string holes
        included) for their effects and crashes; the formatting is ignored."""
        for a in args:
            parts = [fv.value for fv in a.values if isinstance(fv, ast.FormattedValue)] if isinstance(a, ast.JoinedStr) else [a]
            for part in parts:
                try:
                    yield ir.ExprStmt(loc, self.expr(part))
                except LowerError:
                    if any(isinstance(n, ast.Call) for n in ast.walk(part)):
                        raise
                    # pure formatting of something telic does not model: no effect

    def _check_assignable(self, name: str, ty: ir.Type, val: ir.Expr, node: ast.AST) -> None:
        if val.ty != ty and not (isinstance(ty, ir.TList) and isinstance(val.ty, ir.TList) and val.ty.elem == ir.NONE):
            raise LowerError(f"cannot assign {val.ty} to '{name}' of type {ty}", node)

    def _assign(self, target: ast.expr, value: ast.expr, s: ast.stmt, loc: ir.Loc):
        if isinstance(target, ast.Name):
            name = target.id
            if name in self.env and isinstance(self.env[name], ir.TList) and any(
                p.name == name for p in self.fn.params
            ):
                raise LowerError(f"rebinding list parameter '{name}' is not supported (mutate it or copy it to a new name)", s)
            known = self.env.get(name)
            val = self.expr(value, known)
            if known is not None:
                val = self.coerce(val, known)
            self._no_alias(name, val, s)
            self.declare(name, val.ty, s)
            ty = self.env[name]
            val = self.coerce(val, ty)
            self._check_assignable(name, ty, val, s)
            yield ir.Assign(loc, name, val)
            return
        if isinstance(target, ast.Attribute):
            obj = self.expr(target.value)
            if isinstance(obj.ty, ir.TOption):
                obj = self.coerce(obj, obj.ty.inner)
            if isinstance(obj.ty, ir.TOpaque):
                val = self.expr(value)
                yield ir.ExprStmt(loc, ir.Extern(ir.NONE, loc, f"setattr .{target.attr}", (obj, val)))
                return

            if isinstance(obj.ty, ir.TRecord):
                raise LowerError(f"{obj.ty.name} is frozen; build a new one with dataclasses.replace or the constructor", s)
            if not isinstance(obj.ty, ir.TClass):
                raise LowerError(f"cannot assign an attribute of {obj.ty}", s)
            prop = self.fe.member(obj.ty.name, target.attr)
            if prop in self.fe.setters:
                sk = prop + ".setter"
                params, _ = self.fe.signatures[sk]
                val = self.coerce(self.expr(value, params[1].ty), params[1].ty) if len(params) > 1 else self.expr(value)
                call = ir.Extern(ir.NONE, loc, f"@{self.fe.wrapped[sk]} {sk}", (obj, val)) if sk in self.fe.wrapped else ir.Call(ir.NONE, loc, sk, (obj, val))
                yield ir.ExprStmt(loc, call)
                return
            if prop in self.fe.properties:
                yield ir.Raise(loc, f"AttributeError: property '{target.attr}' of {obj.ty.name} has no setter", caught=self.try_depth > 0)
                return
            decl = self.fe.classes[obj.ty.name]
            ft = decl.field_type(target.attr)
            if ft is None:
                raise LowerError(f"{obj.ty.name} has no field '{target.attr}' (declare it in the class or __init__)", s)
            val = self.coerce(self.expr(value, ft), ft)
            self._check_assignable(f"{obj.ty.name}.{target.attr}", ft, val, s)
            if isinstance(ft, (ir.TList, ir.TDict)) and not fresh_list(val) and not self.moved(val, s):
                raise LowerError(f"storing an existing {ft} in a field would alias it; store a copy", s)
            yield ir.FieldAssign(loc, obj, obj.ty.name, target.attr, val)
            return
        if isinstance(target, ast.Subscript) and not isinstance(target.slice, ast.Slice) and isinstance(target.value, ast.Attribute):
            fld = self.expr(target.value)
            if isinstance(fld, ir.Field) and isinstance(fld.obj.ty, ir.TClass) and isinstance(fld.ty, (ir.TList, ir.TDict)):
                if isinstance(fld.ty, ir.TDict):
                    k = self.coerce(self.expr(target.slice), fld.ty.key)
                    val = self.coerce(self.expr(value, fld.ty.val), fld.ty.val)
                    new_v = ir.Builtin(fld.ty, loc, "dict_set", (fld, k, val))
                else:
                    i = self.expr(target.slice)
                    if not isinstance(i.ty, ir.TInt):
                        raise LowerError("list index must be an int", s)
                    val = self.coerce(self.expr(value, fld.ty.elem), fld.ty.elem)
                    new_v = ir.Builtin(fld.ty, loc, "list_set", (fld, i, val))
                yield ir.FieldAssign(loc, fld.obj, fld.obj.ty.name, fld.name, new_v)
                return
            raise LowerError(f"unsupported assignment target: {ast.unparse(target)}", s)
        if isinstance(target, ast.Subscript) and isinstance(self.expr(target.value).ty, ir.TOpaque):
            obj = self.expr(target.value)
            parts = [obj, self.expr(target.slice) if not isinstance(target.slice, ast.Slice) else ir.Lit(ir.STR, loc, "slice"), self.expr(value)]
            yield ir.ExprStmt(loc, ir.Extern(ir.NONE, loc, "setitem", tuple(parts)))
            return
        if isinstance(target, ast.Subscript) and isinstance(target.value, ast.Name) and not isinstance(target.slice, ast.Slice) and isinstance(self.env.get(target.value.id), ir.TDict):
            name = target.value.id
            dt = self.env[name]
            assert isinstance(dt, ir.TDict)
            if dt.key == ir.NONE and dt.val == ir.NONE:  # d = {} ... d[k] = v: the first store decides the type
                dt = ir.TDict(self.expr(target.slice).ty, self.expr(value).ty)
                self.env[name] = dt
            k = self.coerce(self.expr(target.slice), dt.key)
            if k.ty != dt.key:
                raise LowerError(f"key of '{name}' must be {dt.key}, got {k.ty}", s)
            val = self.coerce(self.expr(value, dt.val), dt.val)
            self._check_assignable(f"{name}[...]", dt.val, val, s)
            yield ir.IndexAssign(loc, name, k, val, wrap=False)
            return
        if isinstance(target, ast.Subscript) and isinstance(target.value, ast.Name) and not isinstance(target.slice, ast.Slice):
            name = target.value.id
            t = self.env.get(name)
            if not isinstance(t, ir.TList):
                raise LowerError(f"'{name}[...] = ...' needs '{name}' to be a list", s)
            idx = self.expr(target.slice)
            if not isinstance(idx.ty, ir.TInt):
                raise LowerError("list index must be an int", s)
            val = self.coerce(self.expr(value, t.elem), t.elem)
            if val.ty != t.elem:
                raise LowerError(f"cannot store {val.ty} into {t}", s)
            yield ir.IndexAssign(loc, name, idx, val, wrap=True)
            return
        if isinstance(target, ast.Tuple) and not isinstance(value, ast.Tuple) and isinstance(self.expr(value).ty, ir.TList):
            v = self.expr(value)
            assert isinstance(v.ty, ir.TList)
            k = len(target.elts)
            if isinstance(v, ir.Var):
                src = v
            else:
                t = self.fresh("unpack")
                self.env[t] = v.ty
                yield ir.Assign(loc, t, v)
                src = ir.Var(v.ty, loc, t)
            ln = ir.Binary(ir.BOOL, loc, "eq", ir.Builtin(ir.INT, loc, "len", (src,)), ir.Lit(ir.INT, loc, k))
            if self.try_depth > 0:  # the ValueError goes to a handler
                yield ir.If(loc, ir.Unary(ir.BOOL, loc, "not", ln), (ir.Raise(loc, "ValueError: wrong number of values to unpack", caught=True),), ())
            else:
                yield ir.AssertStmt(loc, ir.Clause("assert", ln, loc, f"unpacking needs exactly {k} elements"), native=True)
            for i, tgt in enumerate(target.elts):
                if not isinstance(tgt, ast.Name):
                    raise LowerError("unpacking targets must be names", s)
                self.declare(tgt.id, v.ty.elem, s)
                yield ir.Assign(loc, tgt.id, self.coerce(ir.Index(v.ty.elem, loc, src, ir.Lit(ir.INT, loc, i), wrap=False), self.env[tgt.id]))
            return
        if isinstance(target, ast.Tuple) and not isinstance(value, ast.Tuple):
            v = self.expr(value)
            if not isinstance(v.ty, ir.TOpaque):
                raise LowerError(f"unpacking a {v.ty} is not supported", s)
            t = self.fresh("tuple")
            self.env[t] = v.ty
            yield ir.Assign(loc, t, v)
            for k, tgt in enumerate(target.elts):
                if not isinstance(tgt, ast.Name):
                    raise LowerError("unpacking targets must be names", s)
                item = ir.Builtin(ir.TOpaque(""), loc, "opaque_op", (ir.Lit(ir.STR, loc, f"item{k}"), ir.Var(v.ty, loc, t)))
                known = self.env.get(tgt.id)
                val = self.coerce(item, known) if known is not None else item
                self.declare(tgt.id, val.ty, s)
                yield ir.Assign(loc, tgt.id, val)
            return
        if isinstance(target, ast.Tuple) and isinstance(value, ast.Tuple) and len(target.elts) == len(value.elts):
            # a, b = e1, e2  ==>  t1 = e1; t2 = e2; a = t1; b = t2
            temps = []
            for v in value.elts:
                val = self.expr(v)
                if isinstance(val.ty, ir.TList) and not fresh_list(val):
                    raise LowerError("tuple assignment of an existing list would alias it; copy it explicitly (xs[:])", s)
                t = self.fresh("tuple")
                self.env[t] = val.ty
                temps.append(t)
                yield ir.Assign(loc, t, val)
            for tgt, t in zip(target.elts, temps):
                load = ast.Name(id=t, ctx=ast.Load())
                ast.copy_location(load, s)
                yield from self._assign(tgt, load, s, loc) if not isinstance(tgt, ast.Name) else self._assign_tmp(tgt.id, t, s, loc)
            return
        raise LowerError(f"unsupported assignment target: {ast.unparse(target)}", s)


    def moved(self, val: ir.Expr, node: ast.AST) -> bool:
        """Is ``val`` a local list/dict variable that is never used after
        ``node``? Then binding it elsewhere moves it: no alias survives."""
        if not isinstance(val, ir.Var) or any(p.name == val.name for p in self.fn.params) or val.name in self.escaped:
            return False
        name = val.name
        end = (getattr(node, "end_lineno", None) or node.lineno, getattr(node, "end_col_offset", None) or 0)
        for x in ast.walk(self.node):
            if isinstance(x, ast.Name) and x.id == name and (x.lineno, x.col_offset) > end:
                return False
            if isinstance(x, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)) and x is not self.node:
                if any(isinstance(y, ast.Name) and y.id == name for y in ast.walk(x)):
                    return False  # a closure may still read it
        # inside a loop, the next iteration would see the moved list again,
        # unless the loop body binds it afresh before this point
        for loop in ast.walk(self.node):
            if isinstance(loop, (ast.For, ast.AsyncFor, ast.While)) and loop.lineno <= node.lineno <= (loop.end_lineno or loop.lineno):
                fresh = any(
                    isinstance(st, (ast.Assign, ast.AnnAssign)) and st.lineno < node.lineno and loop.lineno < st.lineno
                    and any(isinstance(t, ast.Name) and t.id == name for t in (st.targets if isinstance(st, ast.Assign) else [st.target]))
                    for st in ast.walk(loop)
                )
                if not fresh:
                    return False
        return True

    def _no_alias(self, name: str, val: ir.Expr, node: ast.AST) -> None:
        if not isinstance(val.ty, (ir.TList, ir.TDict)):
            return
        if any(p.name == name for p in self.fn.params):
            raise LowerError(f"rebinding list parameter '{name}' is not supported (mutate it, or copy it to a new name)", node)
        if not fresh_list(val) and not self.moved(val, node):
            raise LowerError(
                f"'{name} = ...' would alias an existing list; telic models lists as values, so copy explicitly (xs[:])",
                node,
            )

    def _assign_tmp(self, name: str, tmp: str, s: ast.stmt, loc: ir.Loc):
        ty = self.env[tmp]
        if isinstance(ty, ir.TList) and any(p.name == name for p in self.fn.params):
            raise LowerError(f"rebinding list parameter '{name}' is not supported (mutate it, or copy it to a new name)", s)
        self.declare(name, ty, s)
        yield ir.Assign(loc, name, self.coerce(ir.Var(ty, loc, tmp), self.env[name]))

    def _lower_loop_clauses(self, contracts: list[ContractLine]):
        invs: list[ir.Clause] = []
        dec = None
        for cl in contracts:
            if cl.keyword == "invariant":
                invs.append(self.clause(cl, "invariant", tuple(cl.tags)))
            elif cl.keyword == "decreases":
                dec = self.clause(cl, "decreases", tuple(cl.tags), expect=ir.INT)
        return tuple(invs), dec

    def _for(self, s: ast.For, loc: ir.Loc):
        if s.orelse:
            raise LowerError("for/else is not supported", s)
        contracts = self._loop_contracts(s)
        index_name = None
        for cl in contracts:
            if cl.keyword == "index":
                index_name = cl.payload.strip()
                if not index_name.isidentifier():
                    raise LowerError("'@index' takes a single name", line=cl.line)
        it = s.iter
        if index_name is not None and (index_name in self.env or index_name in self.stored_names):
            raise LowerError(f"'@index {index_name}' names an existing variable; pick a fresh name", s)
        if isinstance(it, ast.Call) and isinstance(it.func, ast.Name) and it.func.id in ("range", "enumerate") and it.func.id in self.fe.bound:
            raise LowerError(f"'{it.func.id}' is rebound in this module, so telic cannot assume the builtin", s)
        # range(...)
        if isinstance(it, ast.Call) and isinstance(it.func, ast.Name) and it.func.id == "range":
            if not isinstance(s.target, ast.Name):
                raise LowerError("range loop target must be a name", s)
            args = [self.expr(a) for a in it.args]
            if not all(isinstance(a.ty, ir.TInt) for a in args):
                raise LowerError("range() bounds must be ints", s)
            if len(args) == 1:
                lo, hi = ir.Lit(ir.INT, loc, 0), args[0]
            elif len(args) == 2:
                lo, hi = args
            else:
                raise LowerError("range() with a step is not supported", s)
            var = s.target.id
            self.declare(var, ir.INT, s)
            body = tuple(self.block(s.body, s))
            invs, dec = self._lower_loop_clauses(contracts)
            if dec is not None:
                raise LowerError("a for-range loop terminates by construction; remove '@decreases'", line=dec.loc.line)
            yield ir.ForRange(loc, var, lo, hi, invs, body)
            return
        # enumerate(xs) / xs
        idx_visible = False
        if isinstance(it, ast.Call) and isinstance(it.func, ast.Name) and it.func.id == "enumerate":
            if len(it.args) != 1 or not (isinstance(s.target, ast.Tuple) and len(s.target.elts) == 2):
                raise LowerError("use 'for i, x in enumerate(xs)'", s)
            i_node, x_node = s.target.elts
            if not (isinstance(i_node, ast.Name) and isinstance(x_node, ast.Name)):
                raise LowerError("enumerate targets must be names", s)
            idx, elem = i_node.id, x_node.id
            seq_node = it.args[0]
            idx_visible = True
        else:
            items_of = None
            if isinstance(it, ast.Call) and isinstance(it.func, ast.Attribute) and it.func.attr == "items" and not it.args and isinstance(s.target, ast.Tuple) and len(s.target.elts) == 2 and all(isinstance(t, ast.Name) for t in s.target.elts):
                d = self.expr(it.func.value)
                if isinstance(d.ty, ir.TDict):
                    items_of = d
            unpack = items_of is None and isinstance(s.target, ast.Tuple) and all(isinstance(t, ast.Name) for t in s.target.elts)
            if items_of is None and not (isinstance(s.target, ast.Name) or unpack):
                raise LowerError("for-loop target must be a name", s)
            elem = s.target.elts[0].id if items_of is not None else self.fresh("tuple") if unpack else s.target.id  # type: ignore[attr-defined]
            idx = index_name or self.fresh("i")
            seq_node = it.func.value if items_of is not None else it  # type: ignore[attr-defined]
        seq = self.expr(seq_node)
        value_name = None
        if isinstance(seq.ty, ir.TDict):
            # for k in d / for k, v in d.items(): iterate over the keys
            if isinstance(s.target, ast.Tuple):
                value_name = s.target.elts[1].id  # type: ignore[attr-defined]
            seq = ir.Builtin(ir.TList(seq.ty.key), seq.loc, "dict_keys", (seq,))
        elif isinstance(seq.ty, ir.TOpaque):
            seq = self.coerce(seq, ir.TList(ir.TOpaque("")))
        if not isinstance(seq.ty, ir.TList):
            raise LowerError("can only iterate over range(...), a list, a dict, or enumerate(list)", s)
        self.declare(idx, ir.INT, s)
        self.declare(elem, seq.ty.elem, s)
        prefix: tuple[ir.Stmt, ...] = ()
        if isinstance(s.target, ast.Tuple) and value_name is None and not idx_visible:
            # for a, b in pairs: the elements are tuples, which are opaque, and so are their items
            if not isinstance(seq.ty.elem, ir.TOpaque):
                raise LowerError(f"unpacking a {seq.ty.elem} is not supported", s)
            items = []
            for k, tgt in enumerate(s.target.elts):
                item = ir.Builtin(ir.TOpaque(""), loc, "opaque_op", (ir.Lit(ir.STR, loc, f"item{k}"), ir.Var(seq.ty.elem, loc, elem)))
                known = self.env.get(tgt.id)  # type: ignore[attr-defined]
                val = self.coerce(item, known) if known is not None else item
                self.declare(tgt.id, val.ty, s)  # type: ignore[attr-defined]
                items.append(ir.Assign(loc, tgt.id, val))  # type: ignore[attr-defined]
            prefix = tuple(items)
        if value_name is not None:
            d_expr = seq.args[0]  # type: ignore[attr-defined]
            self.declare(value_name, d_expr.ty.val, s)
            prefix = (ir.Assign(loc, value_name, ir.Index(d_expr.ty.val, loc, d_expr, ir.Var(seq.ty.elem, loc, elem), wrap=False)),)
        body = prefix + tuple(self.block(s.body, s))
        if isinstance(seq_node, ast.Name) and seq_node.id in ir.assigned_names(body[len(prefix):]):
            raise LowerError(f"loop body modifies '{seq_node.id}' while iterating over it", s)
        invs, dec = self._lower_loop_clauses(contracts)
        if dec is not None:
            raise LowerError("a for-each loop terminates by construction; remove '@decreases'", line=dec.loc.line)
        yield ir.ForEach(loc, elem, idx, seq, invs, body, idx_visible=idx_visible or index_name is not None)


class _ClassScope(FunctionLowerer):
    """Where class invariants are lowered: only 'self' is in scope."""

    def __init__(self, fe: PythonFrontend, cls: str):
        self.fe = fe
        self.cls = cls
        self.key = cls
        self.env = {"self": ir.TClass(cls)}
        self.tmp = 0
        self.current_aims = []
        self.local_contracts = []
        self.stored_names = set()
        self.try_depth = 0
        self.closures = {}
        self.escaped = set()


def fresh_list(e: ir.Expr) -> bool:
    """A list-valued expression that denotes a new list object (so binding it
    to a name creates no alias): a literal, a slice copy, or a call (callees
    may not return their list parameters)."""
    if isinstance(e, (ir.ListLit, ir.Call)):
        return True
    if isinstance(e, ir.Builtin) and e.name in ("slice", "list_copy", "py_mixed_list", "dict_lit", "dict_copy", "comp", "from_opaque", "dict_keys", "dict_values", "list_append", "list_concat", "list_repeat", "range_list"):
        return True
    if isinstance(e, ir.Builtin) and e.name == "await":
        return fresh_list(e.args[0])
    if isinstance(e, ir.Extern):
        return True
    if isinstance(e, ir.Ite):
        return fresh_list(e.then) and fresh_list(e.orelse)
    return False


def _own_fields_only(e: ir.Expr, cls: str, line: int) -> None:
    """A class invariant may only read the object's own fields: otherwise
    code that never touches the object could break it unnoticed."""
    for sub in ir.walk_expr(e):
        if isinstance(sub, ir.Field) and isinstance(sub.obj.ty, ir.TClass) and not (isinstance(sub.obj, ir.Var) and sub.obj.name == "self"):
            raise LowerError(f"a class invariant may only read fields of 'self', not of other objects", line=line)
        if (isinstance(sub, ir.Quant) and "self" in (sub.idx, sub.elem)) or (isinstance(sub, ir.Builtin) and sub.name == "comp" and isinstance(sub.args[1], ir.Lit) and sub.args[1].value == "self"):
            raise LowerError("a class invariant may not rebind 'self'", line=line)
        if isinstance(sub, ir.Call) and any(ir.reaches_object(a.ty) for a in sub.args):
            raise LowerError("a class invariant may not call functions on objects (they could read other objects); write the condition on self's fields", line=line)


PY_GLOBALS = set(dir(__import__("builtins"))) | {"__name__", "__file__", "__spec__", "__package__", "__doc__"} | {"datetime", "time", "uuid", "os", "json", "re", "random", "logging", "Decimal", "sorted", "reversed", "zip", "map", "filter", "open", "input", "id", "hash", "repr", "type", "set", "tuple", "list", "frozenset", "getattr", "setattr", "hasattr", "iter", "next", "divmod", "pow", "chr", "ord", "hex", "bin", "format", "vars", "dir", "callable", "super"}


def _has_opaque(t: ir.Type) -> bool:
    if isinstance(t, ir.TOpaque):
        return True
    if isinstance(t, ir.TList):
        return _has_opaque(t.elem)
    if isinstance(t, ir.TOption):
        return _has_opaque(t.inner)
    if isinstance(t, ir.TDict):
        return _has_opaque(t.key) or _has_opaque(t.val)
    return False


def _desc(n: ast.expr) -> str:
    try:
        return ast.unparse(n)[:40]
    except Exception:  # pragma: no cover
        return "value"


def _about_unchecked(e: ir.Expr) -> bool:
    """Does a condition depend on values from unchecked code?"""
    for x in ir.walk_expr(e):
        if isinstance(x, ir.Extern) or (isinstance(x, ir.Builtin) and x.name in ("opaque_op", "from_opaque")):
            return True
        if isinstance(x, ir.Var) and isinstance(x.ty, ir.TOpaque):
            return True
    return False


def _is_generator(fn: ast.AST) -> bool:
    return any(isinstance(x, (ast.Yield, ast.YieldFrom)) for x in _own_nodes(fn))


def handed_on(module: ir.Module, uses: list[tuple[str, ir.Loc, str]]) -> None:
    """A checked function used as a value may be called by code telic does
    not see, with any arguments its types allow: its precondition is an
    obligation there, carried by a unit that calls it so (and the function
    that hands it on rests on that unit)."""
    for name, loc, owner in uses:
        tgt = module.functions.get(name)
        if tgt is None or not tgt.requires:
            continue
        uid = f"<{name}:{loc.line}:{loc.col}>"
        params = [ir.Param(p.name, p.ty) for p in tgt.params]
        call = ir.Call(tgt.ret, loc, name, tuple(ir.Var(p.ty, loc, p.name) for p in params))
        body: list[ir.Stmt] = [ir.Return(loc, call) if tgt.ret != ir.NONE else ir.ExprStmt(loc, call)]
        module.functions[uid] = ir.Function(uid, loc, loc.line, params, tgt.ret, body=body, exported=False, source=name, locals={p.name: p.ty for p in params}, unit=f"'{ir.source_name(name)}' handed on as a value at line {loc.line}")
        module.code.calls.append((owner, loc, name, (uid,)))


def _located(node: ast.AST, at: ast.AST) -> ast.AST:
    """A node telic builds, placed where ``at`` is in the source."""
    return ast.fix_missing_locations(ast.copy_location(node, at))


def _own_nodes(fn: ast.AST):
    """Nodes of a function body, not descending into nested defs/classes."""
    stack = list(ast.iter_child_nodes(fn))
    while stack:
        n = stack.pop()
        yield n
        if not isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef, ast.Lambda)):
            stack.extend(ast.iter_child_nodes(n))


def _join_optional(a: ir.Type, b: ir.Type) -> ir.Type | None:
    """The optional type covering both (None and T, or T? and T)."""
    for x, y in ((a, b), (b, a)):
        if isinstance(x, ir.TOption) and (y == x.inner or y == ir.NONE):
            return x
        if x == ir.NONE and not isinstance(y, (ir.TList, ir.TDict, ir.TOption)) and y != ir.NONE:
            return ir.TOption(y)
    return None


def _union_parts(n: ast.expr) -> list[ast.expr]:
    if isinstance(n, ast.BinOp) and isinstance(n.op, ast.BitOr):
        return _union_parts(n.left) + _union_parts(n.right)
    return [n]


def _simple_default(d: ast.expr) -> bool:
    if isinstance(d, ast.Constant):
        return True
    if isinstance(d, ast.UnaryOp) and isinstance(d.op, (ast.USub, ast.UAdd)) and isinstance(d.operand, ast.Constant):
        return True
    return False


TRANSPARENT_DECORATORS = {"property", "staticmethod", "classmethod", "setter", "cached_property", "abstractmethod", "override", "final", "lru_cache", "cache", "wraps", "total_ordering", "overload", "no_type_check"}
ROUTE_VERBS = {"get", "post", "put", "patch", "delete", "route", "websocket", "head", "options", "api_route", "on_event", "command", "task", "shared_task", "fixture", "listens_for", "register"}


def _route_decorator(d: ast.expr) -> bool:
    """``@app.get(...)``, ``@router.post(...)``, ``@celery.task``: registration
    decorators that return the function itself."""
    f = d.func if isinstance(d, ast.Call) else d
    return isinstance(f, ast.Attribute) and f.attr in ROUTE_VERBS


class NotModelled(LowerError):
    """A construct telic deliberately treats as library code (a note, not a problem)."""


MODEL_BASES = {"BaseModel", "SQLModel"}
NEUTRAL_BASES = {"object", "ABC", "Generic", "Protocol"}


def _decorator_name(d: ast.expr) -> str:
    if isinstance(d, ast.Subscript):
        d = d.value  # Generic[T]
    if isinstance(d, ast.Call):
        d = d.func
    if isinstance(d, ast.Name):
        return d.id
    if isinstance(d, ast.Attribute):
        return d.attr
    return "?"


BUILTINS = {"len", "abs", "min", "max", "sum", "float", "int", "round", "bool", "all", "any", "range", "enumerate", "print"}


def _as_load(target: ast.expr) -> ast.expr:
    node = ast.parse(ast.unparse(target), mode="eval").body
    ast.copy_location(node, target)
    for n in ast.walk(node):
        ast.copy_location(n, target)
        n.end_lineno, n.end_col_offset = target.end_lineno, target.end_col_offset
    return node


# ---------------------------------------------------------------------------


_CMP = {ast.Lt: "lt", ast.LtE: "le", ast.Gt: "gt", ast.GtE: "ge", ast.Eq: "eq", ast.NotEq: "ne"}


class ExprLowerer:
    def __init__(self, fl: FunctionLowerer, spec: bool = False, result_ty: ir.Type | None = None, line_offset: int = 0, col_offset: int = 0):
        self.fl = fl
        self.spec = spec
        self.result_ty = result_ty
        self.line_offset = line_offset
        self.col_offset = col_offset
        self.bound: dict[str, ir.Type] = {}
        self.aliases: dict[str, ir.Expr] = {}  # comprehension targets that stand for an expression
        self.allow_old = False

    def loc(self, node: ast.AST) -> ir.Loc:
        if self.line_offset:
            return _loc(node, self.line_offset, self.col_offset - 1)
        return _loc(node)

    def err(self, msg: str, node: ast.AST) -> LowerError:
        line = self.loc(node).line
        return LowerError(msg, line=line)

    def lookup(self, name: str, node: ast.AST) -> ir.Type:
        if name in self.bound:
            return self.bound[name]
        if name in self.fl.env:
            return self.fl.env[name]
        raise self.err(f"unknown name '{name}'", node)

    def cond(self, n: ast.expr) -> ir.Expr:
        """Lower an expression used only for its truth value, where Python's
        truthiness applies (if/while/assert/not, and/or operands there)."""
        if isinstance(n, ast.BoolOp):
            op = "and" if isinstance(n.op, ast.And) else "or"
            vals = [self.cond(v) for v in n.values]
            out = vals[0]
            for v in vals[1:]:
                out = ir.Binary(ir.BOOL, self.loc(n), op, out, v)
            return out
        return self.truthy(self.expr(n), n)

    def truthy(self, e: ir.Expr, node: ast.AST) -> ir.Expr:
        t = e.ty
        if isinstance(t, ir.TBool):
            return e
        if isinstance(t, ir.TInt):
            return ir.Binary(ir.BOOL, e.loc, "ne", e, ir.Lit(ir.INT, e.loc, 0))
        if isinstance(t, ir.TReal):
            return ir.Binary(ir.BOOL, e.loc, "ne", e, ir.Lit(ir.REAL, e.loc, Fraction(0)))
        if isinstance(t, ir.TList):
            return ir.Binary(ir.BOOL, e.loc, "gt", ir.Builtin(ir.INT, e.loc, "len", (e,)), ir.Lit(ir.INT, e.loc, 0))
        if isinstance(t, ir.TStr):
            return ir.Binary(ir.BOOL, e.loc, "ne", e, ir.Lit(ir.STR, e.loc, ""))
        if isinstance(t, ir.TOption):
            present = ir.Unary(ir.BOOL, e.loc, "not", ir.Builtin(ir.BOOL, e.loc, "is_none", (e,)))
            if isinstance(t.inner, ir.TRecord) or (isinstance(t.inner, ir.TClass) and not self.fl.fe.custom_bool.get(t.inner.name)):
                return present
            return ir.Binary(ir.BOOL, e.loc, "and", present, self.truthy(ir.Builtin(t.inner, e.loc, "unwrap", (e,)), node))
        if isinstance(t, ir.TOpaque):
            return self.opaque("truthy", [e], ir.BOOL, e.loc)
        if isinstance(t, ir.TEnum):
            return ir.Lit(ir.BOOL, e.loc, True)
        if isinstance(t, ir.TClass) and self.fl.fe.custom_bool.get(t.name):
            raise self.err(f"{t.name} defines __bool__/__len__; its truth value is not modelled", node)
        if isinstance(t, (ir.TClass, ir.TRecord)):
            return ir.Lit(ir.BOOL, e.loc, True)
        raise self.err(f"cannot use a {t} as a condition", node)

    def need(self, e: ir.Expr) -> ir.Expr:
        """An optional used as a plain value: unwrap it (and prove it present)."""
        if isinstance(e.ty, ir.TOption):
            return ir.Builtin(e.ty.inner, e.loc, "unwrap", (e,))
        return e

    def numeric_pair(self, a: ir.Expr, b: ir.Expr, node: ast.AST) -> tuple[ir.Expr, ir.Expr, ir.Type]:
        a, b = self.need(a), self.need(b)
        if not (ir.is_numeric(a.ty) and ir.is_numeric(b.ty)):
            raise self.err(f"arithmetic on {a.ty} and {b.ty}", node)
        if isinstance(a.ty, ir.TReal) or isinstance(b.ty, ir.TReal):
            return self.fl.coerce(a, ir.REAL), self.fl.coerce(b, ir.REAL), ir.REAL
        return a, b, ir.INT

    def expr(self, n: ast.expr, expect: ir.Type | None = None) -> ir.Expr:
        loc = self.loc(n)
        if isinstance(n, ast.Constant):
            v = n.value
            if isinstance(v, bool):
                return ir.Lit(ir.BOOL, loc, v)
            if isinstance(v, int):
                return ir.Lit(ir.INT, loc, v)
            if isinstance(v, float):
                return ir.Lit(ir.REAL, loc, Fraction(repr(v)))
            if isinstance(v, str):
                return ir.Lit(ir.STR, loc, v)
            if v is None:
                return ir.Lit(expect if isinstance(expect, ir.TOption) else ir.NONE, loc, None)
            raise self.err(f"unsupported constant {v!r}", n)
        if isinstance(n, ast.Name):
            if n.id in self.aliases:
                return self.aliases[n.id]
            if self.spec and n.id == "result" and self.result_ty is not None and n.id not in self.bound:
                if self.result_ty == ir.NONE:
                    raise self.err("'result' used but the function returns nothing", n)
                return ir.Result(self.result_ty, loc)
            fe = self.fl.fe
            if n.id not in self.bound and n.id not in self.fl.env:
                if n.id in fe.constants:
                    return self.expr(fe.constants[n.id], expect)
                if n.id in fe.bound or n.id in PY_GLOBALS:
                    if n.id in fe.signatures and n.id not in fe.class_names and not self.spec:
                        fe.handed.append((n.id, loc, self.fl.key))
                    # a module global or import: read fresh each time (it may change)
                    return ir.Extern(ir.TOpaque(n.id), loc, n.id, ())
            return ir.Var(self.lookup(n.id, n), loc, n.id)
        if isinstance(n, ast.Await):
            inner = self.expr(n.value, expect)
            return ir.Builtin(inner.ty, loc, "await", (inner,))
        if isinstance(n, ast.JoinedStr):
            return self.fstring(n, loc)
        if isinstance(n, ast.Tuple):
            parts = [self.expr(x) for x in n.elts]
            if isinstance(expect, ir.TRecord) and expect.name == "tuple":
                if len(parts) != len(expect.fields):
                    raise self.err(f"tuple has {len(parts)} values, expected {len(expect.fields)}", n)
                parts = [self.fl.coerce(x, t) for x, (_, t) in zip(parts, expect.fields)]
                ty = expect
            else:
                if any(_has_mutable_child(x.ty) for x in parts):
                    raise self.err("tuples containing mutable containers need identity-preserving product storage", n)
                ty = ir.TRecord("tuple", tuple((f"_{i}", x.ty) for i, x in enumerate(parts)))
            if any(_has_mutable_child(x.ty) for x in parts):
                raise self.err("tuples containing mutable containers need identity-preserving product storage", n)
            return ir.RecordLit(ty, loc, tuple((field, value) for (field, _), value in zip(ty.fields, parts)))
        if isinstance(n, ast.Set) and not self.spec:
            parts = [self.expr(x) for x in n.elts]
            return self.opaque("set", parts, ir.TOpaque("set"), loc)
        if isinstance(n, ast.UnaryOp) and not isinstance(n.op, ast.Not) and isinstance(self.expr(n.operand).ty, ir.TOpaque):
            return self.opaque(type(n.op).__name__.lower(), [self.expr(n.operand)], ir.TOpaque(""), loc)
        if isinstance(n, ast.UnaryOp):
            a = self.need(self.expr(n.operand)) if not isinstance(n.op, ast.Not) else ir.Lit(ir.BOOL, loc, True)
            if isinstance(n.op, ast.Not):
                return ir.Unary(ir.BOOL, loc, "not", self.cond(n.operand))
            if isinstance(n.op, ast.USub):
                if not ir.is_numeric(a.ty):
                    raise self.err(f"cannot negate {a.ty}", n)
                if isinstance(a, ir.Lit) and not isinstance(a.value, bool):
                    return ir.Lit(a.ty, loc, -a.value)  # type: ignore[operator]
                return ir.Unary(a.ty, loc, "neg", a)
            if isinstance(n.op, ast.UAdd):
                return a
            raise self.err("unsupported unary operator", n)
        if isinstance(n, ast.BinOp):
            return self.binop(n, loc)
        if isinstance(n, ast.BoolOp):
            # As a value, `a or b` is one of its operands, not a bool.
            op = "and" if isinstance(n.op, ast.And) else "or"
            vals = [self.expr(v) for v in n.values]
            if any(isinstance(v.ty, ir.TOpaque) for v in vals):
                return self.opaque(op, vals, ir.TOpaque(""), loc)
            if not all(isinstance(v.ty, ir.TBool) for v in vals):
                return self.value_boolop(op, vals, n, loc)
            out = vals[0]
            for v in vals[1:]:
                out = ir.Binary(ir.BOOL, loc, op, out, v)
            return out
        if isinstance(n, ast.Compare):
            return self.compare(n, loc)
        if isinstance(n, ast.IfExp):
            c = self.cond(n.test)
            a = self.expr(n.body, expect)
            b = self.expr(n.orelse, expect)
            if a.ty != b.ty:
                opt = _join_optional(a.ty, b.ty)
                if isinstance(a.ty, ir.TOpaque) or isinstance(b.ty, ir.TOpaque):
                    a, b = self.fl.coerce(a, ir.TOpaque("")), self.fl.coerce(b, ir.TOpaque(""))
                elif opt is not None:
                    a, b = self.fl.coerce(a, opt), self.fl.coerce(b, opt)
                elif ir.is_numeric(a.ty) and ir.is_numeric(b.ty):
                    a, b, _ = self.numeric_pair(a, b, n)
                else:
                    raise self.err(f"conditional branches have types {a.ty} and {b.ty}", n)
            return ir.Ite(a.ty, loc, c, a, b)
        if isinstance(n, ast.Call):
            return self.call(n, loc, expect)
        if isinstance(n, ast.Subscript):
            seq = self.need(self.expr(n.value))
            if isinstance(seq.ty, ir.TOpaque):
                parts = [seq] + ([self.expr(n.slice)] if not isinstance(n.slice, ast.Slice) else [self.expr(x) for x in (n.slice.lower, n.slice.upper) if x is not None])
                return self.opaque("getitem", parts, ir.TOpaque(""), loc)
            if isinstance(seq.ty, ir.TStr):
                if isinstance(n.slice, ast.Slice):
                    if n.slice.step is not None:
                        return self.opaque("slice_step", [seq], ir.STR, loc)
                    lo = self.expr(n.slice.lower) if n.slice.lower is not None else ir.Lit(ir.NONE, loc, None)
                    hi = self.expr(n.slice.upper) if n.slice.upper is not None else ir.Lit(ir.NONE, loc, None)
                    return ir.Builtin(ir.STR, loc, "str_slice", (seq, lo, hi))
                i = self.expr(n.slice)
                if not isinstance(i.ty, ir.TInt):
                    raise self.err("string index must be an int", n)
                return ir.Builtin(ir.STR, loc, "str_index", (seq, i))
            if isinstance(seq.ty, ir.TDict) and not isinstance(n.slice, ast.Slice):
                k = self.fl.coerce(self.expr(n.slice), seq.ty.key)
                if k.ty != seq.ty.key:
                    raise self.err(f"key must be {seq.ty.key}, got {k.ty}", n)
                return ir.Index(seq.ty.val, loc, seq, k, wrap=False)
            if isinstance(seq.ty, ir.TRecord) and seq.ty.name == "tuple" and isinstance(n.slice, ast.Constant) and isinstance(n.slice.value, int):
                index = n.slice.value
                if index < 0:
                    index += len(seq.ty.fields)
                if 0 <= index < len(seq.ty.fields):
                    name, ty = seq.ty.fields[index]
                    return ir.Field(ty, loc, seq, name)
                raise self.err("tuple index is out of range", n)
            if not isinstance(seq.ty, ir.TList):
                raise self.err(f"cannot index a {seq.ty}", n)
            if isinstance(n.slice, ast.Slice):
                if n.slice.step is not None:
                    raise self.err("slices with a step are not supported", n)
                lo = self.expr(n.slice.lower) if n.slice.lower is not None else ir.Lit(ir.NONE, loc, None)
                hi = self.expr(n.slice.upper) if n.slice.upper is not None else ir.Lit(ir.NONE, loc, None)
                for b in (lo, hi):
                    if b.ty not in (ir.INT, ir.NONE):
                        raise self.err("slice bounds must be ints", n)
                return ir.Builtin(seq.ty, loc, "slice", (seq, lo, hi))
            idx = self.expr(n.slice)
            if not isinstance(idx.ty, ir.TInt):
                raise self.err("list index must be an int", n)
            return ir.Index(seq.ty.elem, loc, seq, idx, wrap=True)
        if isinstance(n, ast.Attribute):
            fe = self.fl.fe
            if isinstance(n.value, ast.Name) and n.value.id not in self.fl.env and n.value.id not in self.bound:
                if n.value.id in fe.enum_types:
                    et = fe.enum_types[n.value.id]
                    if n.attr not in et.members:
                        raise self.err(f"{et.name} has no member '{n.attr}'", n)
                    return ir.Lit(et, loc, et.members.index(n.attr))
                if n.value.id in fe.bound or n.value.id in PY_GLOBALS:
                    return ir.Extern(ir.TOpaque(f"{n.value.id}.{n.attr}"), loc, f"{n.value.id}.{n.attr}", ())
            obj = self.need(self.expr(n.value))
            if isinstance(obj.ty, ir.TOpaque):
                fields = fe.structure_fields(obj.ty.why) if obj.ty.why else None
                # (a field of an immutable structure: part of it, built before it)
                kind = "part" if fields is not None and n.attr in fields else "attr"
                return self.opaque(f"{kind}.{n.attr}", [obj], ir.TOpaque(""), loc)
            if isinstance(obj.ty, ir.TEnum):
                if n.attr == "name":
                    return ir.Builtin(ir.STR, loc, "enum_name", (obj,))
                if n.attr == "value":
                    vals = obj.ty.values
                    kinds = {type(v) for v in vals}
                    if len(kinds) == 1 and kinds <= {int, str}:
                        return ir.Builtin(ir.INT if kinds == {int} else ir.STR, loc, "enum_value", (obj,))
                    return self.opaque("enum_value", [obj], ir.TOpaque(""), loc)
                raise self.err(f"unsupported attribute '.{n.attr}' of an enum", n)
            if isinstance(obj.ty, ir.TClass):
                key = self.fl.fe.member(obj.ty.name, n.attr)
                if key in self.fl.fe.properties:
                    return self.method_call(key, obj, [], [], n, loc)
                ft = self.fl.fe.classes[obj.ty.name].field_type(n.attr)
                if ft is None:
                    raise self.err(f"{obj.ty.name} has no field '{n.attr}'", n)
                return ir.Field(ft, loc, obj, n.attr)
            if isinstance(obj.ty, ir.TRecord):
                ft = obj.ty.field_type(n.attr)
                if ft is None:
                    raise self.err(f"{obj.ty.name} has no field '{n.attr}'", n)
                return ir.Field(ft, loc, obj, n.attr)
            raise self.err(f"unsupported attribute access '.{n.attr}' on {obj.ty}", n)
        if isinstance(n, ast.List):
            elems = [self.expr(e) for e in n.elts]
            if not elems:
                if isinstance(expect, ir.TList):
                    return ir.ListLit(expect, loc, ())
                return ir.ListLit(ir.TList(ir.NONE), loc, ())
            if any(isinstance(e.ty, ir.TReal) for e in elems) and any(isinstance(e.ty, ir.TInt) for e in elems):
                return ir.Builtin(ir.TList(ir.REAL), loc, "py_mixed_list", tuple(elems))
            t = elems[0].ty
            if any(isinstance(e.ty, ir.TReal) for e in elems) and all(ir.is_numeric(e.ty) for e in elems):
                t = ir.REAL
                elems = [self.fl.coerce(e, t) for e in elems]
            if any(e.ty != t for e in elems):
                raise self.err("list elements must all have one type", n)
            return ir.ListLit(ir.TList(t), loc, tuple(elems))
        if isinstance(n, ast.Dict):
            if any(k is None for k in n.keys) and not isinstance(expect, ir.TDict):
                # {**base, "k": v}: a JSON-like payload, not a checked map
                return self.opaque("dict", [self.expr(x) for x in list(filter(None, n.keys)) + n.values], ir.TOpaque("dict"), loc)
            if any(k is None for k in n.keys):
                raise self.err("'**' in dict literals is not supported", n)
            ks = [self.expr(k) for k in n.keys]  # type: ignore[arg-type]
            vs = [self.expr(v) for v in n.values]
            if not isinstance(expect, ir.TDict) and (len({k.ty for k in ks}) > 1 or len({v.ty for v in vs}) > 1) and not all(ir.is_numeric(v.ty) for v in vs):
                return self.opaque("dict", ks + vs, ir.TOpaque("dict"), loc)  # mixed value types: a JSON-like payload
            if not isinstance(expect, ir.TDict) and any(isinstance(v.ty, (ir.TList, ir.TDict, ir.TOption)) for v in vs):
                return self.opaque("dict", ks + vs, ir.TOpaque("dict"), loc)  # containers as values: a JSON-like payload
            if isinstance(expect, ir.TDict):
                dt = expect
            elif ks:
                dt = ir.TDict(ks[0].ty, vs[0].ty)
            else:
                return ir.Builtin(ir.TDict(ir.NONE, ir.NONE), loc, "dict_lit", ())
            args: list[ir.Expr] = []
            for k, v in zip(ks, vs):
                k2, v2 = self.fl.coerce(k, dt.key), self.fl.coerce(v, dt.val)
                if k2.ty != dt.key or v2.ty != dt.val:
                    raise self.err(f"dict entries must be {dt.key}: {dt.val}", n)
                args += [k2, v2]
            return ir.Builtin(dt, loc, "dict_lit", tuple(args))
        if isinstance(n, (ast.GeneratorExp, ast.ListComp)) or (isinstance(n, (ast.DictComp, ast.SetComp)) and not self.spec):
            return self.comprehension(n, loc)
        if isinstance(n, ast.Lambda) and not self.spec:
            self.lambda_unit(n)
            return self.opaque("lambda", [], ir.TOpaque(""), loc)
        raise self.err(f"unsupported expression: {type(n).__name__}", n)

    def lambda_unit(self, lam: ast.Lambda) -> None:
        """A lambda handed on as a value: code telic does not see may call it
        with anything, whenever it likes, so its body is checked as a
        function of its own, over every argument and every value of what it
        captures. Named as the code graph names it, so a proof that hands
        it to unchecked code rests on it."""
        fe = self.fl.fe
        uid = f"<lambda:{lam.lineno}:{lam.col_offset}>"
        a = lam.args
        own = [x.arg for x in a.posonlyargs + a.args + a.kwonlyargs] + [x.arg for x in (a.vararg, a.kwarg) if x]
        caps: dict[str, ir.Type] = {}
        for x in ast.walk(lam.body):
            if isinstance(x, ast.Name) and isinstance(x.ctx, ast.Load) and x.id not in own and x.id not in caps:
                if x.id in self.bound:
                    caps[x.id] = self.bound[x.id]
                elif x.id in self.aliases:
                    caps[x.id] = self.aliases[x.id].ty
                elif x.id in self.fl.env:
                    caps[x.id] = self.fl.env[x.id]
        params = [ir.Param(p, ir.TOpaque("an argument")) for p in own] + [ir.Param(c, t) for c, t in caps.items()]
        body = ast.copy_location(ast.Return(lam.body), lam.body)
        node = ast.copy_location(ast.FunctionDef(uid, ast.arguments([], [ast.arg(p.name) for p in params], None, [], [], None, []), [body], []), lam)
        node.end_lineno = lam.end_lineno
        fe.signatures[uid] = (params, ir.TOpaque(""))
        try:
            fn = FunctionLowerer(fe, node, key=uid, unit=f"the lambda at line {lam.lineno}").lower()
        except LowerError as e:
            fn = ir.Function(uid, ir.Loc(lam.lineno, lam.col_offset), lam.end_lineno or lam.lineno, params, ir.TOpaque(""), exported=False, unit=f"the lambda at line {lam.lineno}")
            fn.unsupported.append((str(e), ir.Loc(e.line or lam.lineno)))
        fn.source = ast.get_source_segment(fe.source, lam) or ""
        fe.module.functions[uid] = fn

    def binop(self, n: ast.BinOp, loc: ir.Loc) -> ir.Expr:
        a = self.expr(n.left)
        b = self.expr(n.right)
        op = n.op
        if isinstance(a.ty, ir.TOpaque) or isinstance(b.ty, ir.TOpaque):
            return self.opaque(type(op).__name__.lower(), [a, b], ir.TOpaque(""), loc)
        if isinstance(a.ty, ir.TStr) or isinstance(b.ty, ir.TStr):
            if isinstance(op, ast.Add) and a.ty == b.ty == ir.STR:
                return ir.Builtin(ir.STR, loc, "str_concat", (a, b))
            if isinstance(op, ast.Mult) and {a.ty, b.ty} == {ir.STR, ir.INT}:
                return ir.Builtin(ir.STR, loc, "str_fn", (ir.Lit(ir.STR, loc, "repeat"), a, b))
            if isinstance(op, ast.Mod) and a.ty == ir.STR:
                return ir.Builtin(ir.STR, loc, "str_fn", (ir.Lit(ir.STR, loc, "percent_format"), a, self.fl.coerce(b, ir.TOpaque("")) if not isinstance(b.ty, ir.TOpaque) else b))
            raise self.err(f"unsupported operation on {a.ty} and {b.ty}", n)
        if isinstance(op, ast.Pow):
            if isinstance(n.right, ast.Constant) and isinstance(n.right.value, int) and 0 <= n.right.value <= 4 and ir.is_numeric(a.ty):
                k = n.right.value
                if k == 0:
                    return ir.Lit(a.ty, loc, 1 if isinstance(a.ty, ir.TInt) else Fraction(1))
                out = a
                for _ in range(k - 1):
                    out = ir.Binary(a.ty, loc, "mul", out, a)
                return out
            return self.opaque("pow", [a, b], ir.TOpaque("") if not (isinstance(a.ty, ir.TReal) or isinstance(b.ty, ir.TReal)) else ir.REAL, loc)
        if isinstance(op, ast.Add) and isinstance(a.ty, ir.TList):
            if isinstance(b, ir.ListLit) and not b.elems:
                b = ir.ListLit(a.ty, b.loc, ())
            if isinstance(a, ir.ListLit) and not a.elems and isinstance(b.ty, ir.TList):
                a = ir.ListLit(b.ty, a.loc, ())
            if b.ty != a.ty:
                raise self.err(f"cannot concatenate {a.ty} and {b.ty}", n)
            return ir.Builtin(a.ty, loc, "list_concat", (a, b))
        if isinstance(op, ast.Mult) and (isinstance(a, ir.ListLit) or isinstance(b, ir.ListLit)):
            lst, k = (a, b) if isinstance(a, ir.ListLit) else (b, a)
            if not lst.elems or not isinstance(k.ty, ir.TInt):
                raise self.err(f"'*' repeats a non-empty list literal an int number of times, not {a.ty} and {b.ty}", n)
            return ir.Builtin(lst.ty, loc, "list_repeat", (lst, k))
        if isinstance(op, ast.Add) and isinstance(a.ty, ir.TStr):
            if b.ty != ir.STR:
                raise self.err(f"cannot concatenate str and {b.ty}", n)
            return ir.Builtin(ir.STR, loc, "str_concat", (a, b))
        if isinstance(op, (ast.Add, ast.Sub, ast.Mult)):
            a, b, t = self.numeric_pair(a, b, n)
            name = {ast.Add: "add", ast.Sub: "sub", ast.Mult: "mul"}[type(op)]
            return ir.Binary(t, loc, name, a, b)
        if isinstance(op, ast.Div):
            a, b, _ = self.numeric_pair(a, b, n)
            return ir.Binary(ir.REAL, loc, "py_rdiv", self.fl.coerce(a, ir.REAL), self.fl.coerce(b, ir.REAL))
        if isinstance(op, ast.FloorDiv):
            a, b, t = self.numeric_pair(a, b, n)
            if t == ir.INT:
                return ir.Binary(ir.INT, loc, "floordiv", a, b)
            q = ir.Binary(ir.REAL, loc, "rdiv", a, b)
            return ir.Builtin(ir.REAL, loc, "to_real", (ir.Builtin(ir.INT, loc, "floor", (q,)),))
        if isinstance(op, ast.Mod):
            a, b, t = self.numeric_pair(a, b, n)
            return ir.Binary(t, loc, "fmod", a, b)
        if isinstance(op, (ast.BitAnd, ast.BitOr, ast.BitXor, ast.LShift, ast.RShift, ast.MatMult)):
            # bit operations (and operator overloads of library values): deterministic, uninterpreted
            ty = ir.INT if a.ty == ir.INT and b.ty == ir.INT else ir.TOpaque("")
            return self.opaque(type(op).__name__.lower(), [a, b], ty, loc)
        raise self.err(f"unsupported operator {type(op).__name__}", n)

    def compare(self, n: ast.Compare, loc: ir.Loc) -> ir.Expr:
        parts = []
        left = self.expr(n.left)
        for op, rnode in zip(n.ops, n.comparators):
            right = self.expr(rnode)
            if (isinstance(left.ty, ir.TOpaque) or isinstance(right.ty, ir.TOpaque)) and not (ir.NONE in (left.ty, right.ty) and isinstance(op, (ast.Is, ast.IsNot, ast.Eq, ast.NotEq))):
                parts.append(self.opaque(f"cmp.{type(op).__name__.lower()}", [left, right], ir.BOOL, loc))
                left = right
                continue
            if isinstance(op, (ast.In, ast.NotIn)) and right.ty == ir.STR:
                if left.ty != ir.STR:
                    raise self.err(f"'in' on a string needs a string on the left, got {left.ty}", n)
                c = ir.Builtin(ir.BOOL, loc, "str_contains", (right, left))
                parts.append(ir.Unary(ir.BOOL, loc, "not", c) if isinstance(op, ast.NotIn) else c)
                left = right
                continue
            if isinstance(left.ty, ir.TEnum) and isinstance(op, (ast.Lt, ast.LtE, ast.Gt, ast.GtE)):
                parts.append(self.opaque(f"cmp.{type(op).__name__.lower()}", [left, right], ir.BOOL, loc))
                left = right
                continue
            if left.ty == right.ty == ir.STR and isinstance(op, (ast.Lt, ast.LtE, ast.Gt, ast.GtE)):
                a_, b_ = (left, right) if isinstance(op, (ast.Lt, ast.LtE)) else (right, left)
                parts.append(ir.Builtin(ir.BOOL, loc, "str_lt" if isinstance(op, (ast.Lt, ast.Gt)) else "str_le", (a_, b_)))
                left = right
                continue
            if (isinstance(op, (ast.Is, ast.IsNot)) and isinstance(left.ty, ir.TOpaque) and isinstance(right.ty, ir.TOpaque)):
                pass
            if (isinstance(op, (ast.Is, ast.IsNot)) and ir.NONE in (left.ty, right.ty) or isinstance(op, (ast.Is, ast.IsNot)) and not (isinstance(left.ty, ir.TClass) and left.ty == right.ty)) or (isinstance(op, (ast.Eq, ast.NotEq)) and ir.NONE in (left.ty, right.ty)):
                other = left if right.ty == ir.NONE else right if left.ty == ir.NONE else None
                if other is None:
                    raise self.err("'is' is only supported against None", n)
                if other.ty == ir.NONE:
                    c = ir.Lit(ir.BOOL, loc, True)
                elif isinstance(other.ty, ir.TOpaque):
                    c = self.opaque("is_none", [other], ir.BOOL, loc)
                elif isinstance(other.ty, ir.TOption):
                    c = ir.Builtin(ir.BOOL, loc, "is_none", (other,))
                else:
                    c = ir.Lit(ir.BOOL, loc, False)  # a non-optional value is never None
                if isinstance(op, (ast.IsNot, ast.NotEq)):
                    c = ir.Unary(ir.BOOL, loc, "not", c)
                parts.append(c)
                left = right
                continue
            if isinstance(left.ty, ir.TClass) or isinstance(right.ty, ir.TClass):
                if not isinstance(op, (ast.Eq, ast.NotEq, ast.Is, ast.IsNot)) or left.ty != right.ty:
                    raise self.err(f"unsupported comparison of {left.ty} with {right.ty}", n)
                c = self.object_eq(left, right, isinstance(op, (ast.Is, ast.IsNot)), n, loc)
                parts.append(ir.Unary(ir.BOOL, loc, "not", c) if isinstance(op, (ast.NotEq, ast.IsNot)) else c)
                left = right
                continue
            if isinstance(op, (ast.In, ast.NotIn)) and isinstance(right.ty, (ir.TDict, ir.TOption)):
                d = self.need(right)
                if not isinstance(d.ty, ir.TDict):
                    raise self.err("'in' needs a list or dict on the right", n)
                k = self.fl.coerce(left, d.ty.key)
                if k.ty != d.ty.key:
                    raise self.err(f"'in' compares {left.ty} against keys of {d.ty}", n)
                c = ir.Builtin(ir.BOOL, loc, "dict_has", (d, k))
                if isinstance(op, ast.NotIn):
                    c = ir.Unary(ir.BOOL, loc, "not", c)
                parts.append(c)
                left = right
                continue
            if isinstance(op, (ast.Eq, ast.NotEq)) and (isinstance(left.ty, ir.TOption) or isinstance(right.ty, ir.TOption)):
                opt = _join_optional(left.ty, right.ty) or (left.ty if left.ty == right.ty else None)
                if opt is None:
                    raise self.err(f"comparing {left.ty} with {right.ty}", n)
                parts.append(ir.Binary(ir.BOOL, loc, "eq" if isinstance(op, ast.Eq) else "ne", self.fl.coerce(left, opt), self.fl.coerce(right, opt)))
                left = right
                continue
            if isinstance(op, (ast.In, ast.NotIn)):
                if not isinstance(right.ty, ir.TList):
                    raise self.err("'in' needs a list on the right", n)
                lhs = self.fl.coerce(left, right.ty.elem)
                if lhs.ty != right.ty.elem:
                    raise self.err(f"'in' compares {left.ty} against {right.ty}", n)
                c: ir.Expr = ir.Builtin(ir.BOOL, loc, "contains", (right, lhs))
                if isinstance(op, ast.NotIn):
                    c = ir.Unary(ir.BOOL, loc, "not", c)
                parts.append(c)
            elif type(op) in _CMP:
                name = _CMP[type(op)]
                l2, r2 = left, right
                if name not in ("eq", "ne"):
                    l2, r2 = self.need(left), self.need(right)
                if ir.is_numeric(l2.ty) and ir.is_numeric(r2.ty):
                    l2, r2, _ = self.numeric_pair(l2, r2, n)
                elif l2.ty != r2.ty and name in ("eq", "ne") and isinstance(l2.ty, ir.TList) and isinstance(r2.ty, ir.TList) and any(isinstance(x, ir.ListLit) and not x.elems for x in (l2, r2)):
                    # xs == []: the empty list at the other side's type
                    l2, r2 = (self.fl.coerce(l2, r2.ty), r2) if isinstance(l2, ir.ListLit) and not l2.elems else (l2, self.fl.coerce(r2, l2.ty))
                elif l2.ty != r2.ty and name in ("eq", "ne") and isinstance(l2.ty, ir.TList) and isinstance(r2.ty, ir.TList) and (_has_opaque(l2.ty) or _has_opaque(r2.ty)):
                    # a list of unchecked values, compared with a checked list
                    l2, r2 = (self.fl.coerce(l2, r2.ty), r2) if _has_opaque(l2.ty) else (l2, self.fl.coerce(r2, l2.ty))
                elif l2.ty != r2.ty:
                    raise self.err(f"comparing {left.ty} with {right.ty}", n)
                elif name not in ("eq", "ne") and not ir.is_numeric(l2.ty):
                    raise self.err(f"ordering comparison on {l2.ty} is not supported", n)
                elif isinstance(l2.ty, (ir.TDict,)):
                    raise self.err("comparing whole dicts is not supported", n)
                parts.append(ir.Binary(ir.BOOL, loc, name, l2, r2))
            else:
                raise self.err(f"unsupported comparison {type(op).__name__}", n)
            left = right
        out = parts[0]
        for p in parts[1:]:
            out = ir.Binary(ir.BOOL, loc, "and", out, p)
        return out

    def object_eq(self, a: ir.Expr, b: ir.Expr, identity: bool, n: ast.AST, loc: ir.Loc) -> ir.Expr:
        """``is`` compares references. ``==`` does too for plain classes, but
        a @dataclass compares its fields, and a custom __eq__ is unknown."""
        fe = self.fl.fe
        cls = a.ty.name  # type: ignore[union-attr]
        if identity:
            return ir.Binary(ir.BOOL, loc, "eq", a, b)
        if fe.member(cls, "__eq__") in fe.signatures or fe.custom_eq.get(cls):
            raise self.err(f"{cls} defines __eq__, which telic does not model; compare fields explicitly", n)
        if cls not in fe.dataclasses:
            return ir.Binary(ir.BOOL, loc, "eq", a, b)
        out: ir.Expr = ir.Lit(ir.BOOL, loc, True)
        for fname, fty in fe.classes[cls].fields:
            if isinstance(fty, (ir.TClass, ir.TDict)):
                raise self.err(f"== on {cls} compares field '{fname}' structurally, which is not modelled; compare fields explicitly", n)
            eq = ir.Binary(ir.BOOL, loc, "eq", ir.Field(fty, loc, a, fname), ir.Field(fty, loc, b, fname))
            out = eq if isinstance(out, ir.Lit) else ir.Binary(ir.BOOL, loc, "and", out, eq)
        return out

    # -- calls ----------------------------------------------------------

    def call(self, n: ast.Call, loc: ir.Loc, expect: ir.Type | None) -> ir.Expr:
        f = n.func
        fe = self.fl.fe
        if not self.spec:
            saved = dict(self.aliases)
            try:
                hof = self.higher_order(n, loc, expect)
            except LowerError:
                hof = None  # a body telic cannot lower in place is checked as a lambda of its own
                self.aliases = saved
            if hof is not None:
                return hof
        # Functions of another checked module imported as a whole.
        if isinstance(f, ast.Attribute) and isinstance(f.value, ast.Name) and f.value.id in fe.module_aliases and f.value.id not in self.fl.env:
            other = fe.module_aliases[f.value.id]
            key = f"{f.value.id}.{f.attr}"
            if f.attr in other.class_names and f.attr in other.module.classes:
                fe.class_names.add(f.attr)
                fe.linked_classes[f.attr] = other
                fe.foreign_classes[f.attr] = other.module.classes[f.attr]
                fe.module.class_origin[f.attr] = other.path
                fe.import_class_info(other, f.attr)
                return self.new(f.attr, n, loc)
            if f.attr in other.signatures and "." not in f.attr:
                if key not in fe.signatures:
                    fe.signatures[key] = other.signatures[f.attr]
                    for attr in ("defaults", "kwonly", "varargs", "wrapped"):
                        if f.attr in getattr(other, attr):
                            getattr(fe, attr)[key] = getattr(other, attr)[f.attr]
                    fe.module.imports[key] = (other.path, f.attr)
                return self.user_call(n, loc, key)
        # Module functions (math.sqrt, json.dumps, requests.get): unchecked.
        if isinstance(f, ast.Attribute) and isinstance(f.value, ast.Name) and f.value.id not in self.fl.env and f.value.id not in self.bound and (f.value.id in fe.modules or (f.value.id in fe.bound and f.value.id not in fe.class_names) or f.value.id in PY_GLOBALS) and f.value.id != "math":
            return self.extern(f"{f.value.id}.{f.attr}", [], n, loc, expect)
        if isinstance(f, ast.Attribute) and isinstance(f.value, ast.Name) and f.value.id == "math" and f.attr not in ("floor", "ceil", "trunc"):
            return self.extern(f"math.{f.attr}", [], n, loc, expect or ir.REAL)
        if isinstance(f, ast.Attribute) and isinstance(f.value, ast.Name) and f.value.id in fe.class_names and f.value.id not in self.fl.env:
            key = fe.member(f.value.id, f.attr)  # a static method
            if key not in fe.signatures and fe.library_derived(f.value.id):
                return self.extern(f"{f.value.id}.{f.attr}", [], n, loc, expect or ir.TOpaque(f"result of {f.value.id}.{f.attr}"))  # e.g. Model.from_orm
            if key not in fe.signatures:
                raise self.err(f"'{key}' is not a checked static method", n)
            return self.method_call(key, None, n.args, n.keywords, n, loc)
        if isinstance(f, ast.Attribute) and not (isinstance(f.value, ast.Name) and f.value.id == "math"):
            obj = self.expr(f.value)
            if isinstance(obj.ty, ir.TOption):
                obj = self.need(obj)
            if isinstance(obj.ty, ir.TEnum):
                return self.extern(f"{obj.ty.name}.{f.attr}", [obj], n, loc, expect)
            if isinstance(obj.ty, ir.TClass):
                key = fe.member(obj.ty.name, f.attr)
                if (key not in fe.signatures or key in fe.properties) and fe.library_derived(obj.ty.name):
                    return self.extern(f"{obj.ty.name}.{f.attr}", [obj], n, loc, expect)  # e.g. pydantic's .dict(), .copy()
                if key not in fe.signatures or key in fe.properties:
                    raise self.err(f"{obj.ty.name} has no checked method '{f.attr}'", n)
                return self.method_call(key, obj, n.args, n.keywords, n, loc)
            if isinstance(obj.ty, ir.TOpaque):
                return self.extern(f"{_desc(f.value)}.{f.attr}", [obj], n, loc, expect)
            if isinstance(obj.ty, ir.TStr):
                return self.str_method(obj, f.attr, n, loc, expect)
            if isinstance(obj.ty, ir.TList) and f.attr not in ("count", "append"):
                return self.list_method(obj, f.attr, n, loc, expect)
            if isinstance(obj.ty, ir.TDict) and f.attr in ("keys", "values", "items", "pop", "setdefault", "update", "clear") :
                return self.dict_method(obj, f.attr, n, loc, expect)
            if isinstance(obj.ty, ir.TDict):
                if n.keywords:
                    raise self.err("keyword arguments to dict methods are not supported", n)
                if f.attr == "get":
                    args = [self.expr(a) for a in n.args]
                    if len(args) not in (1, 2):
                        raise self.err("d.get(k) or d.get(k, default)", n)
                    k = self.fl.coerce(args[0], obj.ty.key)
                    if len(args) == 1:
                        return ir.Builtin(ir.TOption(obj.ty.val), loc, "dict_get_opt", (obj, k))
                    dv = args[1]
                    if dv.ty == ir.NONE:
                        return ir.Builtin(ir.TOption(obj.ty.val), loc, "dict_get_opt", (obj, k))
                    dv = self.fl.coerce(dv, obj.ty.val)
                    if dv.ty != obj.ty.val:
                        raise self.err(f"default of d.get must be {obj.ty.val}", n)
                    return ir.Builtin(obj.ty.val, loc, "dict_get_or", (obj, k, dv))
                if f.attr == "copy" and not n.args:
                    return ir.Builtin(obj.ty, loc, "dict_copy", (obj,))
                raise self.err(f"dict method '.{f.attr}(...)' is not supported yet", n)
        if n.keywords and isinstance(n.func, ast.Name) and n.func.id in ("min", "max", "sum", "sorted", "round") and n.func.id not in fe.bound:
            return self.extern(n.func.id, [], n, loc, expect)
        if n.keywords and isinstance(n.func, ast.Name) and n.func.id in BUILTINS and n.func.id not in fe.bound and n.func.id not in ("print",):
            raise self.err(f"keyword arguments to {n.func.id}() are not modelled", n)
        if isinstance(f, ast.Attribute):
            if isinstance(f.value, ast.Name) and f.value.id == "math" and f.attr in ("floor", "ceil", "trunc"):
                (x,) = self._args(n, 1)
                if isinstance(x.ty, ir.TInt):
                    return x
                if not isinstance(x.ty, ir.TReal):
                    raise self.err(f"math.{f.attr} needs a number", n)
                return ir.Builtin(ir.INT, loc, f.attr, (x,))
            if f.attr == "count":
                seq = self.expr(f.value)
                if not isinstance(seq.ty, ir.TList):
                    raise self.err(".count needs a list", n)
                (v,) = self._args(n, 1)
                return ir.Builtin(ir.INT, loc, "count", (seq, self.fl.coerce(v, seq.ty.elem)))
            raise self.err(f"unsupported method call '.{f.attr}(...)'", n)
        if not isinstance(f, ast.Name):
            if self.spec:
                raise self.err("unsupported call", n)
            return self.extern(_desc(f), [self.fl.coerce(self.expr(f), ir.TOpaque(""))], n, loc, expect)
        name = f.id
        if name in fe.class_names and name not in self.fl.env:
            return self.new(name, n, loc)
        if name == "dict" and name not in fe.bound and not n.args and not n.keywords:
            dt = expect if isinstance(expect, ir.TDict) else ir.TDict(ir.NONE, ir.NONE)
            return ir.Builtin(dt, loc, "dict_lit", ())
        if name in self.fl.fe.signatures:
            return self.user_call(n, loc, name)
        if name in BUILTINS and name in self.fl.fe.bound:
            raise self.err(f"'{name}' is rebound in this module, so telic cannot assume the builtin", n)
        if self.spec and name == "old":
            if self.result_ty is None and not self.allow_old:
                raise self.err("old(...) is only allowed in '@ensures' and loop invariants", n)
            (x,) = self._args(n, 1)
            return ir.Old(x.ty, loc, x)
        if self.spec and name == "implies":
            if len(n.args) != 2:
                raise self.err("implies() takes two arguments", n)
            return ir.Binary(ir.BOOL, loc, "implies", self.cond(n.args[0]), self.cond(n.args[1]))
        if name in ("all", "any"):
            return self.quant(n, loc, "forall" if name == "all" else "exists")
        if name == "len":
            (x,) = self._args(n, 1)
            x = self.need(x)
            if x.ty == ir.STR:
                return ir.Builtin(ir.INT, loc, "str_len", (x,))
            if isinstance(x.ty, (ir.TOpaque, ir.TDict)):
                return self.opaque("len", [x], ir.INT, loc)
            if not isinstance(x.ty, ir.TList):
                raise self.err("len() is supported on lists", n)
            return ir.Builtin(ir.INT, loc, "len", (x,))
        if name in ("abs", "round", "min", "max", "sum") and any(isinstance(self.expr(a).ty, ir.TOpaque) for a in n.args if not isinstance(a, (ast.GeneratorExp, ast.ListComp)) and not (name == "sum" and isinstance(a, ast.List))):
            return self.opaque(name, [self.expr(a) for a in n.args], ir.TOpaque(""), loc)
        if name == "abs":
            (x,) = self._args(n, 1)
            if not ir.is_numeric(x.ty):
                raise self.err("abs() needs a number", n)
            return ir.Builtin(x.ty, loc, "abs", (x,))
        if name in ("min", "max"):
            args = [self.expr(a) for a in n.args]
            if len(args) == 1 and isinstance(args[0].ty, ir.TList):
                raise self.err(f"{name}() over a list is not supported; write a loop", n)
            if len(args) < 2 or not all(ir.is_numeric(a.ty) for a in args):
                raise self.err(f"{name}() needs two or more numbers", n)
            t = ir.REAL if any(isinstance(a.ty, ir.TReal) for a in args) else ir.INT
            return ir.Builtin(t, loc, f"py_{name}", tuple(self.fl.coerce(a, t) for a in args))
        if name == "sum":
            (x,) = self._args(n, 1)
            if not (isinstance(x.ty, ir.TList) and ir.is_numeric(x.ty.elem)):
                raise self.err("sum() needs a list of numbers", n)
            total = ir.sum_of(x, loc)
            if isinstance(x.ty.elem, ir.TReal) and sys.implementation.name == "cpython":
                return ir.Builtin(total.ty, loc, f"py_sum_cpython_{sys.version_info.major}_{sys.version_info.minor}", total.args)
            return total
        if name == "float":
            (x,) = self._args(n, 1)
            if x.ty == ir.STR:
                return ir.Builtin(ir.REAL, loc, "py_float_parse", (x, ir.Lit(ir.BOOL, loc, self.fl.try_depth > 0)))
            if not ir.is_numeric(x.ty):
                return self.extern("float", [x], None, loc, ir.REAL)
            return self.fl.coerce(x, ir.REAL)
        if name == "int":
            (x,) = self._args(n, 1)
            if isinstance(x.ty, ir.TInt):
                return x
            if isinstance(x.ty, ir.TReal):
                return ir.Builtin(ir.INT, loc, "trunc", (x,))
            if x.ty == ir.STR and not n.keywords:
                return ir.Builtin(ir.INT, loc, "py_int_parse", (x, ir.Lit(ir.BOOL, loc, self.fl.try_depth > 0)))
            return self.extern("int", [x], None, loc, ir.INT)  # int(x, base), int(obj): may raise
        if name == "round":
            if len(n.args) != 1:
                return self.extern("round", [], n, loc, ir.REAL)
            (x,) = self._args(n, 1)
            if isinstance(x.ty, ir.TInt):
                return x
            if isinstance(x.ty, ir.TReal):
                return ir.Builtin(ir.INT, loc, "round_even", (x,))
            raise self.err("round() needs a number", n)
        if name == "bool":
            (x,) = self._args(n, 1)
            return self.truthy(x, n)
        if name == "list" and name not in fe.bound and not n.keywords and len(n.args) == 1:
            x = self.expr(n.args[0])
            if isinstance(x.ty, ir.TList):
                return ir.Builtin(x.ty, loc, "slice", (x, ir.Lit(ir.NONE, loc, None), ir.Lit(ir.NONE, loc, None)))
        if name == "range" and not self.spec and not n.keywords and len(n.args) in (1, 2):
            bounds = [self.expr(a) for a in n.args]
            if all(isinstance(b.ty, ir.TInt) for b in bounds):
                lo, hi = (ir.Lit(ir.INT, loc, 0), bounds[0]) if len(bounds) == 1 else bounds
                return ir.Builtin(ir.TList(ir.INT), loc, "range_list", (lo, hi))
        if name in self.fl.fe.module.records:
            rec = self.fl.fe.module.records[name]
            vals: dict[str, ir.Expr] = {}
            if len(n.args) > len(rec.fields):
                raise self.err(f"too many arguments to {name}", n)
            for (fname, fty), a in zip(rec.fields, n.args):
                vals[fname] = self.fl.coerce(self.expr(a, fty), fty)
            for kw in n.keywords:
                if kw.arg is None or rec.field_type(kw.arg) is None:
                    raise self.err(f"{name} has no field '{kw.arg}'", n)
                ft = rec.field_type(kw.arg)
                vals[kw.arg] = self.fl.coerce(self.expr(kw.value, ft), ft)  # type: ignore[arg-type]
            missing = [f for f, _ in rec.fields if f not in vals]
            if missing:
                raise self.err(f"{name}(...) is missing {', '.join(missing)}", n)
            for fname, fty in rec.fields:
                if vals[fname].ty != fty:
                    raise self.err(f"field '{fname}' of {name} expects {fty}, got {vals[fname].ty}", n)
            return ir.RecordLit(rec, loc, tuple((f, vals[f]) for f, _ in rec.fields))
        if name == "str" and name not in fe.bound:
            (x,) = self._args(n, 1)
            if x.ty == ir.STR:
                return x
            if x.ty == ir.INT:
                return ir.Builtin(ir.STR, loc, "str_of_int", (x,))
            if isinstance(x.ty, ir.TEnum):
                return ir.Builtin(ir.STR, loc, "str_fn", (ir.Lit(ir.STR, loc, "str"), ir.Builtin(ir.STR, loc, "enum_name", (x,))))
            return ir.Builtin(ir.STR, loc, "str_fn", (ir.Lit(ir.STR, loc, "str"), self.fl.coerce(x, ir.TOpaque("")) if isinstance(x.ty, (ir.TList, ir.TDict, ir.TOption)) else x))
        if name == "isinstance" and name not in fe.bound:
            x = self.expr(n.args[0])
            # isinstance(x, (A, B)) is isinstance(x, A) or isinstance(x, B): one predicate per class
            classes = n.args[1].elts if isinstance(n.args[1], ast.Tuple) and n.args[1].elts else [n.args[1]]
            out = self.opaque("isinstance", [x, ir.Lit(ir.STR, loc, ast.unparse(classes[0]))], ir.BOOL, loc)
            for c in classes[1:]:
                out = ir.Binary(ir.BOOL, loc, "or", out, self.opaque("isinstance", [x, ir.Lit(ir.STR, loc, ast.unparse(c))], ir.BOOL, loc))
            return out
        if name in fe.signatures and name not in self.fl.env:
            return self.user_call(n, loc, name)
        if not self.spec and name in self.fl.closures:
            captured = [ir.Var(self.fl.env[c], loc, c) for c in self.fl.closures[name] if isinstance(self.fl.env.get(c), (ir.TList, ir.TDict, ir.TClass, ir.TOpaque))]
            return self.extern(f"local {name}", captured, n, loc, expect)
        if not self.spec:
            return self.extern(name, [], n, loc, expect)
        return self.user_call(n, loc, name)

    def higher_order(self, n: ast.Call, loc: ir.Loc, expect: ir.Type | None) -> ir.Expr | None:
        """Library functions that call what they are handed on the elements
        of an iterable (``map``, ``filter``, ``sorted``/``min``/``max`` and
        ``list.sort`` by ``key``, ``functools.reduce``): the callback's body
        runs on each element, so its obligations are checked for every
        element, where it is called, and its effects are this call's."""
        fe, f = self.fl.fe, n.func
        free = lambda name: name not in fe.bound and name not in self.fl.env and name not in self.bound  # noqa: E731
        kw = {k.arg: k.value for k in n.keywords}
        name = f.id if isinstance(f, ast.Name) else ""
        if name in ("map", "filter") and free(name) and len(n.args) == 2 and not n.keywords:
            got = self.element_body(n.args[0], 1)
            if got is None:
                return None
            (p,), body = got
            gen = ast.comprehension(ast.Name(p, ast.Store()), n.args[1], [body] if name == "filter" else [], 0)
            elt = body if name == "map" else ast.Name(p, ast.Load())
            return self.comprehension(_located(ast.GeneratorExp(elt, [gen]), n), loc)
        if name in ("sorted", "min", "max") and free(name) and len(n.args) == 1 and "key" in kw and None not in kw:
            got = self.element_body(kw["key"], 1)
            if got is None:
                return None
            rest = [self.expr(v) for k, v in kw.items() if k != "key"]
            return self.extern_with(name, [self.read_only(self.expr(n.args[0])), self.each_of(got, n.args[0], n, loc), *rest], loc, expect)
        if isinstance(f, ast.Attribute) and f.attr == "sort" and not n.args and "key" in kw and None not in kw:
            obj = self.expr(f.value)
            got = self.element_body(kw["key"], 1)
            if not isinstance(obj, ir.Var) or not isinstance(obj.ty, ir.TList) or got is None:
                return None
            rest = [self.expr(v) for k, v in kw.items() if k != "key"]
            return ir.Extern(ir.TOpaque(""), loc, "list.sort", (obj, self.each_of(got, f.value, n, loc), *rest))
        reduce = (name == "reduce" and any(m == "functools" and a == "reduce" and (al or a) == name for m, _, a, al in fe.imports) and name not in self.fl.env) or (
            isinstance(f, ast.Attribute) and f.attr == "reduce" and isinstance(f.value, ast.Name) and f.value.id == "functools" and f.value.id in fe.modules and f.value.id not in self.fl.env)
        if reduce and len(n.args) in (2, 3) and not n.keywords:
            got = self.element_body(n.args[0], 2)
            if got is None:
                return None
            (acc, p), body = got
            xs = self.expr(n.args[1])
            init = self.expr(n.args[2]) if len(n.args) == 3 else None
            aty = init.ty if init is not None else xs.ty.elem if isinstance(xs.ty, ir.TList) else ir.TOpaque("")
            if not isinstance(aty, (ir.TInt, ir.TReal, ir.TBool, ir.TStr)):
                aty = ir.TOpaque("")
            while True:
                # what the earlier elements left: any value of the accumulator's type
                self.aliases[acc] = ir.Builtin(aty, loc, "opaque_op", (ir.Lit(ir.STR, loc, f"reduce accumulator {loc.line}:{loc.col}"),))
                try:
                    check = self.each_of(((p,), body), n.args[1], n, loc)
                finally:
                    self.aliases.pop(acc, None)
                assert isinstance(check, ir.Builtin)
                returns = check.ty.elem if isinstance(check.ty, ir.TList) else check.args[2].ty
                if isinstance(aty, ir.TOpaque) or returns == aty:
                    break
                aty = ir.TOpaque("")  # the callback returns another type than it started from
            return self.extern_with("functools.reduce", [self.read_only(xs), check] + ([init] if init is not None else []), loc, expect)
        return None

    def element_body(self, cb: ast.expr, k: int) -> tuple[tuple[str, ...], ast.expr] | None:
        """A callback of ``k`` positional arguments as (parameter names,
        body): a lambda, or a checked function of this module named as a
        value (its call then carries its precondition)."""
        fe = self.fl.fe
        if isinstance(cb, ast.Lambda):
            a = cb.args
            if len(a.args) != k or a.posonlyargs or a.kwonlyargs or a.vararg or a.kwarg or a.defaults:
                return None
            return tuple(x.arg for x in a.args), cb.body
        if isinstance(cb, ast.Name) and cb.id in fe.signatures and cb.id not in self.fl.env and cb.id not in self.bound and cb.id not in fe.wrapped and cb.id not in fe.class_names:
            params = fe.signatures[cb.id][0]
            if len(params) != k or any(fe.varargs.get(cb.id, ())):
                return None
            names = tuple(self.fl.fresh("arg") for _ in range(k))
            return names, _located(ast.Call(ast.Name(cb.id, ast.Load()), [ast.Name(x, ast.Load()) for x in names], []), cb)
        return None

    def each_of(self, got: tuple[tuple[str, ...], ast.expr], xs: ast.expr, n: ast.AST, loc: ir.Loc) -> ir.Expr:
        """A callback's body run on every element of ``xs``."""
        (p, *_), body = got
        return self.comprehension(_located(ast.GeneratorExp(body, [ast.comprehension(ast.Name(p, ast.Store()), xs, [], 0)]), n), loc)

    def read_only(self, x: ir.Expr) -> ir.Expr:
        """A list the library only reads: handed over as a value, so the
        call leaves the variable alone."""
        return self.fl.coerce(x, ir.TOpaque("")) if isinstance(x, ir.Var) and isinstance(x.ty, ir.TList) else x

    def extern_with(self, name: str, args: list[ir.Expr], loc: ir.Loc, expect: ir.Type | None) -> ir.Expr:
        ty = expect if expect is not None and not isinstance(expect, ir.TOpaque) else ir.TOpaque(f"result of {name}")
        return ir.Extern(ty, loc, name, tuple(args))

    def user_call(self, n: ast.Call, loc: ir.Loc, name: str) -> ir.Expr:
        sig = self.fl.fe.signatures.get(name)
        if sig is None:
            raise self.err(f"call to '{name}', which telic cannot see (define it in a checked file with a contract)", n)
        params, ret = sig
        args = self.bind_args(name, params, n.args, n.keywords, n)
        if name in self.fl.fe.wrapped:
            return ir.Extern(ret, loc, f"@{self.fl.fe.wrapped[name]} {name}", tuple(args))
        return ir.Call(ret, loc, name, tuple(args))

    def bind_unknown(self, key: str, params: list[ir.Param], pos: list[ast.expr], kws: list[ast.keyword], n: ast.AST) -> list[ir.Expr]:
        """``f(*xs)`` / ``f(**d)``: arguments before the first star bind as
        usual; every other parameter gets some value of its type from the
        unpacked data (an assumption, shown in the trusted base)."""
        loc = _loc(n)
        star, dstar = self.fl.fe.varargs.get(key, (None, None))
        plain = [p for p in params if p.name not in (star, dstar)]
        given: dict[str, ir.Expr] = {}
        for p, a in zip(plain, pos):
            if isinstance(a, ast.Starred):
                break
            given[p.name] = self.fl.coerce(self.expr(a, p.ty), p.ty)
        for k in kws:
            if k.arg is not None and k.arg in {p.name for p in plain}:
                p = next(p for p in plain if p.name == k.arg)
                given[k.arg] = self.fl.coerce(self.expr(k.value, p.ty), p.ty)
        unpacked = [self.expr(a.value) for a in pos if isinstance(a, ast.Starred)] + [self.expr(k.value) for k in kws if k.arg is None]
        out = []
        for p in plain:
            if p.name in given:
                out.append(given[p.name])
            else:
                raw = self.opaque(f"arg:{p.name}", unpacked, ir.TOpaque(""), loc)
                out.append(ir.Builtin(p.ty, loc, "from_opaque", (raw,)))
        return out

    def bind_args(self, key: str, params: list[ir.Param], pos: list[ast.expr], kws: list[ast.keyword], n: ast.AST) -> list[ir.Expr]:
        """Match positional and keyword arguments to parameters, filling in
        defaults; then lower and type-check each argument."""
        fe = self.fl.fe
        defaults = fe.defaults.get(key, {})
        kwonly = fe.kwonly.get(key, set())
        star, dstar = fe.varargs.get(key, (None, None))
        chosen: dict[str, ast.expr] = {}
        positional = [p for p in params if p.name not in kwonly and p.name not in (star, dstar)]
        if any(isinstance(a, ast.Starred) for a in pos) or any(k.arg is None for k in kws):
            return self.bind_unknown(key, params, pos, kws, n)
        extra_pos = pos[len(positional):]
        if extra_pos and star is None:
            raise self.err(f"'{key}' takes {len(positional)} positional arguments, got {len(pos)}", n)
        for p, a in zip(positional, pos):
            chosen[p.name] = a
        names = {p.name for p in params} - {star, dstar}
        extra_kw: list[ast.keyword] = []
        for k in kws:
            if k.arg not in names:
                if dstar is None:
                    raise self.err(f"'{key}' has no parameter '{k.arg}'", n)
                extra_kw.append(k)
                continue
            if k.arg in chosen:
                raise self.err(f"'{key}' got two values for '{k.arg}'", n)
            chosen[k.arg] = k.value  # type: ignore[index]
        loc = self.loc(n)
        packed: dict[str, ir.Expr] = {}
        if star is not None:
            packed[star] = self.opaque("tuple", [self.expr(a) for a in extra_pos], ir.TOpaque("*args"), loc)
        if dstar is not None:
            packed[dstar] = self.opaque("dict", [self.expr(k.value) for k in extra_kw], ir.TOpaque("**kwargs"), loc)
        out = []
        for p in params:
            if p.name in packed:
                out.append(packed[p.name])
                continue
            a = chosen.get(p.name, defaults.get(p.name))
            if a is None and p.name in defaults:
                out.append(ir.Extern(p.ty, self.loc(n), f"default of '{p.name}'", ()))  # computed default
                continue
            if a is None:
                raise self.err(f"'{key}' is missing argument '{p.name}'", n)
            v = self.fl.coerce(self.expr(a, p.ty), p.ty)
            if v.ty != p.ty and not (isinstance(p.ty, ir.TList) and isinstance(v.ty, ir.TList) and v.ty.elem == ir.NONE):
                raise self.err(f"argument '{p.name}' of '{key}' expects {p.ty}, got {v.ty}", n)
            out.append(v)
        return out

    def method_call(self, key: str, obj: ir.Expr | None, pos: list[ast.expr], kws: list[ast.keyword], n: ast.AST, loc: ir.Loc) -> ir.Expr:
        fe = self.fl.fe
        params, ret = fe.signatures[key]
        if key in fe.classmethods:
            cls_v = self.opaque("class", [ir.Lit(ir.STR, loc, key.split(".")[0])], ir.TOpaque("cls"), loc)
            args = [cls_v] + self.bind_args(key, params[1:], pos, kws, n)
        elif obj is None:
            args = self.bind_args(key, params, pos, kws, n)
        else:
            args = [obj] + self.bind_args(key, params[1:], pos, kws, n)
        if key in fe.wrapped:
            return ir.Extern(ret, loc, f"@{fe.wrapped[key]} {key}", tuple(args))
        return ir.Call(ret, loc, key, tuple(args))

    def new(self, cls: str, n: ast.Call, loc: ir.Loc) -> ir.Expr:
        fe = self.fl.fe
        if self.spec:
            raise self.err("specifications cannot create objects", n)
        init = fe.member(cls, "__init__")
        if init in fe.signatures:
            params, _ = fe.signatures[init]
            args = self.bind_args(init, params[1:], n.args, n.keywords, n)
        elif cls in fe.dataclass_defaults:
            decl = fe.classes[cls]
            params = [ir.Param(f, t) for f, t in decl.fields]
            fe.defaults.setdefault(f"{cls}()", fe.dataclass_defaults[cls])
            args = self.bind_args(f"{cls}()", params, n.args, n.keywords, n)
            for (fname, fty), a in zip(decl.fields, args):
                if isinstance(fty, (ir.TList, ir.TDict)) and not fresh_list(a) and not self.fl.moved(a, n):
                    raise self.err(f"passing an existing {fty} as field '{fname}' would alias it; pass a copy", n)
        else:
            if n.args or n.keywords:
                raise self.err(f"{cls} has no __init__ taking arguments", n)
            args = []
            if fe.classes[cls].fields:
                raise self.err(f"{cls} has fields but no __init__ to set them; add one (or make it a @dataclass)", n)
        return ir.New(ir.TClass(cls), loc, cls, tuple(args))

    def _args(self, n: ast.Call, k: int) -> list[ir.Expr]:
        if len(n.args) != k:
            raise self.err(f"expected {k} argument(s)", n)
        return [self.expr(a) for a in n.args]

    # -- gradual fallbacks ------------------------------------------------

    def value_boolop(self, op: str, vals: list[ir.Expr], n: ast.AST, loc: ir.Loc) -> ir.Expr:
        #@ requires len(vals) > 0
        """``a or b`` is ``a`` if ``a`` is truthy, else ``b`` (``and`` the
        reverse): the usual defaulting idiom."""
        out = vals[-1]
        for v in reversed(vals[:-1]):
            if op == "or":
                # x or default: when x is truthy its value (unwrapped from an optional)
                val = ir.Builtin(v.ty.inner, loc, "unwrap", (v,)) if isinstance(v.ty, ir.TOption) and not isinstance(out.ty, ir.TOption) else v
                if val.ty != out.ty:
                    val, out = self.fl.coerce(val, out.ty), out
                if val.ty != out.ty:
                    raise self.err(f"'or' of {v.ty} and {out.ty}: the operands need one type", n)
                out = ir.Ite(out.ty, loc, self.truthy(v, n), val, out)
            else:
                if isinstance(v.ty, ir.TOption) and isinstance(v.ty.inner, ir.TClass) and not self.fl.fe.custom_bool.get(v.ty.inner.name):
                    # obj and obj.attr: None when obj is None
                    rty = out.ty if isinstance(out.ty, ir.TOption) else ir.TOption(out.ty)
                    out = ir.Ite(rty, loc, ir.Builtin(ir.BOOL, loc, "is_none", (v,)), ir.Lit(rty, loc, None), self.fl.coerce(out, rty))
                elif v.ty == out.ty:
                    out = ir.Ite(out.ty, loc, self.truthy(v, n), out, v)
                else:
                    raise self.err(f"'and' of {v.ty} and {out.ty} returns either operand; compare explicitly", n)
        return out

    def opaque(self, op: str, parts: list[ir.Expr], ty: ir.Type, loc: ir.Loc) -> ir.Expr:
        """An operation telic does not interpret: deterministic, unknown result."""
        return ir.Builtin(ty, loc, "opaque_op", (ir.Lit(ir.STR, loc, op), *parts))

    def extern(self, name: str, pre: list[ir.Expr], n: ast.Call | None, loc: ir.Loc, expect: ir.Type | None) -> ir.Expr:
        """A call into unchecked code."""
        if self.spec:
            raise self.err(f"specifications cannot call unchecked code ('{name}')", n or ast.Constant(0))
        args = list(pre)
        if n is not None:
            for a in n.args:
                if isinstance(a, ast.Starred):
                    a = a.value
                args.append(self.expr(a))
            for k in n.keywords:
                args.append(self.expr(k.value))
        ty = expect if expect is not None and not isinstance(expect, ir.TOpaque) else ir.TOpaque(f"result of {name}")
        return ir.Extern(ty, loc, name, tuple(args))

    def fstring(self, n: ast.JoinedStr, loc: ir.Loc) -> ir.Expr:
        out: ir.Expr | None = None
        for part in n.values:
            if isinstance(part, ast.Constant):
                piece: ir.Expr = ir.Lit(ir.STR, loc, str(part.value))
            else:
                assert isinstance(part, ast.FormattedValue)
                v = self.expr(part.value)
                if v.ty == ir.STR and part.conversion == -1 and part.format_spec is None:
                    piece = v
                elif v.ty == ir.INT and part.conversion == -1 and part.format_spec is None:
                    piece = ir.Builtin(ir.STR, loc, "str_of_int", (v,))
                else:
                    spec = ast.unparse(part.format_spec) if part.format_spec is not None else ""
                    if isinstance(v.ty, (ir.TList, ir.TDict, ir.TOption, ir.TClass, ir.TEnum)):
                        v = self.opaque("repr", [v], ir.TOpaque(""), loc) if not isinstance(v.ty, ir.TEnum) else ir.Builtin(ir.STR, loc, "enum_name", (v,))
                    piece = ir.Builtin(ir.STR, loc, "str_fn", (ir.Lit(ir.STR, loc, f"format{part.conversion}{spec}"), v))
            out = piece if out is None else ir.Builtin(ir.STR, loc, "str_concat", (out, piece))
        return out if out is not None else ir.Lit(ir.STR, loc, "")

    def str_method(self, obj: ir.Expr, attr: str, n: ast.Call, loc: ir.Loc, expect: ir.Type | None) -> ir.Expr:
        args = [self.expr(a) for a in n.args]
        if n.keywords:
            return self.extern(f"str.{attr}", [obj], n, loc, expect)
        if attr in ("startswith", "endswith") and len(args) == 1 and args[0].ty == ir.STR:
            return ir.Builtin(ir.BOOL, loc, f"str_{attr}", (obj, args[0]))
        if attr == "find" and len(args) == 1 and args[0].ty == ir.STR:
            return ir.Builtin(ir.INT, loc, "str_find", (obj, args[0]))
        if attr in ("lower", "upper", "strip", "lstrip", "rstrip", "title", "capitalize", "casefold", "replace", "zfill", "ljust", "rjust", "center", "removeprefix", "removesuffix", "format", "join") and all(not isinstance(a.ty, (ir.TList, ir.TDict)) or attr == "join" for a in args):
            parts = [self.fl.coerce(a, ir.TOpaque("")) if isinstance(a.ty, (ir.TList, ir.TDict, ir.TOption, ir.TClass)) else a for a in args]
            return ir.Builtin(ir.STR, loc, "str_fn", (ir.Lit(ir.STR, loc, attr), obj, *parts))
        if attr in ("isdigit", "isalpha", "isalnum", "isspace", "islower", "isupper", "isnumeric", "isdecimal", "isidentifier"):
            return ir.Builtin(ir.BOOL, loc, "str_fn", (ir.Lit(ir.STR, loc, attr), obj))
        if attr in ("split", "splitlines", "rsplit"):
            return self.extern(f"str.{attr}", [obj], n, loc, ir.TList(ir.STR))
        if attr in ("count", "index", "rfind"):
            return self.extern(f"str.{attr}", [obj], n, loc, ir.INT)
        return self.extern(f"str.{attr}", [obj], n, loc, expect)

    def list_method(self, obj: ir.Expr, attr: str, n: ast.Call, loc: ir.Loc, expect: ir.Type | None) -> ir.Expr:
        assert isinstance(obj.ty, ir.TList)
        res = {"pop": obj.ty.elem, "index": ir.INT, "copy": obj.ty}.get(attr, ir.NONE)
        if attr == "copy" and not n.args:
            return ir.Builtin(obj.ty, loc, "list_copy", (obj,))
        if not isinstance(obj, ir.Var) and attr not in ("index",):
            raise self.err(f"'.{attr}()' on a list that is not a variable is not tracked", n)
        return self.extern(f"list.{attr}", [obj], n, loc, res if res != ir.NONE else ir.TOpaque(""))

    def dict_method(self, obj: ir.Expr, attr: str, n: ast.Call, loc: ir.Loc, expect: ir.Type | None) -> ir.Expr:
        assert isinstance(obj.ty, ir.TDict)
        if attr == "keys" and not n.args:
            return ir.Builtin(ir.TList(obj.ty.key), loc, "dict_keys", (obj,))
        if attr == "values" and not n.args:
            return ir.Builtin(ir.TList(obj.ty.val), loc, "dict_values", (obj,))
        if not isinstance(obj, ir.Var):
            raise self.err(f"'.{attr}()' on a dict that is not a variable is not tracked", n)
        res = {"pop": obj.ty.val, "setdefault": obj.ty.val}.get(attr)
        return self.extern(f"dict.{attr}", [obj], n, loc, res or ir.TOpaque(""))

    def comprehension(self, n: ast.GeneratorExp | ast.ListComp | ast.SetComp | ast.DictComp, loc: ir.Loc) -> ir.Expr:
        """``[f(x) for x in xs if c(x)]``: a new list, precise for one 'for'
        and a scalar element (element i is f(xs[i]) when the body is pure).
        Other shapes are an unknown value whose every element still carries
        its obligations and effects."""
        saved, saved_aliases = dict(self.bound), dict(self.aliases)
        try:
            gens: list[tuple[ir.Expr, str, ir.Expr | None]] = []
            for gen in n.generators:
                if gen.is_async:
                    raise self.err("async comprehensions are not modelled", n)
                seq, elem = self.comp_source(gen, loc)
                cond: ir.Expr | None = None
                for c in gen.ifs:
                    cc = self.cond(c)
                    cond = cc if cond is None else ir.Binary(ir.BOOL, loc, "and", cond, cc)
                gens.append((seq, elem, cond))
            if isinstance(n, ast.DictComp):
                body = self.opaque("entry", [self.expr(n.key), self.expr(n.value)], ir.TOpaque(""), loc)
            else:
                body = self.expr(n.elt)
        finally:
            self.bound, self.aliases = saved, saved_aliases
        if len(gens) == 1 and isinstance(n, (ast.GeneratorExp, ast.ListComp)) and not isinstance(body.ty, (ir.TList, ir.TDict)):
            seq, elem, cond = gens[0]
            return ir.Builtin(ir.TList(body.ty), loc, "comp", (seq, ir.Lit(ir.STR, loc, elem), body) + ((cond,) if cond is not None else ()))
        out = body
        for seq, elem, cond in reversed(gens):
            out = ir.Builtin(ir.TOpaque(""), loc, "each", (seq, ir.Lit(ir.STR, loc, elem), out) + ((cond,) if cond is not None else ()))
        return out

    def comp_source(self, gen: ast.comprehension, loc: ir.Loc) -> tuple[ir.Expr, str]:
        """What one 'for' clause iterates, as a list, and the name bound to
        its element; other target names become aliases for expressions
        over that element."""
        it, tgt = gen.iter, gen.target
        names = [t.id for t in tgt.elts] if isinstance(tgt, ast.Tuple) and all(isinstance(t, ast.Name) for t in tgt.elts) else None  # type: ignore[attr-defined]
        if not isinstance(tgt, ast.Name) and names is None:
            raise self.err("comprehension targets must be a name or a tuple of names", gen.target)
        builtin = isinstance(it, ast.Call) and isinstance(it.func, ast.Name) and it.func.id not in self.fl.fe.bound and it.func.id not in self.fl.env and not it.keywords
        bounds = [self.need(self.expr(a)) for a in it.args] if builtin and it.func.id == "range" and isinstance(tgt, ast.Name) else []  # type: ignore[union-attr]
        if len(bounds) in (1, 2) and all(b.ty == ir.INT for b in bounds):
            lo, hi = (ir.Lit(ir.INT, loc, 0), bounds[0]) if len(bounds) == 1 else bounds
            self.bind(tgt.id, ir.INT)  # type: ignore[union-attr]
            return ir.Builtin(ir.TList(ir.INT), loc, "range_list", (lo, hi)), tgt.id  # type: ignore[union-attr]
        if builtin and it.func.id == "enumerate" and names is not None and len(names) == 2 and len(it.args) == 1:  # type: ignore[union-attr]
            xs = self.expr(it.args[0])  # type: ignore[union-attr]
            # the list is read again for each element: only when that reads the same list
            if isinstance(xs.ty, ir.TList) and not any(isinstance(x, (ir.Extern, ir.Call, ir.New)) for x in ir.walk_expr(xs)):
                i, x = names
                self.bind(i, ir.INT)
                self.aliases[x] = ir.Index(xs.ty.elem, loc, xs, ir.Var(ir.INT, loc, i), wrap=False)
                return ir.Builtin(ir.TList(ir.INT), loc, "range_list", (ir.Lit(ir.INT, loc, 0), ir.Builtin(ir.INT, loc, "len", (xs,)))), i
        if isinstance(it, ast.Call) and isinstance(it.func, ast.Attribute) and it.func.attr == "items" and not it.args and names is not None and len(names) == 2:
            d = self.expr(it.func.value)
            # the dict is read again for each element: only when that reads the same dict
            if isinstance(d.ty, ir.TDict) and ir.NONE not in (d.ty.key, d.ty.val) and not any(isinstance(x, (ir.Extern, ir.Call, ir.New)) for x in ir.walk_expr(d)):
                k, v = names
                self.bind(k, d.ty.key)
                self.aliases[v] = ir.Index(d.ty.val, loc, d, ir.Var(d.ty.key, loc, k), wrap=False)
                return ir.Builtin(ir.TList(d.ty.key), loc, "dict_keys", (d,)), k
            seq = self.opaque("items", [d], ir.TOpaque(""), loc) if isinstance(d.ty, ir.TDict) else self.expr(it)
        else:
            seq = self.expr(it)
        if isinstance(seq.ty, ir.TDict):
            seq = ir.Builtin(ir.TList(seq.ty.key), loc, "dict_keys", (seq,))
        elif not isinstance(seq.ty, (ir.TList, ir.TOpaque)):
            seq = self.opaque("iter", [seq], ir.TOpaque(""), loc)  # a string, a generator, ...: unknown elements
        if isinstance(seq.ty, ir.TOpaque) or (isinstance(seq.ty, ir.TList) and seq.ty.elem == ir.NONE):
            seq = self.fl.coerce(seq, ir.TList(ir.TOpaque("")))
        if isinstance(tgt, ast.Name):
            self.bind(tgt.id, seq.ty.elem)
            return seq, tgt.id
        assert names is not None
        if not isinstance(seq.ty.elem, ir.TOpaque):
            raise self.err(f"unpacking a {seq.ty.elem} is not supported", tgt)
        # for a, b in pairs: the elements are opaque; a list or tuple's items are its [k]
        elem = self.fl.fresh("tuple")
        self.bind(elem, seq.ty.elem)
        at = lambda node: ast.copy_location(node, tgt)  # noqa: E731
        seqlike = self.cond(at(ast.Call(at(ast.Name("isinstance", ast.Load())), [at(ast.Name(elem, ast.Load())), at(ast.Tuple([at(ast.Name("list", ast.Load())), at(ast.Name("tuple", ast.Load()))], ast.Load()))], [])))
        for k, name in enumerate(names):
            item = self.expr(at(ast.Subscript(at(ast.Name(elem, ast.Load())), at(ast.Constant(k)), ast.Load())))
            other = self.opaque(f"item{k}", [ir.Var(seq.ty.elem, loc, elem)], item.ty, loc)
            self.aliases[name] = ir.Ite(item.ty, loc, seqlike, item, other)
        return seq, elem

    def bind(self, name: str, ty: ir.Type) -> None:
        self.bound[name] = ty
        self.aliases.pop(name, None)

    def quant(self, n: ast.Call, loc: ir.Loc, kind: str) -> ir.Expr:
        if len(n.args) != 1 or not isinstance(n.args[0], (ast.GeneratorExp, ast.ListComp)):
            raise self.err("all()/any() need a generator: all(p(x) for x in xs)", n)
        g = n.args[0]
        if len(g.generators) != 1:
            raise self.err("all()/any() support a single 'for' clause", n)
        gen = g.generators[0]
        it = gen.iter
        saved, saved_aliases = dict(self.bound), dict(self.aliases)
        try:
            elem = seq = None
            if isinstance(it, ast.Call) and isinstance(it.func, ast.Name) and it.func.id == "range":
                if not isinstance(gen.target, ast.Name):
                    raise self.err("range generator target must be a name", n)
                bounds = [self.expr(a) for a in it.args]
                if len(bounds) == 1:
                    lo, hi = ir.Lit(ir.INT, loc, 0), bounds[0]
                elif len(bounds) == 2:
                    lo, hi = bounds
                else:
                    raise self.err("range() with a step is not supported", n)
                idx = gen.target.id
                self.bind(idx, ir.INT)
            else:
                if isinstance(it, ast.Call) and isinstance(it.func, ast.Name) and it.func.id == "enumerate":
                    if not (isinstance(gen.target, ast.Tuple) and len(gen.target.elts) == 2 and all(isinstance(t, ast.Name) for t in gen.target.elts)):
                        raise self.err("use 'for i, x in enumerate(xs)'", n)
                    idx = gen.target.elts[0].id  # type: ignore[attr-defined]
                    elem = gen.target.elts[1].id  # type: ignore[attr-defined]
                    seq = self.expr(it.args[0])
                else:
                    if not isinstance(gen.target, ast.Name):
                        raise self.err("generator target must be a name", n)
                    elem = gen.target.id
                    idx = f"{elem}$idx"
                    seq = self.expr(it)
                if isinstance(seq.ty, ir.TDict) and elem is not None and idx == f"{elem}$idx":
                    # all(p(k) for k in d): over the keys d holds
                    self.bind(elem, seq.ty.key)
                    body = self.cond(g.elt)
                    for cond in gen.ifs:
                        body = ir.Binary(ir.BOOL, loc, "implies" if kind == "forall" else "and", self.cond(cond), body)
                    zero = ir.Lit(ir.INT, loc, 0)
                    return ir.Quant(ir.BOOL, loc, kind, idx, zero, zero, body, elem, seq)
                if isinstance(seq.ty, ir.TOpaque):
                    seq = ir.Builtin(ir.TList(ir.TOpaque("")), loc, "from_opaque", (seq,))  # an unchecked value iterated as a list
                if not isinstance(seq.ty, ir.TList):
                    raise self.err("generator must range over range(...), a list or a dict", n)
                lo = ir.Lit(ir.INT, loc, 0)
                hi = ir.Builtin(ir.INT, loc, "len", (seq,))
                self.bind(idx, ir.INT)
                self.bind(elem, seq.ty.elem)
            body = self.cond(g.elt)
            for cond in gen.ifs:
                c = self.cond(cond)
                body = ir.Binary(ir.BOOL, loc, "implies" if kind == "forall" else "and", c, body)
            return ir.Quant(ir.BOOL, loc, kind, idx, lo, hi, body, elem, seq)
        finally:
            self.bound, self.aliases = saved, saved_aliases


def lower_python(path: str, source: str) -> ir.Module:
    return PythonFrontend(path, source).run()


# ---------------------------------------------------------------------------
# Projects: imports between checked modules


def _dotted(rel: str) -> str:
    p = rel[:-3] if rel.endswith(".py") else rel
    p = p.replace("\\", "/")
    if p.endswith("/__init__"):
        p = p[: -len("/__init__")]
    return p.replace("/", ".")


def project_imports(path: str, root: str) -> list[str]:
    """Python files under ``root`` that ``path`` imports (best effort)."""
    try:
        tree = ast.parse(Path(path).read_text())
    except (OSError, SyntaxError, ValueError):
        return []
    here = os.path.dirname(os.path.abspath(path))
    out: list[str] = []

    def cands(dotted: str, base: str) -> list[str]:
        p = os.path.join(base, *dotted.split(".")) if dotted else base
        return [p + ".py", os.path.join(p, "__init__.py")]

    for node in ast.walk(tree):
        names: list[tuple[str, int]] = []
        if isinstance(node, ast.ImportFrom):
            names.append((node.module or "", node.level))
            names += [((node.module + "." if node.module else "") + a.name, node.level) for a in node.names]
        elif isinstance(node, ast.Import):
            names += [(a.name, 0) for a in node.names]
        for dotted, level in names:
            if level:
                base = here
                for _ in range(level - 1):
                    base = os.path.dirname(base)
                bases = [base]
            else:
                bases = [os.path.abspath(root), here]
            for b in bases:
                for c in cands(dotted, b):
                    if os.path.isfile(c) and os.path.abspath(c).startswith(os.path.abspath(root)) and os.path.abspath(c) != os.path.abspath(path):
                        out.append(c)
    return sorted(set(out))


def ancestor_files(path: str, root: str) -> list[str]:
    """Python files under ``root``, other than ``path``, that define an
    ancestor of a class ``path`` defines (best effort, by name through imports)."""
    out: list[str] = []
    todo = [os.path.abspath(path)]
    seen: set[str] = set(todo)
    while todo:
        cur = todo.pop()
        try:
            tree = ast.parse(Path(cur).read_text())
        except (OSError, SyntaxError, ValueError):
            continue
        bases = {b.id if isinstance(b, ast.Name) else b.attr for n in ast.walk(tree) if isinstance(n, ast.ClassDef) for b in n.bases if isinstance(b, (ast.Name, ast.Attribute))}
        if not bases:
            continue
        for imp in project_imports(cur, root):
            imp = os.path.abspath(imp)
            if imp in seen:
                continue
            try:
                defined = {n.name for n in ast.walk(ast.parse(Path(imp).read_text())) if isinstance(n, ast.ClassDef)}
            except (OSError, SyntaxError, ValueError):
                continue
            if defined & bases:
                seen.add(imp)
                out.append(imp)
                todo.append(imp)
    return sorted(out)


def lower_python_project(files: list[tuple[str, str]]) -> list[ir.Module]:
    """Lower several modules so that ``from .models import Order`` or
    ``import billing`` between them resolve to the checked definitions:
    classes, enums, records, functions and module constants."""
    fes = [PythonFrontend(rel, src) for rel, src in files]
    by_dotted: dict[str, PythonFrontend] = {}
    for fe in fes:
        by_dotted[_dotted(fe.path)] = fe

    def find(importer: PythonFrontend, module: str, level: int) -> PythonFrontend | None:
        if level:
            pkg = _dotted(importer.path).split(".")
            if not importer.path.endswith("__init__.py"):
                pkg = pkg[:-1]
            base = pkg[: len(pkg) - (level - 1)] if level > 1 else pkg
            name = ".".join(base + ([module] if module else []))
            return by_dotted.get(name)
        if module in by_dotted:
            return by_dotted[module]
        hits = [fe for d, fe in by_dotted.items() if d.endswith("." + module)]
        return hits[0] if len(hits) == 1 else None

    gens = [fe.stages() for fe in fes]

    def advance(to: str) -> None:
        for fe, g in zip(fes, gens):
            if getattr(fe, "_stage", None) == "done":
                continue
            for got in g:
                if got == to:
                    fe._stage = to  # type: ignore[attr-defined]
                    break
            else:
                fe._stage = "done"  # type: ignore[attr-defined]

    advance("names")
    for fe in fes:
        for node in ast.walk(getattr(fe, "tree", ast.Module([], []))):
            if isinstance(node, ast.ImportFrom) and node not in fe.tree.body:
                other = find(fe, node.module or "", node.level)
                if other is not None and other is not fe:
                    fe.nested_imports[id(node)] = other.path
        for module, level, name, asname in fe.imports:
            if not name:  # 'import pkg.mod [as m]'
                other = find(fe, module, 0)
                if other is not None and other is not fe:
                    fe.module_aliases[asname or module] = other
                continue
            sub = find(fe, f"{module}.{name}" if module else name, level)
            if sub is not None and sub is not fe:  # 'from . import models'
                fe.module_aliases[asname or name] = sub
                continue
            other = find(fe, module, level)
            if other is None or other is fe:
                continue
            local = asname or name
            if name in other.enum_types:
                fe.enum_types[local] = other.enum_types[name]
                fe.enums[local] = other.enums[name]
            elif name in other.module.records:
                fe.module.records[local] = other.module.records[name]
            elif name in other.class_names and local == name:
                fe.class_names.add(name)
                fe.linked_classes[name] = other
            elif name in other.constants:
                fe.constants[local] = other.constants[name]
            elif name in other.ignored_classes:
                fe.ignored_classes.add(local)
            else:
                fe.linked_functions[local] = (other, name)
    advance("fields")
    advance("signatures")
    for fe in fes:
        for cname, other in list(fe.linked_classes.items()):
            decl = other.module.classes.get(cname)
            if decl is None:
                fe.class_names.discard(cname)
                continue
            fe.foreign_classes[cname] = decl
            fe.import_class_info(other, cname)
            # ... and its ancestors, wherever they live: inherited members resolve through them
            todo = [(cname, other)]
            while todo:
                c, owner_fe = todo.pop()
                fe.class_bases[c] = list(owner_fe.class_bases.get(c, []))
                for b in fe.class_bases[c]:
                    bfe = owner_fe if b in owner_fe.module.classes else owner_fe.linked_classes.get(b)
                    if bfe is None or b not in bfe.module.classes or b in fe.foreign_classes or b in fe.module.classes:
                        continue
                    fe.foreign_classes[b] = bfe.module.classes[b]
                    fe.import_class_info(bfe, b)
                    todo.append((b, bfe))
        for local, (other, name) in fe.linked_functions.items():
            if name in other.signatures and local == name:
                fe.import_function(other, name)
    home = {id(decl): fe.module.path for fe in fes for decl in fe.module.classes.values()}
    for fe in fes:
        for cname, decl in fe.foreign_classes.items():
            if id(decl) in home:
                fe.module.class_origin[cname] = home[id(decl)]
    owners: dict[str, PythonFrontend | None] = {}
    for fe in fes:
        for cname in fe.module.classes:
            owners[cname] = fe if cname not in owners else None  # ambiguous names reach nowhere
    registry = {n: o for n, o in owners.items() if o is not None}
    for fe in fes:
        fe.project = registry
        fe.peers = fes
    # A class can be dropped as unmodelable after other types mention it
    # (a field of type Settings, where Settings subclasses a library base):
    # those mentions become opaque, like any other library type.
    for fe in fes:
        valid = set(fe.classes)
        fe.signatures = {k: ([ir.Param(p.name, _forget_classes(p.ty, valid)) for p in ps], _forget_classes(r, valid)) for k, (ps, r) in fe.signatures.items()}
        for decl in fe.module.classes.values():
            decl.fields = [(f, _forget_classes(t, valid)) for f, t in decl.fields]
    advance("done")
    return [fe.module for fe in fes]


def _forget_classes(t: ir.Type, valid: set[str]) -> ir.Type:
    if isinstance(t, ir.TClass):
        return t if t.name in valid else ir.TOpaque(t.name)
    if isinstance(t, ir.TList):
        e = _forget_classes(t.elem, valid)
        return t if e is t.elem else ir.TList(e)
    if isinstance(t, ir.TOption):
        i = _forget_classes(t.inner, valid)
        return t if i is t.inner else ir.TOption(i)
    if isinstance(t, ir.TDict):
        v = _forget_classes(t.val, valid)
        return t if v is t.val else ir.TDict(t.key, v, t.js)
    return t
