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
import io
import tokenize
from fractions import Fraction

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

PY_ASSUMPTIONS = [
    "float is modelled as exact rational arithmetic (rounding error ignored)",
    "distinct list arguments do not alias each other",
    "print() and logging calls have no effect on program state",
]

IGNORED_CALLS = {"print"}
EXCEPTION_BASES = {"Exception", "BaseException", "ValueError", "KeyError", "RuntimeError", "TypeError", "LookupError", "ArithmeticError", "PermissionError", "HTTPException"}
IGNORED_ATTR_CALLS = {"debug", "info", "warning", "error", "exception", "critical"}


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

    # -- entry --------------------------------------------------------------

    def run(self) -> ir.Module:
        try:
            tree = ast.parse(self.source, filename=self.path)
        except SyntaxError as e:
            self.module.problems.append((f"syntax error: {e.msg}", ir.Loc(e.lineno or 0)))
            return self.module
        try:
            self.contract_lines = parse_comment_lines(self._comments(), "#")
        except ContractSyntaxError as e:
            self.module.problems.append((str(e), ir.Loc(e.line, e.col)))
            return self.module

        # Names bound at module level shadow builtins of the same name.
        assigned: dict[str, int] = {}
        for node in tree.body:
            if isinstance(node, (ast.Import, ast.ImportFrom)):
                for a in node.names:
                    self.bound.add((a.asname or a.name).split(".")[0])
                    if isinstance(node, ast.Import):
                        self.modules.add((a.asname or a.name).split(".")[0])
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
                bases = {_decorator_name(b) for b in node.bases}
                if bases & {"Enum", "IntEnum", "StrEnum", "Flag", "IntFlag"}:
                    members, values = [], []
                    for st in node.body:
                        if isinstance(st, ast.Assign) and len(st.targets) == 1 and isinstance(st.targets[0], ast.Name) and not st.targets[0].id.startswith("_"):
                            members.append(st.targets[0].id)
                            values.append(st.value.value if isinstance(st.value, ast.Constant) else None)
                    mixed = bases & {"IntEnum", "StrEnum", "str", "int", "Flag", "IntFlag"}
                    if members and not mixed and not any(isinstance(st, (ast.FunctionDef, ast.AsyncFunctionDef)) for st in node.body):
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
        for node in classes:
            try:
                self._class_fields(node)
            except LowerError as e:
                self.class_names.discard(node.name)
                self.module.problems.append((f"class {node.name}: {e}", ir.Loc(e.line or node.lineno)))
        classes = [c for c in classes if c.name in self.module.classes]
        methods: list[tuple[ast.FunctionDef, str]] = []
        for node in tree.body:
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                try:
                    self.signatures[node.name] = self._signature(node)
                except LowerError as e:
                    self.module.problems.append((f"{node.name}: {e}", ir.Loc(e.line)))
        for c in classes:
            for sub in c.body:
                if not isinstance(sub, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    continue
                decos = {_decorator_name(d) for d in sub.decorator_list}
                key = f"{c.name}.{sub.name}"
                try:
                    if decos - {"property", "staticmethod"}:
                        raise LowerError(f"decorator @{sorted(decos - {'property', 'staticmethod'})[0]} is not modelled", sub)
                    self.signatures[key] = self._signature(sub, c.name, static="staticmethod" in decos)
                    if "property" in decos:
                        self.properties.add(key)
                    methods.append((sub, c.name))
                except LowerError as e:
                    self.module.problems.append((f"{key}: {e}", ir.Loc(e.line or sub.lineno)))
        for c in classes:
            self._class_invariants(c)
        for node in tree.body:
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and node.name in self.signatures:
                fn = FunctionLowerer(self, node).lower()
                self.module.functions[fn.name] = fn
        for node, cname in methods:
            fn = FunctionLowerer(self, node, cname).lower()
            self.module.functions[fn.name] = fn

        # Module-level intent declarations (anything not consumed by a function).
        for cl in self.contract_lines:
            if cl.consumed:
                continue
            if cl.keyword == "intent":
                try:
                    ids, text = parse_intent_directive(cl)
                except ContractSyntaxError as e:
                    self.module.problems.append((str(e), ir.Loc(e.line, e.col)))
                    cl.consumed = True
                    continue
                if text is None:
                    self.module.problems.append(
                        ("'@intent ID' outside a function links nothing; declare with '@intent ID: sentence'", ir.Loc(cl.line, cl.col))
                    )
                else:
                    self.module.intents.append(ir.IntentDecl(ids[0], text, ir.Loc(cl.line, cl.col)))
                cl.consumed = True
        spans: list[tuple[int, int, str]] = []
        for node in ast.walk(tree):
            if isinstance(node, ast.ClassDef):
                for sub in node.body:
                    if isinstance(sub, (ast.FunctionDef, ast.AsyncFunctionDef)) and f"{node.name}.{sub.name}" not in self.signatures:
                        spans.append((min([sub.lineno] + [d.lineno for d in sub.decorator_list]) - 3, sub.end_lineno or sub.lineno, f"'{node.name}.{sub.name}' is not checked (see the problem reported for it or its class)"))
            elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and node not in tree.body and not any(node is m for m, _ in methods):
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
        return self.module

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
        model_base = bool(set(bases) & {"BaseModel", "SQLModel"})  # pydantic: a validated dataclass
        if any(b not in ("object", "BaseModel", "SQLModel") for b in bases) or (node.keywords and not model_base):
            raise LowerError("inheritance is not modelled yet", node)
        decos = {_decorator_name(d) for d in node.decorator_list}
        if decos - {"dataclass"}:
            raise LowerError(f"class decorator @{sorted(decos - {'dataclass'})[0]} is not modelled", node)
        is_dc = "dataclass" in decos or model_base
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
                elif isinstance(val, ast.Attribute) and isinstance(val.value, ast.Name) and val.value.id in self.enum_types:
                    ty = self.enum_types[val.value.id]
                else:
                    ty = ir.TOpaque(f"field {tgt.attr}")  # annotate it to have it checked
                fields.append((tgt.attr, ty))
                known.add(tgt.attr)
        self.module.classes[node.name] = ir.ClassDecl(node.name, fields, [], ir.Loc(node.lineno, node.col_offset))
        if is_dc:
            self.dataclasses.add(node.name)
        dunders = {st.name for st in node.body if isinstance(st, (ast.FunctionDef, ast.AsyncFunctionDef))}
        self.custom_eq[node.name] = "__eq__" in dunders
        self.custom_bool[node.name] = bool(dunders & {"__bool__", "__len__"})
        if is_dc and init is None:
            self.dataclass_defaults[node.name] = defaults

    def _class_invariants(self, node: ast.ClassDef) -> None:
        decl = self.module.classes[node.name]
        methods = [(min([m.lineno] + [d.lineno for d in m.decorator_list]) - 1, m.end_lineno or m.lineno) for m in node.body if isinstance(m, (ast.FunctionDef, ast.AsyncFunctionDef))]
        lo, hi = node.lineno, node.end_lineno or node.lineno
        stub = _ClassScope(self, node.name)
        for cl in self.contract_lines:
            if cl.consumed or not (lo <= cl.line <= hi) or cl.keyword != "invariant":
                continue
            if any(a + 1 < cl.line <= b for a, b in methods):
                continue  # inside a method: a loop invariant
            cl.consumed = True
            try:
                c = stub.clause(cl, "invariant", tuple(cl.tags))
                _own_fields_only(c.expr, node.name, cl.line)
                decl.invariants.append(c)
            except (LowerError, ContractSyntaxError) as e:
                self.module.problems.append((f"class {node.name}: invariant: {e}", ir.Loc(cl.line, cl.col)))

    def type_of_annotation(self, ann: ast.expr | None) -> ir.Type:
        if ann is None:
            raise LowerError("missing type annotation")
        if isinstance(ann, ast.Constant) and ann.value is None:
            return ir.NONE
        if isinstance(ann, ast.Constant) and isinstance(ann.value, str):
            return self.type_of_annotation(ast.parse(ann.value, mode="eval").body)
        if isinstance(ann, ast.Attribute):
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
        return ir.TOpaque(ast.unparse(ann))

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
        if isinstance(inner, (ir.TList, ir.TDict, ir.TOption)):
            return ir.TOpaque(ast.unparse(node))
        return ir.TOption(inner)

    def _signature(self, node: ast.FunctionDef, cls: str | None = None, static: bool = False) -> tuple[list[ir.Param], ir.Type]:
        a = node.args
        if a.vararg or a.kwarg or a.posonlyargs:
            raise LowerError("*args, **kwargs and positional-only parameters are not supported", node)
        params = []
        args = list(a.args) + list(a.kwonlyargs)
        for i, arg in enumerate(args):
            if i == 0 and cls is not None and not static:
                if arg.annotation is not None and not (isinstance(arg.annotation, ast.Name) and arg.annotation.id in (cls, "Self")):
                    raise LowerError(f"'{arg.arg}' of a method of {cls} must be the instance", arg)
                params.append(ir.Param(arg.arg, ir.TClass(cls)))
                continue
            if arg.annotation is None:
                params.append(ir.Param(arg.arg, ir.TOpaque("unannotated")))
                continue
            params.append(ir.Param(arg.arg, self.type_of_annotation(arg.annotation)))
        # Default values, by parameter name: substituted at call sites.
        key = f"{cls}.{node.name}" if cls else node.name
        defaults: dict[str, ast.expr] = {}
        for arg, d in zip(a.args[len(a.args) - len(a.defaults):], a.defaults):
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
    def __init__(self, fe: PythonFrontend, node: ast.FunctionDef, cls: str | None = None):
        self.fe = fe
        self.node = node
        self.cls = cls
        self.key = f"{cls}.{node.name}" if cls else node.name
        self.env: dict[str, ir.Type] = {}
        self.fn: ir.Function
        self.tmp = 0
        # contract lines inside this function's line span, not yet consumed
        self.local_contracts = [
            cl for cl in fe.contract_lines if node.lineno <= cl.line <= (node.end_lineno or node.lineno)
        ]
        self.current_intents: list[str] = []
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
        )
        for p in params:
            self.env[p.name] = p.ty

        for cl in self._header_contracts():
            cl.consumed = True
            try:
                self._function_contract(cl)
            except (LowerError, ContractSyntaxError) as e:
                self.fn.unsupported.append((f"contract: {e}", ir.Loc(getattr(e, "line", cl.line))))

        body = node.body
        if body and isinstance(body[0], ast.Expr) and isinstance(body[0].value, ast.Constant) and isinstance(body[0].value.value, str):
            body = body[1:]
        self.fn.body = list(self.block(body, node))
        self.fn.locals = dict(self.env)
        return self.fn

    def _function_contract(self, cl: ContractLine) -> None:
        kw = cl.keyword
        if kw == "intent":
            ids, text = parse_intent_directive(cl)
            if text is not None:
                self.fe.module.intents.append(ir.IntentDecl(ids[0], text, ir.Loc(cl.line, cl.col)))
            for i in ids:
                if i not in self.fn.intents:
                    self.fn.intents.append(i)
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
        tags = tuple(cl.tags) or tuple(self.current_intents)
        for t in tags:
            if t not in self.fn.intents:
                self.fn.intents.append(t)
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
        el.allow_old = kind == "invariant" and not isinstance(self, _ClassScope)
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
            raise LowerError(f"variable '{name}' changes type from {old} to {ty}; telic requires one type per variable", node)

    def coerce(self, e: ir.Expr, ty: ir.Type) -> ir.Expr:
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
            decl = self.fe.module.classes[obj.ty.name]
            ft = decl.field_type(target.attr)
            if ft is None:
                raise LowerError(f"{obj.ty.name} has no field '{target.attr}' (declare it in the class or __init__)", s)
            val = self.coerce(self.expr(value, ft), ft)
            self._check_assignable(f"{obj.ty.name}.{target.attr}", ft, val, s)
            if isinstance(ft, (ir.TList, ir.TDict)) and not fresh_list(val):
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

    def _no_alias(self, name: str, val: ir.Expr, node: ast.AST) -> None:
        if not isinstance(val.ty, (ir.TList, ir.TDict)):
            return
        if any(p.name == name for p in self.fn.params):
            raise LowerError(f"rebinding list parameter '{name}' is not supported (mutate it, or copy it to a new name)", node)
        if not fresh_list(val):
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
            if items_of is None and not isinstance(s.target, ast.Name):
                raise LowerError("for-loop target must be a name", s)
            elem = s.target.elts[0].id if items_of is not None else s.target.id  # type: ignore[attr-defined]
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
        self.current_intents = []
        self.local_contracts = []
        self.stored_names = set()
        self.try_depth = 0


def fresh_list(e: ir.Expr) -> bool:
    """A list-valued expression that denotes a new list object (so binding it
    to a name creates no alias): a literal, a slice copy, or a call (callees
    may not return their list parameters)."""
    if isinstance(e, (ir.ListLit, ir.Call)):
        return True
    if isinstance(e, ir.Builtin) and e.name in ("slice", "dict_lit", "dict_copy", "comp", "from_opaque", "dict_keys", "dict_values", "list_append"):
        return True
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
        if isinstance(sub, ir.Call) and any(isinstance(a.ty, ir.TClass) for a in sub.args):
            raise LowerError("a class invariant may not call methods (they could read other objects); write the condition on self's fields", line=line)


PY_GLOBALS = {"datetime", "time", "uuid", "os", "json", "re", "random", "logging", "Decimal", "sorted", "reversed", "zip", "map", "filter", "open", "input", "id", "hash", "repr", "type", "set", "tuple", "list", "frozenset", "getattr", "setattr", "hasattr", "iter", "next", "divmod", "pow", "chr", "ord", "hex", "bin", "format", "vars", "dir", "callable", "super"}


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


def _decorator_name(d: ast.expr) -> str:
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
            if self.spec and n.id == "result" and self.result_ty is not None and n.id not in self.bound:
                if self.result_ty == ir.NONE:
                    raise self.err("'result' used but the function returns nothing", n)
                return ir.Result(self.result_ty, loc)
            fe = self.fl.fe
            if n.id not in self.bound and n.id not in self.fl.env:
                if n.id in fe.constants:
                    return self.expr(fe.constants[n.id], expect)
                if n.id in fe.bound or n.id in PY_GLOBALS:
                    # a module global or import: read fresh each time (it may change)
                    return ir.Extern(ir.TOpaque(n.id), loc, n.id, ())
            return ir.Var(self.lookup(n.id, n), loc, n.id)
        if isinstance(n, ast.Await):
            inner = self.expr(n.value, expect)
            return ir.Builtin(inner.ty, loc, "await", (inner,))
        if isinstance(n, ast.JoinedStr):
            return self.fstring(n, loc)
        if isinstance(n, (ast.Tuple, ast.Set)) and not self.spec:
            parts = [self.expr(x) for x in n.elts]
            return self.opaque("tuple" if isinstance(n, ast.Tuple) else "set", parts, ir.TOpaque("tuple"), loc)
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
                raise self.err(f"'{op}' on non-bool values returns an operand, not a bool; compare explicitly", n)
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
                if opt is not None:
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
                return self.opaque(f"attr.{n.attr}", [obj], ir.TOpaque(""), loc)
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
                key = f"{obj.ty.name}.{n.attr}"
                if key in self.fl.fe.properties:
                    return self.method_call(key, obj, [], [], n, loc)
                ft = self.fl.fe.module.classes[obj.ty.name].field_type(n.attr)
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
            t = elems[0].ty
            if any(isinstance(e.ty, ir.TReal) for e in elems) and all(ir.is_numeric(e.ty) for e in elems):
                t = ir.REAL
                elems = [self.fl.coerce(e, t) for e in elems]
            if any(e.ty != t for e in elems):
                raise self.err("list elements must all have one type", n)
            return ir.ListLit(ir.TList(t), loc, tuple(elems))
        if isinstance(n, ast.Dict):
            if any(k is None for k in n.keys):
                raise self.err("'**' in dict literals is not supported", n)
            ks = [self.expr(k) for k in n.keys]  # type: ignore[arg-type]
            vs = [self.expr(v) for v in n.values]
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
        if isinstance(n, (ast.GeneratorExp, ast.ListComp)):
            return self.comprehension(n, loc)
        if isinstance(n, (ast.DictComp, ast.SetComp, ast.Lambda)) and not self.spec:
            return self.opaque(type(n).__name__.lower(), [], ir.TOpaque(""), loc)
        raise self.err(f"unsupported expression: {type(n).__name__}", n)

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
            raise self.err("'**' is supported only with a literal exponent 0..4", n)
        if isinstance(op, ast.Add) and isinstance(a.ty, ir.TList):
            raise self.err("list concatenation is not supported", n)
        if isinstance(op, ast.Add) and isinstance(a.ty, ir.TStr):
            raise self.err("string concatenation is not supported", n)
        if isinstance(op, (ast.Add, ast.Sub, ast.Mult)):
            a, b, t = self.numeric_pair(a, b, n)
            name = {ast.Add: "add", ast.Sub: "sub", ast.Mult: "mul"}[type(op)]
            return ir.Binary(t, loc, name, a, b)
        if isinstance(op, ast.Div):
            a, b, _ = self.numeric_pair(a, b, n)
            return ir.Binary(ir.REAL, loc, "rdiv", self.fl.coerce(a, ir.REAL), self.fl.coerce(b, ir.REAL))
        if isinstance(op, ast.FloorDiv):
            a, b, t = self.numeric_pair(a, b, n)
            if t == ir.INT:
                return ir.Binary(ir.INT, loc, "floordiv", a, b)
            q = ir.Binary(ir.REAL, loc, "rdiv", a, b)
            return ir.Builtin(ir.REAL, loc, "to_real", (ir.Builtin(ir.INT, loc, "floor", (q,)),))
        if isinstance(op, ast.Mod):
            a, b, t = self.numeric_pair(a, b, n)
            return ir.Binary(t, loc, "fmod", a, b)
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
        if f"{cls}.__eq__" in fe.signatures or fe.custom_eq.get(cls):
            raise self.err(f"{cls} defines __eq__, which telic does not model; compare fields explicitly", n)
        if cls not in fe.dataclasses:
            return ir.Binary(ir.BOOL, loc, "eq", a, b)
        out: ir.Expr = ir.Lit(ir.BOOL, loc, True)
        for fname, fty in fe.module.classes[cls].fields:
            if isinstance(fty, (ir.TClass, ir.TDict)):
                raise self.err(f"== on {cls} compares field '{fname}' structurally, which is not modelled; compare fields explicitly", n)
            eq = ir.Binary(ir.BOOL, loc, "eq", ir.Field(fty, loc, a, fname), ir.Field(fty, loc, b, fname))
            out = eq if isinstance(out, ir.Lit) else ir.Binary(ir.BOOL, loc, "and", out, eq)
        return out

    # -- calls ----------------------------------------------------------

    def call(self, n: ast.Call, loc: ir.Loc, expect: ir.Type | None) -> ir.Expr:
        f = n.func
        fe = self.fl.fe
        # Module functions (math.sqrt, json.dumps, requests.get): unchecked.
        if isinstance(f, ast.Attribute) and isinstance(f.value, ast.Name) and f.value.id not in self.fl.env and f.value.id not in self.bound and (f.value.id in fe.modules or (f.value.id in fe.bound and f.value.id not in fe.class_names) or f.value.id in PY_GLOBALS) and f.value.id != "math":
            return self.extern(f"{f.value.id}.{f.attr}", [], n, loc, expect)
        if isinstance(f, ast.Attribute) and isinstance(f.value, ast.Name) and f.value.id == "math" and f.attr not in ("floor", "ceil", "trunc"):
            return self.extern(f"math.{f.attr}", [], n, loc, expect or ir.REAL)
        if isinstance(f, ast.Attribute) and isinstance(f.value, ast.Name) and f.value.id in fe.class_names and f.value.id not in self.fl.env:
            key = f"{f.value.id}.{f.attr}"  # a static method
            if key not in fe.signatures:
                raise self.err(f"'{key}' is not a checked static method", n)
            return self.method_call(key, None, n.args, n.keywords, n, loc)
        if isinstance(f, ast.Attribute) and not (isinstance(f.value, ast.Name) and f.value.id == "math"):
            obj = self.expr(f.value)
            if isinstance(obj.ty, ir.TOption) and isinstance(obj.ty.inner, (ir.TClass, ir.TDict)):
                obj = self.need(obj)
            if isinstance(obj.ty, ir.TClass):
                key = f"{obj.ty.name}.{f.attr}"
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
        if n.keywords and not (isinstance(n.func, ast.Name) and (n.func.id in fe.module.records or n.func.id in fe.signatures or n.func.id in fe.class_names)):
            raise self.err("keyword arguments are only supported for checked functions and constructors", n)
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
            raise self.err("unsupported call", n)
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
            if x.ty == ir.STR:
                return ir.Builtin(ir.INT, loc, "str_len", (x,))
            if isinstance(x.ty, (ir.TOpaque, ir.TDict)):
                return self.opaque("len", [x], ir.INT, loc)
            if not isinstance(x.ty, ir.TList):
                raise self.err("len() is supported on lists", n)
            return ir.Builtin(ir.INT, loc, "len", (x,))
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
            return ir.Builtin(t, loc, name, tuple(self.fl.coerce(a, t) for a in args))
        if name == "sum":
            (x,) = self._args(n, 1)
            if not (isinstance(x.ty, ir.TList) and ir.is_numeric(x.ty.elem)):
                raise self.err("sum() needs a list of numbers", n)
            return ir.Builtin(x.ty.elem, loc, "sum", (x,))
        if name == "float":
            (x,) = self._args(n, 1)
            if not ir.is_numeric(x.ty):
                return self.extern("float", [x], None, loc, ir.REAL)
            return self.fl.coerce(x, ir.REAL)
        if name == "int":
            (x,) = self._args(n, 1)
            if isinstance(x.ty, ir.TInt):
                return x
            if isinstance(x.ty, ir.TReal):
                return ir.Builtin(ir.INT, loc, "trunc", (x,))
            return self.extern("int", [x], None, loc, ir.INT)  # int(s): parsing, may raise
        if name == "round":
            if len(n.args) != 1:
                raise self.err("round() with ndigits is not supported", n)
            (x,) = self._args(n, 1)
            if isinstance(x.ty, ir.TInt):
                return x
            if isinstance(x.ty, ir.TReal):
                return ir.Builtin(ir.INT, loc, "round_even", (x,))
            raise self.err("round() needs a number", n)
        if name == "bool":
            (x,) = self._args(n, 1)
            return self.truthy(x, n)
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
            return self.opaque("isinstance", [x, ir.Lit(ir.STR, loc, ast.unparse(n.args[1]))], ir.BOOL, loc)
        if name in fe.signatures:
            return self.user_call(n, loc, name)
        if not self.spec:
            return self.extern(name, [], n, loc, expect)
        return self.user_call(n, loc, name)

    def user_call(self, n: ast.Call, loc: ir.Loc, name: str) -> ir.Expr:
        sig = self.fl.fe.signatures.get(name)
        if sig is None:
            raise self.err(f"call to '{name}', which telic cannot see (define it in a checked file with a contract)", n)
        params, ret = sig
        args = self.bind_args(name, params, n.args, n.keywords, n)
        return ir.Call(ret, loc, name, tuple(args))

    def bind_args(self, key: str, params: list[ir.Param], pos: list[ast.expr], kws: list[ast.keyword], n: ast.AST) -> list[ir.Expr]:
        """Match positional and keyword arguments to parameters, filling in
        defaults; then lower and type-check each argument."""
        fe = self.fl.fe
        defaults = fe.defaults.get(key, {})
        kwonly = fe.kwonly.get(key, set())
        chosen: dict[str, ast.expr] = {}
        positional = [p for p in params if p.name not in kwonly]
        if any(isinstance(a, ast.Starred) for a in pos) or any(k.arg is None for k in kws):
            raise self.err("*args / **kwargs at call sites are not supported", n)
        if len(pos) > len(positional):
            raise self.err(f"'{key}' takes {len(positional)} positional arguments, got {len(pos)}", n)
        for p, a in zip(positional, pos):
            chosen[p.name] = a
        names = {p.name for p in params}
        for k in kws:
            if k.arg not in names:
                raise self.err(f"'{key}' has no parameter '{k.arg}'", n)
            if k.arg in chosen:
                raise self.err(f"'{key}' got two values for '{k.arg}'", n)
            chosen[k.arg] = k.value  # type: ignore[index]
        out = []
        for p in params:
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
        params, ret = self.fl.fe.signatures[key]
        if obj is None:
            return ir.Call(ret, loc, key, tuple(self.bind_args(key, params, pos, kws, n)))
        rest = self.bind_args(key, params[1:], pos, kws, n)
        return ir.Call(ret, loc, key, (obj, *rest))

    def new(self, cls: str, n: ast.Call, loc: ir.Loc) -> ir.Expr:
        fe = self.fl.fe
        if self.spec:
            raise self.err("specifications cannot create objects", n)
        init = f"{cls}.__init__"
        if init in fe.signatures:
            params, _ = fe.signatures[init]
            args = self.bind_args(init, params[1:], n.args, n.keywords, n)
        elif cls in fe.dataclass_defaults:
            decl = fe.module.classes[cls]
            params = [ir.Param(f, t) for f, t in decl.fields]
            fe.defaults.setdefault(f"{cls}()", fe.dataclass_defaults[cls])
            args = self.bind_args(f"{cls}()", params, n.args, n.keywords, n)
            for (fname, fty), a in zip(decl.fields, args):
                if isinstance(fty, (ir.TList, ir.TDict)) and not fresh_list(a):
                    raise self.err(f"passing an existing {fty} as field '{fname}' would alias it; pass a copy", n)
        else:
            if n.args or n.keywords:
                raise self.err(f"{cls} has no __init__ taking arguments", n)
            args = []
            if fe.module.classes[cls].fields:
                raise self.err(f"{cls} has fields but no __init__ to set them; add one (or make it a @dataclass)", n)
        return ir.New(ir.TClass(cls), loc, cls, tuple(args))

    def _args(self, n: ast.Call, k: int) -> list[ir.Expr]:
        if len(n.args) != k:
            raise self.err(f"expected {k} argument(s)", n)
        return [self.expr(a) for a in n.args]

    # -- gradual fallbacks ------------------------------------------------

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
            return ir.Builtin(obj.ty, loc, "slice", (obj, ir.Lit(ir.NONE, loc, None), ir.Lit(ir.NONE, loc, None)))
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

    def comprehension(self, n: ast.GeneratorExp | ast.ListComp, loc: ir.Loc) -> ir.Expr:
        """``[f(x) for x in xs if c(x)]``: a new list. Precise when the body
        is pure (element i is f(xs[i]), same length without a filter)."""
        if len(n.generators) != 1 or n.generators[0].is_async:
            return self.opaque("comprehension", [], ir.TOpaque(""), loc)
        gen = n.generators[0]
        seq = self.expr(gen.iter)
        if isinstance(seq.ty, ir.TOpaque):
            seq = self.fl.coerce(seq, ir.TList(ir.TOpaque("")))
        if not isinstance(seq.ty, ir.TList) or not isinstance(gen.target, ast.Name):
            return self.opaque("comprehension", [seq] if not isinstance(seq.ty, ir.TList) else [], ir.TOpaque(""), loc)
        saved = dict(self.bound)
        try:
            elem = gen.target.id
            self.bound[elem] = seq.ty.elem
            body = self.expr(n.elt)
            conds = [self.cond(c) for c in gen.ifs]
        finally:
            self.bound = saved
        cond: ir.Expr | None = None
        for c in conds:
            cond = c if cond is None else ir.Binary(ir.BOOL, loc, "and", cond, c)
        if isinstance(body.ty, (ir.TList, ir.TDict)):
            return self.opaque("comprehension", [], ir.TOpaque(""), loc)
        return ir.Builtin(ir.TList(body.ty), loc, "comp", (seq, ir.Lit(ir.STR, loc, elem), body) + ((cond,) if cond is not None else ()))

    def quant(self, n: ast.Call, loc: ir.Loc, kind: str) -> ir.Expr:
        if len(n.args) != 1 or not isinstance(n.args[0], (ast.GeneratorExp, ast.ListComp)):
            raise self.err("all()/any() need a generator: all(p(x) for x in xs)", n)
        g = n.args[0]
        if len(g.generators) != 1:
            raise self.err("all()/any() support a single 'for' clause", n)
        gen = g.generators[0]
        it = gen.iter
        saved = dict(self.bound)
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
                self.bound[idx] = ir.INT
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
                if not isinstance(seq.ty, ir.TList):
                    raise self.err("generator must range over range(...) or a list", n)
                lo = ir.Lit(ir.INT, loc, 0)
                hi = ir.Builtin(ir.INT, loc, "len", (seq,))
                self.bound[idx] = ir.INT
                self.bound[elem] = seq.ty.elem
            body = self.cond(g.elt)
            for cond in gen.ifs:
                c = self.cond(cond)
                body = ir.Binary(ir.BOOL, loc, "implies" if kind == "forall" else "and", c, body)
            return ir.Quant(ir.BOOL, loc, kind, idx, lo, hi, body, elem, seq)
        finally:
            self.bound = saved


def lower_python(path: str, source: str) -> ir.Module:
    return PythonFrontend(path, source).run()
