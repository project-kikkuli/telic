"""Runtime contract checking for Python (C0's ``-d`` mode).

Contracts live in comments, so normal execution pays nothing for them. This
module rewrites a module's AST so that every ``@requires``, ``@ensures``,
``@invariant``, ``@assert`` and ``@assume`` is checked while the code runs --
used to replay counterexamples, by ``telic run``, and by the pytest plugin.

    python -m telic run script.py        # run with contracts enforced
    pytest -p telic.pytest_plugin        # enforce contracts during tests
"""

from __future__ import annotations

import ast
import copy
import importlib.abc
import importlib.util
import os
import sys
import types
from pathlib import Path
from typing import Any

from . import ir

RUNTIME_NAME = "__telic_rt__"


class ContractViolation(AssertionError):
    def __init__(self, kind: str, text: str, line: int, func: str, detail: str = ""):
        self.kind = kind
        self.text = text
        self.line = line
        self.func = func
        self.detail = detail
        msg = f"{func}: @{kind} {text} (line {line}) failed"
        if detail:
            msg += f" -- {detail}"
        super().__init__(msg)


def check(ok: Any, kind: str, text: str, line: int, func: str, detail: str = "") -> None:
    if not ok:
        raise ContractViolation(kind, text, line, func, detail)


def implies(a: Any, b: Any) -> bool:
    return (not a) or bool(b)


def snapshot(v: Any) -> Any:
    return copy.deepcopy(v)


def show(v: Any, depth: int = 0) -> str:
    """repr, but objects show their fields instead of an address."""
    if isinstance(v, list):
        return "[" + ", ".join(show(x, depth + 1) for x in v) + "]"
    if isinstance(v, dict):
        return "{" + ", ".join(f"{show(k)}: {show(x, depth + 1)}" for k, x in v.items()) + "}"
    d = getattr(v, "__dict__", None)
    if d is not None and not isinstance(v, type) and type(v).__repr__ is object.__repr__ and not hasattr(v, "__dataclass_fields__"):
        if depth > 2:
            return f"<{type(v).__name__}>"
        return f"<{type(v).__name__} " + " ".join(f"{k}={show(x, depth + 1)}" for k, x in d.items()) + ">"
    return repr(v)


def settle(r: Any) -> Any:
    """Run a coroutine to completion (replaying an async function)."""
    import asyncio
    import inspect

    if inspect.iscoroutine(r):
        return asyncio.run(r)
    return r


def check_written(objs: list, invs: dict, func: str) -> None:
    seen: set[int] = set()
    for o in objs:
        if id(o) in seen:
            continue
        seen.add(id(o))
        for text, line, pred in invs.get(type(o).__name__, ()):
            check(pred(o), "class.inv", text, line, func)


def _rt_namespace() -> types.SimpleNamespace:
    return types.SimpleNamespace(check=check, implies=implies, snapshot=snapshot, show=show, check_written=check_written, ContractViolation=ContractViolation)


# ---------------------------------------------------------------------------
# Instrumentation


def _parse_clause(text: str) -> ast.expr:
    return ast.parse("(" + text + "\n)", mode="eval").body


class _Rename(ast.NodeTransformer):
    def __init__(self, mapping: dict[str, str]):
        self.mapping = mapping

    def visit_Name(self, node: ast.Name) -> ast.AST:
        if node.id in self.mapping and isinstance(node.ctx, ast.Load):
            return ast.copy_location(ast.Name(id=self.mapping[node.id], ctx=ast.Load()), node)
        return node


class _Specs(ast.NodeTransformer):
    """Rewrite spec-only syntax: ``implies(a, b)`` and ``old(e)``."""

    def __init__(self) -> None:
        self.olds: list[ast.expr] = []

    def visit_Call(self, node: ast.Call) -> ast.AST:
        self.generic_visit(node)
        if isinstance(node.func, ast.Name) and node.func.id == "implies":
            node.func = ast.Attribute(value=ast.Name(id=RUNTIME_NAME, ctx=ast.Load()), attr="implies", ctx=ast.Load())
        elif isinstance(node.func, ast.Name) and node.func.id == "old" and len(node.args) == 1:
            k = len(self.olds)
            self.olds.append(node.args[0])
            return ast.copy_location(ast.Name(id=f"__telic_old{k}", ctx=ast.Load()), node)
        return node


def _check_stmt(expr: ast.expr, kind: str, clause: ir.Clause, func: str, detail: ast.expr | None = None) -> ast.stmt:
    call = ast.Call(
        func=ast.Attribute(value=ast.Name(id=RUNTIME_NAME, ctx=ast.Load()), attr="check", ctx=ast.Load()),
        args=[expr, ast.Constant(kind), ast.Constant(clause.text), ast.Constant(clause.loc.line), ast.Constant(func)]
        + ([detail] if detail is not None else []),
        keywords=[],
    )
    return ast.Expr(call)


def _stmt_lists(node: ast.AST):
    for field in ("body", "orelse", "finalbody"):
        v = getattr(node, field, None)
        if isinstance(v, list) and v and isinstance(v[0], ast.stmt):
            yield node, field, v


class FunctionInstrumenter:
    def __init__(self, fn_ir: ir.Function, node: ast.FunctionDef, classes: dict[str, ir.ClassDecl] | None = None):
        self.classes = classes or {}
        self.fn = fn_ir
        self.node = node
        self.loops = {}
        self.asserts: list[ir.AssertStmt | ir.AssumeStmt] = []
        for s in ir.walk_stmts(fn_ir.body):
            if isinstance(s, (ir.While, ir.ForRange, ir.ForEach)):
                self.loops[s.loc.line] = s
            elif isinstance(s, (ir.AssertStmt, ir.AssumeStmt)) and not getattr(s, "native", False):
                self.asserts.append(s)

    def spec(self, clause: ir.Clause, mapping: dict[str, str] | None = None) -> tuple[ast.expr, list[ast.expr]]:
        e = _parse_clause(clause.text)
        sp = _Specs()
        e = sp.visit(e)
        if mapping:
            e = _Rename(mapping).visit(e)
            sp.olds = [_Rename({}).visit(o) for o in sp.olds]
        return e, sp.olds

    def run(self) -> None:
        fn = self.fn
        name = fn.name
        pre: list[ast.stmt] = []
        # Snapshot scalar parameters: @ensures sees their entry values.
        mapping = {"result": "__telic_r"}
        for p in fn.params:
            if not isinstance(p.ty, (ir.TList, ir.TDict)):
                pre.append(ast.Assign(targets=[ast.Name(id=f"__telic_p_{p.name}", ctx=ast.Store())], value=ast.Name(id=p.name, ctx=ast.Load())))
                mapping[p.name] = f"__telic_p_{p.name}"
        # Objects passed in must satisfy their class invariants (except the
        # object a constructor is building); they must again on return.
        inv_post: list[ast.stmt] = []
        for i, p in enumerate(fn.params):
            if isinstance(p.ty, ir.TClass) and p.ty.name in self.classes:
                for inv in self.classes[p.ty.name].invariants:
                    e, _ = self.spec(inv, {"self": p.name})
                    if not (i == 0 and fn.name.endswith(".__init__")):
                        pre.append(_check_stmt(e, "requires", inv, name))
                    inv_post.append(_check_stmt(copy.deepcopy(e), "class.inv", inv, name))
        for r in fn.requires:
            e, _ = self.spec(r)
            pre.append(_check_stmt(e, "requires", r, name))
        post_checks: list[ast.stmt] = []
        old_k = 0
        for en in fn.ensures:
            e, olds = self.spec(en, mapping)
            # old(...) is evaluated on entry, before the body runs
            renum: dict[str, str] = {}
            for i, o in enumerate(olds):
                nm = f"__telic_old{old_k}"
                renum[f"__telic_old{i}"] = nm
                old_k += 1
                pre.append(
                    ast.Assign(
                        targets=[ast.Name(id=nm, ctx=ast.Store())],
                        value=ast.Call(
                            func=ast.Attribute(value=ast.Name(id=RUNTIME_NAME, ctx=ast.Load()), attr="snapshot", ctx=ast.Load()),
                            args=[o],
                            keywords=[],
                        ),
                    )
                )
            e = _Rename(renum).visit(e)
            shown = ast.Call(func=ast.Attribute(value=ast.Name(id=RUNTIME_NAME, ctx=ast.Load()), attr="show", ctx=ast.Load()), args=[ast.Name(id="__telic_r", ctx=ast.Load())], keywords=[])
            detail = ast.JoinedStr([ast.Constant("returned "), ast.FormattedValue(shown, -1)])
            post_checks.append(_check_stmt(e, "ensures", en, name, detail))
        # Objects passed in change only as their lifecycles allow.
        for i, p in enumerate(fn.params):
            if not isinstance(p.ty, ir.TClass) or (i == 0 and fn.name.endswith((".__init__", ".__post_init__"))):
                continue
            for owner, lc in _lifecycles(self.classes, p.ty.name):
                sp = _Specs()
                # a subclass's lifecycle binds only objects of that subclass
                e = _Rename({"self": p.name}).visit(sp.visit(_parse_clause(f"not isinstance(self, {ir.source_name(owner)}) or ({lc.code})")))
                renum = {}
                for k, o in enumerate(sp.olds):
                    nm = f"__telic_old{old_k}"
                    renum[f"__telic_old{k}"] = nm
                    old_k += 1
                    snap = ast.Call(func=ast.Attribute(value=ast.Name(id=RUNTIME_NAME, ctx=ast.Load()), attr="snapshot", ctx=ast.Load()), args=[_Rename({"self": p.name}).visit(o)], keywords=[])
                    pre.append(ast.Assign(targets=[ast.Name(id=nm, ctx=ast.Store())], value=snap))
                inv_post.append(_check_stmt(_Rename(renum).visit(e), "lifecycle", lc.clause, name))
        self.track_writes = any(isinstance(st, ir.FieldAssign) for st in ir.walk_stmts(fn.body)) and any(c.invariants for c in self.classes.values())
        if self.track_writes:
            pre.append(ast.Assign(targets=[ast.Name(id="__telic_w__", ctx=ast.Store())], value=ast.List(elts=[], ctx=ast.Load())))
            inv_post.append(ast.Expr(ast.Call(
                func=ast.Attribute(value=ast.Name(id=RUNTIME_NAME, ctx=ast.Load()), attr="check_written", ctx=ast.Load()),
                args=[ast.Name(id="__telic_w__", ctx=ast.Load()), ast.Name(id="__telic_invs__", ctx=ast.Load()), ast.Constant(name)],
                keywords=[],
            )))
        # Loop invariants may mention old(...): snapshot those on entry too.
        self.inv_exprs: dict[int, ast.expr] = {}
        for loop in self.loops.values():
            for inv in loop.invariants:
                e, olds = self.spec(inv)
                renum = {}
                for i, o in enumerate(olds):
                    nm = f"__telic_old{old_k}"
                    renum[f"__telic_old{i}"] = nm
                    old_k += 1
                    pre.append(ast.Assign(targets=[ast.Name(id=nm, ctx=ast.Store())], value=ast.Call(func=ast.Attribute(value=ast.Name(id=RUNTIME_NAME, ctx=ast.Load()), attr="snapshot", ctx=ast.Load()), args=[o], keywords=[])))
                self.inv_exprs[id(inv)] = _Rename(renum).visit(e)
        self.post_checks = post_checks + inv_post
        post_checks = self.post_checks
        self._instrument_block(self.node, "body")
        body = self.node.body
        # docstring stays first
        doc: list[ast.stmt] = []
        if body and isinstance(body[0], ast.Expr) and isinstance(body[0].value, ast.Constant) and isinstance(body[0].value.value, str):
            doc, body = [body[0]], body[1:]
        tail: list[ast.stmt] = []
        if fn.ret == ir.NONE and post_checks:
            tail = [ast.Assign(targets=[ast.Name(id="__telic_r", ctx=ast.Store())], value=ast.Constant(None))] + post_checks
        body = body + tail
        if inv_post and not fn.name.endswith(".__init__"):
            # an exception carries the objects to whoever catches it: their
            # invariants must hold then too (an initializer's object is lost)
            violation = ast.Attribute(value=ast.Name(id=RUNTIME_NAME, ctx=ast.Load()), attr="ContractViolation", ctx=ast.Load())
            body = [
                ast.Try(
                    body=body,
                    handlers=[
                        ast.ExceptHandler(type=violation, name=None, body=[ast.Raise()]),
                        ast.ExceptHandler(type=ast.Name(id="Exception", ctx=ast.Load()), name=None, body=[
                            ast.Try(
                                body=[copy.deepcopy(c) for c in inv_post],
                                handlers=[ast.ExceptHandler(type=copy.deepcopy(violation), name="__telic_v", body=[
                                    ast.Assign(targets=[ast.Attribute(value=ast.Name(id="__telic_v", ctx=ast.Load()), attr="detail", ctx=ast.Store())], value=ast.Constant("raised")),
                                    ast.Raise(exc=ast.Name(id="__telic_v", ctx=ast.Load())),
                                ])],
                                orelse=[],
                                finalbody=[],
                            ),
                            ast.Raise(),
                        ]),
                    ],
                    orelse=[],
                    finalbody=[],
                )
            ]
        self.node.body = doc + pre + body

    def _instrument_block(self, parent: ast.AST, field: str) -> None:
        stmts: list[ast.stmt] = getattr(parent, field)
        out: list[ast.stmt] = []
        start = getattr(parent, "lineno", 0)
        for s in stmts:
            out.extend(self._asserts_between(start, s.lineno, s.col_offset))
            out.extend(self._stmt(s))
            start = s.end_lineno or s.lineno
        if stmts:
            out.extend(self._asserts_between(start, 10**9, stmts[0].col_offset))
        setattr(parent, field, out)

    def _asserts_between(self, lo: int, hi: int, col: int) -> list[ast.stmt]:
        out = []
        for a in list(self.asserts):
            if lo < a.clause.loc.line < hi and a.clause.loc.col >= col:
                e, _ = self.spec(a.clause)
                kind = "assert" if isinstance(a, ir.AssertStmt) else "assume"
                out.append(_check_stmt(e, kind, a.clause, self.fn.name))
                self.asserts.remove(a)
        return out

    def _stmt(self, s: ast.stmt) -> list[ast.stmt]:
        tgts = s.targets if isinstance(s, ast.Assign) else [s.target] if isinstance(s, (ast.AugAssign, ast.AnnAssign)) else []
        if self.track_writes and any(isinstance(t, ast.Attribute) for t in tgts):
            # remember objects whose fields this function writes: their
            # class invariants are checked when it returns
            rec = [
                ast.Expr(ast.Call(func=ast.Attribute(value=ast.Name(id="__telic_w__", ctx=ast.Load()), attr="append", ctx=ast.Load()), args=[copy.deepcopy(t.value)], keywords=[]))
                for t in tgts
                if isinstance(t, ast.Attribute)
            ]
            return [s] + rec
        if isinstance(s, ast.Return):
            val = s.value if s.value is not None else ast.Constant(None)
            assign = ast.Assign(targets=[ast.Name(id="__telic_r", ctx=ast.Store())], value=val)
            ret = ast.Return(value=ast.Name(id="__telic_r", ctx=ast.Load()))
            return [assign] + [copy.deepcopy(c) for c in self.post_checks] + [ret]
        if isinstance(s, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef, ast.Lambda)):
            return [s]
        loop = self.loops.get(s.lineno) if isinstance(s, (ast.While, ast.For)) else None
        for _, field, _v in list(_stmt_lists(s)):
            self._instrument_block(s, field)
        if isinstance(s, ast.If) and s.orelse:
            pass
        if loop is not None and loop.invariants:
            return self._loop(s, loop)
        return [s]

    def _loop(self, s: ast.stmt, loop) -> list[ast.stmt]:
        checks = []
        for inv in loop.invariants:
            e = self.inv_exprs.get(id(inv)) or self.spec(inv)[0]
            checks.append((inv, e))
        top = [_check_stmt(copy.deepcopy(e), "invariant", inv, self.fn.name) for inv, e in checks]
        prelude: list[ast.stmt] = []
        if isinstance(s, ast.While):
            s.body = top + s.body
            exit_checks = [_check_stmt(copy.deepcopy(e), "invariant", inv, self.fn.name) for inv, e in checks]
            if not s.orelse:
                s.orelse = exit_checks
            return [s]
        assert isinstance(s, ast.For)
        # for-loops: the index seen by invariants is the *next* iteration's.
        if isinstance(loop, ir.ForRange):
            idx = loop.var
            rng = f"__telic_rng{s.lineno}"
            prelude.append(ast.Assign(targets=[ast.Name(id=rng, ctx=ast.Store())], value=s.iter))
            s.iter = ast.Name(id=rng, ctx=ast.Load())
            exit_val: ast.expr = ast.parse(f"({rng}.stop if len({rng}) else {rng}.start)", mode="eval").body
        else:
            idx = loop.idx
            seq = f"__telic_seq{s.lineno}"
            it = s.iter
            if not loop.idx_visible:
                return [s]
            if isinstance(it, ast.Call) and isinstance(it.func, ast.Name) and it.func.id == "enumerate":
                prelude.append(ast.Assign(targets=[ast.Name(id=seq, ctx=ast.Store())], value=it.args[0]))
                it.args[0] = ast.Name(id=seq, ctx=ast.Load())
            else:
                # '@index k' on a plain for-each: enumerate it for checking
                prelude.append(ast.Assign(targets=[ast.Name(id=seq, ctx=ast.Store())], value=it))
                s.iter = ast.Call(func=ast.Name(id="enumerate", ctx=ast.Load()), args=[ast.Name(id=seq, ctx=ast.Load())], keywords=[])
                s.target = ast.Tuple(elts=[ast.Name(id=idx, ctx=ast.Store()), s.target], ctx=ast.Store())
            exit_val = ast.parse(f"len({seq})", mode="eval").body
        s.body = top + s.body
        exit_checks = []
        for inv, e in checks:
            lam = ast.Lambda(
                args=ast.arguments(posonlyargs=[], args=[ast.arg(arg=idx)], kwonlyargs=[], kw_defaults=[], defaults=[]),
                body=copy.deepcopy(e),
            )
            call = ast.Call(func=lam, args=[copy.deepcopy(exit_val)], keywords=[])
            exit_checks.append(_check_stmt(call, "invariant", inv, self.fn.name))
        if not s.orelse:
            s.orelse = exit_checks
        return prelude + [s]


def _lifecycles(classes: dict[str, ir.ClassDecl], cname: str) -> list[tuple[str, ir.Lifecycle]]:
    """(owner, lifecycle) for what an object of static type ``cname`` may
    keep: its classes' and, when it is one, its subclasses' (never lines
    are consequences)."""
    def up(c: str) -> list[str]:
        return [c] + [x for b in classes[c].bases if b in classes for x in up(b)] if c in classes else []

    owners = up(cname) + [c for c in classes if c != cname and cname in up(c)]
    return [(c, lc) for c in dict.fromkeys(owners) for lc in classes[c].lifecycles if lc.kind != "never"]


def _with_inherited_contracts(module: ir.Module) -> ir.Module:
    """Overrides without a contract of their own run under their base method's."""
    from .program import Program

    Program.build([module])
    return module


def instrument_source(source: str, module: ir.Module, filename: str = "<telic>") -> ast.Module:
    tree = ast.parse(source, filename=filename)
    targets: list[tuple[ast.FunctionDef, str]] = []
    for node in tree.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            targets.append((node, node.name))
        elif isinstance(node, ast.ClassDef):
            targets.extend((sub, f"{node.name}.{sub.name}" + (".setter" if any(isinstance(d, ast.Attribute) and d.attr == "setter" for d in sub.decorator_list) else "")) for sub in node.body if isinstance(sub, (ast.FunctionDef, ast.AsyncFunctionDef)))
    for node, key in targets:
        if key in module.functions:
            fn = module.functions[key]
            if fn.unsupported and not (fn.requires or fn.ensures):
                continue
            try:
                FunctionInstrumenter(fn, node, module.classes).run()
            except SyntaxError:
                continue
    # Class invariants as predicates, for objects written through non-parameters.
    entries = []
    for cname, decl in module.classes.items():
        preds = []
        for inv in decl.invariants:
            lam = ast.Lambda(args=ast.arguments(posonlyargs=[], args=[ast.arg(arg="self")], kwonlyargs=[], kw_defaults=[], defaults=[]), body=_Specs().visit(_parse_clause(inv.text)))
            preds.append(ast.Tuple(elts=[ast.Constant(inv.text), ast.Constant(inv.loc.line), lam], ctx=ast.Load()))
        entries.append((ast.Constant(cname), ast.List(elts=preds, ctx=ast.Load())))
    tree.body.append(ast.Assign(targets=[ast.Name(id="__telic_invs__", ctx=ast.Store())], value=ast.Dict(keys=[k for k, _ in entries], values=[v for _, v in entries])))
    tree.body.insert(0, ast.ImportFrom(module="telic.runtime", names=[ast.alias(name="_rt_namespace")], level=0))
    tree.body.insert(1, ast.Assign(targets=[ast.Name(id=RUNTIME_NAME, ctx=ast.Store())], value=ast.Call(func=ast.Name(id="_rt_namespace", ctx=ast.Load()), args=[], keywords=[])))
    # keep `from __future__` imports first
    fut = [n for n in tree.body if isinstance(n, ast.ImportFrom) and n.module == "__future__"]
    rest = [n for n in tree.body if n not in fut]
    tree.body = fut + rest
    ast.fix_missing_locations(tree)
    return tree


def load_instrumented(path: str, name: str | None = None, root: str | None = None) -> types.ModuleType:
    """Load a module with its contracts enforced. With ``root``, it is loaded
    under its package name so relative imports work."""
    from .frontend.python import _dotted, lower_python

    src = Path(path).read_text()
    mod_ir = _with_inherited_contracts(lower_python(path, src))
    tree = instrument_source(src, mod_ir, path)
    package = None
    if root is not None:
        rel = os.path.relpath(os.path.abspath(path), os.path.abspath(root))
        if not rel.startswith(".."):
            dotted = _dotted(rel)
            name = dotted
            package = dotted if rel.endswith("__init__.py") else dotted.rpartition(".")[0]
            if root not in sys.path:
                sys.path.insert(0, root)
    name = name or Path(path).stem
    module = types.ModuleType(name)
    module.__file__ = path
    if package is not None:
        module.__package__ = package
    sys.modules[name] = module
    exec(compile(tree, path, "exec"), module.__dict__)
    return module


class ContractFinder(importlib.abc.MetaPathFinder):
    """Import hook: modules under ``roots`` are loaded with contracts enforced."""

    def __init__(self, roots: list[str]):
        self.roots = [str(Path(r).resolve()) for r in roots]

    def find_spec(self, fullname, path, target=None):
        spec = importlib.machinery.PathFinder.find_spec(fullname, path)
        if spec is None or not spec.origin or not spec.origin.endswith(".py"):
            return None
        origin = str(Path(spec.origin).resolve())
        if not any(origin.startswith(r + "/") or origin == r for r in self.roots):
            return None
        if "site-packages" in origin or "/telic/" in origin.replace("\\", "/"):
            return None
        src = Path(origin).read_text()
        if "#@" not in src:
            return None
        spec.loader = _ContractLoader(origin, src)
        return spec


class _ContractLoader(importlib.abc.Loader):
    def __init__(self, origin: str, source: str):
        self.origin = origin
        self.source = source

    def create_module(self, spec):
        return None

    def exec_module(self, module):
        from .frontend.python import lower_python

        mod_ir = _with_inherited_contracts(lower_python(self.origin, self.source))
        tree = instrument_source(self.source, mod_ir, self.origin)
        exec(compile(tree, self.origin, "exec"), module.__dict__)


def install(roots: list[str]) -> ContractFinder:
    finder = ContractFinder(roots)
    sys.meta_path.insert(0, finder)
    return finder
