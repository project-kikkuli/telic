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
import sys
import types
from pathlib import Path
from typing import Any

from . import ir

RUNTIME_NAME = "__telic_rt"


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


def _rt_namespace() -> types.SimpleNamespace:
    return types.SimpleNamespace(check=check, implies=implies, snapshot=snapshot, ContractViolation=ContractViolation)


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
    def __init__(self, fn_ir: ir.Function, node: ast.FunctionDef):
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
            if not isinstance(p.ty, ir.TList):
                pre.append(ast.Assign(targets=[ast.Name(id=f"__telic_p_{p.name}", ctx=ast.Store())], value=ast.Name(id=p.name, ctx=ast.Load())))
                mapping[p.name] = f"__telic_p_{p.name}"
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
            detail = ast.JoinedStr([ast.Constant("returned "), ast.FormattedValue(ast.Name(id="__telic_r", ctx=ast.Load()), ord("r"))])
            post_checks.append(_check_stmt(e, "ensures", en, name, detail))
        self.post_checks = post_checks
        self._instrument_block(self.node, "body")
        body = self.node.body
        # docstring stays first
        doc: list[ast.stmt] = []
        if body and isinstance(body[0], ast.Expr) and isinstance(body[0].value, ast.Constant) and isinstance(body[0].value.value, str):
            doc, body = [body[0]], body[1:]
        tail: list[ast.stmt] = []
        if fn.ret == ir.NONE and post_checks:
            tail = [ast.Assign(targets=[ast.Name(id="__telic_r", ctx=ast.Store())], value=ast.Constant(None))] + post_checks
        self.node.body = doc + pre + body + tail

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
            e, _ = self.spec(inv)
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


def instrument_source(source: str, module: ir.Module, filename: str = "<telic>") -> ast.Module:
    tree = ast.parse(source, filename=filename)
    for node in tree.body:
        if isinstance(node, ast.FunctionDef) and node.name in module.functions:
            fn = module.functions[node.name]
            if fn.unsupported and not (fn.requires or fn.ensures):
                continue
            try:
                FunctionInstrumenter(fn, node).run()
            except SyntaxError:
                continue
    tree.body.insert(0, ast.ImportFrom(module="telic.runtime", names=[ast.alias(name="_rt_namespace")], level=0))
    tree.body.insert(1, ast.Assign(targets=[ast.Name(id=RUNTIME_NAME, ctx=ast.Store())], value=ast.Call(func=ast.Name(id="_rt_namespace", ctx=ast.Load()), args=[], keywords=[])))
    # keep `from __future__` imports first
    fut = [n for n in tree.body if isinstance(n, ast.ImportFrom) and n.module == "__future__"]
    rest = [n for n in tree.body if n not in fut]
    tree.body = fut + rest
    ast.fix_missing_locations(tree)
    return tree


def load_instrumented(path: str, name: str | None = None) -> types.ModuleType:
    from .frontend.python import lower_python

    src = Path(path).read_text()
    mod_ir = lower_python(path, src)
    tree = instrument_source(src, mod_ir, path)
    name = name or Path(path).stem
    module = types.ModuleType(name)
    module.__file__ = path
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

        mod_ir = lower_python(self.origin, self.source)
        tree = instrument_source(self.source, mod_ir, self.origin)
        exec(compile(tree, self.origin, "exec"), module.__dict__)


def install(roots: list[str]) -> ContractFinder:
    finder = ContractFinder(roots)
    sys.meta_path.insert(0, finder)
    return finder
