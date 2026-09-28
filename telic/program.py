"""Whole-program facts the verifier needs: name resolution, the call graph,
recursion SCCs, which functions are *definitional* (usable inside specs), and
which list parameters a function mutates."""

from __future__ import annotations

import re
from dataclasses import dataclass, field

from . import ir


@dataclass
class FuncRef:
    module: ir.Module
    fn: ir.Function

    @property
    def key(self) -> str:
        return f"{self.module.path}::{self.fn.name}"


@dataclass
class Program:
    modules: list[ir.Module]
    funcs: dict[str, FuncRef] = field(default_factory=dict)
    callees: dict[str, set[str]] = field(default_factory=dict)
    scc_of: dict[str, int] = field(default_factory=dict)
    recursive: set[str] = field(default_factory=set)
    definitional: set[str] = field(default_factory=set)
    mutated: dict[str, set[str]] = field(default_factory=dict)
    appends: dict[str, set[str]] = field(default_factory=dict)
    logic_names: dict[str, str] = field(default_factory=dict)

    @classmethod
    def build(cls, modules: list[ir.Module]) -> "Program":
        p = cls(modules)
        for m in modules:
            for f in m.functions.values():
                ref = FuncRef(m, f)
                p.funcs[ref.key] = ref
        p._call_graph()
        p._sccs()
        p._mutation()
        p._definitional()
        p._names()
        return p

    def resolve(self, module: ir.Module, name: str) -> FuncRef | None:
        return self.funcs.get(f"{module.path}::{name}")

    def ref(self, key: str) -> FuncRef:
        return self.funcs[key]

    # ------------------------------------------------------------------

    def _calls_in(self, ref: FuncRef) -> set[str]:
        out: set[str] = set()
        exprs: list[ir.Expr] = []
        for s in ir.walk_stmts(ref.fn.body):
            exprs.extend(ir.stmt_exprs(s))
            if isinstance(s, (ir.While, ir.ForRange, ir.ForEach)):
                exprs.extend(c.expr for c in s.invariants)
            if isinstance(s, (ir.AssertStmt, ir.AssumeStmt)):
                exprs.append(s.clause.expr)
        for c in ref.fn.requires + ref.fn.ensures + ref.fn.raises:
            exprs.append(c.expr)
        for e in exprs:
            for sub in ir.walk_expr(e):
                if isinstance(sub, ir.Call):
                    tgt = self.resolve(ref.module, sub.func)
                    if tgt is not None:
                        out.add(tgt.key)
        return out

    def _call_graph(self) -> None:
        for key, ref in self.funcs.items():
            self.callees[key] = self._calls_in(ref)

    def _sccs(self) -> None:
        index: dict[str, int] = {}
        low: dict[str, int] = {}
        stack: list[str] = []
        on: set[str] = set()
        counter = [0]
        comp = [0]

        def strong(v: str) -> None:
            index[v] = low[v] = counter[0]
            counter[0] += 1
            stack.append(v)
            on.add(v)
            for w in self.callees.get(v, ()):
                if w not in index:
                    strong(w)
                    low[v] = min(low[v], low[w])
                elif w in on:
                    low[v] = min(low[v], index[w])
            if low[v] == index[v]:
                members = []
                while True:
                    w = stack.pop()
                    on.discard(w)
                    self.scc_of[w] = comp[0]
                    members.append(w)
                    if w == v:
                        break
                if len(members) > 1 or v in self.callees.get(v, ()):
                    self.recursive.update(members)
                comp[0] += 1

        for v in self.funcs:
            if v not in index:
                strong(v)

    def same_scc(self, a: str, b: str) -> bool:
        return a in self.recursive and self.scc_of.get(a) == self.scc_of.get(b)

    def _mutation(self) -> None:
        for key, ref in self.funcs.items():
            params = {p.name for p in ref.fn.params if isinstance(p.ty, ir.TList)}
            muts: set[str] = set()
            apps: set[str] = set()
            for s in ir.walk_stmts(ref.fn.body):
                if isinstance(s, (ir.IndexAssign, ir.Append)) and s.name in params:
                    muts.add(s.name)
                    if isinstance(s, ir.Append):
                        apps.add(s.name)
            self.mutated[key] = muts
            self.appends[key] = apps
        # Propagate through calls that pass a list parameter to a mutating callee.
        changed = True
        while changed:
            changed = False
            for key, ref in self.funcs.items():
                params = {p.name for p in ref.fn.params if isinstance(p.ty, ir.TList)}
                for s in ir.walk_stmts(ref.fn.body):
                    for e in ir.stmt_exprs(s):
                        for sub in ir.walk_expr(e):
                            if not isinstance(sub, ir.Call):
                                continue
                            tgt = self.resolve(ref.module, sub.func)
                            if tgt is None:
                                continue
                            for p, a in zip(tgt.fn.params, sub.args):
                                if p.name in self.mutated[tgt.key] and isinstance(a, ir.Var) and a.name in params:
                                    if a.name not in self.mutated[key]:
                                        self.mutated[key].add(a.name)
                                        changed = True
                                    if p.name in self.appends[tgt.key] and a.name not in self.appends[key]:
                                        self.appends[key].add(a.name)
                                        changed = True

    def _definitional(self) -> None:
        """A function is definitional if its body is loop-free, mutation-free,
        free of raises, and only calls other definitional functions. Its body
        then *is* a logical definition, so specs may call it."""
        cand: set[str] = set()
        for key, ref in self.funcs.items():
            fn = ref.fn
            if fn.unsupported or fn.trusted or fn.ret == ir.NONE or isinstance(fn.ret, ir.TList):
                continue
            ok = True
            for s in ir.walk_stmts(fn.body):
                if isinstance(s, (ir.While, ir.ForRange, ir.ForEach, ir.IndexAssign, ir.Append, ir.Raise, ir.Break, ir.Continue, ir.ExprStmt, ir.Unsupported, ir.AssumeStmt)):
                    ok = False
                    break
            if ok:
                cand.add(key)
        changed = True
        while changed:
            changed = False
            for key in list(cand):
                if not self.callees[key] <= cand:
                    cand.discard(key)
                    changed = True
        self.definitional = cand

    def _names(self) -> None:
        by_name: dict[str, list[str]] = {}
        for key, ref in self.funcs.items():
            by_name.setdefault(ref.fn.name, []).append(key)
        used: set[str] = set()
        for name, keys in by_name.items():
            for key in keys:
                if len(keys) == 1 and not name.startswith(("seqsum", "seqcount", "Telic")):
                    cand = name
                else:
                    stem = re.sub(r"\W", "_", self.funcs[key].module.path.rsplit("/", 1)[-1])
                    cand = f"{stem}_{name}"
                base, k = cand, 1
                while cand in used:
                    k += 1
                    cand = f"{base}_{k}"
                used.add(cand)
                self.logic_names[key] = cand
