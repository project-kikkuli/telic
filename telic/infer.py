"""Cheap, verified inference of the boring parts of a proof.

Nobody should have to write ``0 <= i <= len(xs)`` by hand. telic guesses
candidate loop invariants and termination measures from the shape of the code
and keeps only the ones it can *prove* (the Houdini algorithm: Flanagan &
Leino, 2001). Inferred facts are shown in reports, marked as inferred, and
carry the same proof obligations as hand-written ones -- inference can make a
proof succeed, never make a false claim.
"""

from __future__ import annotations

from dataclasses import dataclass, field

from . import ir
from .program import FuncRef, Program
from .render_expr import render
from .smt import Theory, solve
from .vcgen import Options, VCError, VCGen

MAX_ROUNDS = 8


def _v(name: str, ty: ir.Type, loc: ir.Loc) -> ir.Var:
    return ir.Var(ty, loc, name)


def _int(v: int, loc: ir.Loc) -> ir.Lit:
    return ir.Lit(ir.INT, loc, v)


def _cmp(op: str, a: ir.Expr, b: ir.Expr, loc: ir.Loc) -> ir.Expr:
    return ir.Binary(ir.BOOL, loc, op, a, b)


def _clause(e: ir.Expr, loc: ir.Loc) -> ir.Clause:
    return ir.Clause("invariant", e, loc, render(e), inferred=True)


def _mentions(e: ir.Expr, names: set[str]) -> bool:
    return any(isinstance(x, ir.Var) and x.name in names for x in ir.walk_expr(e))


def _comparisons(e: ir.Expr):
    if isinstance(e, ir.Binary) and e.op == "and":
        yield from _comparisons(e.left)
        yield from _comparisons(e.right)
    elif isinstance(e, ir.Binary) and e.op in ("lt", "le", "gt", "ge", "ne"):
        yield e


@dataclass
class LoopSite:
    stmt: ir.Stmt
    before: list[ir.Stmt]  # statements preceding the loop in its block
    defined: set[str]  # names certainly bound when the loop starts


def _binds(s: ir.Stmt) -> set[str]:
    if isinstance(s, ir.Assign):
        return {s.name}
    if isinstance(s, ir.If):
        return ir.assigned_names(s.then) & ir.assigned_names(s.orelse)
    return set()


def loop_sites(stmts, before=None, defined: set[str] | None = None) -> list[LoopSite]:
    out: list[LoopSite] = []
    prefix: list[ir.Stmt] = list(before or [])
    defined = set(defined or ())
    for s in stmts:
        if isinstance(s, (ir.While, ir.ForRange, ir.ForEach)):
            out.append(LoopSite(s, list(prefix), set(defined)))
            inner = set(defined)
            if isinstance(s, ir.ForRange):
                inner.add(s.var)
            if isinstance(s, ir.ForEach):
                inner |= {s.elem, s.idx}
            out.extend(loop_sites(s.body, [], inner))
        elif isinstance(s, ir.If):
            out.extend(loop_sites(s.then, [], defined))
            out.extend(loop_sites(s.orelse, [], defined))
        prefix.append(s)
        defined |= _binds(s)
    return out


def invariant_candidates(fn: ir.Function, site: LoopSite) -> list[ir.Clause]:
    s = site.stmt
    loc = ir.Loc(s.loc.line)
    body = list(s.body) + (list(s.step) if isinstance(s, ir.While) else [])
    mod = ir.assigned_names(body)
    known = site.defined | {p.name for p in fn.params}
    ints = sorted(n for n in mod if isinstance(fn.locals.get(n), ir.TInt) and "$" not in n and n in known)
    lists = sorted(n for n, t in fn.locals.items() if isinstance(t, ir.TList) and "$" not in n and n in known)
    exprs: list[ir.Expr] = []

    def add(e: ir.Expr) -> None:
        if all(render(e) != render(x) for x in exprs):
            exprs.append(e)

    if isinstance(s, ir.While):
        for c in _comparisons(s.cond):
            for x, y, flip in ((c.left, c.right, False), (c.right, c.left, True)):
                if isinstance(x, ir.Var) and x.name in mod and x.name in known and not _mentions(y, mod):
                    op = c.op
                    if flip:
                        op = {"lt": "gt", "le": "ge", "gt": "lt", "ge": "le", "ne": "ne"}[op]
                    if op == "lt":
                        add(_cmp("le", x, y, loc))
                    elif op == "gt":
                        add(_cmp("ge", x, y, loc))
                    elif op == "le":
                        add(_cmp("le", x, ir.Binary(ir.INT, loc, "add", y, _int(1, loc)), loc))
                    elif op == "ge":
                        add(_cmp("ge", x, ir.Binary(ir.INT, loc, "sub", y, _int(1, loc)), loc))
                    elif op == "ne" and isinstance(x.ty, ir.TInt):
                        add(_cmp("le", x, y, loc))
                        add(_cmp("ge", x, y, loc))
    reals = sorted(n for n in mod if isinstance(fn.locals.get(n), ir.TReal) and "$" not in n and n in known)
    for n in reals:
        add(_cmp("ge", _v(n, ir.REAL, loc), ir.Lit(ir.REAL, loc, 0), loc))
    for n in ints:
        v = _v(n, ir.INT, loc)
        add(_cmp("ge", v, _int(0, loc), loc))
        # x >= its initial value, when that value is loop-invariant
        for prev in reversed(site.before):
            if isinstance(prev, ir.Assign) and prev.name == n:
                if not _mentions(prev.value, mod) and isinstance(prev.value.ty, ir.TInt):
                    add(_cmp("ge", v, prev.value, loc))
                    add(_cmp("le", v, prev.value, loc))
                break
        for xs in lists:
            if xs in mod:
                continue
            ln = ir.Builtin(ir.INT, loc, "len", (_v(xs, fn.locals[xs], loc),))
            add(_cmp("le", v, ln, loc))
    for a in ints:
        for b in ints:
            if a < b:
                va, vb = _v(a, ir.INT, loc), _v(b, ir.INT, loc)
                add(_cmp("le", va, vb, loc))
                add(_cmp("le", va, ir.Binary(ir.INT, loc, "add", vb, _int(1, loc)), loc))
                add(_cmp("le", vb, va, loc))
    for e in accumulator_candidates(fn, site, known):
        add(e)
    for e in append_candidates(fn, site, known):
        add(e)
    return [_clause(e, loc) for e in exprs]


def _initial(site: LoopSite, name: str) -> ir.Expr | None:
    for prev in reversed(site.before):
        if isinstance(prev, ir.Assign) and prev.name == name:
            return prev.value
        if name in ir.assigned_names([prev]):
            return None
    return None


def append_candidates(fn: ir.Function, site: LoopSite, known: set[str]) -> list[ir.Expr]:
    """A list appended exactly once per iteration of a counted loop grows in
    lock-step with the counter: ``len(out) == len0 + (i - lo)``."""
    s = site.stmt
    loc = ir.Loc(s.loc.line)
    if isinstance(s, ir.ForEach):
        idx, lo = s.idx, ir.Lit(ir.INT, loc, 0)
    elif isinstance(s, ir.ForRange):
        idx, lo = s.var, s.lo
    else:
        return []
    out: list[ir.Expr] = []
    for st in s.body:
        if not isinstance(st, ir.Append) or st.name not in known:
            continue
        others = [x for x in ir.walk_stmts(s.body) if x is not st and isinstance(x, (ir.Append, ir.Assign)) and x.name == st.name]
        if others:
            continue
        init = _initial(site, st.name)
        if not isinstance(init, ir.ListLit):
            continue
        ty = fn.locals[st.name]
        length = ir.Builtin(ir.INT, loc, "len", (ir.Var(ty, loc, st.name),))
        steps = ir.Binary(ir.INT, loc, "sub", ir.Var(ir.INT, loc, idx), lo) if not (isinstance(lo, ir.Lit) and lo.value == 0) else ir.Var(ir.INT, loc, idx)
        rhs = steps if not init.elems else ir.Binary(ir.INT, loc, "add", ir.Lit(ir.INT, loc, len(init.elems)), steps)
        out.append(ir.Binary(ir.BOOL, loc, "eq", length, rhs))
    return out


def accumulator_candidates(fn: ir.Function, site: LoopSite, known: set[str]) -> list[ir.Expr]:
    """``acc += x`` over a sequence  ==>  ``acc == init + sum(seq[:i])``;
    ``if p(x): n += 1``  ==>  ``n == init + count`` is left to the user."""
    s = site.stmt
    loc = ir.Loc(s.loc.line)
    out: list[ir.Expr] = []
    if isinstance(s, ir.ForEach):
        seq, idx, elem = s.seq, s.idx, s.elem
        lo: ir.Expr = ir.Lit(ir.INT, loc, 0)
    elif isinstance(s, ir.ForRange):
        seq, idx, elem, lo = None, s.var, None, s.lo
    else:
        return out
    mod = ir.assigned_names(s.body)
    for st in s.body:
        if not (isinstance(st, ir.Assign) and st.name in known and isinstance(st.value, ir.Binary) and st.value.op == "add"):
            continue
        acc = st.name
        if ir.assigned_names([x for x in s.body if x is not st]) & {acc}:
            continue
        left, right = st.value.left, st.value.right
        if not (isinstance(left, ir.Var) and left.name == acc):
            continue
        term = right
        # Accept x (the element) or seq[idx] for some list seq.
        src = None
        if seq is not None and isinstance(term, ir.Var) and term.name == elem:
            src = seq
        elif isinstance(term, ir.Index) and isinstance(term.idx, ir.Var) and term.idx.name == idx and not _mentions(term.seq, mod):
            src = term.seq
        if src is None or not isinstance(src.ty, ir.TList) or _mentions(src, mod):
            continue
        init = _initial(site, acc)
        if init is None or _mentions(init, mod):
            continue
        ity = ir.INT
        prefix = ir.Builtin(src.ty, loc, "slice", (src, ir.Lit(ir.NONE, loc, None), ir.Var(ity, loc, idx)))
        if seq is None and not (isinstance(lo, ir.Lit) and lo.value == 0):
            prefix = ir.Builtin(src.ty, loc, "slice", (src, lo, ir.Var(ity, loc, idx)))
        total = ir.Builtin(src.ty.elem, loc, "sum", (prefix,))
        rhs = total if isinstance(init, ir.Lit) and init.value == 0 else ir.Binary(total.ty, loc, "add", init, total)
        if rhs.ty != fn.locals.get(acc):
            continue
        out.append(ir.Binary(ir.BOOL, loc, "eq", ir.Var(rhs.ty, loc, acc), rhs))
    return out


def variant_candidates(fn: ir.Function, s: ir.While) -> list[ir.Expr]:
    loc = ir.Loc(s.loc.line)
    out: list[ir.Expr] = []
    one = _int(1, loc)
    for c in _comparisons(s.cond):
        a, b = c.left, c.right
        if not (isinstance(a.ty, ir.TInt) and isinstance(b.ty, ir.TInt)):
            continue
        d_ba = ir.Binary(ir.INT, loc, "sub", b, a)
        d_ab = ir.Binary(ir.INT, loc, "sub", a, b)
        if c.op == "lt":
            out.append(d_ba)
        elif c.op == "le":
            out.append(ir.Binary(ir.INT, loc, "add", d_ba, one))
        elif c.op == "gt":
            out.append(d_ab)
        elif c.op == "ge":
            out.append(ir.Binary(ir.INT, loc, "add", d_ab, one))
        elif c.op == "ne":
            out += [d_ba, d_ab]
    for n, t in fn.locals.items():
        if isinstance(t, ir.TInt) and "$" not in n and n in ir.assigned_names(s.body):
            out.append(_v(n, ir.INT, loc))
    return out


def measure_candidates(fn: ir.Function) -> list[ir.Expr]:
    loc = fn.loc
    out: list[ir.Expr] = []
    ints = [p for p in fn.params if isinstance(p.ty, ir.TInt)]
    for p in ints:
        out.append(_v(p.name, ir.INT, loc))
    for p in fn.params:
        if isinstance(p.ty, ir.TList):
            out.append(ir.Builtin(ir.INT, loc, "len", (_v(p.name, p.ty, loc),)))
    for p in ints:
        for q in ints:
            if p.name != q.name:
                out.append(ir.Binary(ir.INT, loc, "sub", _v(q.name, ir.INT, loc), _v(p.name, ir.INT, loc)))
                out.append(ir.Binary(ir.INT, loc, "add", ir.Binary(ir.INT, loc, "sub", _v(q.name, ir.INT, loc), _v(p.name, ir.INT, loc)), _int(1, loc)))
    return out


@dataclass
class Inferred:
    options: Options = field(default_factory=Options)
    invariants: dict[int, list[ir.Clause]] = field(default_factory=dict)
    variants: dict[int, str] = field(default_factory=dict)
    measure: str | None = None
    solver_calls: int = 0

    def summary(self) -> dict:
        return {
            "method": "inference",
            "inv": {str(k): [c.text for c in v] for k, v in self.invariants.items()},
            "var": {str(k): v for k, v in self.variants.items()},
            "measure": self.measure,
        }


def _all_proved(obs, theory: Theory, timeout_ms: int, inf: Inferred) -> bool:
    for ob in obs:
        inf.solver_calls += 1
        if solve(ob, theory, timeout_ms).status != "proved":
            return False
    return True


def from_cache(fn: ir.Function, ref: FuncRef, sites: list[LoopSite], cached: dict) -> Inferred:
    inf = Inferred()
    for site in sites:
        line = site.stmt.loc.line
        keep = set(cached.get("inv", {}).get(str(line), []))
        cs = [c for c in invariant_candidates(fn, site) if c.text in keep]
        if cs:
            inf.invariants[line] = cs
        want = cached.get("var", {}).get(str(line))
        if want and isinstance(site.stmt, ir.While):
            for cand in variant_candidates(fn, site.stmt):
                if render(cand) == want:
                    inf.options.variants[line] = cand
                    inf.variants[line] = want
                    break
    inf.options.extra_invariants = inf.invariants
    if cached.get("measure"):
        for cand in measure_candidates(fn):
            if render(cand) == cached["measure"]:
                inf.options.measures[ref.key] = cand
                inf.measure = cached["measure"]
                break
    return inf


def infer(program: Program, ref: FuncRef, theory: Theory, timeout_ms: int = 3000, cached: dict | None = None) -> Inferred:
    fn = ref.fn
    sites = loop_sites(fn.body)
    if cached is not None and cached.get("method") == "inference":
        return from_cache(fn, ref, sites, cached)
    inf = Inferred()

    # 1. Houdini over candidate loop invariants.
    cands: dict[int, list[ir.Clause]] = {}
    for site in sites:
        cs = invariant_candidates(fn, site)
        if cs:
            cands[site.stmt.loc.line] = cs
    if cands:
        for _ in range(MAX_ROUNDS):
            opts = Options(extra_invariants=cands)
            try:
                obs = VCGen(program, ref, opts).run()
            except VCError:
                cands = {}
                break
            failed: set[int] = set()
            for ob in obs:
                if ob.kind in ("inv.entry", "inv.step") and ob.clause is not None and ob.clause.inferred:
                    if id(ob.clause) in failed:
                        continue
                    inf.solver_calls += 1
                    if solve(ob, theory, timeout_ms).status != "proved":
                        failed.add(id(ob.clause))
            if not failed:
                break
            cands = {line: [c for c in cs if id(c) not in failed] for line, cs in cands.items()}
            cands = {line: cs for line, cs in cands.items() if cs}
        inf.invariants = cands
        inf.options.extra_invariants = cands

    # 2. Loop variants for while-loops without '@decreases'.
    for site in sites:
        s = site.stmt
        if not isinstance(s, ir.While) or s.decreases is not None:
            continue
        for cand in variant_candidates(fn, s):
            opts = Options(extra_invariants=inf.options.extra_invariants, variants={**inf.options.variants, s.loc.line: cand})
            try:
                obs = VCGen(program, ref, opts).run()
            except VCError:
                break
            vobs = [o for o in obs if o.kind == "variant" and o.loc.line == s.loc.line]
            if vobs and _all_proved(vobs, theory, timeout_ms, inf):
                inf.options.variants[s.loc.line] = cand
                inf.variants[s.loc.line] = render(cand)
                break

    # 3. Recursion measure for self-recursive functions without '@decreases'.
    if ref.key in program.recursive and fn.decreases is None:
        scc = [k for k in program.funcs if program.same_scc(ref.key, k)]
        if scc == [ref.key]:
            for cand in measure_candidates(fn):
                opts = Options(
                    extra_invariants=inf.options.extra_invariants,
                    variants=inf.options.variants,
                    measures={ref.key: cand},
                )
                try:
                    obs = VCGen(program, ref, opts).run()
                except VCError:
                    break
                vobs = [o for o in obs if o.kind == "variant" and o.site is None and "recurs" in o.message]
                if vobs and _all_proved(vobs, theory, timeout_ms, inf):
                    inf.options.measures[ref.key] = cand
                    inf.measure = render(cand)
                    break
    return inf
