"""Verification-condition generation by symbolic execution.

Each function is executed symbolically from a state where its parameters are
fresh constants and its ``@requires`` hold. Every point where the program or
its contract can go wrong becomes one :class:`Obligation` -- a list of
hypotheses and one goal -- tagged with the exact source location it is about:

* ``ensures``        a postcondition, checked at every ``return``
* ``call``           a callee's ``@requires`` at a call site
* ``inv.entry``      a loop invariant holds before the loop
* ``inv.step``       ... and is preserved by one iteration
* ``variant``        a loop / recursion measure is bounded and decreases
* ``assert``         ``@assert`` and native ``assert`` statements
* ``div``            division / modulo by zero
* ``index``          list index out of bounds
* ``raise``          a ``raise`` is reachable outside its ``@raises`` condition
* ``return``         control can fall off the end of a value-returning function

Calls are modular: a call site proves the callee's precondition and assumes
its postcondition, so a function's proof depends only on its own body and the
*contracts* of what it calls. That is the locality property the ledger's
cache exploits: editing a body invalidates only that body's obligations.

Branches are merged (``ite``) rather than enumerated, so the number of
obligations grows with the size of the function, not with its path count.
"""

from __future__ import annotations

import itertools
from dataclasses import dataclass, field
from fractions import Fraction
from typing import Union

from . import ir
from . import logic as L
from .program import FuncRef, Program

# ---------------------------------------------------------------------------
# Symbolic values


@dataclass(frozen=True)
class ListVal:
    arr: L.Term
    off: L.Term
    len: L.Term
    ty: ir.TList

    def at(self, i: L.Term) -> L.Term:
        return L.select(self.arr, L.add(self.off, i))


Val = Union[L.Term, ListVal]
NONE_V = L.Const("None", L.Sort("None"))


def sort_of(ty: ir.Type) -> L.Sort:
    if isinstance(ty, ir.TInt):
        return L.INT
    if isinstance(ty, ir.TReal):
        return L.REAL
    if isinstance(ty, ir.TBool):
        return L.BOOL
    if isinstance(ty, ir.TStr):
        return L.STR
    if isinstance(ty, ir.TRecord):
        return L.REC(ty.name, tuple((n, sort_of(t)) for n, t in ty.fields))
    if isinstance(ty, ir.TList):
        return L.ARRAY(sort_of(ty.elem))
    raise VCError(f"no logical sort for {ty}")


def ite_val(c: L.Term, a: Val, b: Val) -> Val:
    if isinstance(a, ListVal) and isinstance(b, ListVal):
        return ListVal(L.ite(c, a.arr, b.arr), L.ite(c, a.off, b.off), L.ite(c, a.len, b.len), a.ty)
    assert not isinstance(a, ListVal) and not isinstance(b, ListVal)
    return L.ite(c, a, b)


def flatten(v: Val) -> tuple[L.Term, ...]:
    if isinstance(v, ListVal):
        return (v.arr, v.off, v.len)
    return (v,)


class VCError(Exception):
    """An internal limitation hit while generating VCs (reported, not hidden)."""

    def __init__(self, msg: str, loc: ir.Loc | None = None):
        super().__init__(msg)
        self.loc = loc


# ---------------------------------------------------------------------------
# Obligations


@dataclass
class Obligation:
    id: str
    func: str  # FuncRef key
    kind: str
    loc: ir.Loc  # the clause / construct the obligation is about
    site: ir.Loc | None  # where it is checked (return, call, loop end)
    message: str
    hyps: list[L.Term]
    goal: L.Term
    clause: ir.Clause | None = None
    intents: tuple[str, ...] = ()
    inputs: list[tuple[str, Val]] = field(default_factory=list)
    deps: set[str] = field(default_factory=set)  # callee contracts assumed
    exclude_axioms: set[str] = field(default_factory=set)
    inferred: bool = False  # about an inferred invariant / measure
    candidate: str | None = None  # Houdini candidate id this is about

    def formula(self) -> L.Term:
        return L.implies(L.and_(*self.hyps), self.goal)


@dataclass
class Exit:
    facts: list[L.Term]
    value: Val | None
    env: dict[str, Val]
    loc: ir.Loc


# ---------------------------------------------------------------------------
# Evaluation contexts


class State:
    def __init__(self, env: dict[str, Val], facts: list[L.Term]):
        self.env = env
        self.facts = facts
        self.alive = True

    def copy(self) -> "State":
        s = State(dict(self.env), list(self.facts))
        s.alive = self.alive
        return s


@dataclass
class Ctx:
    """Where an expression is being evaluated.

    ``base`` is the fact list of the enclosing state (shared, so assumptions
    made by calls land in the state). ``guard`` are extra conditions that hold
    only within this sub-expression (short-circuit operands, quantifier
    ranges); assumptions made under a guard are recorded as implications.
    """

    base: list[L.Term]
    env: dict[str, Val]
    module: ir.Module
    guard: tuple[L.Term, ...] = ()
    bound: dict[str, Val] = field(default_factory=dict)
    old_env: dict[str, Val] | None = None
    result: Val | None = None
    spec: bool = False
    quiet: bool = False  # suppress safety obligations (callee specs)
    state: State | None = None
    label: str = ""

    def sub(self, cond: L.Term | None = None, **kw) -> "Ctx":
        c = Ctx(
            base=self.base,
            env=self.env,
            module=self.module,
            guard=self.guard + ((cond,) if cond is not None else ()),
            bound=dict(self.bound),
            old_env=self.old_env,
            result=self.result,
            spec=self.spec,
            quiet=self.quiet,
            state=self.state,
            label=self.label,
        )
        for k, v in kw.items():
            setattr(c, k, v)
        return c

    def hyps(self) -> list[L.Term]:
        return list(self.base) + list(self.guard)

    def assume(self, t: L.Term) -> None:
        self.base.append(L.implies(L.and_(*self.guard), t) if self.guard else t)


@dataclass
class LoopFrame:
    breaks: list[State] = field(default_factory=list)
    continues: list[State] = field(default_factory=list)


# ---------------------------------------------------------------------------


@dataclass
class Options:
    # Extra loop invariants (by loop line) -- used by Houdini inference.
    extra_invariants: dict[int, list[ir.Clause]] = field(default_factory=dict)
    # Loop variants (by loop line) overriding / supplying '@decreases'.
    variants: dict[int, ir.Expr] = field(default_factory=dict)
    # Function measures (by FuncRef key) for recursion.
    measures: dict[str, ir.Expr] = field(default_factory=dict)


class VCGen:
    def __init__(self, program: Program, ref: FuncRef, opts: Options | None = None, inputs: dict[str, Val] | None = None):
        self.input_override = inputs or {}
        self.program = program
        self.ref = ref
        self.fn = ref.fn
        self.module = ref.module
        self.opts = opts or Options()
        self.obligations: list[Obligation] = []
        self.exits: list[Exit] = []
        self.loops: list[LoopFrame] = []
        self.counter = itertools.count(1)
        self.ids: dict[str, int] = {}
        self.deps: set[str] = set()
        self.theory_fns: set[str] = set()
        self.entry: dict[str, Val] = {}
        self.inputs: list[tuple[str, Val]] = []
        self.assumptions: list[tuple[ir.Loc, str]] = []
        self.definitional_mode = False
        self.raise_paths: list[list[L.Term]] = []
        self.loop_notes: list[tuple[int, str]] = []

    # -- naming -----------------------------------------------------------

    def fresh(self, base: str, ty: ir.Type, len_: L.Term | None = None) -> Val:
        n = next(self.counter)
        if isinstance(ty, ir.TList):
            arr = L.Const(f"{base}@{n}.arr", sort_of(ty))
            ln = len_ if len_ is not None else L.Const(f"{base}@{n}.len", L.INT)
            return ListVal(arr, L.ZERO, ln, ty)
        return L.Const(f"{base}@{n}", sort_of(ty))

    def param_val(self, name: str, ty: ir.Type) -> Val:
        if isinstance(ty, ir.TList):
            return ListVal(L.Const(f"{name}.arr", sort_of(ty)), L.ZERO, L.Const(f"{name}.len", L.INT), ty)
        return L.Const(name, sort_of(ty))

    # -- obligations ------------------------------------------------------

    def oblige(
        self,
        kind: str,
        ctx: Ctx,
        goal: L.Term,
        loc: ir.Loc,
        message: str,
        site: ir.Loc | None = None,
        clause: ir.Clause | None = None,
        inferred: bool = False,
    ) -> None:
        if ctx.quiet or self.definitional_mode:
            return
        base = f"{kind}@{loc.line}" + (f">{site.line}" if site is not None and site.line != loc.line else "")
        k = self.ids.get(base, 0)
        self.ids[base] = k + 1
        oid = f"{self.fn.name}/{base}" + (f"#{k + 1}" if k else "")
        excl = {key for key in self.program.funcs if self.program.same_scc(self.ref.key, key)}
        if self.ref.key in self.program.definitional:
            excl.add(self.ref.key)
        self.obligations.append(
            Obligation(
                id=oid,
                func=self.ref.key,
                kind=kind,
                loc=loc,
                site=site,
                message=message,
                hyps=ctx.hyps(),
                goal=goal,
                clause=clause,
                intents=clause.intents if clause else (),
                inputs=list(self.inputs),
                deps=set(self.deps),
                exclude_axioms=excl,
                inferred=inferred or (clause.inferred if clause else False),
            )
        )

    # -- entry point ------------------------------------------------------

    def run(self) -> list[Obligation]:
        fn = self.fn
        env: dict[str, Val] = {}
        facts: list[L.Term] = []
        for p in fn.params:
            v = self.input_override.get(p.name) or self.param_val(p.name, p.ty)
            env[p.name] = v
            self.inputs.append((p.name, v))
            if isinstance(v, ListVal):
                facts.append(L.le(L.ZERO, v.len))
        self.entry = dict(env)
        st = State(env, facts)
        ctx = self.ctx(st, spec=True)
        for r in fn.requires:
            # Preconditions must be well-defined given the earlier ones.
            t = self.ev(r.expr, ctx.sub(label="requires"))
            st.facts.append(t)
        st = self.block(fn.body, st)
        if st.alive and fn.ret != ir.NONE:
            self.oblige(
                "return",
                self.ctx(st),
                L.FALSE,
                ir.Loc(fn.end_line),
                f"'{fn.name}' can reach its end without returning a value",
            )
        if st.alive:
            self.exits.append(Exit(list(st.facts), None, dict(st.env), ir.Loc(fn.end_line)))
        self.check_exits()
        return self.obligations

    def ctx(self, st: State, **kw) -> Ctx:
        c = Ctx(base=st.facts, env=st.env, module=self.module, state=st)
        for k, v in kw.items():
            setattr(c, k, v)
        return c

    def post_env(self, exit_env: dict[str, Val]) -> dict[str, Val]:
        """What a caller can observe: scalar parameters keep their entry
        values; list parameters show their final contents."""
        out: dict[str, Val] = {}
        for p in self.fn.params:
            out[p.name] = exit_env[p.name] if isinstance(p.ty, ir.TList) else self.entry[p.name]
        return out

    def check_exits(self) -> None:
        fn = self.fn
        for ex in self.exits:
            if ex.value is None and fn.ret != ir.NONE:
                continue  # falling off the end is its own ('return') obligation
            st = State(dict(ex.env), list(ex.facts))
            penv = self.post_env(ex.env)
            for en in fn.ensures:
                ctx = Ctx(base=st.facts, env=penv, module=self.module, old_env=self.entry, result=ex.value, spec=True)
                goal = self.ev(en.expr, ctx.sub(label="ensures"))
                self.oblige(
                    "ensures",
                    ctx,
                    goal,
                    en.loc,
                    f"postcondition '{en.text}'",
                    site=ex.loc,
                    clause=en,
                )
            if fn.raises:
                ctx = Ctx(base=st.facts, env=self.entry, module=self.module, spec=True, quiet=True)
                cond = L.or_(*[self.ev(r.expr, ctx) for r in fn.raises])
                self.oblige(
                    "raises",
                    ctx,
                    L.not_(cond),
                    fn.raises[0].loc,
                    f"returns normally although '@raises {fn.raises[0].text}' holds",
                    site=ex.loc,
                    clause=fn.raises[0],
                )

    # -- statements -------------------------------------------------------

    def block(self, stmts, st: State) -> State:
        for s in stmts:
            if not st.alive:
                break
            st = self.stmt(s, st)
        return st

    def stmt(self, s: ir.Stmt, st: State) -> State:
        if isinstance(s, ir.Assign):
            st.env[s.name] = self.ev(s.value, self.ctx(st))
            return st
        if isinstance(s, ir.IndexAssign):
            lst = st.env[s.name]
            assert isinstance(lst, ListVal)
            ctx = self.ctx(st)
            i = self.index_of(lst, self.ev(s.idx, ctx), s.wrap, ctx, s.loc, s.name)
            v = self.ev(s.value, ctx)
            st.env[s.name] = ListVal(L.store(lst.arr, L.add(lst.off, i), v), lst.off, lst.len, lst.ty)
            return st
        if isinstance(s, ir.Append):
            lst = st.env[s.name]
            assert isinstance(lst, ListVal)
            v = self.ev(s.value, self.ctx(st))
            st.env[s.name] = ListVal(L.store(lst.arr, L.add(lst.off, lst.len), v), lst.off, L.add(lst.len, L.ONE), lst.ty)
            return st
        if isinstance(s, ir.If):
            c = self.ev(s.cond, self.ctx(st))
            t = st.copy()
            t.facts.append(c)
            t = self.block(s.then, t)
            e = st.copy()
            e.facts.append(L.not_(c))
            e = self.block(s.orelse, e)
            return self.merge([t, e])
        if isinstance(s, ir.While):
            return self.loop_while(s, st)
        if isinstance(s, ir.ForRange):
            return self.loop_range(s, st)
        if isinstance(s, ir.ForEach):
            return self.loop_each(s, st)
        if isinstance(s, ir.Return):
            v = self.ev(s.value, self.ctx(st)) if s.value is not None else None
            self.exits.append(Exit(list(st.facts), v, dict(st.env), s.loc))
            st.alive = False
            return st
        if isinstance(s, ir.Break):
            self.loops[-1].breaks.append(st.copy())
            st.alive = False
            return st
        if isinstance(s, ir.Continue):
            self.loops[-1].continues.append(st.copy())
            st.alive = False
            return st
        if isinstance(s, ir.AssertStmt):
            # A native assert runs (with effects); an '@assert' comment never does.
            ctx = self.ctx(st) if s.native else self.ctx(st, spec=True)
            g = self.ev(s.clause.expr, ctx)
            what = "assert" if s.native else "@assert"
            self.oblige("assert", ctx, g, s.clause.loc, f"{what} {s.clause.text}", clause=s.clause)
            st.facts.append(g)
            return st
        if isinstance(s, ir.AssumeStmt):
            g = self.ev(s.clause.expr, self.ctx(st, spec=True))
            st.facts.append(g)
            self.assumptions.append((s.clause.loc, s.clause.text))
            return st
        if isinstance(s, ir.Raise):
            self.raise_paths.append(list(st.facts))
            ctx = self.ctx(st)
            if self.fn.raises:
                ectx = Ctx(base=st.facts, env=self.entry, module=self.module, spec=True, quiet=True)
                cond = L.or_(*[self.ev(r.expr, ectx) for r in self.fn.raises])
                self.oblige("raise", ctx, cond, s.loc, f"raise {s.what} outside '@raises {self.fn.raises[0].text}'")
            else:
                self.oblige("raise", ctx, L.FALSE, s.loc, f"raise {s.what} is reachable (add '@raises <condition>' if intended)")
            st.alive = False
            return st
        if isinstance(s, ir.ExprStmt):
            self.ev(s.expr, self.ctx(st))
            return st
        if isinstance(s, ir.Unsupported):
            raise VCError(s.reason, s.loc)
        raise VCError(f"unhandled statement {type(s).__name__}", s.loc)

    # -- merging ----------------------------------------------------------

    def merge(self, states: list[State]) -> State:
        live = [s for s in states if s.alive]
        if not live:
            dead = states[0].copy()
            dead.alive = False
            return dead
        if len(live) == 1:
            return live[0]
        k = 0
        first = live[0].facts
        while all(len(s.facts) > k and s.facts[k] is first[k] for s in live):
            k += 1
        guards = [L.and_(*s.facts[k:]) for s in live]
        facts = list(first[:k]) + [L.or_(*guards)]
        env: dict[str, Val] = {}
        names = set().union(*(s.env.keys() for s in live))
        for name in names:
            vals = [s.env.get(name) for s in live]
            if any(v is None for v in vals):
                continue  # possibly unbound: reading it later is an error, not a guess
            if all(v == vals[0] for v in vals):
                env[name] = vals[0]  # type: ignore[assignment]
                continue
            out = vals[-1]
            for g, v in zip(reversed(guards[:-1]), reversed(vals[:-1])):
                out = ite_val(g, v, out)  # type: ignore[arg-type]
            env[name] = out  # type: ignore[assignment]
        st = State(env, facts)
        return st

    # -- loops ------------------------------------------------------------

    def modified(self, stmts) -> tuple[set[str], set[str]]:
        """(names possibly reassigned/mutated, list names possibly appended)."""
        names = ir.assigned_names(stmts)
        appends: set[str] = set()
        for s in ir.walk_stmts(stmts):
            if isinstance(s, ir.Append):
                appends.add(s.name)
            elif isinstance(s, ir.Assign) and isinstance(self.fn.locals.get(s.name), ir.TList):
                appends.add(s.name)
            for e in ir.stmt_exprs(s):
                for sub in ir.walk_expr(e):
                    if isinstance(sub, ir.Call):
                        tgt = self.program.resolve(self.module, sub.func)
                        if tgt is None:
                            continue
                        for p, a in zip(tgt.fn.params, sub.args):
                            if isinstance(a, ir.Var) and p.name in self.program.mutated.get(tgt.key, ()):
                                names.add(a.name)
                                if p.name in self.program.appends.get(tgt.key, ()):
                                    appends.add(a.name)
        return names, appends

    def havoc(self, st: State, names: set[str], appends: set[str]) -> State:
        h = st.copy()
        for name in sorted(names):
            if name not in h.env:
                continue
            old = h.env[name]
            ty = self.fn.locals.get(name)
            if ty is None:
                continue
            if isinstance(old, ListVal):
                keep = None if name in appends else old.len
                nv = self.fresh(name, ty, len_=keep)
                assert isinstance(nv, ListVal)
                if keep is None:
                    h.facts.append(L.le(L.ZERO, nv.len))
                else:
                    nv = ListVal(nv.arr, old.off, keep, nv.ty)
                h.env[name] = nv
            else:
                h.env[name] = self.fresh(name, ty)
        return h

    def invariants_for(self, line: int, user: tuple[ir.Clause, ...]) -> list[ir.Clause]:
        return list(user) + list(self.opts.extra_invariants.get(line, []))

    def check_invs(self, invs: list[ir.Clause], st: State, kind: str, site: ir.Loc, env_override: dict[str, Val] | None = None) -> None:
        env = dict(st.env)
        if env_override:
            env.update(env_override)
        for inv in invs:
            ctx = Ctx(base=st.facts, env=env, module=self.module, state=None, spec=True)
            g = self.ev(inv.expr, ctx.sub(label="invariant"))
            what = "holds on entry" if kind == "inv.entry" else "is preserved"
            self.oblige(kind, ctx, g, inv.loc, f"loop invariant '{inv.text}' {what}", site=site, clause=inv)

    def assume_invs(self, invs: list[ir.Clause], st: State, env_override: dict[str, Val] | None = None) -> None:
        env = dict(st.env)
        if env_override:
            env.update(env_override)
        for inv in invs:
            ctx = Ctx(base=st.facts, env=env, module=self.module, spec=True, quiet=True)
            st.facts.append(self.ev(inv.expr, ctx))

    def run_iteration(self, body, st: State) -> tuple[State, LoopFrame]:
        frame = LoopFrame()
        self.loops.append(frame)
        try:
            end = self.block(body, st)
        finally:
            self.loops.pop()
        return end, frame

    def loop_while(self, s: ir.While, st: State) -> State:
        invs = self.invariants_for(s.loc.line, s.invariants)
        self.check_invs(invs, st, "inv.entry", s.loc)
        names, appends = self.modified(list(s.body) + list(s.step) + [ir.ExprStmt(s.loc, s.cond)])
        head = self.havoc(st, names, appends)
        self.assume_invs(invs, head)
        c = self.ev(s.cond, self.ctx(head))
        body_st = head.copy()
        body_st.facts.append(c)
        variant = s.decreases.expr if s.decreases is not None else self.opts.variants.get(s.loc.line)
        v0 = None
        if variant is not None:
            vctx = self.ctx(body_st, spec=True)
            v0 = self.ev(variant, vctx)
            self.oblige(
                "variant",
                vctx,
                L.le(L.ZERO, v0),
                s.decreases.loc if s.decreases else s.loc,
                f"loop measure '{_expr_text(s.decreases, variant)}' is non-negative",
                inferred=s.decreases is None,
            )
        end, frame = self.run_iteration(s.body, body_st)
        for it_end in [end] + frame.continues:
            if not it_end.alive:
                continue
            it_end = self.block(s.step, it_end)
            if not it_end.alive:
                continue
            self.check_invs(invs, it_end, "inv.step", s.loc)
            if v0 is not None:
                vctx = self.ctx(it_end, spec=True)
                v1 = self.ev(variant, vctx)  # type: ignore[arg-type]
                self.oblige(
                    "variant",
                    vctx,
                    L.lt(v1, v0),
                    s.decreases.loc if s.decreases else s.loc,
                    f"loop measure '{_expr_text(s.decreases, variant)}' decreases",
                    inferred=s.decreases is None,
                )
        if v0 is None:
            self.loop_notes.append((s.loc.line, "no-variant"))
        out = head.copy()
        out.facts.append(L.not_(c))
        return self.merge([out] + frame.breaks)

    def _counted_loop(self, s, st: State, lo_v: L.Term, hi_v: L.Term, idx: str, bind) -> State:
        """Shared shape of ``for i in range`` and ``for x in xs``.

        The hidden counter ``k`` runs over ``[lo, hi)``; invariants see the
        index name bound to ``k`` (the *next* iteration), so after the last
        iteration it equals ``hi``.
        """
        invs = self.invariants_for(s.loc.line, s.invariants)
        counter = f"{idx}$k"
        view_entry = {idx: lo_v}
        entry = st.copy()
        entry.env[counter] = lo_v
        self.check_invs(invs, entry, "inv.entry", s.loc, view_entry)
        names, appends = self.modified(s.body)
        names = set(names) | {counter}
        self.fn.locals.setdefault(counter, ir.INT)
        head = self.havoc(entry, names, appends)
        k = head.env[counter]
        assert not isinstance(k, ListVal)
        # By construction the counter stays within [lo, max(lo, hi)].
        head.facts.append(L.le(lo_v, k))
        head.facts.append(L.le(k, L.max_(lo_v, hi_v)))
        view = {idx: k}
        self.assume_invs(invs, head, view)
        c = L.lt(k, hi_v)
        body_st = head.copy()
        body_st.facts.append(c)
        bind(body_st, k)
        end, frame = self.run_iteration(s.body, body_st)
        for it_end in [end] + frame.continues:
            if not it_end.alive:
                continue
            k1 = L.add(k, L.ONE)
            it_end.env[counter] = k1
            self.check_invs(invs, it_end, "inv.step", s.loc, {idx: k1})
        out = head.copy()
        out.facts.append(L.not_(c))
        return self.merge([out] + frame.breaks)

    def loop_range(self, s: ir.ForRange, st: State) -> State:
        ctx = self.ctx(st)
        lo_v = self.ev(s.lo, ctx)
        hi_v = self.ev(s.hi, ctx)
        prior = st.env.get(s.var)

        def bind(body_st: State, k: L.Term) -> None:
            body_st.env[s.var] = k

        if s.reeval:
            self._bound_fixed(s.hi, s.body, s.loc)
        out = self._counted_loop(s, st, lo_v, hi_v, s.var, bind)
        out.env.pop(f"{s.var}$k", None)
        if prior is None:
            out.env.pop(s.var, None)  # bound only if the loop ran: reading it is an error
        elif _has_break(s.body) or s.var in ir.assigned_names(s.body):
            out.env[s.var] = self.fresh(s.var, ir.INT)
        else:
            # After a completed range loop the variable holds hi - 1 (Python).
            out.env[s.var] = L.ite(L.lt(lo_v, hi_v), L.sub(hi_v, L.ONE), prior)
        return out

    def _bound_fixed(self, hi: ir.Expr, body, loc: ir.Loc) -> None:
        """JavaScript re-evaluates a for-loop condition every iteration; the
        counted-loop model needs its bound to stay put."""
        names, appends = self.modified(body)

        def changed(e: ir.Expr) -> set[str]:
            # len(xs) is fixed if the body only writes elements of xs
            if isinstance(e, ir.Builtin) and e.name == "len" and isinstance(e.args[0], ir.Var):
                v = e.args[0].name
                return {v} if v in appends else set()
            if isinstance(e, ir.Var):
                return {e.name} & names
            out: set[str] = set()
            for child in _children(e):
                out |= changed(child)
            return out

        bad = changed(hi)
        if bad:
            raise VCError(f"the loop bound depends on {', '.join(sorted(bad))}, which the loop body changes", loc)

    def loop_each(self, s: ir.ForEach, st: State) -> State:
        ctx = self.ctx(st)
        seq = self.ev(s.seq, ctx)
        assert isinstance(seq, ListVal)
        names, _ = self.modified(s.body)
        seq_vars = {x.name for x in ir.walk_expr(s.seq) if isinstance(x, ir.Var)}
        if names & seq_vars:
            raise VCError(f"the loop body changes {', '.join(sorted(names & seq_vars))} while iterating over it", s.loc)
        before = set(st.env)

        def bind(body_st: State, k: L.Term) -> None:
            body_st.env[s.elem] = seq.at(k)
            body_st.env[s.idx] = k

        out = self._counted_loop(s, st, L.ZERO, seq.len, s.idx, bind)
        out.env.pop(f"{s.idx}$k", None)
        for name in (s.elem, s.idx):
            if name in before and name in self.fn.locals:
                out.env[name] = self.fresh(name, self.fn.locals[name])
            else:
                out.env.pop(name, None)
        return out

    # -- expressions ------------------------------------------------------

    def lookup(self, name: str, ctx: Ctx, loc: ir.Loc) -> Val:
        if name in ctx.bound:
            return ctx.bound[name]
        if name in ctx.env:
            return ctx.env[name]
        raise VCError(f"'{name}' may be used before it is assigned", loc)

    def index_of(self, lst: ListVal, i: L.Term, wrap: bool, ctx: Ctx, loc: ir.Loc, what: str) -> L.Term:
        n = lst.len
        if wrap:
            ok = L.and_(L.le(L.neg(n), i), L.lt(i, n))
            self.oblige("index", ctx, ok, loc, f"index into '{what}' is within -len..len-1")
            return L.ite(L.lt(i, L.ZERO), L.add(i, n), i)
        ok = L.and_(L.le(L.ZERO, i), L.lt(i, n))
        self.oblige("index", ctx, ok, loc, f"index into '{what}' is within 0..len-1")
        return i

    def ev(self, e: ir.Expr, ctx: Ctx) -> Val:
        m = getattr(self, "ev_" + type(e).__name__)
        return m(e, ctx)

    def ev_Lit(self, e: ir.Lit, ctx: Ctx) -> Val:
        v = e.value
        if v is None:
            return NONE_V
        if isinstance(v, bool):
            return L.BoolV(v)
        if isinstance(v, int):
            if isinstance(e.ty, ir.TReal):
                return L.RealV(Fraction(v))
            return L.IntV(v)
        if isinstance(v, Fraction):
            return L.RealV(v)
        if isinstance(v, str):
            return L.StrV(v)
        raise VCError(f"unsupported literal {v!r}", e.loc)

    def ev_Var(self, e: ir.Var, ctx: Ctx) -> Val:
        return self.lookup(e.name, ctx, e.loc)

    def ev_Result(self, e: ir.Result, ctx: Ctx) -> Val:
        if ctx.result is None:
            raise VCError("'result' is not available here", e.loc)
        return ctx.result

    def ev_Old(self, e: ir.Old, ctx: Ctx) -> Val:
        if ctx.old_env is None:
            raise VCError("old(...) is only meaningful in '@ensures'", e.loc)
        return self.ev(e.expr, ctx.sub(env=ctx.old_env))

    def ev_Unary(self, e: ir.Unary, ctx: Ctx) -> Val:
        a = self.ev(e.arg, ctx)
        assert not isinstance(a, ListVal)
        if e.op == "neg":
            return L.neg(a)
        if e.op == "not":
            return L.not_(a)
        raise VCError(f"unknown unary operator {e.op}", e.loc)

    def ev_Binary(self, e: ir.Binary, ctx: Ctx) -> Val:
        op = e.op
        if op in ("and", "or", "implies"):
            a = self.ev(e.left, ctx)
            assert not isinstance(a, ListVal)
            b = self.ev(e.right, ctx.sub(a if op in ("and", "implies") else L.not_(a)))
            assert not isinstance(b, ListVal)
            return {"and": L.and_, "or": L.or_}[op](a, b) if op != "implies" else L.implies(a, b)
        a = self.ev(e.left, ctx)
        b = self.ev(e.right, ctx)
        if op in ("eq", "ne"):
            r = self.equal(a, b)
            return r if op == "eq" else L.not_(r)
        assert not isinstance(a, ListVal) and not isinstance(b, ListVal)
        if op == "add":
            return L.add(a, b)
        if op == "sub":
            return L.sub(a, b)
        if op == "mul":
            return L.mul(a, b)
        if op == "lt":
            return L.lt(a, b)
        if op == "le":
            return L.le(a, b)
        if op == "gt":
            return L.gt(a, b)
        if op == "ge":
            return L.ge(a, b)
        if op in ("rdiv", "floordiv", "fmod", "tmod"):
            zero = L.lit(0, b.sort)
            sym = {"rdiv": "/", "floordiv": "//", "fmod": "%", "tmod": "%"}[op]
            self.oblige("div", ctx, L.ne(b, zero), e.loc, f"divisor of '{sym}' is non-zero")
            if op == "rdiv":
                return L.rdiv(a, b)
            if a.sort == L.REAL:
                # % on reals: fmod floors the quotient, tmod truncates it
                q = L.rdiv(a, b)
                qi = L.floor(q) if op in ("fmod", "floordiv") else L.ite(L.le(L.RealV(Fraction(0)), q), L.floor(q), L.neg(L.floor(L.neg(q))))
                if op == "floordiv":
                    return L.to_real(qi)
                return L.sub(a, L.mul(b, L.to_real(qi)))
            if op == "floordiv":
                return floordiv(a, b)
            if op == "fmod":
                return L.sub(a, L.mul(b, floordiv(a, b)))
            return L.sub(a, L.mul(b, truncdiv(a, b)))
        raise VCError(f"unknown operator {op}", e.loc)

    def equal(self, a: Val, b: Val) -> L.Term:
        if isinstance(a, ListVal) or isinstance(b, ListVal):
            assert isinstance(a, ListVal) and isinstance(b, ListVal)
            i = L.Const(f"eq!{next(self.counter)}", L.INT)
            same = L.forall([i], L.implies(L.and_(L.le(L.ZERO, i), L.lt(i, a.len)), L.eq(a.at(i), b.at(i))))
            return L.and_(L.eq(a.len, b.len), same)
        return L.eq(a, b)

    def ev_Ite(self, e: ir.Ite, ctx: Ctx) -> Val:
        c = self.ev(e.cond, ctx)
        assert not isinstance(c, ListVal)
        a = self.ev(e.then, ctx.sub(c))
        b = self.ev(e.orelse, ctx.sub(L.not_(c)))
        return ite_val(c, a, b)

    def ev_Index(self, e: ir.Index, ctx: Ctx) -> Val:
        seq = self.ev(e.seq, ctx)
        assert isinstance(seq, ListVal)
        i = self.ev(e.idx, ctx)
        assert not isinstance(i, ListVal)
        j = self.index_of(seq, i, e.wrap, ctx, e.loc, _expr_name(e.seq))
        return seq.at(j)

    def ev_Field(self, e: ir.Field, ctx: Ctx) -> Val:
        obj = self.ev(e.obj, ctx)
        assert not isinstance(obj, ListVal)
        return L.field(obj, e.name)

    def ev_RecordLit(self, e: ir.RecordLit, ctx: Ctx) -> Val:
        vals = []
        for _, fe in e.fields:
            v = self.ev(fe, ctx)
            assert not isinstance(v, ListVal)
            vals.append(v)
        return L.mkrec(sort_of(e.ty), tuple(vals))

    def ev_ListLit(self, e: ir.ListLit, ctx: Ctx) -> Val:
        assert isinstance(e.ty, ir.TList)
        if e.ty.elem == ir.NONE:
            ty = ir.TList(ir.INT)
        else:
            ty = e.ty
        base = self.fresh("lit", ty, len_=L.ZERO)
        assert isinstance(base, ListVal)
        arr = base.arr
        for i, x in enumerate(e.elems):
            v = self.ev(x, ctx)
            assert not isinstance(v, ListVal)
            arr = L.store(arr, L.IntV(i), v)
        return ListVal(arr, L.ZERO, L.IntV(len(e.elems)), ty)

    def ev_Quant(self, e: ir.Quant, ctx: Ctx) -> Val:
        lo = self.ev(e.lo, ctx)
        hi = self.ev(e.hi, ctx)
        assert not isinstance(lo, ListVal) and not isinstance(hi, ListVal)
        i = L.Const(f"{e.idx.split('$')[0]}!{next(self.counter)}", L.INT)
        rng = L.and_(L.le(lo, i), L.lt(i, hi))
        sub = ctx.sub(rng)
        sub.bound[e.idx] = i
        if e.seq is not None and e.elem is not None:
            seq = self.ev(e.seq, ctx)
            assert isinstance(seq, ListVal)
            sub.bound[e.elem] = seq.at(i)
        body = self.ev(e.body, sub)
        assert not isinstance(body, ListVal)
        if e.kind == "forall":
            return L.forall([i], L.implies(rng, body))
        return L.exists([i], L.and_(rng, body))

    def ev_Builtin(self, e: ir.Builtin, ctx: Ctx) -> Val:
        name = e.name
        args = [self.ev(a, ctx) for a in e.args]
        if name == "len":
            (xs,) = args
            assert isinstance(xs, ListVal)
            return xs.len
        if name == "abs":
            return L.abs_(args[0])  # type: ignore[arg-type]
        if name in ("min", "max"):
            f = L.min_ if name == "min" else L.max_
            out = args[0]
            for a in args[1:]:
                out = f(out, a)  # type: ignore[arg-type]
            return out
        if name == "sum":
            (xs,) = args
            assert isinstance(xs, ListVal)
            fd = "seqsum" if xs.ty.elem == ir.INT else "seqsum_r"
            self.theory_fns.add(fd)
            return L.Fn(fd, (xs.arr, xs.off, L.add(xs.off, xs.len)), sort_of(xs.ty.elem))
        if name == "count":
            xs, v = args
            assert isinstance(xs, ListVal)
            fd = f"seqcount_{sort_of(xs.ty.elem).name.lower()}"
            self.theory_fns.add(fd)
            return L.Fn(fd, (xs.arr, xs.off, L.add(xs.off, xs.len), v), L.INT)  # type: ignore[arg-type]
        if name == "contains":
            xs, v = args
            assert isinstance(xs, ListVal)
            i = L.Const(f"in!{next(self.counter)}", L.INT)
            return L.exists([i], L.and_(L.le(L.ZERO, i), L.lt(i, xs.len), L.eq(xs.at(i), v)))  # type: ignore[arg-type]
        if name == "slice":
            xs, lo, hi = args
            assert isinstance(xs, ListVal)
            n = xs.len

            def norm(b: Val, default: L.Term) -> L.Term:
                if b is NONE_V:
                    return default
                assert not isinstance(b, ListVal)
                return L.ite(L.lt(b, L.ZERO), L.max_(L.add(b, n), L.ZERO), L.min_(b, n))

            lo2 = norm(lo, L.ZERO)
            hi2 = norm(hi, n)
            return ListVal(xs.arr, L.add(xs.off, lo2), L.max_(L.sub(hi2, lo2), L.ZERO), xs.ty)
        (x,) = args[:1]
        assert not isinstance(x, ListVal)
        if name == "to_real":
            return L.to_real(x)
        if name == "floor":
            return L.floor(x)
        if name == "ceil":
            return L.neg(L.floor(L.neg(x)))
        if name == "trunc":
            return L.ite(L.le(L.RealV(Fraction(0)), x), L.floor(x), L.neg(L.floor(L.neg(x))))
        if name == "round_even":
            return round_even(x)
        if name == "round_up":
            return L.floor(L.add(x, L.RealV(Fraction(1, 2))))
        if name == "is_int":
            return L.is_int(x)
        raise VCError(f"unknown builtin {name}", e.loc)

    def ev_Call(self, e: ir.Call, ctx: Ctx) -> Val:
        callee = self.program.resolve(ctx.module, e.func)
        if callee is None:
            raise VCError(f"unknown function '{e.func}'", e.loc)
        fn = callee.fn
        args = [self.ev(a, ctx) for a in e.args]
        # A list argument is a reference: a later argument that mutates the
        # same list changes what the callee sees. Re-read list variables.
        if ctx.state is not None:
            args = [ctx.state.env.get(a_e.name, a) if isinstance(a_e, ir.Var) and isinstance(a, ListVal) else a for a_e, a in zip(e.args, args)]
        muts = self.program.mutated.get(callee.key, set())
        list_vars = [a_e.name for a_e, p in zip(e.args, fn.params) if isinstance(a_e, ir.Var) and isinstance(p.ty, ir.TList)]
        if muts and len(list_vars) != len(set(list_vars)):
            raise VCError(f"the same list is passed twice to '{fn.name}', which mutates a list parameter; the two parameters would alias", e.loc)
        pmap: dict[str, Val] = {p.name: a for p, a in zip(fn.params, args)}
        definitional = callee.key in self.program.definitional
        if ctx.spec and not definitional:
            raise VCError(
                f"specs may only call pure (loop-free, mutation-free) functions; '{fn.name}' is not",
                e.loc,
            )
        # Callee preconditions.
        cctx = Ctx(base=ctx.base, env=pmap, module=callee.module, guard=ctx.guard, spec=True, quiet=True)
        for r in fn.requires:
            g = self.ev(r.expr, cctx)
            self.oblige(
                "call",
                ctx,
                g,
                e.loc,
                f"call to '{fn.name}' satisfies '@requires {r.text}'",
                clause=r,
            )
        if fn.raises and not ctx.spec:
            rc = L.or_(*[self.ev(r.expr, cctx) for r in fn.raises])
            self.oblige("call", ctx, L.not_(rc), e.loc, f"call to '{fn.name}' cannot raise ('@raises {fn.raises[0].text}')")
        # Termination of recursion.
        if self.program.same_scc(self.ref.key, callee.key):
            self.recursion_check(callee, pmap, ctx, e.loc)
        self.deps.add(callee.key)
        # Result.
        if definitional:
            r: Val = self.apply_def(callee, args)
        elif fn.ret == ir.NONE:
            r = NONE_V
        else:
            r = self.fresh(f"{fn.name}()", fn.ret)
        # Mutated list arguments get fresh contents.
        post = dict(pmap)
        if muts and ctx.state is not None:
            for p, a_expr in zip(fn.params, e.args):
                if p.name in muts:
                    if not isinstance(a_expr, ir.Var):
                        continue
                    old = ctx.state.env[a_expr.name]
                    assert isinstance(old, ListVal)
                    keep = None if p.name in self.program.appends.get(callee.key, ()) else old.len
                    nv = self.fresh(a_expr.name, p.ty, len_=keep)
                    assert isinstance(nv, ListVal)
                    if keep is not None:
                        nv = ListVal(nv.arr, old.off, keep, nv.ty)
                    else:
                        ctx.assume(L.le(L.ZERO, nv.len))
                    ctx.state.env[a_expr.name] = nv
                    post[p.name] = nv
        # Assume the postcondition (code context; spec calls use lemma axioms).
        if not ctx.spec and fn.ensures and not self.definitional_mode:
            ectx = Ctx(base=ctx.base, env=post, module=callee.module, guard=ctx.guard, old_env=pmap, result=r if r is not NONE_V else None, spec=True, quiet=True)
            for en in fn.ensures:
                ctx.assume(self.ev(en.expr, ectx))
        return r

    def apply_def(self, callee: FuncRef, args: list[Val]) -> L.Term:
        flat: list[L.Term] = []
        for a in args:
            flat.extend(flatten(a))
        return L.Fn(self.program.logic_names[callee.key], tuple(flat), sort_of(callee.fn.ret))

    def recursion_check(self, callee: FuncRef, pmap: dict[str, Val], ctx: Ctx, loc: ir.Loc) -> None:
        me = self.opts.measures.get(self.ref.key) or (self.fn.decreases.expr if self.fn.decreases else None)
        them = self.opts.measures.get(callee.key) or (callee.fn.decreases.expr if callee.fn.decreases else None)
        if me is None or them is None:
            self.oblige(
                "variant",
                ctx,
                L.FALSE,
                loc,
                f"recursive call to '{callee.fn.name}' terminates (add '@decreases <measure>')",
            )
            return
        mctx = Ctx(base=ctx.base, env=self.entry, module=self.module, guard=ctx.guard, spec=True, quiet=True)
        m0 = self.ev(me, mctx)
        cctx = Ctx(base=ctx.base, env=pmap, module=callee.module, guard=ctx.guard, spec=True, quiet=True)
        m1 = self.ev(them, cctx)
        inferred = self.fn.decreases is None
        self.oblige("variant", ctx, L.le(L.ZERO, m0), loc, "recursion measure is non-negative", inferred=inferred)
        self.oblige("variant", ctx, L.lt(m1, m0), loc, f"recursive call to '{callee.fn.name}' decreases the measure", inferred=inferred)


# ---------------------------------------------------------------------------
# Language arithmetic in terms of Euclidean division


def floordiv(a: L.Term, b: L.Term) -> L.Term:
    """Python ``a // b``: floor(a / b)."""
    return L.ite(L.lt(L.ZERO, b), L.ediv(a, b), L.ediv(L.neg(a), L.neg(b)))


def truncdiv(a: L.Term, b: L.Term) -> L.Term:
    """Truncating division (JavaScript ``Math.trunc(a / b)``)."""
    q = L.ediv(L.abs_(a), L.abs_(b))
    return L.ite(L.eq(L.le(L.ZERO, a), L.lt(L.ZERO, b)), q, L.neg(q))


def round_even(x: L.Term) -> L.Term:
    """Python ``round(x)``: nearest integer, ties to even."""
    f = L.floor(x)
    d = L.sub(x, L.to_real(f))
    half = L.RealV(Fraction(1, 2))
    return L.ite(
        L.lt(d, half),
        f,
        L.ite(L.lt(half, d), L.add(f, L.ONE), L.ite(L.eq(L.emod(f, L.IntV(2)), L.ZERO), f, L.add(f, L.ONE))),
    )


def _expr_name(e: ir.Expr) -> str:
    if isinstance(e, ir.Var):
        return e.name
    return "list"


def _expr_text(clause: ir.Clause | None, e: ir.Expr) -> str:
    if clause is not None:
        return clause.text
    from .render_expr import render

    return render(e)


def _children(e: ir.Expr) -> list[ir.Expr]:
    direct: list[ir.Expr] = []
    for name in ("arg", "left", "right", "cond", "then", "orelse", "expr", "seq", "idx", "obj", "lo", "hi", "body"):
        v = getattr(e, name, None)
        if isinstance(v, ir.Expr):
            direct.append(v)
    for name in ("args", "elems"):
        for v in getattr(e, name, ()) or ():
            if isinstance(v, ir.Expr):
                direct.append(v)
    if isinstance(e, ir.RecordLit):
        direct.extend(v for _, v in e.fields)
    return direct


def _has_break(stmts) -> bool:
    for s in ir.walk_stmts(stmts):
        if isinstance(s, ir.Break):
            return True
    return False


# ---------------------------------------------------------------------------
# Definitions of pure functions


def build_fundef(program: Program, ref: FuncRef, measure: ir.Expr | None) -> L.FunDef:
    """Turn a definitional function's body into a logical definition."""
    g = VCGen(program, ref)
    g.definitional_mode = True
    env: dict[str, Val] = {}
    params: list[L.Const] = []
    for p in ref.fn.params:
        v = g.param_val(p.name, p.ty)
        env[p.name] = v
        for t in flatten(v):
            if isinstance(t, L.Const):
                params.append(t)
            else:  # the zero offset of a list parameter becomes a real parameter
                c = L.Const(f"{p.name}.off", L.INT)
                params.append(c)
        if isinstance(v, ListVal):
            env[p.name] = ListVal(v.arr, L.Const(f"{p.name}.off", L.INT), v.len, v.ty)
    g.entry = dict(env)
    st = State(env, [])
    st = g.block(ref.fn.body, st)
    exits = [ex for ex in g.exits if ex.value is not None]
    if not exits:
        raise VCError(f"'{ref.fn.name}' never returns a value", ref.fn.loc)
    body = exits[-1].value
    assert body is not None and not isinstance(body, ListVal)
    for ex in reversed(exits[:-1]):
        assert ex.value is not None and not isinstance(ex.value, ListVal)
        body = L.ite(L.and_(*ex.facts), ex.value, body)
    # Outside its precondition a function has no meaning; giving it a fixed
    # default there keeps the definition total and well-founded (a recursive
    # equation that does not terminate could otherwise be inconsistent).
    rctx = Ctx(base=[], env=env, module=ref.module, spec=True, quiet=True)
    req = L.and_(*[g.ev(r.expr, rctx) for r in ref.fn.requires])
    inner = body
    if req != L.TRUE:
        body = L.ite(req, body, default_value(sort_of(ref.fn.ret)))
    name = program.logic_names[ref.key]
    m = None
    if measure is not None:
        mctx = Ctx(base=[], env=env, module=ref.module, spec=True, quiet=True)
        m = g.ev(measure, mctx)
    return L.FunDef(
        name,
        tuple(params),
        sort_of(ref.fn.ret),
        body,
        recursive=ref.key in program.recursive,
        measure=m,  # type: ignore[arg-type]
        doc=f"{ref.module.path}:{ref.fn.loc.line}",
        guard=req if req != L.TRUE else None,
        inner=inner,
    )


def default_value(s: L.Sort) -> L.Term:
    if s == L.INT:
        return L.ZERO
    if s == L.REAL:
        return L.RealV(Fraction(0))
    if s == L.BOOL:
        return L.FALSE
    if s == L.STR:
        return L.StrV("")
    if s.name == "Rec":
        return L.mkrec(s, tuple(default_value(fs) for _, fs in s.fields))
    raise VCError(f"no default value for {s}")


def build_axioms(program: Program, ref: FuncRef, fundef: L.FunDef) -> list[L.Axiom]:
    """A definitional function's ``@ensures`` become lemmas usable everywhere
    outside its own recursion group (where they would be circular)."""
    if not ref.fn.ensures:
        return []
    g = VCGen(program, ref)
    g.definitional_mode = True
    env: dict[str, Val] = {}
    it = iter(fundef.params)
    args: list[Val] = []
    for p in ref.fn.params:
        if isinstance(p.ty, ir.TList):
            arr, off, ln = next(it), next(it), next(it)
            v: Val = ListVal(arr, off, ln, p.ty)
        else:
            v = next(it)
        env[p.name] = v
        args.append(v)
    call = L.Fn(fundef.name, fundef.params, fundef.sort)
    base: list[L.Term] = []
    ctx = Ctx(base=base, env=env, module=ref.module, spec=True, quiet=True)
    hyps = [g.ev(r.expr, ctx) for r in ref.fn.requires]
    for p in ref.fn.params:
        v = env[p.name]
        if isinstance(v, ListVal):
            hyps.append(L.le(L.ZERO, v.len))
    ectx = Ctx(base=base, env=env, module=ref.module, old_env=env, result=call, spec=True, quiet=True)
    goals = [g.ev(en.expr, ectx) for en in ref.fn.ensures]
    formula = L.forall(fundef.params, L.implies(L.and_(*hyps), L.and_(*goals)))
    return [L.Axiom(f"{fundef.name}_spec", formula, about=ref.key, doc=f"@ensures of {ref.fn.name}")]
