"""Checking lifecycles as a whole: what the per-function obligations add up to.

Each function proves that the objects it may change keep every lifecycle
from its entry to its return (``lifecycle`` obligations, in ``vcgen``). This
module adds what makes those proofs mean something across calls:

* each relation is reflexive and transitive, so a sequence of calls that each
  keep it keeps it too (and an object a call leaves alone keeps it);
* each ``never A -> B`` follows from the class's other lifecycles, so it holds
  across any sequence of calls, not only within one;
* coverage: which steps some function can actually take (a satisfiable
  entry-to-return path), so a lifecycle nothing exercises reads ``vacuous``
  rather than proved, and unexercised transitions are listed.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any

from . import ir
from . import logic as L
from .program import FuncRef, Program
from .vcgen import Obligation, VCError, VCGen


@dataclass
class Step:
    label: str
    by: list[str] = field(default_factory=list)  # functions that take it
    unknown: bool = False  # some probe was undecided


@dataclass
class LifecycleReport:
    cls: str
    module: ir.Module
    lc: ir.Lifecycle
    status: str = "proved"  # proved | refuted | open | vacuous
    functions: list[str] = field(default_factory=list)  # names of the functions whose proofs back it
    problems: list[str] = field(default_factory=list)
    steps: list[Step] = field(default_factory=list)

    @property
    def clause(self) -> ir.Clause:
        return self.lc.clause

    @property
    def aims(self) -> tuple[str, ...]:
        return self.lc.clause.aims

    def to_json(self) -> dict[str, Any]:
        return {
            "class": ir.source_name(self.cls),
            "at": f"{self.module.path}:{self.clause.loc.line}",
            "kind": self.lc.kind,
            "text": self.clause.text,
            "status": self.status,
            "functions": self.functions,
            "problems": self.problems,
            "steps": [{"step": s.label, "by": s.by, "unknown": s.unknown} for s in self.steps],
        }


def _same_clause(ob: Obligation, c: ir.Clause) -> bool:
    if ob.clause is None:  # restored from a receipt: no clause, but its place and text
        return ob.loc == c.loc and ob.message.endswith(f"('{c.text}')")
    return ob.clause.loc == c.loc and ob.clause.text == c.text


class _Scope:
    """Abstract states of one object of a class, for class-level obligations."""

    def __init__(self, program: Program, cls: str):
        module = program.class_module[cls]
        decl = program.classes[cls]
        fn = ir.Function(f"{cls}.<lifecycle>", decl.loc, decl.loc.line, [ir.Param("self", ir.TClass(cls))], ir.NONE)
        self.gen = VCGen(program, FuncRef(module, fn))
        self.cls = cls
        self.module = module
        self.ref = L.Const("self", L.INT)
        base: dict = {}
        self.gen.heap_init(base)
        self.keys = [(k, v.sort) for k, v in base.items() if k.startswith("@")]  # type: ignore[union-attr]

    def state(self, i: int) -> dict:
        return {k: L.Const(f"{k[1:]}!{i}", srt) for k, srt in self.keys}

    def invariants(self, env: dict, base: list) -> list[L.Term]:
        return [t for _, t in self.gen.class_invariants(self.cls, self.ref, env, base)]

    def obligation(self, lc: ir.Lifecycle, what: str, hyps: list[L.Term], goal: L.Term) -> Obligation:
        return Obligation(id=f"{self.cls}/lifecycle.{what}@{lc.clause.loc.line}", func=f"{self.module.path}::{self.cls}", kind=f"lifecycle.{what}", loc=lc.clause.loc, site=None, message=what, hyps=hyps, goal=goal, clause=lc.clause)


def _may_change(program: Program, ref: FuncRef, family: set[str]) -> bool:
    fn = ref.fn
    if any(isinstance(p.ty, ir.TClass) and p.ty.name in family for p in fn.params):
        return True
    if any(fn.name.startswith(f"{c}.") for c in family):
        return True
    return any(k.split(".", 1)[0] in family for k in program.heap_writes.get(ref.key, {}))


def check(program: Program, functions: list[Any], gens: dict[str, VCGen], solve, cache, key) -> list[LifecycleReport]:
    """``solve(obligations)`` returns one SmtResult each; ``cache``/``key``
    remember decided probes across runs."""
    owners = [c for c, d in program.classes.items() if d.lifecycles and not program.class_module[c].context]
    if not owners:
        return []
    reports: list[LifecycleReport] = []
    todo: list[tuple[Obligation, Any]] = []  # (obligation, how to record its answer)

    # Class level: reflexive, transitive, and the never lines.
    for cls in owners:
        sc = _Scope(program, cls)
        mine = [(c, lc) for c, lc in program.lifecycles_for(cls) if c in program.mro(cls)]
        for lc in program.classes[cls].lifecycles:
            rep = LifecycleReport(cls, sc.module, lc)
            reports.append(rep)
            s0, s1, s2 = sc.state(0), sc.state(1), sc.state(2)
            base: list[L.Term] = []
            rel = lambda a, b, lc=lc: sc.gen.two_state(lc.clause.expr, cls, sc.ref, a, b, base)  # noqa: E731
            if lc.kind == "never":
                hyps = sc.invariants(s0, base) + sc.invariants(s1, base) + [sc.gen.two_state(o.clause.expr, c, sc.ref, s0, s1, base) for c, o in mine]
                todo.append((sc.obligation(lc, "never", hyps, rel(s0, s1)), (rep, "the other lifecycles of the class allow this step across calls (list its transitions so that it is unreachable)")))
                continue
            todo.append((sc.obligation(lc, "refl", sc.invariants(s0, base), rel(s0, s0)), (rep, "it is not reflexive: a call that leaves the object alone breaks it")))
            hyps = sc.invariants(s0, base) + sc.invariants(s1, base) + sc.invariants(s2, base) + [rel(s0, s1), rel(s1, s2)]
            todo.append((sc.obligation(lc, "trans", hyps, rel(s0, s2)), (rep, "it is not transitive: two calls that each keep it can break it together")))

    # Coverage: the steps functions can take.
    by_rep = {id(r.lc): r for r in reports}
    for r in reports:
        r.steps = [Step(p.label) for p in r.lc.probes]
    probes: list[tuple[Obligation, str, LifecycleReport, int]] = []
    for f in functions:
        if f.status in ("unsupported", "error", "trusted") or f.ref.module.context:
            continue
        gen = gens.get(f.ref.key)
        if gen is None or not getattr(gen, "ran", False):
            if not any(_may_change(program, f.ref, set(program.mro(c)) | {x for x in program.classes if c in program.mro(x)}) for c in owners):
                continue
            try:
                gen = VCGen(program, f.ref, f.inferred.options if f.inferred else None)
                gen.run()
            except VCError:
                continue
        for facts, pc, ref, cls, env, created in gen.lc_sites:
            for owner, lc in program.lifecycles_for(cls, never=True):
                r = by_rep.get(id(lc))
                if r is None:
                    continue
                for i, p in enumerate(lc.probes):
                    e = p.created if created else p.step
                    if e is None:
                        continue
                    try:
                        t = gen.two_state(e, owner, ref, None if created else gen.entry, env, list(facts))
                    except VCError:
                        continue
                    ob = Obligation(id=f"{f.fn.name}/lifecycle.probe", func=f.ref.key, kind="lifecycle.probe", loc=lc.clause.loc, site=None, message=p.label, hyps=list(facts) + [pc, t], goal=L.FALSE, exclude_axioms={k for k in program.funcs if program.same_scc(f.ref.key, k)})
                    probes.append((ob, f.fn.name, r, i))

    obs = [o for o, _ in todo] + [o for o, _, _, _ in probes]
    keys = ["lc:" + key(o) for o in obs]
    answers: list[str | None] = [(cache.get(k) or {}).get("method") for k in keys]
    ask = [i for i, a in enumerate(answers) if a is None]
    for i, res in zip(ask, solve([obs[i] for i in ask])):
        answers[i] = res.status
        if res.status in ("proved", "refuted"):
            cache.put(keys[i], {"method": res.status})
    for (ob, (rep, why)), a in zip(todo, answers[: len(todo)]):
        if a == "refuted":
            rep.status = "refuted"
            rep.problems.append(why)
        elif a != "proved" and rep.status != "refuted":
            rep.status = "open"
            rep.problems.append(f"telic could not decide whether it is {_PROPERTY[ob.kind]}")
    for (ob, fname, rep, i), a in zip(probes, answers[len(todo) :]):
        st = rep.steps[i]
        if a == "refuted":  # satisfiable: some run takes this step
            if fname not in st.by:
                st.by.append(fname)
        elif a != "proved":
            st.unknown = True

    # Per-function proofs, and the functions no proof covers.
    for r in reports:
        family = set(program.mro(r.cls)) | {x for x in program.classes if r.cls in program.mro(x)}
        for f in functions:
            if f.ref.module.context:
                continue
            vs = [v for v in f.verdicts if v.ob.kind == "lifecycle" and _same_clause(v.ob, r.clause)]
            if r.lc.kind == "never":
                vs = [v for v in f.verdicts if v.ob.kind == "lifecycle" and any(_same_clause(v.ob, o.clause) for c, o in program.lifecycles_for(r.cls) if c in program.mro(r.cls))]
            if vs:
                name = ir.source_name(f.fn.name)
                if f.fn.name not in r.functions:
                    r.functions.append(f.fn.name)
                bad = next((v for v in vs if v.status == "refuted"), None) or next((v for v in vs if v.status != "proved"), None)
                other = bad.ob.message.rsplit("('", 1)[-1][:-2] if bad is not None else ""
                what = "it" if bad is None or _same_clause(bad.ob, r.clause) else f"'{other}', which it rests on"
                if bad is not None and bad.status == "refuted":
                    r.status = "refuted"
                    r.problems.append(f"{name} breaks {what}")
                elif bad is not None and r.status != "refuted":
                    r.status = "open"
                    r.problems.append(f"{name} is not proved to keep {what}")
            elif f.status in ("unsupported", "error") and _may_change(program, f.ref, family):
                if r.status == "proved":
                    r.status = "open"
                r.problems.append(f"{ir.source_name(f.fn.name)} may change {ir.source_name(r.cls)} objects but is not checked ({f.status})")
        if r.status == "proved" and r.steps and all(not s.by and not s.unknown for s in r.steps):
            r.status = "vacuous"
            r.problems.append(_vacuous(r))
    return reports


_PROPERTY = {"lifecycle.refl": "reflexive", "lifecycle.trans": "transitive", "lifecycle.never": "implied by the other lifecycles"}


def _vacuous(r: LifecycleReport) -> str:
    cls = ir.source_name(r.cls)
    if r.lc.kind == "graph":
        return f"no function takes any of its steps, so it holds only because nothing changes {cls} objects this way"
    if r.lc.kind == "never":
        return f"no function brings a {cls} to {r.steps[0].label.removeprefix('reaches ')}, so it holds only because the state is never reached"
    if r.lc.kind == "monotonic":
        return "no function makes it grow, so it holds only because nothing changes it"
    return f"no function makes it true and no {cls} is created with it, so it holds only because it is never true"
