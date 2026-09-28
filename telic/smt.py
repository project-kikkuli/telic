"""Z3 backend: discharge an obligation or produce a counterexample model."""

from __future__ import annotations

import time
from dataclasses import dataclass, field
from fractions import Fraction
from typing import Any

import z3

from . import logic as L
from .vcgen import ListVal, Obligation, Val


@dataclass
class Theory:
    """Definitions and lemmas that obligations may refer to."""

    fundefs: dict[str, L.FunDef] = field(default_factory=dict)
    axioms: list[L.Axiom] = field(default_factory=list)

    def closure(self, terms: list[L.Term], exclude: set[str], lemmas: bool = True) -> tuple[list[L.FunDef], list[L.Axiom]]:
        """Definitions and axioms reachable from ``terms``."""
        need: set[str] = set()
        todo: list[L.Term] = list(terms)
        axioms: list[L.Axiom] = []
        seen_ax: set[str] = set()
        while todo:
            t = todo.pop()
            for name in L.fns(t):
                if name in need:
                    continue
                need.add(name)
                fd = self.fundefs.get(name)
                if fd is not None and fd.body is not None:
                    todo.append(fd.body)
                for ax in self.axioms:
                    if (ax.about and ax.about in exclude) or ax.name in seen_ax:
                        continue
                    if ax.name == f"{name}_spec" or (lemmas and ax.symbol == name):
                        seen_ax.add(ax.name)
                        axioms.append(ax)
                        todo.append(ax.formula)
        defs = [self.fundefs[n] for n in sorted(need) if n in self.fundefs]
        return defs, axioms


@dataclass
class SmtResult:
    status: str  # proved | refuted | unknown
    seconds: float
    model: dict[str, Any] = field(default_factory=dict)  # input name -> python value
    state: dict[str, Any] = field(default_factory=dict)  # other constants
    reason: str = ""


class Z3Encoder:
    def __init__(self, theory_defs: list[L.FunDef]):
        self.ctx = z3.Context()
        self.consts: dict[L.Const, z3.ExprRef] = {}
        self.funcs: dict[str, z3.FuncDeclRef] = {}
        self.datatypes: dict[str, Any] = {}
        self.defs = {d.name: d for d in theory_defs}
        for d in theory_defs:
            self.declare(d)
        for d in theory_defs:
            if d.body is not None:
                self.define(d)

    # -- sorts ------------------------------------------------------------

    def sort(self, s: L.Sort) -> z3.SortRef:
        c = self.ctx
        if s == L.INT:
            return z3.IntSort(c)
        if s == L.REAL:
            return z3.RealSort(c)
        if s == L.BOOL:
            return z3.BoolSort(c)
        if s == L.STR:
            return z3.StringSort(c)
        if s.name == "Array":
            assert s.elem is not None
            return z3.ArraySort(z3.IntSort(c), self.sort(s.elem))
        if s.name == "Rec":
            return self.record(s)[0]
        if s.name == "None":
            return z3.IntSort(c)
        raise TypeError(s)

    def record(self, s: L.Sort):
        assert s.rec is not None
        if s.rec not in self.datatypes:
            dt = z3.Datatype(s.rec, ctx=self.ctx)
            dt.declare(f"mk_{s.rec}", *[(f"{s.rec}.{n}", self.sort(fs)) for n, fs in s.fields])
            sort = dt.create()
            self.datatypes[s.rec] = (sort, s)
        return self.datatypes[s.rec]

    # -- functions --------------------------------------------------------

    def declare(self, d: L.FunDef) -> None:
        doms = [self.sort(p.sort) for p in d.params]
        if d.body is not None:
            f = z3.RecFunction(d.name, *doms, self.sort(d.sort))
        else:
            f = z3.Function(d.name, *doms, self.sort(d.sort))
        self.funcs[d.name] = f

    def define(self, d: L.FunDef) -> None:
        args = [self.term(p) for p in d.params]
        assert d.body is not None
        z3.RecAddDefinition(self.funcs[d.name], args, self.term(d.body))

    # -- terms ------------------------------------------------------------

    def term(self, t: L.Term) -> z3.ExprRef:
        c = self.ctx
        if isinstance(t, L.Const):
            if t not in self.consts:
                self.consts[t] = z3.Const(t.name, self.sort(t.sort))
            return self.consts[t]
        if isinstance(t, L.IntV):
            return z3.IntVal(t.value, c)
        if isinstance(t, L.RealV):
            return z3.RealVal(f"{t.value.numerator}/{t.value.denominator}", c)
        if isinstance(t, L.BoolV):
            return z3.BoolVal(t.value, c)
        if isinstance(t, L.StrV):
            return z3.StringVal(t.value, c)
        if isinstance(t, L.Quant):
            vs = [self.term(v) for v in t.vars]
            body = self.term(t.body)
            if t.patterns and t.kind == "forall":
                pats = [z3.MultiPattern(*[self.term(x) for x in p]) if len(p) > 1 else self.term(p[0]) for p in t.patterns]
                return z3.ForAll(vs, body, patterns=pats)
            return z3.ForAll(vs, body) if t.kind == "forall" else z3.Exists(vs, body)
        if isinstance(t, L.Fn):
            f = self.funcs.get(t.name)
            if f is None:
                f = z3.Function(t.name, *[self.sort(a.sort) for a in t.args], self.sort(t.sort))
                self.funcs[t.name] = f
            return f(*[self.term(a) for a in t.args])
        assert isinstance(t, L.App)
        a = [self.term(x) for x in t.args]
        op = t.op
        if op == "add":
            return a[0] + a[1]
        if op == "sub":
            return a[0] - a[1]
        if op == "mul":
            return a[0] * a[1]
        if op == "neg":
            return -a[0]
        if op == "rdiv":
            return a[0] / a[1]
        if op == "ediv":
            return a[0] / a[1]  # Z3 integer division is Euclidean
        if op == "emod":
            return a[0] % a[1]
        if op == "lt":
            return a[0] < a[1]
        if op == "le":
            return a[0] <= a[1]
        if op == "eq":
            return a[0] == a[1]
        if op == "not":
            return z3.Not(a[0])
        if op == "and":
            return z3.And(*a)
        if op == "or":
            return z3.Or(*a)
        if op == "implies":
            return z3.Implies(a[0], a[1])
        if op == "ite":
            return z3.If(a[0], a[1], a[2])
        if op == "to_real":
            return z3.ToReal(a[0])
        if op == "floor":
            return z3.ToInt(a[0])
        if op == "is_int":
            return z3.IsInt(a[0])
        if op == "select":
            return z3.Select(a[0], a[1])
        if op == "store":
            return z3.Store(a[0], a[1], a[2])
        if op.startswith("field:"):
            sort, s = self.record(t.args[0].sort)
            idx = [n for n, _ in s.fields].index(op[6:])
            return sort.accessor(0, idx)(a[0])
        if op.startswith("mk:"):
            sort, _ = self.record(t.sort)
            return sort.constructor(0)(*a)
        raise TypeError(f"no Z3 encoding for {op}")

    # -- model values -----------------------------------------------------

    def value(self, model: z3.ModelRef, t: L.Term) -> Any:
        v = model.eval(self.term(t), model_completion=True)
        return to_python(v)

    def list_value(self, model: z3.ModelRef, v: ListVal, cap: int = 256) -> list[Any]:
        n = self.value(model, v.len)
        if not isinstance(n, int):
            return []
        out = []
        for i in range(max(0, min(n, cap))):
            out.append(self.value(model, L.select(v.arr, L.add(v.off, L.IntV(i)))))
        return out


def to_python(v: z3.ExprRef) -> Any:
    if z3.is_int_value(v):
        return v.as_long()
    if z3.is_rational_value(v):
        return Fraction(v.numerator_as_long(), v.denominator_as_long())
    if z3.is_algebraic_value(v):
        return Fraction(v.approx(20).as_decimal(20).rstrip("?"))
    if z3.is_true(v):
        return True
    if z3.is_false(v):
        return False
    if z3.is_string_value(v):
        return v.as_string()
    if z3.is_app(v) and v.decl().kind() == z3.Z3_OP_DT_CONSTRUCTOR:
        return {v.decl().name(): [to_python(a) for a in v.children()]}
    return str(v)


def decode(enc: Z3Encoder, model: z3.ModelRef, val: Val, rec_fields=None) -> Any:
    if isinstance(val, ListVal):
        return [x for x in enc.list_value(model, val)]
    if val.sort.name == "Rec":
        out = {}
        for fname, _ in val.sort.fields:
            out[fname] = decode(enc, model, L.field(val, fname))
        return out
    return enc.value(model, val)


def solve(ob: Obligation, theory: Theory, timeout_ms: int = 8000) -> SmtResult:
    """Two phases. Theory lemmas are consequences of the definitions, so a
    model found without them is a genuine model; but their quantifiers can
    stop Z3 from finding models at all. So: first without them (fast, good
    counterexamples), then with them only if the first phase is undecided."""
    t0 = time.perf_counter()
    terms = list(ob.hyps) + [ob.goal]
    with_lemmas = theory.closure(terms, ob.exclude_axioms, lemmas=True)
    without = theory.closure(terms, ob.exclude_axioms, lemmas=False)
    if len(with_lemmas[1]) == len(without[1]):
        return _solve(ob, with_lemmas, timeout_ms, t0)
    first = _solve(ob, without, max(500, timeout_ms // 3), t0)
    if first.status != "unknown":
        return first
    second = _solve(ob, with_lemmas, timeout_ms, t0)
    return second


def _solve(ob: Obligation, closure, timeout_ms: int, t0: float) -> SmtResult:
    terms = list(ob.hyps) + [ob.goal]
    defs, axioms = closure
    enc = Z3Encoder(defs)
    s = z3.Solver(ctx=enc.ctx)
    s.set("timeout", timeout_ms)
    try:
        for ax in axioms:
            s.add(enc.term(ax.formula))
        for h in ob.hyps:
            s.add(enc.term(h))
        s.add(z3.Not(enc.term(ob.goal)))
        r = s.check()
    except z3.Z3Exception as e:  # pragma: no cover - defensive
        return SmtResult("unknown", time.perf_counter() - t0, reason=f"z3 error: {e}")
    dt = time.perf_counter() - t0
    if r == z3.unsat:
        return SmtResult("proved", dt)
    if r == z3.sat:
        m = s.model()
        model = {name: decode(enc, m, v) for name, v in ob.inputs}
        too_big = any(isinstance(v, ListVal) and isinstance(enc.value(m, v.len), int) and enc.value(m, v.len) > 256 for _, v in ob.inputs)
        state: dict[str, Any] = {}
        input_consts = set()
        for _, v in ob.inputs:
            if isinstance(v, ListVal):
                input_consts |= {v.arr, v.len}
            else:
                input_consts.add(v)
        for c in sorted(set().union(*(L.consts(t) for t in terms)), key=lambda c: c.name):
            if c in input_consts or "!" in c.name or c.sort.name in ("Array", "Rec"):
                continue
            try:
                state[c.name] = enc.value(m, c)
            except Exception:  # pragma: no cover
                pass
        # A model is only trustworthy if quantifiers did not force an
        # incomplete answer; Z3 reports that as 'unknown', not 'sat'.
        res = SmtResult("refuted", dt, model=model, state=state)
        if too_big:
            res.reason = "the model's list input is too large to replay"
        return res
    return SmtResult("unknown", dt, reason=s.reason_unknown() or "unknown")
