"""Z3 backend: discharge an obligation or produce a counterexample model."""

from __future__ import annotations

import threading
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
        self.key_candidates: dict[str, list[Any]] = {}
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
            return z3.ArraySort(self.sort(L.index_sort(s)), self.sort(s.elem))
        if s.name == "Rec":
            return self.record(s)[0]
        if s.name == "None":
            return z3.IntSort(c)
        if s == L.OPAQUE:
            if "Opaque" not in self.datatypes:
                self.datatypes["Opaque"] = z3.DeclareSort("Opaque", c)
            return self.datatypes["Opaque"]
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
            f = self.funcs.get(t.name)  # a defined function
            if f is None:
                # uninterpreted: one symbol per signature (str.lower of a str
                # here, of an opaque value there)
                key = (t.name, tuple(a.sort for a in t.args), t.sort)
                f = self.funcs.get(key)  # type: ignore[call-overload]
                if f is None:
                    f = z3.Function(t.name, *[self.sort(a.sort) for a in t.args], self.sort(t.sort))
                    self.funcs[key] = f  # type: ignore[index]
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
        if op == "str.++":
            return z3.Concat(*a)
        if op == "str.len":
            return z3.Length(a[0])
        if op == "str.contains":
            return z3.Contains(a[0], a[1])
        if op == "str.prefixof":
            return z3.PrefixOf(a[0], a[1])
        if op == "str.suffixof":
            return z3.SuffixOf(a[0], a[1])
        if op == "str.from_int":
            # Python str(n): a leading '-' for negatives
            return z3.If(a[0] >= 0, z3.IntToStr(a[0]), z3.Concat(z3.StringVal("-", c), z3.IntToStr(-a[0])))
        if op == "str.at":
            return z3.SubString(a[0], a[1], z3.IntVal(1, c))
        if op == "str.substr":
            return z3.SubString(a[0], a[1], a[2])
        if op == "str.indexof":
            return z3.IndexOf(a[0], a[1], a[2])
        if op == "str.lt":
            return a[0] < a[1]
        if op == "str.le":
            return a[0] <= a[1]
        if op == "K":
            return z3.K(self.sort(L.index_sort(t.sort)), a[0])
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


def _lit(k: Any, sort: L.Sort | None) -> L.Term:
    if isinstance(k, bool):
        return L.BoolV(k)
    if isinstance(k, int):
        return L.IntV(k)
    if isinstance(k, str):
        return L.StrV(k)
    raise ValueError(k)


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


def array_entries(v: z3.ExprRef) -> tuple[list[tuple[Any, Any]], Any]:
    """Explicit entries and default of an array value from a model."""
    entries: list[tuple[Any, Any]] = []
    seen = set()
    while True:
        if z3.is_store(v):
            k, x = to_python(v.arg(1)), to_python(v.arg(2))
            if k not in seen:
                seen.add(k)
                entries.append((k, x))
            v = v.arg(0)
        elif z3.is_K(v):
            return entries, to_python(v.arg(0))
        elif z3.is_lambda(v) or z3.is_quantifier(v):
            return entries, None
        else:
            return entries, None


def decode(enc: Z3Encoder, model: z3.ModelRef, val: Val, rec_fields=None) -> Any:
    from .vcgen import DictVal, ObjVal, OptVal, TypedView
    from . import ir

    if isinstance(val, TypedView):
        ty = val.ty
        if isinstance(ty, ir.TEnum):
            i = enc.value(model, val.val)
            return {"__enum__": ty.name, "member": ty.members[i] if isinstance(i, int) and 0 <= i < len(ty.members) else ty.members[0]}
        if isinstance(ty, ir.TRecord):
            return {"__record__": ty.name, "fields": decode(enc, model, val.val)}
        if isinstance(ty, ir.TList) and isinstance(ty.elem, ir.TRecord) and isinstance(val.val, ListVal):
            return [{"__record__": ty.elem.name, "fields": x} for x in decode(enc, model, val.val)]
        if isinstance(ty, ir.TList) and isinstance(val.val, ListVal):
            items = enc.list_value(model, val.val)
            if isinstance(ty.elem, ir.TEnum):
                return [{"__enum__": ty.elem.name, "member": ty.elem.members[i] if isinstance(i, int) and 0 <= i < len(ty.elem.members) else ty.elem.members[0]} for i in items]
            if isinstance(ty.elem, ir.TClass):
                return [{"__class__": ty.elem.name, "__ref__": r, "__stub__": True} for r in items]
        return decode(enc, model, val.val)

    if isinstance(val, ListVal):
        n = enc.value(model, val.len)
        if not isinstance(n, int):
            return []
        return [decode(enc, model, L.select(val.arr, L.add(val.off, L.IntV(i)))) for i in range(max(0, min(n, 256)))]
    if isinstance(val, L.Term) and val.sort == L.OPAQUE:
        return {"__opaque__": True}
    if isinstance(val, OptVal):
        if enc.value(model, val.some) is not True:
            return None
        return decode(enc, model, val.val)
    if isinstance(val, ObjVal):
        out: dict[str, Any] = {"__class__": val.cls, "__ref__": enc.value(model, val.ref)}
        if val.fields is None:
            out["__stub__"] = True
            return out
        for fname, fv in val.fields:  # noqa
            out[fname] = decode(enc, model, fv)
        return out
    if isinstance(val, DictVal):
        has = model.eval(enc.term(val.has), model_completion=True)
        entries, default = array_entries(has)
        keys = [k for k, x in entries if x is True]
        if default is not False:
            # "every key" is not a real dict: show the keys that matter,
            # i.e. the other inputs of the key's type the model mentions
            ks = val.has.sort.index or L.INT
            cands = list(enc.key_candidates.get(ks.name, ()))
            for k in cands:
                if k not in keys and enc.value(model, L.select(val.has, _lit(k, ks))) is True:
                    keys.append(k)
        return {k: enc.value(model, L.select(val.vals, _lit(k, val.has.sort.index))) for k in keys}
    if not isinstance(val, L.Term):
        return str(val)
    if val.sort.name == "Rec" and str(val.sort.rec).startswith("Opt_"):
        if enc.value(model, L.field(val, "some")) is not True:
            return None
        return decode(enc, model, L.field(val, "val"))
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
    # Phase one only needs long enough to find a model or a quick proof;
    # quantified lemmas are what unlock the rest.
    first = _solve(ob, without, max(300, min(800, timeout_ms // 10)), t0)
    if first.status != "unknown":
        return first
    second = _solve(ob, with_lemmas, timeout_ms, t0)
    return second


def _solve(ob: Obligation, closure, timeout_ms: int, t0: float) -> SmtResult:
    terms = list(ob.hyps) + [ob.goal]
    defs, axioms = closure
    enc = Z3Encoder(defs)
    # Z3's rewriter unfolds a recursive definition applied to literals while
    # asserting, outside the solver's timeout; only an interrupt stops that.
    deadline = threading.Timer(timeout_ms / 1000, enc.ctx.interrupt)
    deadline.start()
    try:
        return _run(ob, enc, axioms, terms, timeout_ms, t0)
    except z3.Z3Exception as e:
        if deadline.finished.is_set():
            return SmtResult("unknown", time.perf_counter() - t0, reason="timeout")
        return SmtResult("unknown", time.perf_counter() - t0, reason=f"z3 error: {e}")  # pragma: no cover - defensive
    finally:
        deadline.cancel()
        deadline.join()  # no thread may outlive the call: the checker forks workers


def _run(ob: Obligation, enc: "Z3Encoder", axioms, terms, timeout_ms: int, t0: float) -> SmtResult:
    start = time.perf_counter()
    s = z3.Solver(ctx=enc.ctx)
    for ax in axioms:
        s.add(enc.term(ax.formula))
    for h in ob.hyps:
        s.add(enc.term(h))
    s.add(z3.Not(enc.term(ob.goal)))
    left = timeout_ms - int((time.perf_counter() - start) * 1000)
    if left <= 0:
        return SmtResult("unknown", time.perf_counter() - t0, reason="timeout")
    s.set("timeout", left)
    r = s.check()
    dt = time.perf_counter() - t0
    if r == z3.unsat:
        return SmtResult("proved", dt)
    if r == z3.sat:
        m = s.model()
        enc.key_candidates = {}
        for _, v in ob.inputs:
            if isinstance(v, L.Term) and v.sort in (L.INT, L.STR, L.BOOL):
                x = enc.value(m, v)
                enc.key_candidates.setdefault(v.sort.name, []).append(x)
        for sname, default in (("Str", ""), ("Int", 0)):
            enc.key_candidates.setdefault(sname, []).append(default)
        model = {name: decode(enc, m, v) for name, v in ob.inputs}
        too_big = any(isinstance(v, ListVal) and isinstance(enc.value(m, v.len), int) and enc.value(m, v.len) > 256 for _, v in ob.inputs)
        state: dict[str, Any] = {}
        input_consts = set()
        for _, v in ob.inputs:
            if isinstance(v, ListVal):
                input_consts |= {v.arr, v.len}
            elif isinstance(v, L.Term):
                input_consts.add(v)
            else:
                input_consts |= set(getattr(v, "__dict__", {}).values()) if hasattr(v, "__dict__") else set()
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
