"""Z3 backend: discharge an obligation or produce a counterexample model."""

from __future__ import annotations

import dataclasses
import struct
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
            for name in sorted(L.fns(t)):
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
    def __init__(self, theory_defs: list[L.FunDef], rlimit: int = 0):
        self.ctx = z3.Context(rlimit=rlimit)
        self.consts: dict[L.Const, z3.ExprRef] = {}
        self.funcs: dict[str, z3.FuncDeclRef] = {}
        self.datatypes: dict[str, Any] = {}
        self.key_candidates: dict[str, list[Any]] = {}
        # keys an unchecked value rebuilt as JSON may have: those the obligation names
        self.json_keys: list[str] | None = None
        self.regexes: dict[str, z3.ReRef] = {}
        self.json_attrs: set[L.Term] = set()  # t.k reads the obligation makes
        self.json_ops: set[str] = set()
        self.json_kinds: set[str] = set()
        self.json_containers: set[L.Term] = set()  # values the obligation looks inside
        self.json_lits: list[str] = []
        self.json_model: z3.ModelRef | None = None
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
        if s == L.FLOAT32:
            return z3.FPSort(8, 24, c)
        if s == L.FLOAT64:
            return z3.FPSort(11, 53, c)
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

    def regex(self, text: str) -> z3.ReRef:
        """A regular language written in SMT-LIB, in this context."""
        if text not in self.regexes:
            (f,) = z3.parse_smt2_string(f"(declare-const s String)(assert (str.in_re s {text}))", ctx=self.ctx)
            self.regexes[text] = f.arg(1)
        return self.regexes[text]

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
            if t.sort == L.UNIT:
                return z3.IntVal(0, c)
            if t not in self.consts:
                self.consts[t] = z3.Const(t.name, self.sort(t.sort))
            return self.consts[t]
        if isinstance(t, L.IntV):
            return z3.IntVal(t.value, c)
        if isinstance(t, L.RealV):
            return z3.RealVal(f"{t.value.numerator}/{t.value.denominator}", c)
        if isinstance(t, L.FloatV):
            width = 32 if t.sort == L.FLOAT32 else 64
            ebits, sbits = (8, 24) if width == 32 else (11, 53)
            return z3.fpBVToFP(z3.BitVecVal(t.bits, width, c), z3.FPSort(ebits, sbits, c), ctx=c)
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
        if op == "fp.add":
            return z3.fpAdd(z3.RNE(c), a[0], a[1], ctx=c)
        if op == "fp.sub":
            return z3.fpSub(z3.RNE(c), a[0], a[1], ctx=c)
        if op == "fp.mul":
            return z3.fpMul(z3.RNE(c), a[0], a[1], ctx=c)
        if op == "fp.div":
            return z3.fpDiv(z3.RNE(c), a[0], a[1], ctx=c)
        if op == "fp.neg":
            return z3.fpNeg(a[0], ctx=c)
        if op == "fp.abs":
            return z3.fpAbs(a[0], ctx=c)
        if op == "fp.lt":
            return z3.fpLT(a[0], a[1], ctx=c)
        if op == "fp.leq":
            return z3.fpLEQ(a[0], a[1], ctx=c)
        if op == "fp.eq":
            return z3.fpEQ(a[0], a[1], ctx=c)
        if op == "fp.isNaN":
            return z3.fpIsNaN(a[0], ctx=c)
        if op == "fp.isInfinite":
            return z3.fpIsInf(a[0], ctx=c)
        if op == "fp.isZero":
            return z3.fpIsZero(a[0], ctx=c)
        if op == "fp.isNegative":
            return z3.fpIsNegative(a[0], ctx=c)
        if op == "fp.to_real":
            return z3.fpToReal(a[0], ctx=c)
        if op in ("fp.of_int", "fp.of_real", "fp.from_int", "fp.from_real", "fp.cast"):
            target = self.sort(t.sort)
            exact = z3.ToReal(a[0]) if op in ("fp.of_int", "fp.from_int") else a[0]
            return z3.fpToFP(z3.RNE(c), exact, target, ctx=c)
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
        if op == "str.to_int":
            return z3.StrToInt(a[0])
        if op == "str.in_re":
            return z3.InRe(a[0], self.regex(t.args[1].value))  # type: ignore[attr-defined]
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


def _object(enc: Z3Encoder, model: z3.ModelRef, cls: str, ref: Any, fields: tuple) -> dict[str, Any]:
    """An object held in a list or dict, with its fields as the model's heap has them."""
    from .vcgen import pack

    if not fields or not isinstance(ref, int):
        return {"__class__": cls, "__ref__": ref, "__stub__": True}
    out: dict[str, Any] = {"__class__": cls, "__ref__": ref}
    for fname, fty, arrays in fields:
        out[fname] = decode(enc, model, pack(fty, [L.select(a, L.IntV(ref)) for a in arrays]))
    return out


def _lit(k: Any, sort: L.Sort | None) -> L.Term:
    if isinstance(k, bool):
        return L.BoolV(k)
    if isinstance(k, int):
        return L.IntV(k)
    if isinstance(k, str):
        return L.StrV(k)
    if isinstance(k, Fraction):
        return L.RealV(k)  # a TypeScript number key
    raise ValueError(k)


def to_python(v: z3.ExprRef) -> Any:
    if z3.is_fp_value(v):
        if v.isNaN():
            return float("nan")
        if v.isInf():
            return float("-inf") if v.isNegative() else float("inf")
        bits = z3.simplify(z3.fpToIEEEBV(v, ctx=v.ctx)).as_long()
        return struct.unpack("<f" if v.sort().ebits() == 8 else "<d", bits.to_bytes(4 if v.sort().ebits() == 8 else 8, "little"))[0]
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
                return [_object(enc, model, ty.elem.name, r, val.fields) for r in items]
        if isinstance(ty, ir.TDict) and isinstance(ty.val, ir.TClass):
            return {k: _object(enc, model, ty.val.name, r, val.fields) for k, r in decode(enc, model, val.val).items()}
        return decode(enc, model, val.val)

    if isinstance(val, ListVal):
        n = enc.value(model, val.len)
        if not isinstance(n, int):
            return []
        return [decode(enc, model, L.select(val.arr, L.add(val.off, L.IntV(i)))) for i in range(max(0, min(n, 256)))]
    if isinstance(val, L.Term) and val.sort == L.OPAQUE:
        if enc.json_keys is not None:
            return {"__json__": unchecked_json(enc, enc.json_model or model, val, 0)}
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


def _has_opaque(v: Val) -> bool:
    from .program import reaches_unchecked

    if isinstance(v, L.Term):
        return v.sort == L.OPAQUE
    ty = getattr(v, "ty", None)
    return ty is not None and reaches_unchecked(ty)


KINDS = ("dict", "list", "str", "int", "float")
MEMBERSHIP = ("opaque.cmp.in.Bool", "opaque.cmp.notin.Bool", "opaque.in.Bool")


def _json_hints(enc: Z3Encoder, s: z3.Solver, m: z3.ModelRef, terms: list[L.Term]) -> None:
    """What the obligation says about its unchecked values' shapes: the
    keys, types and string literals it names, for ``unchecked_json``."""
    fns = [x for t in terms for x in L.iter_terms(t) if isinstance(x, L.Fn)]
    enc.json_model = _json_model(enc, s, terms) or m
    enc.json_ops = {x.name for x in fns}
    enc.json_attrs = {x for x in fns if x.name.startswith("opaque.attr.")}
    keys = {x.args[0] for x in fns if x.name in MEMBERSHIP} | {x.args[1] for x in fns if x.name == "opaque.getitem.Opaque"}
    enc.json_keys = sorted({k.value for k in keys if isinstance(k, L.StrV)} | {a.name[len("opaque.attr.") : -len(".Opaque")] for a in enc.json_attrs})
    enc.json_containers = {x.args[1] for x in fns if x.name in MEMBERSHIP} | {x.args[0] for x in fns if x.name == "opaque.getitem.Opaque" or x.name.startswith("opaque.attr.")}
    enc.json_kinds = {x.args[1].value for x in fns if x.name == "opaque.isinstance.Bool" and isinstance(x.args[1], L.StrV)}
    enc.json_lits = sorted({x.args[0].value for x in fns if x.name == "box.str" and isinstance(x.args[0], L.StrV)})


def _json_model(enc: Z3Encoder, s: z3.Solver, terms: list[L.Term]) -> z3.ModelRef | None:
    """The same counterexample with each unchecked value of one Python type
    at most (the obligation alone need not say so), if there is one."""
    seen = [x for t in terms for x in L.iter_terms(t)]
    if not any(isinstance(x, L.Fn) and x.name == "opaque.isinstance.Bool" for x in seen):
        return None
    values = {x for x in seen if not isinstance(x, L.Quant) and x.sort == L.OPAQUE and not any("!" in c.name for c in L.consts(x))}
    none = any(isinstance(x, L.Fn) and x.name == "opaque.is_none.Bool" for x in seen)
    s.push()
    try:
        for u in values:
            isk = [enc.term(L.Fn("opaque.isinstance.Bool", (u, L.StrV(k)), L.BOOL)) for k in KINDS]
            s.add(z3.AtMost(*isk, *([enc.term(L.Fn("opaque.is_none.Bool", (u,), L.BOOL))] if none else []), 1))
        return s.model() if s.check() == z3.sat else None
    finally:
        s.pop()


JSON_DEPTH = 6
JSON_LEN = 16


def unchecked_json(enc: Z3Encoder, model: z3.ModelRef, t: L.Term, depth: int) -> Any:
    """An unchecked value as the JSON the model says it is, through the
    operations specs use on it (Python and TypeScript spell them apart).
    What the model leaves open becomes null; replay decides whether the
    value is a real counterexample."""

    def ask(name: str, *args: L.Term, sort: L.Sort = L.BOOL) -> Any:
        # an operation the obligation never applies says nothing about the value
        return enc.value(model, L.Fn(name, (t, *args), sort)) if name in enc.json_ops else None

    def kind(k: str) -> bool:
        return k in enc.json_kinds and ask("opaque.isinstance.Bool", L.StrV(k)) is True

    def same(x: L.Term) -> bool:
        return enc.value(model, L.eq(t, x)) is True

    if depth > JSON_DEPTH or ask("opaque.is_none.Bool") is True or ask("opaque.is_null.Bool") is True:
        return None
    typeof = ask("opaque.typeof.Str", sort=L.STR)
    if kind("bool") or typeof == "boolean":
        return ask("opaque.truthy.Bool") is True
    if kind("int") or typeof == "number":
        n = ask("unbox.int.", sort=L.INT) if kind("int") else 0
        return n if isinstance(n, int) else 0
    if kind("str") or typeof == "string":
        for k in enc.json_lits:
            if same(L.Fn("box.str", (L.StrV(k),), L.OPAQUE)):
                return k
        v = ask("unbox.str.", sort=L.STR) if kind("str") else ""
        return v if isinstance(v, str) else ""
    if kind("list"):
        n = ask("opaque.len.Int", sort=L.INT)
        n = n if isinstance(n, int) else 0
        return [unchecked_json(enc, model, L.Fn("opaque.getitem.Opaque", (t, L.IntV(i)), L.OPAQUE), depth + 1) for i in range(max(0, min(n, JSON_LEN)))]
    out: dict[str, Any] = {}
    for k in enc.json_keys or ():
        held = any(enc.value(model, L.Fn(op, (L.StrV(k), t), L.BOOL)) is True for op in ("opaque.cmp.in.Bool", "opaque.in.Bool") if op in enc.json_ops)
        attr = L.Fn(f"opaque.attr.{k}.Opaque", (t,), L.OPAQUE)
        if attr in enc.json_attrs:
            held = held or not any(enc.value(model, L.Fn(op, (attr,), L.BOOL)) is True for op in ("opaque.is_undefined.Bool", "opaque.is_nullish.Bool") if op in enc.json_ops)
        if held:
            out[k] = unchecked_json(enc, model, attr if attr in enc.json_attrs else L.Fn("opaque.getitem.Opaque", (t, L.StrV(k)), L.OPAQUE), depth + 1)
    if out or kind("dict") or typeof == "object" or t in enc.json_containers:
        return out
    return None


# The proof budget is Z3's resource limit, not time: the same obligation gets
# the same verdict on a loaded machine. It covers stating the problem, solving
# it and reading a model; wall-clock time is only a safety net.
RLIMIT = 2_000_000
SEED = 0


def solve(ob: Obligation, theory: Theory, timeout_ms: int = 60000, rlimit: int = RLIMIT) -> SmtResult:
    """Theory lemmas are consequences of the definitions, so a model found
    without them is a genuine model; but their quantifiers can stop Z3 from
    finding models at all. So: first without them (fast, good
    counterexamples), then with them only if the first stage is undecided.

    An undecided stage is retried with recursive definitions (seqsum)
    opaque: Z3 keeps unfolding them where a proof never needs it. Opaque, a
    model may be spurious, so only a proof counts."""
    t0 = time.perf_counter()
    terms = list(ob.hyps) + [ob.goal]
    with_lemmas = theory.closure(terms, ob.exclude_axioms, lemmas=True)
    without = theory.closure(terms, ob.exclude_axioms, lemmas=False)
    stages = [(with_lemmas, rlimit)] if len(with_lemmas[1]) == len(without[1]) else [(without, rlimit // 10), (with_lemmas, rlimit)]
    res = SmtResult("unknown", 0.0)
    for (defs, axioms), budget in stages:
        res = _solve(ob, (defs, axioms), timeout_ms, budget, t0)
        if res.status != "unknown" or res.reason.startswith("timeout"):
            return res
        if any(d.recursive for d in defs):
            opaque = [dataclasses.replace(d, body=None) if d.recursive else d for d in defs]
            again = _solve(ob, (opaque, axioms), timeout_ms, budget, t0)
            if again.status == "proved":
                return again
    return res


class _Deadline:
    """Interrupts a Z3 context after ``ms``: the safety net for a machine too
    loaded to exhaust the resource limit in time, and for Z3's rewriter, which
    unfolds a recursive definition applied to literals while an assertion is
    added without checking the limit."""

    def __init__(self, ctx: z3.Context, ms: int):
        self.fired = False
        self.ctx = ctx
        self.timer = threading.Timer(ms / 1000, self._fire)

    def _fire(self) -> None:
        self.fired = True
        self.ctx.interrupt()

    def __enter__(self) -> "_Deadline":
        self.timer.start()
        return self

    def __exit__(self, kind: Any, exc: Any, tb: Any) -> bool:
        self.timer.cancel()
        self.timer.join()  # no thread may outlive the call: the checker forks workers
        return self.fired and isinstance(exc, Exception)  # whatever the interrupt cut short


def _solve(ob: Obligation, closure, timeout_ms: int, rlimit: int, t0: float) -> SmtResult:
    terms = list(ob.hyps) + [ob.goal]
    defs, axioms = closure
    enc = Z3Encoder(defs, rlimit)
    s = z3.Solver(ctx=enc.ctx)
    s.set("random_seed", SEED)
    # Each stage gets the whole net, so a slow statement never eats into solving.
    try:
        with _Deadline(enc.ctx, timeout_ms) as d:
            for ax in axioms:
                s.add(enc.term(ax.formula))
            for h in ob.hyps:
                s.add(enc.term(h))
            s.add(z3.Not(enc.term(ob.goal)))
        if d.fired:
            return SmtResult("unknown", time.perf_counter() - t0, reason="timeout")
        with _Deadline(enc.ctx, timeout_ms) as d:
            r = s.check()
        if d.fired:
            return SmtResult("unknown", time.perf_counter() - t0, reason="timeout")
    except z3.Z3Exception as e:
        why = _unknown_reason(str(e))
        return SmtResult("unknown", time.perf_counter() - t0, reason=why if why == "resource limit" else f"z3 error: {e}")
    dt = time.perf_counter() - t0
    if r == z3.unsat:
        return SmtResult("proved", dt)
    if r == z3.sat:
        with _Deadline(enc.ctx, timeout_ms) as d:
            model = _small_lists(ob, enc, s)
            res = _refutation(ob, enc, s, terms, dt, model)
        if d.fired:
            return SmtResult("unknown", time.perf_counter() - t0, reason="timeout reading the model")
        return res
    return SmtResult("unknown", dt, reason=_unknown_reason(s.reason_unknown()))


SMALL_LIST = 8


def _small_lists(ob: Obligation, enc: "Z3Encoder", s: z3.Solver) -> z3.ModelRef:
    """Leave the solver at a model whose input lists are short, if one
    exists: a counterexample is only confirmed by running it."""
    lens = [enc.term(v.len) for _, v in ob.inputs if isinstance(v, ListVal)]
    m = s.model()
    if not any(m.eval(n, model_completion=True).as_long() > SMALL_LIST for n in lens):
        return m
    s.push()
    s.add(*[n <= SMALL_LIST for n in lens])
    if s.check() == z3.sat:
        return s.model()  # keep the short-list frame active for model reads
    s.pop()
    return m


def _unknown_reason(why: str) -> str:
    # our own interrupt is reported as a timeout, so a cancel here is the limit
    return "resource limit" if "canceled" in why or "resource limit" in why else why or "unknown"


def _refutation(ob: Obligation, enc: "Z3Encoder", s: z3.Solver, terms: list[L.Term], dt: float, m: z3.ModelRef) -> SmtResult:
    enc.key_candidates = {}
    for _, v in ob.inputs:
        if isinstance(v, L.Term) and v.sort in (L.INT, L.REAL, L.STR, L.BOOL):
            x = enc.value(m, v)
            enc.key_candidates.setdefault(v.sort.name, []).append(x)
    for sname, default in (("Str", ""), ("Int", 0)):
        enc.key_candidates.setdefault(sname, []).append(default)
    if any(_has_opaque(v) for _, v in ob.inputs):
        _json_hints(enc, s, m, terms)
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
