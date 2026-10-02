"""A small many-sorted term language for verification conditions.

VCs are built here once and then *printed* to every backend (Z3, Lean), which
keeps the backends honest: a Lean theorem and the SMT query it replaces are
two renderings of the same term. Terms are immutable and hash-consed by
structure, and the smart constructors fold constants so that goals shown to
humans (and to Lean) stay small.

Integer division is always Euclidean (``ediv``/``emod``) -- the one convention
Z3 and Lean agree on. Language operators such as Python's floor division are
expressed in terms of it by the VC generator.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
import math
import struct
from typing import Iterable

# ---------------------------------------------------------------------------
# Sorts


@dataclass(frozen=True)
class Sort:
    name: str  # Int | Real | Bool | Str | Array | Rec
    elem: "Sort | None" = None  # Array element sort
    index: "Sort | None" = None  # Array index sort (None = Int)
    rec: str | None = None  # record name
    fields: tuple[tuple[str, "Sort"], ...] = ()

    def __str__(self) -> str:
        if self.name == "Array":
            return f"Array[{self.elem}]" if self.index is None else f"Array[{self.index}->{self.elem}]"
        if self.name == "Rec":
            return self.rec or "Rec"
        return self.name


INT = Sort("Int")
REAL = Sort("Real")
FLOAT32 = Sort("Float32")
FLOAT64 = Sort("Float64")
BOOL = Sort("Bool")
STR = Sort("Str")
UNIT = Sort("None")
OPAQUE = Sort("Opaque")  # values of unchecked code: an uninterpreted sort


def ARRAY(elem: Sort, index: Sort | None = None) -> Sort:
    return Sort("Array", elem=elem, index=None if index == INT else index)


def array_lambda(binder: "Const", body: "Term") -> "ArrayLambda":
    return ArrayLambda(binder, body, ARRAY(body.sort, binder.sort))


def index_sort(s: Sort) -> Sort:
    return s.index or INT


def const_array(sort: Sort, v: Term) -> Term:
    """The array mapping every index to ``v``."""
    return App("K", (v,), sort)


def REC(name: str, fields: tuple[tuple[str, Sort], ...]) -> Sort:
    return Sort("Rec", rec=name, fields=fields)


# ---------------------------------------------------------------------------
# Terms


class Term:
    sort: Sort
    __slots__ = ()

    def __repr__(self) -> str:
        return show(self)


@dataclass(frozen=True, repr=False)
class Const(Term):
    name: str
    sort: Sort


@dataclass(frozen=True, repr=False)
class IntV(Term):
    value: int
    sort: Sort = INT


@dataclass(frozen=True, repr=False)
class RealV(Term):
    value: Fraction
    sort: Sort = REAL


@dataclass(frozen=True, repr=False)
class FloatV(Term):
    bits: int
    sort: Sort

    @property
    def value(self) -> float:
        if self.sort == FLOAT32:
            return struct.unpack("<f", struct.pack("<I", self.bits))[0]
        return struct.unpack("<d", struct.pack("<Q", self.bits))[0]


def fval(value: float, sort: Sort) -> FloatV:
    if sort == FLOAT32:
        try:
            return FloatV(struct.unpack("<I", struct.pack("<f", value))[0], sort)
        except OverflowError:
            return FloatV(struct.unpack("<I", struct.pack("<f", math.copysign(math.inf, value)))[0], sort)
    if sort == FLOAT64:
        return FloatV(struct.unpack("<Q", struct.pack("<d", value))[0], sort)
    raise TypeError(sort)


def fval_fraction(value: Fraction, sort: Sort) -> FloatV:
    if sort == FLOAT64:
        try:
            return fval(float(value), sort)
        except OverflowError:
            return fval(-math.inf if value < 0 else math.inf, sort)
    if sort != FLOAT32:
        raise TypeError(sort)
    sign = value < 0
    q = abs(value)
    if q == 0:
        bits = 0
    else:
        e = q.numerator.bit_length() - q.denominator.bit_length()
        if e >= 0 and q < 2**e or e < 0 and q < Fraction(2**e):
            e -= 1
        scale = 149 if e < -126 else 23 - e
        scaled = q * (2**scale if scale >= 0 else Fraction(1, 2**-scale))
        n, rem = divmod(scaled.numerator, scaled.denominator)
        twice = rem * 2
        if twice > scaled.denominator or twice == scaled.denominator and n & 1:
            n += 1
        if e < -126:
            bits = n if n < 2**23 else 1 << 23
        else:
            if n == 2**24:
                n >>= 1
                e += 1
            bits = (0xFF << 23) if e > 127 else ((e + 127) << 23) | (n - (1 << 23))
    return FloatV(bits | (int(sign) << 31), sort)


@dataclass(frozen=True, repr=False)
class BoolV(Term):
    value: bool
    sort: Sort = BOOL


@dataclass(frozen=True, repr=False)
class StrV(Term):
    value: str
    sort: Sort = STR


@dataclass(frozen=True, repr=False)
class App(Term):
    """Built-in operator application.

    ops: add sub mul neg rdiv ediv emod | lt le eq | and or not implies ite |
         to_real floor is_int | select store | field:<name> mk:<rec> | havoc
    """

    op: str
    args: tuple[Term, ...]
    sort: Sort


@dataclass(frozen=True, repr=False)
class ArrayLambda(Term):
    binder: Const
    body: Term
    sort: Sort

    def __post_init__(self) -> None:
        if self.sort.name != "Array" or index_sort(self.sort) != self.binder.sort or self.sort.elem != self.body.sort:
            raise TypeError(f"array lambda sort {self.sort} does not match {self.binder.sort} -> {self.body.sort}")


@dataclass(frozen=True, repr=False)
class Fn(Term):
    """Application of a named function: a defined (possibly recursive)
    function from the :class:`Theory`, or an uninterpreted symbol."""

    name: str
    args: tuple[Term, ...]
    sort: Sort


@dataclass(frozen=True, repr=False)
class Quant(Term):
    kind: str  # forall | exists
    vars: tuple[Const, ...]
    body: Term
    sort: Sort = BOOL
    # SMT trigger patterns: each inner tuple is one multi-pattern.
    patterns: tuple[tuple[Term, ...], ...] = ()


TRUE = BoolV(True)
FALSE = BoolV(False)
ZERO = IntV(0)
ONE = IntV(1)

# ---------------------------------------------------------------------------
# Smart constructors


def _num(t: Term):
    if isinstance(t, IntV):
        return t.value
    if isinstance(t, RealV):
        return t.value
    return None


def lit(v, sort: Sort) -> Term:
    if sort == INT:
        return IntV(int(v))
    if sort == REAL:
        return RealV(Fraction(v))
    if sort in (FLOAT32, FLOAT64):
        return fval_fraction(Fraction(v), sort)
    if sort == BOOL:
        return BoolV(bool(v))
    if sort == STR:
        return StrV(str(v))
    raise TypeError(sort)


def _float_pair(a: Term, b: Term) -> tuple[Term, Term] | None:
    if a.sort not in (FLOAT32, FLOAT64) and b.sort not in (FLOAT32, FLOAT64):
        return None
    sort = FLOAT64 if FLOAT64 in (a.sort, b.sort) else FLOAT32
    return to_float(a, sort), to_float(b, sort)


def add(a: Term, b: Term) -> Term:
    pair = _float_pair(a, b)
    if pair is not None:
        return fbin("fp.add", *pair)
    x, y = _num(a), _num(b)
    if x is not None and y is not None:
        return lit(x + y, a.sort)
    if x == 0:
        return b
    if y == 0:
        return a
    # (e + c1) + c2  ==>  e + (c1 + c2)
    if y is not None and isinstance(a, App) and a.op == "add" and _num(a.args[1]) is not None:
        return add(a.args[0], lit(_num(a.args[1]) + y, a.sort))
    if y is not None and y < 0:
        return App("sub", (a, lit(-y, a.sort)), a.sort)
    return App("add", (a, b), a.sort)


def sub(a: Term, b: Term) -> Term:
    pair = _float_pair(a, b)
    if pair is not None:
        return fbin("fp.sub", *pair)
    x, y = _num(a), _num(b)
    if x is not None and y is not None:
        return lit(x - y, a.sort)
    if y == 0:
        return a
    if a == b:
        return lit(0, a.sort)
    if y is not None and isinstance(a, App) and a.op == "add" and _num(a.args[1]) is not None:
        return add(a.args[0], lit(_num(a.args[1]) - y, a.sort))
    if y is not None and isinstance(a, App) and a.op == "sub" and _num(a.args[1]) is not None:
        return sub(a.args[0], lit(_num(a.args[1]) + y, a.sort))
    if y is not None and y < 0:
        return add(a, lit(-y, a.sort))
    return App("sub", (a, b), a.sort)


def mul(a: Term, b: Term) -> Term:
    pair = _float_pair(a, b)
    if pair is not None:
        return fbin("fp.mul", *pair)
    x, y = _num(a), _num(b)
    if x is not None and y is not None:
        return lit(x * y, a.sort)
    if x == 0 or y == 0:
        return lit(0, a.sort)
    if x == 1:
        return b
    if y == 1:
        return a
    return App("mul", (a, b), a.sort)


def neg(a: Term) -> Term:
    if a.sort in (FLOAT32, FLOAT64):
        return fneg(a)
    x = _num(a)
    if x is not None:
        return lit(-x, a.sort)
    if isinstance(a, App) and a.op == "neg":
        return a.args[0]
    return App("neg", (a,), a.sort)


def rdiv(a: Term, b: Term) -> Term:
    pair = _float_pair(a, b)
    if pair is not None:
        return fbin("fp.div", *pair)
    x, y = _num(a), _num(b)
    if x is not None and y is not None and y != 0:
        return RealV(Fraction(x) / Fraction(y))
    if y == 1:
        return a
    return App("rdiv", (a, b), REAL)


def ediv(a: Term, b: Term) -> Term:
    """Euclidean division (remainder always non-negative)."""
    x, y = _num(a), _num(b)
    if x is not None and y is not None and y != 0:
        q = x // y if y > 0 else -(x // -y)
        return IntV(q)
    if y == 1:
        return a
    return App("ediv", (a, b), INT)


def emod(a: Term, b: Term) -> Term:
    x, y = _num(a), _num(b)
    if x is not None and y is not None and y != 0:
        return IntV(x % abs(y))
    return App("emod", (a, b), INT)


def to_real(a: Term) -> Term:
    if isinstance(a, IntV):
        return RealV(Fraction(a.value))
    return App("to_real", (a,), REAL)


def floor(a: Term) -> Term:
    if isinstance(a, RealV):
        return IntV(a.value.numerator // a.value.denominator)
    if isinstance(a, App) and a.op == "to_real":
        return a.args[0]
    return App("floor", (a,), INT)


def is_int(a: Term) -> Term:
    if a.sort in (FLOAT32, FLOAT64):
        return and_(is_finite(a), is_int(fto_real(a)))
    if isinstance(a, RealV):
        return BoolV(a.value.denominator == 1)
    if isinstance(a, App) and a.op == "to_real":
        return TRUE
    return App("is_int", (a,), BOOL)


def lt(a: Term, b: Term) -> Term:
    if a.sort in (FLOAT32, FLOAT64) or b.sort in (FLOAT32, FLOAT64):
        return fcmp("fp.lt", a, b)
    x, y = _num(a), _num(b)
    if x is not None and y is not None:
        return BoolV(x < y)
    if a == b:
        return FALSE
    return App("lt", (a, b), BOOL)


def le(a: Term, b: Term) -> Term:
    if a.sort in (FLOAT32, FLOAT64) or b.sort in (FLOAT32, FLOAT64):
        return fcmp("fp.leq", a, b)
    x, y = _num(a), _num(b)
    if x is not None and y is not None:
        return BoolV(x <= y)
    if a == b:
        return TRUE
    return App("le", (a, b), BOOL)


def gt(a: Term, b: Term) -> Term:
    return lt(b, a)


def ge(a: Term, b: Term) -> Term:
    return le(b, a)


def eq(a: Term, b: Term) -> Term:
    if a.sort in (FLOAT32, FLOAT64) or b.sort in (FLOAT32, FLOAT64):
        return fcmp("fp.eq", a, b)
    if a == b:
        return TRUE
    if isinstance(a, (IntV, RealV, BoolV, StrV)) and isinstance(b, (IntV, RealV, BoolV, StrV)):
        return BoolV(a.value == b.value)
    if a.sort == BOOL:
        if b == TRUE:
            return a
        if b == FALSE:
            return not_(a)
        if a == TRUE:
            return b
        if a == FALSE:
            return not_(b)
    return App("eq", (a, b), BOOL)


def ne(a: Term, b: Term) -> Term:
    return not_(eq(a, b))


def not_(a: Term) -> Term:
    if isinstance(a, BoolV):
        return BoolV(not a.value)
    if isinstance(a, App) and a.op == "not":
        return a.args[0]
    return App("not", (a,), BOOL)


def and_(*xs: Term) -> Term:
    out: list[Term] = []
    for x in xs:
        if x == TRUE:
            continue
        if x == FALSE:
            return FALSE
        if isinstance(x, App) and x.op == "and":
            for y in x.args:
                if y not in out:
                    out.append(y)
        elif x not in out:
            out.append(x)
    if not out:
        return TRUE
    if len(out) == 1:
        return out[0]
    return App("and", tuple(out), BOOL)


def or_(*xs: Term) -> Term:
    out: list[Term] = []
    for x in xs:
        if x == FALSE:
            continue
        if x == TRUE:
            return TRUE
        if isinstance(x, App) and x.op == "or":
            for y in x.args:
                if y not in out:
                    out.append(y)
        elif x not in out:
            out.append(x)
    if not out:
        return FALSE
    if len(out) == 1:
        return out[0]
    return App("or", tuple(out), BOOL)


def implies(a: Term, b: Term) -> Term:
    if a == TRUE:
        return b
    if a == FALSE or b == TRUE:
        return TRUE
    if b == FALSE:
        return not_(a)
    return App("implies", (a, b), BOOL)


def ite(c: Term, a: Term, b: Term) -> Term:
    if c == TRUE:
        return a
    if c == FALSE:
        return b
    if a == b:
        return a
    if a.sort == BOOL and a == TRUE and b == FALSE:
        return c
    if a.sort == BOOL and a == FALSE and b == TRUE:
        return not_(c)
    return App("ite", (c, a, b), a.sort)


def select(arr: Term, idx: Term) -> Term:
    if isinstance(arr, ArrayLambda):
        if arr.binder.sort != idx.sort:
            raise TypeError(f"array lambda index has sort {arr.binder.sort}, got {idx.sort}")
        return substitute(arr.body, {arr.binder: idx})
    if isinstance(arr, App) and arr.op == "K":
        return arr.args[0]
    if isinstance(arr, App) and arr.op == "store":
        base, k, v = arr.args
        if k == idx:
            return v
        if isinstance(k, IntV) and isinstance(idx, IntV):
            return select(base, idx)
    assert arr.sort.elem is not None
    return App("select", (arr, idx), arr.sort.elem)


def store(arr: Term, idx: Term, val: Term) -> Term:
    return App("store", (arr, idx, val), arr.sort)


def field(obj: Term, name: str) -> Term:
    if isinstance(obj, App) and obj.op.startswith("mk:"):
        for (fname, _), v in zip(obj.sort.fields, obj.args):
            if fname == name:
                return v
    for fname, fsort in obj.sort.fields:
        if fname == name:
            return App(f"field:{name}", (obj,), fsort)
    raise KeyError(name)


def mkrec(sort: Sort, vals: tuple[Term, ...]) -> Term:
    return App(f"mk:{sort.rec}", vals, sort)


def forall(vs: Iterable[Const], body: Term) -> Term:
    vs = tuple(v for v in vs if occurs(v, body))
    if not vs or isinstance(body, BoolV):
        return body
    return Quant("forall", vs, body)


def exists(vs: Iterable[Const], body: Term) -> Term:
    vs = tuple(v for v in vs if occurs(v, body))
    if not vs or isinstance(body, BoolV):
        return body
    return Quant("exists", vs, body)


def abs_(a: Term) -> Term:
    if a.sort in (FLOAT32, FLOAT64):
        if isinstance(a, FloatV):
            return fval(abs(a.value), a.sort)
        return App("fp.abs", (a,), a.sort)
    return ite(le(lit(0, a.sort), a), a, neg(a))


def fbin(op: str, a: Term, b: Term) -> Term:
    s = a.sort
    if isinstance(a, FloatV) and isinstance(b, FloatV):
        x, y = a.value, b.value
        if op == "fp.add":
            z = x + y
            exact = Fraction(x) + Fraction(y) if s == FLOAT32 and math.isfinite(x) and math.isfinite(y) else None
        elif op == "fp.sub":
            z = x - y
            exact = Fraction(x) - Fraction(y) if s == FLOAT32 and math.isfinite(x) and math.isfinite(y) else None
        elif op == "fp.mul":
            z = x * y
            exact = Fraction(x) * Fraction(y) if s == FLOAT32 and math.isfinite(x) and math.isfinite(y) else None
        elif op == "fp.div" and y != 0.0 and s != FLOAT32:
            z = x / y
            exact = None
        else:
            return App(op, (a, b), s)
        if exact is not None and exact:
            return fval_fraction(exact, s)
        return fval(z, s)
    return App(op, (a, b), s)


def fneg(a: Term) -> Term:
    if isinstance(a, FloatV):
        return fval(-a.value, a.sort)
    return App("fp.neg", (a,), a.sort)


def fcmp(op: str, a: Term, b: Term) -> Term:
    if a.sort in (FLOAT32, FLOAT64) and b.sort in (FLOAT32, FLOAT64):
        if a.sort != b.sort:
            b = to_float(b, a.sort)
        def integer_cast(x: Term) -> Term | None:
            if isinstance(x, App) and x.op in ("fp.from_int", "fp.of_int") and len(x.args) == 1 and x.args[0].sort == INT:
                return x.args[0]
            return None

        def zero(x: Term) -> bool:
            return isinstance(x, FloatV) and x.value == 0.0

        cast = integer_cast(b)
        if zero(a) and cast is not None:
            return {"fp.lt": gt, "fp.leq": ge, "fp.eq": eq}[op](cast, IntV(0))
        cast = integer_cast(a)
        if cast is not None and zero(b):
            return {"fp.lt": lt, "fp.leq": le, "fp.eq": eq}[op](cast, IntV(0))
        if isinstance(a, FloatV) and isinstance(b, FloatV):
            x, y = a.value, b.value
            return BoolV(x < y if op == "fp.lt" else x <= y if op == "fp.leq" else x == y)
        return App(op, (a, b), BOOL)
    return xcmp(op, a, b)


def fpred(op: str, a: Term) -> Term:
    if isinstance(a, FloatV):
        x = a.value
        if op == "fp.isNegative":
            return BoolV(math.copysign(1.0, x) < 0 and not math.isnan(x))
        return BoolV(math.isnan(x) if op == "fp.isNaN" else math.isinf(x) if op == "fp.isInfinite" else x == 0.0)
    return App(op, (a,), BOOL)


def fto_real(a: Term) -> Term:
    if isinstance(a, FloatV) and math.isfinite(a.value):
        return RealV(Fraction(a.value))
    return App("fp.to_real", (a,), REAL)


def xcmp(op: str, a: Term, b: Term) -> Term:
    flip = a.sort not in (FLOAT32, FLOAT64)
    f, x = (b, a) if flip else (a, b)
    xr = x if x.sort == REAL else to_real(x)
    fr = fto_real(f)
    nan, inf = fpred("fp.isNaN", f), fpred("fp.isInfinite", f)
    pos = not_(fpred("fp.isNegative", f))
    if op == "fp.eq":
        return and_(not_(nan), not_(inf), eq(fr, xr))
    exact = (lt(xr, fr) if op == "fp.lt" else le(xr, fr)) if flip else (lt(fr, xr) if op == "fp.lt" else le(fr, xr))
    beyond = pos if flip else not_(pos)
    return and_(not_(nan), ite(inf, beyond, exact))


def is_finite(a: Term) -> Term:
    if isinstance(a, FloatV):
        return BoolV(math.isfinite(a.value))
    return and_(not_(App("fp.isNaN", (a,), BOOL)), not_(App("fp.isInfinite", (a,), BOOL)))


def to_float(a: Term, sort: Sort) -> Term:
    if a.sort == sort:
        return a
    if isinstance(a, (IntV, RealV)):
        return fval_fraction(Fraction(a.value), sort)
    if a.sort in (FLOAT32, FLOAT64):
        return App("fp.cast", (a,), sort)
    return App("fp.from_int" if a.sort == INT else "fp.from_real", (a,), sort)


def min_(a: Term, b: Term) -> Term:
    return ite(le(a, b), a, b)


def max_(a: Term, b: Term) -> Term:
    return ite(le(a, b), b, a)


# ---------------------------------------------------------------------------
# Traversal


def children(t: Term) -> tuple[Term, ...]:
    if isinstance(t, (App, Fn)):
        return t.args
    if isinstance(t, ArrayLambda):
        return (t.body,)
    if isinstance(t, Quant):
        return (t.body, *(term for pattern in t.patterns for term in pattern))
    return ()


def iter_terms(t: Term):
    stack = [t]
    seen: set[int] = set()
    while stack:
        x = stack.pop()
        if id(x) in seen:
            continue
        seen.add(id(x))
        yield x
        stack.extend(children(x))


def occurs(v: Const, t: Term) -> bool:
    return any(x == v for x in iter_terms(t))


def consts(t: Term) -> set[Const]:
    bound: set[Const] = set()
    out: set[Const] = set()

    def go(x: Term) -> None:
        if isinstance(x, Const):
            if x not in bound:
                out.add(x)
        elif isinstance(x, Quant):
            saved = set(bound)
            bound.update(x.vars)
            go(x.body)
            for pattern in x.patterns:
                for term in pattern:
                    go(term)
            bound.clear()
            bound.update(saved)
        elif isinstance(x, ArrayLambda):
            saved = set(bound)
            bound.add(x.binder)
            go(x.body)
            bound.clear()
            bound.update(saved)
        else:
            for c in children(x):
                go(c)

    go(t)
    return out


def fns(t: Term) -> set[str]:
    return {x.name for x in iter_terms(t) if isinstance(x, Fn)}


def _term_names(t: Term) -> set[str]:
    names: set[str] = set()
    for x in iter_terms(t):
        if isinstance(x, Const):
            names.add(x.name)
        elif isinstance(x, Quant):
            names.update(v.name for v in x.vars)
        elif isinstance(x, ArrayLambda):
            names.add(x.binder.name)
    return names


def _fresh_binder(binder: Const, used: set[str]) -> Const:
    stem = f"{binder.name}$alpha"
    name, suffix = stem, 0
    while name in used:
        suffix += 1
        name = f"{stem}{suffix}"
    used.add(name)
    return Const(name, binder.sort)


def substitute(t: Term, m: dict[Term, Term]) -> Term:
    if t in m:
        return m[t]
    if isinstance(t, App):
        args = tuple(substitute(a, m) for a in t.args)
        if args == t.args:
            return t
        return rebuild(t.op, args, t.sort)
    if isinstance(t, Fn):
        args = tuple(substitute(a, m) for a in t.args)
        return t if args == t.args else Fn(t.name, args, t.sort)
    if isinstance(t, ArrayLambda):
        inner = {k: v for k, v in m.items() if k != t.binder and t.binder not in consts(k)}
        body, binder = t.body, t.binder
        replacements = set().union(*(consts(v) for v in inner.values())) if inner else set()
        if binder in replacements:
            used = _term_names(body) | {binder.name}
            for key, value in inner.items():
                used.update(_term_names(key))
                used.update(_term_names(value))
            renamed = _fresh_binder(binder, used)
            body = substitute(body, {binder: renamed})
            binder = renamed
        new_body = substitute(body, inner)
        return t if binder == t.binder and new_body is t.body else ArrayLambda(binder, new_body, t.sort)
    if isinstance(t, Quant):
        inner = {
            k: v for k, v in m.items()
            if k not in t.vars and not any(var in consts(k) for var in t.vars)
        }
        body, vars_ = t.body, t.vars
        renaming = {}
        replacements = set().union(*(consts(v) for v in inner.values())) if inner else set()
        if replacements.intersection(vars_):
            used = _term_names(body) | {var.name for var in vars_}
            for pattern in t.patterns:
                for term in pattern:
                    used.update(_term_names(term))
            for key, value in inner.items():
                used.update(_term_names(key))
                used.update(_term_names(value))
            renamed = []
            for var in vars_:
                if var not in replacements:
                    renamed.append(var)
                    continue
                fresh = _fresh_binder(var, used)
                renaming[var] = fresh
                renamed.append(fresh)
            if renaming:
                body = substitute(body, renaming)
                vars_ = tuple(renamed)
        body = substitute(body, inner)
        patterns = tuple(tuple(substitute(substitute(p, renaming), inner) for p in ps) for ps in t.patterns)
        if body is t.body and vars_ == t.vars and patterns == t.patterns:
            return t
        return Quant(t.kind, vars_, body, patterns=patterns)
    return t


_REBUILD = {
    "add": add,
    "sub": sub,
    "mul": mul,
    "neg": neg,
    "rdiv": rdiv,
    "ediv": ediv,
    "emod": emod,
    "lt": lt,
    "le": le,
    "eq": eq,
    "not": not_,
    "implies": implies,
    "ite": ite,
    "to_real": to_real,
    "floor": floor,
    "is_int": is_int,
    "select": select,
    "store": store,
    "fp.add": lambda a, b: fbin("fp.add", a, b),
    "fp.sub": lambda a, b: fbin("fp.sub", a, b),
    "fp.mul": lambda a, b: fbin("fp.mul", a, b),
    "fp.div": lambda a, b: fbin("fp.div", a, b),
    "fp.neg": fneg,
    "fp.lt": lambda a, b: fcmp("fp.lt", a, b),
    "fp.leq": lambda a, b: fcmp("fp.leq", a, b),
    "fp.eq": lambda a, b: fcmp("fp.eq", a, b),
    "fp.to_real": fto_real,
    "fp.abs": abs_,
    "fp.isNaN": lambda a: fpred("fp.isNaN", a),
    "fp.isInfinite": lambda a: fpred("fp.isInfinite", a),
    "fp.isZero": lambda a: fpred("fp.isZero", a),
    "fp.isNegative": lambda a: fpred("fp.isNegative", a),
}


def rebuild(op: str, args: tuple[Term, ...], sort: Sort) -> Term:
    if op == "and":
        return and_(*args)
    if op == "or":
        return or_(*args)
    if op in ("fp.from_int", "fp.from_real", "fp.cast"):
        return to_float(args[0], sort)
    f = _REBUILD.get(op)
    if f is not None:
        return f(*args)
    if op.startswith("field:"):
        return field(args[0], op[6:])
    return App(op, args, sort)


# ---------------------------------------------------------------------------
# Theory: defined functions and axioms


@dataclass
class FunDef:
    name: str
    params: tuple[Const, ...]
    sort: Sort
    body: Term | None  # None = uninterpreted
    recursive: bool = False
    # For Lean: a Nat-valued fuel/measure is not needed when the definition is
    # structural over a builtin (seqsum); user definitions carry a measure,
    # lexicographic when it has several parts.
    measure: tuple[Term, ...] | None = None
    doc: str = ""
    # For guarded definitions f(x) = if guard then inner else default:
    guard: Term | None = None
    inner: Term | None = None


@dataclass
class Axiom:
    name: str
    formula: Term
    about: str  # FuncRef key of the function whose contract this is ("" for theory lemmas)
    doc: str = ""
    symbol: str = ""  # logical function whose presence brings the axiom in


def seqsum_def(elem: Sort) -> FunDef:
    """``seqsum(a, lo, hi) = a[lo] + ... + a[hi-1]`` (0 when hi <= lo)."""
    name = {INT: "seqsum", REAL: "seqsum_r", FLOAT32: "seqsum_f32", FLOAT64: "seqsum_f64"}.get(elem, "seqsum_r")
    a = Const("a", ARRAY(elem))
    lo = Const("lo", INT)
    hi = Const("hi", INT)
    rec = Fn(name, (a, lo, sub(hi, ONE)), elem)
    body = ite(le(hi, lo), lit(0, elem), add(rec, select(a, sub(hi, ONE))))
    return FunDef(name, (a, lo, hi), elem, body, recursive=True, measure=(sub(hi, lo),), doc="sum of a[lo:hi]")


def seqsum_literal(a: Term, lo: Term, hi: Term, elem: Sort) -> Term | None:
    if not isinstance(lo, IntV) or not isinstance(hi, IntV):
        return None
    total = lit(0, elem)
    for i in range(lo.value, max(lo.value, hi.value)):
        total = add(total, select(a, IntV(i)))
    return total


def python_float_sum_defs(major: int, minor: int) -> tuple[FunDef, FunDef]:
    """CPython 3.12+ Neumaier summation over binary64 list elements."""
    state_name = f"py_sum_state_cpython_{major}_{minor}"
    sum_name = f"seqsum_py_cpython_{major}_{minor}"
    state_sort = REC(f"PySumState_cpython_{major}_{minor}", (("hi", FLOAT64), ("lo", FLOAT64)))
    a = Const("a", ARRAY(FLOAT64))
    lo, hi = Const("lo", INT), Const("hi", INT)
    prev = Fn(state_name, (a, lo, sub(hi, ONE)), state_sort)
    prev_hi, prev_lo = field(prev, "hi"), field(prev, "lo")
    x = select(a, sub(hi, ONE))
    next_hi, next_lo = _neumaier_step(prev_hi, prev_lo, x)
    zero = fval(0.0, FLOAT64)
    initial = mkrec(state_sort, (zero, zero))
    step = mkrec(state_sort, (next_hi, next_lo))
    state_body = ite(le(hi, lo), initial, step)
    state_def = FunDef(state_name, (a, lo, hi), state_sort, state_body, recursive=True, measure=(sub(hi, lo),), doc="CPython compensated float sum state")
    state = Fn(state_name, (a, lo, hi), state_sort)
    total_hi, total_lo = field(state, "hi"), field(state, "lo")
    body = ite(and_(ne(total_lo, zero), is_finite(total_lo)), add(total_hi, total_lo), total_hi)
    sum_def = FunDef(sum_name, (a, lo, hi), FLOAT64, body, doc="CPython compensated float sum")
    return state_def, sum_def


def python_numeric_sum_defs(major: int, minor: int) -> tuple[FunDef, FunDef]:
    """CPython sum state for lists whose elements may be ints or binary64 floats."""
    state_name = f"py_numeric_sum_state_cpython_{major}_{minor}"
    sum_name = f"seqsum_py_numeric_cpython_{major}_{minor}"
    state_sort = REC(
        f"PyNumericSumState_cpython_{major}_{minor}",
        (("in_float", BOOL), ("int_total", INT), ("fast", BOOL), ("ordinary", FLOAT64), ("hi", FLOAT64), ("lo", FLOAT64)),
    )
    number_sort = REC("PythonNumber", (("is_int", BOOL), ("integer", INT), ("floating", FLOAT64)))
    values = Const("values", ARRAY(number_sort))
    lo, hi = Const("lo", INT), Const("hi", INT)
    prev = Fn(state_name, (values, lo, sub(hi, ONE)), state_sort)
    in_float = field(prev, "in_float")
    int_total = field(prev, "int_total")
    fast = field(prev, "fast")
    ordinary = field(prev, "ordinary")
    comp_hi = field(prev, "hi")
    comp_lo = field(prev, "lo")
    idx = sub(hi, ONE)
    item = select(values, idx)
    is_int = field(item, "is_int")
    i = field(item, "integer")
    x = field(item, "floating")
    i_float = to_float(i, FLOAT64)
    entered = ite(is_int, i_float, x)
    start_int = and_(not_(in_float), is_int)
    start_float = and_(not_(in_float), not_(is_int))
    next_ordinary = ite(in_float, add(ordinary, entered), add(to_float(int_total, FLOAT64), entered))
    neumaier_hi, neumaier_lo = _neumaier_step(comp_hi, comp_lo, entered)
    zero = fval(0.0, FLOAT64)
    long_min, long_max = IntV(-(1 << 63)), IntV((1 << 63) - 1)
    next_int_total = add(int_total, i)
    next_fast = and_(fast, le(long_min, i), le(i, long_max), le(long_min, next_int_total), le(next_int_total, long_max))
    step_state = mkrec(
        state_sort,
        (
            not_(start_int),
            ite(start_int, next_int_total, int_total),
            ite(start_int, next_fast, fast),
            ite(start_int, ordinary, next_ordinary),
            ite(start_int, comp_hi, ite(start_float, next_ordinary, neumaier_hi)),
            ite(start_int, comp_lo, ite(start_float, zero, neumaier_lo)),
        ),
    )
    initial = mkrec(state_sort, (FALSE, ZERO, TRUE, zero, zero, zero))
    state_body = ite(le(hi, lo), initial, step_state)
    state_def = FunDef(state_name, (values, lo, hi), state_sort, state_body, recursive=True, measure=(sub(hi, lo),), doc="CPython mixed numeric sum state")
    state = Fn(state_name, (values, lo, hi), state_sort)
    corrected = ite(and_(ne(field(state, "lo"), zero), is_finite(field(state, "lo"))), add(field(state, "hi"), field(state, "lo")), field(state, "hi"))
    result = ite(field(state, "fast"), corrected, field(state, "ordinary")) if (major, minor) >= (3, 12) else field(state, "ordinary")
    number_sort = REC("PythonNumber", (("is_int", BOOL), ("integer", INT), ("floating", FLOAT64)))
    tagged_result = mkrec(number_sort, (not_(field(state, "in_float")), field(state, "int_total"), result))
    sum_def = FunDef(sum_name, (values, lo, hi), number_sort, tagged_result, doc="CPython mixed numeric sum")
    return state_def, sum_def


def _neumaier_step(hi: Term, lo: Term, x: Term) -> tuple[Term, Term]:
    total = add(hi, x)
    correction = ite(
        le(abs_(x), abs_(hi)),
        add(lo, add(sub(hi, total), x)),
        add(lo, add(sub(x, total), hi)),
    )
    return total, correction


def python_float_sum(a: Term, lo: Term, hi: Term, major: int, minor: int) -> Term:
    zero = fval(0.0, FLOAT64)
    if isinstance(lo, IntV) and isinstance(hi, IntV):
        total_hi, total_lo = zero, zero
        for i in range(lo.value, max(lo.value, hi.value)):
            total_hi, total_lo = _neumaier_step(total_hi, total_lo, select(a, IntV(i)))
    else:
        state_sort = REC(f"PySumState_cpython_{major}_{minor}", (("hi", FLOAT64), ("lo", FLOAT64)))
        state = Fn(f"py_sum_state_cpython_{major}_{minor}", (a, lo, hi), state_sort)
        total_hi, total_lo = field(state, "hi"), field(state, "lo")
    return ite(and_(ne(total_lo, zero), is_finite(total_lo)), add(total_hi, total_lo), total_hi)


def python_numeric_sum_literal(values: Term, lo: int, hi: int, major: int, minor: int) -> Term:
    """Unroll CPython's mixed int/float sum for a statically sized list."""
    in_float = FALSE
    int_total = ZERO
    fast = TRUE
    ordinary = hi_sum = lo_sum = fval(0.0, FLOAT64)
    zero = fval(0.0, FLOAT64)
    long_min, long_max = IntV(-(1 << 63)), IntV((1 << 63) - 1)
    for index in range(lo, max(lo, hi)):
        item = select(values, IntV(index))
        is_int = field(item, "is_int")
        int_value = field(item, "integer")
        float_value = field(item, "floating")
        was_in_float = in_float
        start_int = and_(not_(was_in_float), is_int)
        start_float = and_(not_(was_in_float), not_(is_int))
        entered = ite(is_int, to_float(int_value, FLOAT64), float_value)
        next_int_total = add(int_total, int_value)
        next_fast = and_(fast, le(long_min, int_value), le(int_value, long_max), le(long_min, next_int_total), le(next_int_total, long_max))
        next_ordinary = ite(was_in_float, add(ordinary, entered), add(to_float(int_total, FLOAT64), entered))
        next_hi, next_lo = _neumaier_step(hi_sum, lo_sum, entered)
        ordinary = ite(start_int, ordinary, next_ordinary)
        hi_sum = ite(start_int, hi_sum, ite(start_float, next_ordinary, next_hi))
        lo_sum = ite(start_int, lo_sum, ite(start_float, zero, next_lo))
        fast = ite(start_int, next_fast, fast)
        int_total = ite(start_int, next_int_total, int_total)
        in_float = or_(was_in_float, not_(is_int))
    if (major, minor) >= (3, 12):
        corrected = ite(and_(ne(lo_sum, zero), is_finite(lo_sum)), add(hi_sum, lo_sum), hi_sum)
        result = ite(fast, corrected, ordinary)
    else:
        result = ordinary
    number_sort = REC("PythonNumber", (("is_int", BOOL), ("integer", INT), ("floating", FLOAT64)))
    return mkrec(number_sort, (not_(in_float), int_total, result))


def theory_lemmas(elem: Sort) -> list[Axiom]:
    """Facts about ``seqsum``/``seqcount`` that need induction to prove.

    Every one of these is proved in Lean in ``telic/lean/Theory.lean`` (and
    checked by the test suite), so Z3 may use them without trusting them.
    """
    ss = "seqsum" if elem == INT else "seqsum_r"
    sc = f"seqcount_{elem.name.lower()}"
    arr = ARRAY(elem)
    a, b = Const("a", arr), Const("b", arr)
    lo, mid, hi, k, i = (Const(n, INT) for n in ("lo", "mid", "hi", "k", "i"))
    v = Const("v", elem)
    zero = lit(0, elem)

    def S(x: Term, l: Term, h: Term) -> Term:
        return Fn(ss, (x, l, h), elem)

    def C(x: Term, l: Term, h: Term, y: Term) -> Term:
        return Fn(sc, (x, l, h, y), INT)

    out: list[Axiom] = []
    q = lambda vs, body, pats: Quant("forall", tuple(vs), body, patterns=pats)  # noqa: E731
    out.append(Axiom(f"{ss}_front", q((a, lo, hi), implies(lt(lo, hi), eq(S(a, lo, hi), add(select(a, lo), S(a, add(lo, ONE), hi)))), ((S(a, lo, hi), select(a, lo)),)), "", "sum peels off its first element", ss))
    inner = Quant("forall", (i,), implies(and_(le(lo, i), lt(i, hi)), le(zero, select(a, i))))
    out.append(Axiom(f"{ss}_nonneg", q((a, lo, hi), implies(inner, le(zero, S(a, lo, hi))), ((S(a, lo, hi),),)), "", "sum of non-negatives is non-negative", ss))
    inner_np = Quant("forall", (i,), implies(and_(le(lo, i), lt(i, hi)), le(select(a, i), zero)))
    out.append(Axiom(f"{ss}_nonpos", q((a, lo, hi), implies(inner_np, le(S(a, lo, hi), zero)), ((S(a, lo, hi),),)), "", "sum of non-positives is non-positive", ss))
    upd = store(a, k, v)
    out.append(
        Axiom(
            f"{ss}_store",
            q((a, lo, hi, k, v), eq(S(upd, lo, hi), add(S(a, lo, hi), ite(and_(le(lo, k), lt(k, hi)), sub(v, select(a, k)), zero))), ((S(upd, lo, hi),),)),
            "",
            "updating one element changes the sum by the difference",
            ss,
        )
    )
    out.append(Axiom(f"{ss}_split", q((a, lo, mid, hi), implies(and_(le(lo, mid), le(mid, hi)), eq(S(a, lo, hi), add(S(a, lo, mid), S(a, mid, hi)))), ((S(a, lo, mid), S(a, mid, hi)),)), "", "sum splits at any midpoint", ss))
    at_k = and_(le(lo, k), lt(k, hi))
    out.append(Axiom(f"{ss}_elem_le", q((a, lo, hi, k), implies(and_(inner, at_k), le(select(a, k), S(a, lo, hi))), ((S(a, lo, hi), select(a, k)),)), "", "each of non-negatives is at most their sum", ss))
    out.append(Axiom(f"{ss}_elem_ge", q((a, lo, hi, k), implies(and_(inner_np, at_k), le(S(a, lo, hi), select(a, k))), ((S(a, lo, hi), select(a, k)),)), "", "each of non-positives is at least their sum", ss))
    out.append(Axiom(f"{sc}_bounds", q((a, lo, hi, v), and_(le(ZERO, C(a, lo, hi, v)), le(C(a, lo, hi, v), max_(sub(hi, lo), ZERO))), ((C(a, lo, hi, v),),)), "", "a count lies between 0 and the length", sc))
    out.append(Axiom(f"{sc}_front", q((a, lo, hi, v), implies(lt(lo, hi), eq(C(a, lo, hi, v), add(ite(eq(select(a, lo), v), ONE, ZERO), C(a, add(lo, ONE), hi, v)))), ((C(a, lo, hi, v), select(a, lo)),)), "", "count peels off its first element", sc))
    del mid
    return out


def seqcount_def(elem: Sort) -> FunDef:
    name = f"seqcount_{elem.name.lower()}"
    a = Const("a", ARRAY(elem))
    lo = Const("lo", INT)
    hi = Const("hi", INT)
    v = Const("v", elem)
    rec = Fn(name, (a, lo, sub(hi, ONE), v), INT)
    body = ite(le(hi, lo), ZERO, add(rec, ite(eq(select(a, sub(hi, ONE)), v), ONE, ZERO)))
    return FunDef(name, (a, lo, hi, v), INT, body, recursive=True, measure=(sub(hi, lo),), doc="occurrences of v in a[lo:hi]")


# ---------------------------------------------------------------------------
# Regular languages of text the parsing builtins accept (SMT-LIB syntax)

_D = "(re.range \"0\" \"9\")"
_WS = "(re.union (str.to_re \" \") (re.range \"\\u{9}\" \"\\u{d}\"))"
_SIGN = "(re.opt (re.union (str.to_re \"+\") (str.to_re \"-\")))"
_PART = f"(re.++ {_D} (re.* (re.++ (re.opt (str.to_re \"_\")) {_D})))"  # 1_000
_EXP = f"(re.++ (re.union (str.to_re \"e\") (str.to_re \"E\")) {_SIGN} {_PART})"
_WORDS = "(re.union " + " ".join(f"(str.to_re \"{w}\")" for w in ("inf", "infinity", "nan", "Inf", "Infinity", "NaN", "INF", "INFINITY", "NAN")) + ")"
REGEXES = {
    "digits": f"(re.+ {_D})",
    "neg_digits": f"(re.++ (str.to_re \"-\") (re.+ {_D}))",
    "pos_digits": f"(re.++ (str.to_re \"+\") (re.+ {_D}))",
    # Python's int(): spaces, a sign, digits with single underscores (ASCII only: a
    # string outside may still parse, with Unicode digits)
    "py_int": f"(re.++ (re.* {_WS}) {_SIGN} {_PART} (re.* {_WS}))",
    # Python's float() (the words in a few spellings; outside may still parse)
    "py_float": f"(re.++ (re.* {_WS}) {_SIGN} (re.union (re.++ (re.union (re.++ {_PART} (re.opt (re.++ (str.to_re \".\") (re.opt {_PART})))) (re.++ (str.to_re \".\") {_PART})) (re.opt {_EXP})) {_WORDS}) (re.* {_WS}))",
    # float() text that is not a finite number
    "py_float_word": f"(re.++ (re.* {_WS}) {_SIGN} {_WORDS} (re.* {_WS}))",
    # JavaScript's parseInt/parseFloat read a leading number: after spaces and a sign, a digit
    "js_num_prefix": f"(re.++ (re.* {_WS}) {_SIGN} {_D} re.all)",
    "js_nonneg_prefix": f"(re.++ (re.* {_WS}) (re.opt (str.to_re \"+\")) {_D} re.all)",
}


def in_re(s: Term, name: str) -> Term:
    """``s`` is in the regular language ``REGEXES[name]``."""
    return App("str.in_re", (s, StrV(REGEXES[name])), BOOL)


def str_to_int(s: Term) -> Term:
    """The number a string of decimal digits spells (-1 for any other string)."""
    return App("str.to_int", (s,), INT)


# ---------------------------------------------------------------------------
# Pretty printing (for humans; also the canonical text used for hashing)

_INFIX = {
    "add": ("+", 6),
    "sub": ("-", 6),
    "mul": ("*", 7),
    "rdiv": ("/", 7),
    "ediv": ("ediv", 7),
    "emod": ("emod", 7),
    "lt": ("<", 4),
    "le": ("<=", 4),
    "eq": ("==", 4),
    "and": ("and", 2),
    "or": ("or", 1),
    "implies": ("==>", 0),
}


def show(t: Term, prec: int = -1) -> str:
    if isinstance(t, Const):
        return t.name
    if isinstance(t, IntV):
        return str(t.value)
    if isinstance(t, RealV):
        v = t.value
        return str(v.numerator) if v.denominator == 1 else f"{v.numerator}/{v.denominator}"
    if isinstance(t, FloatV):
        return repr(t.value)
    if isinstance(t, BoolV):
        return "true" if t.value else "false"
    if isinstance(t, StrV):
        return repr(t.value)
    if isinstance(t, Quant):
        vs = ", ".join(v.name for v in t.vars)
        s = f"{t.kind} {vs}. {show(t.body, 0)}"
        return f"({s})" if prec >= 0 else s
    if isinstance(t, ArrayLambda):
        s = f"fun {t.binder.name} => {show(t.body)}"
        return f"({s})" if prec >= 0 else s
    if isinstance(t, Fn):
        return f"{t.name}({', '.join(show(a) for a in t.args)})"
    assert isinstance(t, App)
    op = t.op
    if op in _INFIX:
        sym, p = _INFIX[op]
        if op in ("and", "or"):
            s = f" {sym} ".join(show(a, p + 1) for a in t.args)
        elif op in ("ediv", "emod"):
            return f"{sym}({show(t.args[0])}, {show(t.args[1])})"
        else:
            s = f"{show(t.args[0], p)} {sym} {show(t.args[1], p + 1)}"
        return f"({s})" if p <= prec else s
    if op == "not":
        a = t.args[0]
        if isinstance(a, App) and a.op == "eq":
            s = f"{show(a.args[0], 5)} != {show(a.args[1], 5)}"
            return f"({s})" if 4 <= prec else s
        return f"not {show(a, 8)}"
    if op == "neg":
        return f"-{show(t.args[0], 8)}"
    if op == "ite":
        s = f"if {show(t.args[0])} then {show(t.args[1])} else {show(t.args[2])}"
        return f"({s})"
    if op == "select":
        return f"{show(t.args[0], 9)}[{show(t.args[1])}]"
    if op == "store":
        return f"{show(t.args[0], 9)}[{show(t.args[1])} := {show(t.args[2])}]"
    if op.startswith("field:"):
        return f"{show(t.args[0], 9)}.{op[6:]}"
    if op.startswith("mk:"):
        fs = ", ".join(f"{n}={show(a)}" for (n, _), a in zip(t.sort.fields, t.args))
        return f"{op[3:]}({fs})"
    return f"{op}({', '.join(show(a) for a in t.args)})"


def canonical(t: Term) -> str:
    """Fully parenthesised, sort-annotated text: stable across runs."""
    if isinstance(t, Const):
        return f"{t.name}:{t.sort}"
    if isinstance(t, (IntV, BoolV, StrV)):
        return repr(t.value)
    if isinstance(t, RealV):
        return f"{t.value.numerator}/{t.value.denominator}"
    if isinstance(t, FloatV):
        return f"f{t.bits:x}:{t.sort}"
    if isinstance(t, Quant):
        return f"({t.kind} ({' '.join(canonical(v) for v in t.vars)}) {canonical(t.body)})"
    if isinstance(t, ArrayLambda):
        return f"(array_lambda {canonical(t.binder)} {canonical(t.body)} : {t.sort})"
    if isinstance(t, Fn):
        return f"({t.name} {' '.join(canonical(a) for a in t.args)})"
    assert isinstance(t, App)
    return f"({t.op} {' '.join(canonical(a) for a in t.args)})"
