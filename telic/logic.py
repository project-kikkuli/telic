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
BOOL = Sort("Bool")
STR = Sort("Str")
OPAQUE = Sort("Opaque")  # values of unchecked code: an uninterpreted sort


def ARRAY(elem: Sort, index: Sort | None = None) -> Sort:
    return Sort("Array", elem=elem, index=None if index == INT else index)


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
    if sort == BOOL:
        return BoolV(bool(v))
    if sort == STR:
        return StrV(str(v))
    raise TypeError(sort)


def add(a: Term, b: Term) -> Term:
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
    x = _num(a)
    if x is not None:
        return lit(-x, a.sort)
    if isinstance(a, App) and a.op == "neg":
        return a.args[0]
    return App("neg", (a,), a.sort)


def rdiv(a: Term, b: Term) -> Term:
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
    if isinstance(a, RealV):
        return BoolV(a.value.denominator == 1)
    if isinstance(a, App) and a.op == "to_real":
        return TRUE
    return App("is_int", (a,), BOOL)


def lt(a: Term, b: Term) -> Term:
    x, y = _num(a), _num(b)
    if x is not None and y is not None:
        return BoolV(x < y)
    if a == b:
        return FALSE
    return App("lt", (a, b), BOOL)


def le(a: Term, b: Term) -> Term:
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
    return ite(le(lit(0, a.sort), a), a, neg(a))


def min_(a: Term, b: Term) -> Term:
    return ite(le(a, b), a, b)


def max_(a: Term, b: Term) -> Term:
    return ite(le(a, b), b, a)


# ---------------------------------------------------------------------------
# Traversal


def children(t: Term) -> tuple[Term, ...]:
    if isinstance(t, (App, Fn)):
        return t.args
    if isinstance(t, Quant):
        return (t.body,)
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
            bound.clear()
            bound.update(saved)
        else:
            for c in children(x):
                go(c)

    go(t)
    return out


def fns(t: Term) -> set[str]:
    return {x.name for x in iter_terms(t) if isinstance(x, Fn)}


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
    if isinstance(t, Quant):
        inner = {k: v for k, v in m.items() if k not in t.vars}
        body = substitute(t.body, inner)
        if body is t.body:
            return t
        return Quant(t.kind, t.vars, body, patterns=tuple(tuple(substitute(p, inner) for p in ps) for ps in t.patterns))
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
}


def rebuild(op: str, args: tuple[Term, ...], sort: Sort) -> Term:
    if op == "and":
        return and_(*args)
    if op == "or":
        return or_(*args)
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
    name = "seqsum" if elem == INT else "seqsum_r"
    a = Const("a", ARRAY(elem))
    lo = Const("lo", INT)
    hi = Const("hi", INT)
    rec = Fn(name, (a, lo, sub(hi, ONE)), elem)
    body = ite(le(hi, lo), lit(0, elem), add(rec, select(a, sub(hi, ONE))))
    return FunDef(name, (a, lo, hi), elem, body, recursive=True, measure=(sub(hi, lo),), doc="sum of a[lo:hi]")


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
    if isinstance(t, BoolV):
        return "true" if t.value else "false"
    if isinstance(t, StrV):
        return repr(t.value)
    if isinstance(t, Quant):
        vs = ", ".join(v.name for v in t.vars)
        s = f"{t.kind} {vs}. {show(t.body, 0)}"
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
    if isinstance(t, Quant):
        return f"({t.kind} ({' '.join(canonical(v) for v in t.vars)}) {canonical(t.body)})"
    if isinstance(t, Fn):
        return f"({t.name} {' '.join(canonical(a) for a in t.args)})"
    assert isinstance(t, App)
    return f"({t.op} {' '.join(canonical(a) for a in t.args)})"
