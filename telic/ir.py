"""The telic program IR.

Every frontend (Python, TypeScript, ...) lowers source code and its ``@``-comment
contracts into this small, language-neutral imperative language. Everything
downstream -- verification-condition generation, SMT, Lean export, mutation,
equivalence -- only ever sees this IR, so adding a language means writing one
lowering pass and nothing else.

The IR is deliberately tiny and explicit. Operators that differ between host
languages are *different operators* here (``floordiv`` is Python's ``//``,
``tmod`` is JavaScript's ``%``), so language semantics are never smuggled in
through shared names. Constructs a frontend cannot lower faithfully become
:class:`Unsupported` -- never an approximation.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from fractions import Fraction
from typing import Any, Union

# ---------------------------------------------------------------------------
# Types


@dataclass(frozen=True)
class TInt:
    def __str__(self) -> str:
        return "int"


@dataclass(frozen=True)
class TReal:
    def __str__(self) -> str:
        return "real"


@dataclass(frozen=True)
class TBool:
    def __str__(self) -> str:
        return "bool"


@dataclass(frozen=True)
class TStr:
    def __str__(self) -> str:
        return "str"


@dataclass(frozen=True)
class TNone:
    def __str__(self) -> str:
        return "none"


@dataclass(frozen=True)
class TList:
    elem: "Type"

    def __str__(self) -> str:
        return f"list[{self.elem}]"


@dataclass(frozen=True)
class TRecord:
    name: str
    fields: tuple[tuple[str, "Type"], ...]
    # a discriminated union: the tag field, and each tag value's fields (replay drops the rest)
    tag: str = field(default="", compare=False)
    variants: tuple[tuple[str, tuple[str, ...]], ...] = field(default=(), compare=False)

    def field_type(self, name: str) -> "Type | None":
        for fname, ftype in self.fields:
            if fname == name:
                return ftype
        return None

    def __str__(self) -> str:
        return self.name


@dataclass(frozen=True)
class TOption:
    """``Optional[T]`` / ``T | None`` / ``T | undefined``."""

    inner: "Type"

    def __str__(self) -> str:
        return f"{self.inner} | None"


@dataclass(frozen=True)
class TDict:
    """``dict[K, V]`` / ``Map<K, V>`` / ``Record<K, V>``: a finite map."""

    key: "Type"
    val: "Type"
    js: str = field(default="", compare=False)  # "map" | "object" in TypeScript (replay only)

    def __str__(self) -> str:
        return f"dict[{self.key}, {self.val}]"


@dataclass(frozen=True)
class TClass:
    """A reference to a mutable object of a user class (heap allocated;
    two references may point to the same object)."""

    name: str

    def __str__(self) -> str:
        return self.name


@dataclass(frozen=True)
class TOpaque:
    """A value telic knows nothing about (unannotated, ``Any``, a library
    type). It can be stored, passed and compared; every operation on it
    has an unconstrained result. Gradual verification: code around opaque
    values is still checked, and nothing is assumed about them."""

    why: str = ""

    def __eq__(self, other: object) -> bool:
        return isinstance(other, TOpaque)

    def __hash__(self) -> int:
        return hash("TOpaque")

    def __str__(self) -> str:
        return "opaque"


@dataclass(frozen=True)
class TEnum:
    """An ``Enum``: one of finitely many members, modelled by index."""

    name: str
    members: tuple[str, ...]
    values: tuple[object, ...] = ()  # literal member values, when known

    def __str__(self) -> str:
        return self.name


Type = Union[TInt, TReal, TBool, TStr, TNone, TList, TRecord, TOption, TDict, TClass, TOpaque, TEnum]


def reaches_object(t: Type) -> bool:
    """Can a value of type ``t`` lead to an object's fields?"""
    if isinstance(t, TClass):
        return True
    if isinstance(t, TList):
        return reaches_object(t.elem)
    if isinstance(t, TDict):
        return reaches_object(t.key) or reaches_object(t.val)
    if isinstance(t, TOption):
        return reaches_object(t.inner)
    if isinstance(t, TRecord):
        return any(reaches_object(ft) for _, ft in t.fields)
    return False

INT, REAL, BOOL, STR, NONE = TInt(), TReal(), TBool(), TStr(), TNone()

RESOURCE_MODELS = {
    "work": "executed source-lowered IR operations",
    "alloc": "abstract materialized cells (list elements, string units, dict entries, and objects)",
    "peak": "maximum live abstract cells allocated during this invocation (input and caller heap excluded)",
    "external_calls": "unchecked call sites executed",
}
RESOURCE_KEYS = {name: f"@telic.cost.{name}" for name in RESOURCE_MODELS}
RESOURCE_STATE_MODELS = ("work", "alloc", "peak", "external_calls")


def is_numeric(t: Type) -> bool:
    return isinstance(t, (TInt, TReal))


# ---------------------------------------------------------------------------
# Source locations


@dataclass(frozen=True)
class Loc:
    line: int
    col: int = 0
    end_col: int = 0

    def __str__(self) -> str:
        return str(self.line)


NOLOC = Loc(0)

# ---------------------------------------------------------------------------
# Expressions
#
# Every expression carries its static type (``ty``) as computed by the
# frontend, plus a source location for diagnostics.


@dataclass(frozen=True)
class Expr:
    ty: Type
    loc: Loc


@dataclass(frozen=True)
class Lit(Expr):
    value: Union[int, Fraction, bool, str, None]


@dataclass(frozen=True)
class Var(Expr):
    name: str


@dataclass(frozen=True)
class Result(Expr):
    """The return value, only meaningful inside an ``ensures`` clause."""


@dataclass(frozen=True)
class Old(Expr):
    """``old(e)``: ``e`` evaluated in the function's entry state."""

    expr: Expr


# Unary operators: neg, not
@dataclass(frozen=True)
class Unary(Expr):
    op: str
    arg: Expr


# Binary operators.
#   arithmetic: add sub mul
#   rdiv       true division producing a real (Python ``/``, JS ``/``)
#   floordiv   floor division on ints (Python ``//``)
#   fmod       modulo with the sign of the divisor (Python ``%``)
#   tmod       modulo with the sign of the dividend (JS ``%`` on integers)
#   comparisons: lt le gt ge eq ne
#   logic: and or implies   (short-circuiting: rhs evaluated only if needed)
@dataclass(frozen=True)
class Binary(Expr):
    op: str
    left: Expr
    right: Expr


@dataclass(frozen=True)
class Ite(Expr):
    cond: Expr
    then: Expr
    orelse: Expr


@dataclass(frozen=True)
class Call(Expr):
    """A call to a user function (resolved by name within the program)."""

    func: str
    args: tuple[Expr, ...]


# Builtins with fixed, language-specific meaning:
#   len(xs)  abs(x)  min(a, b, ...)  max(a, b, ...)  sum(xs)
#   to_real(i)          int -> real (Python ``float(i)``, implicit in JS)
#   floor(x) ceil(x)    real -> int
#   trunc(x)            real -> int, toward zero (Python ``int(x)``, ``Math.trunc``)
#   round_even(x)       real -> int, ties to even (Python ``round(x)``)
#   round_up(x)         real -> int, ties toward +inf (JS ``Math.round``)
#   is_int(x)           real -> bool (JS ``Number.isInteger``)
#   contains(xs, v)     ``v in xs`` / ``xs.includes(v)``
#   slice(xs, lo, hi)   Python/JS slice semantics (negative wrap + clamp);
#                       lo/hi may be ``Lit(None)`` for "omitted".
#   count(xs, v)        number of occurrences
#   some(x)             wrap a value as a present optional
#   is_none(o)          optional is absent (``o is None``)
#   unwrap(o)           the value of a present optional (obligation: not None)
#   dict_has(d, k)      ``k in d`` / ``m.has(k)``
#   dict_get_opt(d, k)  ``d.get(k)`` / ``m.get(k)``: an optional
#   dict_get_or(d, k, v)  ``d.get(k, v)``
#   dict_lit(k1, v1, ...) a fresh dict
@dataclass(frozen=True)
class Builtin(Expr):
    name: str
    args: tuple[Expr, ...]


@dataclass(frozen=True)
class Index(Expr):
    """``seq[idx]``. ``wrap`` enables Python's negative-index semantics."""

    seq: Expr
    idx: Expr
    wrap: bool


@dataclass(frozen=True)
class Field(Expr):
    obj: Expr
    name: str


@dataclass(frozen=True)
class Quant(Expr):
    """A bounded quantifier over integers ``idx`` in ``[lo, hi)``.

    If ``seq`` is given, ``elem`` is bound to ``seq[idx]`` inside ``body``;
    this is how ``all(p(x) for x in xs)`` and ``xs.every(x => p(x))`` lower.
    """

    kind: str  # "forall" | "exists"
    idx: str
    lo: Expr
    hi: Expr
    body: Expr
    elem: str | None = None
    seq: Expr | None = None


@dataclass(frozen=True)
class Extern(Expr):
    """A call into code telic does not check (a library, an unannotated
    module). Its result is unconstrained; mutable arguments may change;
    that it does not raise is a listed assumption."""

    name: str
    args: tuple[Expr, ...]


@dataclass(frozen=True)
class New(Expr):
    """``C(args)`` / ``new C(args)``: allocate a fresh object and run
    ``C.__init__`` on it."""

    cls: str
    args: tuple[Expr, ...]


@dataclass(frozen=True)
class ListLit(Expr):
    elems: tuple[Expr, ...]


@dataclass(frozen=True)
class RecordLit(Expr):
    fields: tuple[tuple[str, Expr], ...]


# ---------------------------------------------------------------------------
# Statements


@dataclass(frozen=True)
class Stmt:
    loc: Loc


@dataclass(frozen=True)
class Assign(Stmt):
    name: str
    value: Expr


@dataclass(frozen=True)
class IndexAssign(Stmt):
    name: str
    idx: Expr
    value: Expr
    wrap: bool


@dataclass(frozen=True)
class Append(Stmt):
    name: str
    value: Expr


@dataclass(frozen=True)
class FieldAssign(Stmt):
    """``obj.f = value`` on a class instance."""

    obj: Expr
    cls: str
    field: str
    value: Expr


@dataclass(frozen=True)
class DictDel(Stmt):
    name: str
    key: Expr
    strict: bool = True  # Python 'del d[k]' needs the key; JS 'm.delete(k)' does not


@dataclass(frozen=True)
class If(Stmt):
    cond: Expr
    then: tuple[Stmt, ...]
    orelse: tuple[Stmt, ...]


@dataclass(frozen=True)
class Clause:
    """One contract clause as written in a comment."""

    kind: str  # requires | ensures | invariant | assert | assume | decreases
    expr: Expr
    loc: Loc
    text: str
    aims: tuple[str, ...] = ()
    inferred: bool = False


@dataclass(frozen=True)
class While(Stmt):
    cond: Expr
    invariants: tuple[Clause, ...]
    decreases: Clause | None
    body: tuple[Stmt, ...]
    # Statements executed after the body and after ``continue`` (JS ``for``
    # update clauses). They are part of every iteration.
    step: tuple[Stmt, ...] = ()


@dataclass(frozen=True)
class ForRange(Stmt):
    """``for var in range(lo, hi)``. Invariants see ``var`` as the index of
    the *next* iteration, so it equals ``hi`` after the last one."""

    var: str
    lo: Expr
    hi: Expr
    invariants: tuple[Clause, ...]
    body: tuple[Stmt, ...]
    reeval: bool = False  # JS: the bound is re-evaluated every iteration


@dataclass(frozen=True)
class ForEach(Stmt):
    """``for elem in seq`` (optionally ``for idx, elem in enumerate(seq)``).

    ``idx`` names the iteration counter visible to invariants; like
    :class:`ForRange` it equals ``len(seq)`` after the loop.
    """

    elem: str
    idx: str
    seq: Expr
    invariants: tuple[Clause, ...]
    body: tuple[Stmt, ...]
    idx_visible: bool = False  # True if the source binds idx (enumerate)


@dataclass(frozen=True)
class Return(Stmt):
    value: Expr | None


@dataclass(frozen=True)
class Break(Stmt):
    pass


@dataclass(frozen=True)
class Continue(Stmt):
    pass


@dataclass(frozen=True)
class AssertStmt(Stmt):
    clause: Clause
    native: bool = False  # a language-level ``assert``, not an ``@assert``


@dataclass(frozen=True)
class AssumeStmt(Stmt):
    clause: Clause


@dataclass(frozen=True)
class Raise(Stmt):
    what: str
    caught: bool = False  # inside a try with handlers: jumps to a handler


@dataclass(frozen=True)
class Try(Stmt):
    """``try``/``except``/``else``/``finally``. A handler may start from any
    state the body could have reached (modelled by forgetting what the body
    changes); ``finally`` runs on the normal paths."""

    body: tuple[Stmt, ...]
    handlers: tuple[tuple[Stmt, ...], ...]
    orelse: tuple[Stmt, ...] = ()
    finalbody: tuple[Stmt, ...] = ()


@dataclass(frozen=True)
class ExprStmt(Stmt):
    expr: Expr


@dataclass(frozen=True)
class Unsupported(Stmt):
    reason: str


# ---------------------------------------------------------------------------
# Declarations


@dataclass(frozen=True)
class Param:
    name: str
    ty: Type


@dataclass
class Function:
    name: str
    loc: Loc
    end_line: int
    params: list[Param]
    ret: Type
    requires: list[Clause] = field(default_factory=list)
    ensures: list[Clause] = field(default_factory=list)
    decreases: Clause | None = None
    raises: list[Clause] = field(default_factory=list)  # "@raises cond"
    body: list[Stmt] = field(default_factory=list)
    aims: list[str] = field(default_factory=list)
    mirrors: list[tuple[str, Loc, tuple[str, ...]]] = field(default_factory=list)  # (target, where, aims its tag names)
    unsupported: list[tuple[str, Loc]] = field(default_factory=list)
    trusted: bool = False  # "@trusted": contract assumed, body not verified
    exported: bool = True
    is_async: bool = False  # a call it does not await runs (some of) it later
    source: str = ""  # exact source text of the function
    locals: dict[str, "Type"] = field(default_factory=dict)  # every variable's type
    # locals captured by closures that escape: any unchecked call may change them
    escaped: set[str] = field(default_factory=set)
    # code handed on as a value (a lambda, a closure, an event handler), as a
    # reader knows it: checked on its own, for every argument its type allows
    unit: str = ""
    rejects: bool = False  # a unit whose raise its runner turns into a value (a promise's rejection)

    @property
    def has_contract(self) -> bool:
        return bool(self.requires or self.ensures or self.raises)

    @property
    def declared_claims(self) -> list[Clause]:
        clauses = self.requires + self.ensures + self.raises + ([self.decreases] if self.decreases else [])
        for stmt in walk_stmts(self.body):
            if isinstance(stmt, AssertStmt) and not stmt.native:
                clauses.append(stmt.clause)
            if isinstance(stmt, (While, ForRange, ForEach)):
                clauses.extend(stmt.invariants)
            if isinstance(stmt, While) and stmt.decreases:
                clauses.append(stmt.decreases)
        return clauses


@dataclass(frozen=True)
class AimDecl:
    id: str
    text: str
    loc: Loc


@dataclass(frozen=True)
class Probe:
    """A step a lifecycle names, asked of every method: can any call take
    an object from before to after this way (``step``, over ``old(...)``),
    or create one this way (``created``, over the new object)?"""

    label: str
    step: Expr
    created: Expr | None = None


@dataclass(frozen=True)
class Lifecycle:
    """How an object may change from one call to the next (a history
    constraint): ``clause.expr`` relates the object before a call
    (``old(...)``) to after it. ``never`` lines are consequences of the
    others, proved once for the class; the rest are proved for every
    function that may change the object. ``code`` is the relation in the
    host language, for runtime checks."""

    kind: str  # graph | never | monotonic | once | step
    clause: Clause
    code: str
    probes: tuple[Probe, ...] = ()


@dataclass
class ClassDecl:
    """A mutable class: typed fields, invariants over ``self``, methods
    (lowered as functions named ``Class.method`` whose first parameter is
    ``self``), and a constructor ``Class.__init__``."""

    name: str
    fields: list[tuple[str, Type]]  # inherited fields first, as Python orders them
    invariants: list[Clause] = field(default_factory=list)  # its own; bases' apply too
    loc: Loc = NOLOC
    bases: list[str] = field(default_factory=list)  # checked base classes
    owner: dict[str, str] = field(default_factory=dict)  # field -> the class that introduced it
    lifecycles: list[Lifecycle] = field(default_factory=list)  # its own; bases' apply too

    def field_type(self, name: str) -> Type | None:
        for f, t in self.fields:
            if f == name:
                return t
        return None

    def field_owner(self, name: str) -> str:
        """The class a field belongs to: objects of a subclass keep inherited
        fields in the same place as the base class does."""
        return self.owner.get(name, self.name)


@dataclass
class CodeGraph:
    """Calls that may run code of this module although no ``Call`` names it:
    through a function value, a lambda, a nested function or a decorator's
    wrapper. A target is a function of the module, a unit (code telic does
    not check as a function), a name bound at module level (``bindings``),
    an imported name, or ``?``: any function whose value escaped."""

    units: dict[str, tuple[Loc, str, str]] = field(default_factory=dict)  # id -> (loc, label, source)
    calls: list[tuple[str, Loc, str, tuple[str, ...]]] = field(default_factory=list)  # (caller, loc, callee as written, targets)
    bindings: dict[str, tuple[str, ...]] = field(default_factory=dict)
    imports: dict[str, tuple[str, str]] = field(default_factory=dict)  # name -> (module path, name there)
    escaped: set[str] = field(default_factory=set)
    # calls that only schedule what they are given (addEventListener,
    # setTimeout, then): it runs later on a fresh stack, so these carry
    # effects but never recursion
    later: list[tuple[str, Loc, str, tuple[str, ...]]] = field(default_factory=list)
    # functions whose calls are unchecked (``@wrapper f``) but run the
    # function itself with the same arguments: generators, library decorators
    passthrough: set[str] = field(default_factory=set)
    # (callees, argument position ('^i' after a receiver), keyword or '*'
    # (any), targets): what a call passes, so a call through a parameter
    # runs only what its callers pass
    flows: list[tuple[tuple[str, ...], int | str, tuple[str, ...]]] = field(default_factory=list)


@dataclass
class Module:
    path: str  # as given on the command line / relative to project root
    language: str  # "python" | "typescript"
    source: str
    functions: dict[str, Function] = field(default_factory=dict)
    aims: list[AimDecl] = field(default_factory=list)
    records: dict[str, TRecord] = field(default_factory=dict)
    classes: dict[str, "ClassDecl"] = field(default_factory=dict)
    # local name -> (module path, name there): calls into other checked modules
    imports: dict[str, tuple[str, str]] = field(default_factory=dict)
    # loaded only for what other modules import from it (not checked this run)
    context: bool = False
    problems: list[tuple[str, Loc]] = field(default_factory=list)
    # what is deliberately not modelled (library subclasses, ...): reported quietly
    notes: list[tuple[str, Loc]] = field(default_factory=list)
    # Assumptions the language model makes, listed verbatim in reports.
    assumptions: list[str] = field(default_factory=list)
    # class name used here -> path of the checked module that defines it (imports)
    class_origin: dict[str, str] = field(default_factory=dict)
    # class name used here that several checked files define, and telic cannot tell which -> why
    ambiguous_classes: dict[str, str] = field(default_factory=dict)
    # (subclass, base as written, loc) for subclasses the frontend does not model
    opaque_subclasses: list[tuple[str, str, Loc]] = field(default_factory=list)
    code: CodeGraph = field(default_factory=CodeGraph)


def source_name(name: str) -> str:
    """A class or function name as the source spells it: ``Lowerer@rust.run``
    (a class qualified because another checked file has one of the same
    name) -> ``Lowerer.run``."""
    return re.sub(r"@\w+", "", name) if "@" in name else name


def sum_of(xs: Expr, loc: Loc) -> Builtin:
    """``sum(xs)``. A filtered comprehension is summed as a mapped one,
    ``sum(f(x) if c(x) else 0 for x in s)``: the same total, and each element
    is determined by its source element."""
    if isinstance(xs, Builtin) and xs.name == "comp" and len(xs.args) == 4 and isinstance(xs.ty, TList):
        seq, elem, body, cond = xs.args
        zero = Lit(body.ty, loc, Fraction(0) if isinstance(body.ty, TReal) else 0)
        xs = Builtin(xs.ty, xs.loc, "comp", (seq, elem, Ite(body.ty, body.loc, cond, body, zero)))
    assert isinstance(xs.ty, TList)
    return Builtin(xs.ty.elem, loc, "sum", (xs,))


def walk_stmts(stmts: Any):
    """Yield every statement in ``stmts`` recursively (pre-order)."""
    for s in stmts:
        yield s
        if isinstance(s, If):
            yield from walk_stmts(s.then)
            yield from walk_stmts(s.orelse)
        elif isinstance(s, While):
            yield from walk_stmts(s.body)
            yield from walk_stmts(s.step)
        elif isinstance(s, (ForRange, ForEach)):
            yield from walk_stmts(s.body)
        elif isinstance(s, Try):
            yield from walk_stmts(s.body)
            for h in s.handlers:
                yield from walk_stmts(h)
            yield from walk_stmts(s.orelse)
            yield from walk_stmts(s.finalbody)


def walk_expr(e: Expr):
    """Yield every sub-expression of ``e`` (pre-order)."""
    yield e
    if isinstance(e, Old):
        yield from walk_expr(e.expr)
    elif isinstance(e, Unary):
        yield from walk_expr(e.arg)
    elif isinstance(e, Binary):
        yield from walk_expr(e.left)
        yield from walk_expr(e.right)
    elif isinstance(e, Ite):
        yield from walk_expr(e.cond)
        yield from walk_expr(e.then)
        yield from walk_expr(e.orelse)
    elif isinstance(e, (Call, Builtin, New, Extern)):
        for a in e.args:
            yield from walk_expr(a)
    elif isinstance(e, Index):
        yield from walk_expr(e.seq)
        yield from walk_expr(e.idx)
    elif isinstance(e, Field):
        yield from walk_expr(e.obj)
    elif isinstance(e, Quant):
        yield from walk_expr(e.lo)
        yield from walk_expr(e.hi)
        if e.seq is not None:
            yield from walk_expr(e.seq)
        yield from walk_expr(e.body)
    elif isinstance(e, ListLit):
        for a in e.elems:
            yield from walk_expr(a)
    elif isinstance(e, RecordLit):
        for _, a in e.fields:
            yield from walk_expr(a)


def stmt_exprs(s: Stmt):
    """Top-level expressions directly owned by a statement."""
    if isinstance(s, Assign):
        yield s.value
    elif isinstance(s, IndexAssign):
        yield s.idx
        yield s.value
    elif isinstance(s, Append):
        yield s.value
    elif isinstance(s, If):
        yield s.cond
    elif isinstance(s, While):
        yield s.cond
    elif isinstance(s, ForRange):
        yield s.lo
        yield s.hi
    elif isinstance(s, ForEach):
        yield s.seq
    elif isinstance(s, Return) and s.value is not None:
        yield s.value
    elif isinstance(s, ExprStmt):
        yield s.expr
    elif isinstance(s, FieldAssign):
        yield s.obj
        yield s.value
    elif isinstance(s, DictDel):
        yield s.key
    elif isinstance(s, AssertStmt) and s.native:
        yield s.clause.expr  # a native assert executes, effects included


def assigned_names(stmts: Any) -> set[str]:
    """Variables (re)bound or mutated anywhere in ``stmts``."""
    out: set[str] = set()
    for s in walk_stmts(stmts):
        if isinstance(s, (Assign, IndexAssign, Append, DictDel)):
            out.add(s.name)
        elif isinstance(s, ForRange):
            out.add(s.var)
        elif isinstance(s, ForEach):
            out.add(s.elem)
            out.add(s.idx)
    return out
