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

    def field_type(self, name: str) -> "Type | None":
        for fname, ftype in self.fields:
            if fname == name:
                return ftype
        return None

    def __str__(self) -> str:
        return self.name


Type = Union[TInt, TReal, TBool, TStr, TNone, TList, TRecord]

INT, REAL, BOOL, STR, NONE = TInt(), TReal(), TBool(), TStr(), TNone()


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
    intents: tuple[str, ...] = ()
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
    intents: list[str] = field(default_factory=list)
    mirrors: list[tuple[str, Loc]] = field(default_factory=list)
    unsupported: list[tuple[str, Loc]] = field(default_factory=list)
    trusted: bool = False  # "@trusted": contract assumed, body not verified
    exported: bool = True
    source: str = ""  # exact source text of the function
    locals: dict[str, "Type"] = field(default_factory=dict)  # every variable's type

    @property
    def has_contract(self) -> bool:
        return bool(self.requires or self.ensures or self.raises)


@dataclass(frozen=True)
class IntentDecl:
    id: str
    text: str
    loc: Loc


@dataclass
class Module:
    path: str  # as given on the command line / relative to project root
    language: str  # "python" | "typescript"
    source: str
    functions: dict[str, Function] = field(default_factory=dict)
    intents: list[IntentDecl] = field(default_factory=list)
    records: dict[str, TRecord] = field(default_factory=dict)
    problems: list[tuple[str, Loc]] = field(default_factory=list)
    # Assumptions the language model makes, listed verbatim in reports.
    assumptions: list[str] = field(default_factory=list)


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
    elif isinstance(e, (Call, Builtin)):
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
    elif isinstance(s, AssertStmt) and s.native:
        yield s.clause.expr  # a native assert executes, effects included


def assigned_names(stmts: Any) -> set[str]:
    """Variables (re)bound or mutated anywhere in ``stmts``."""
    out: set[str] = set()
    for s in walk_stmts(stmts):
        if isinstance(s, (Assign, IndexAssign, Append)):
            out.add(s.name)
        elif isinstance(s, ForRange):
            out.add(s.var)
        elif isinstance(s, ForEach):
            out.add(s.elem)
            out.add(s.idx)
    return out
