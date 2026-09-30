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
from .program import FuncRef, Program, in_place, reaches_unchecked, unchecked_constructor

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


@dataclass(frozen=True)
class OptVal:
    """An optional: present iff ``some``; ``val`` is meaningful only then."""

    some: L.Term
    val: L.Term
    ty: ir.TOption


@dataclass(frozen=True)
class DictVal:
    """A finite map: ``has[k]`` says whether ``k`` is a key, ``vals[k]`` its value."""

    vals: L.Term
    has: L.Term
    ty: ir.TDict


@dataclass(frozen=True)
class ObjVal:
    """How an object input is shown in a counterexample: its reference and
    its field values at entry (only used for decoding models)."""

    ref: L.Term
    cls: str
    fields: tuple[tuple[str, "Val"], ...] | None  # None: beyond the shown depth


@dataclass(frozen=True)
class TypedView:
    """A counterexample input whose type decoding needs (enums, lists of
    objects); only used for decoding models."""

    val: "Val"
    ty: ir.Type
    # for a list or dict of objects: each field of theirs, with the heap arrays holding it
    fields: tuple[tuple[str, ir.Type, tuple[L.Term, ...]], ...] = ()


Val = Union[L.Term, ListVal, OptVal, DictVal]
NONE_V = L.Const("None", L.Sort("None"))
# the objects of a class a function has written a field of (a ghost set, not heap:
# callees and other tasks do not add to it)
WRITTEN = "%written."
NO_WRITES = L.const_array(L.ARRAY(L.BOOL), L.FALSE)
ANY_WRITES = L.const_array(L.ARRAY(L.BOOL), L.TRUE)
# the heap when this run of the function last resumed (entry, or the latest
# await or yield): lifecycles bind each stretch that runs without suspending
SEGMENT = "%segment"


def suspends(e: ir.Expr) -> bool:
    return (isinstance(e, ir.Builtin) and e.name == "await") or (isinstance(e, ir.Extern) and e.name == "yield")


def components(ty: ir.Type) -> list[tuple[str, L.Sort]]:
    """How a value of ``ty`` is represented in logic, as named components."""
    if isinstance(ty, ir.TList):
        return [("arr", L.ARRAY(sort_of(ty.elem))), ("off", L.INT), ("len", L.INT)]
    if isinstance(ty, ir.TOption):
        if isinstance(ty.inner, (ir.TList, ir.TDict, ir.TOption)):
            raise VCError(f"optional {ty.inner} is not supported yet")
        return [("some", L.BOOL), ("val", sort_of(ty.inner))]
    if isinstance(ty, ir.TDict):
        if isinstance(ty.val, (ir.TList, ir.TDict, ir.TOption)):
            raise VCError(f"dict values of type {ty.val} are not supported yet")
        k = sort_of(ty.key)
        return [("vals", L.ARRAY(sort_of(ty.val), k)), ("has", L.ARRAY(L.BOOL, k))]
    return [("", sort_of(ty))]


def arity(ty: ir.Type) -> int:
    """How many logical components a value of ``ty`` has."""
    if isinstance(ty, ir.TList):
        return 3
    if isinstance(ty, (ir.TOption, ir.TDict)):
        return 2
    return 1


def pack(ty: ir.Type, comps: list[L.Term]) -> Val:
    #@ requires len(comps) == arity(ty)
    if isinstance(ty, ir.TList):
        return ListVal(comps[0], comps[1], comps[2], ty)
    if isinstance(ty, ir.TOption):
        return OptVal(comps[0], comps[1], ty)
    if isinstance(ty, ir.TDict):
        return DictVal(comps[0], comps[1], ty)
    return comps[0]


def val_type(v: Val) -> ir.Type | None:
    return v.ty if isinstance(v, (ListVal, OptVal, DictVal)) else None


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
        return L.REC(ty.name, tuple((n, field_sort(t)) for n, t in ty.fields))
    if isinstance(ty, ir.TList):
        return L.ARRAY(sort_of(ty.elem))
    if isinstance(ty, ir.TClass):
        return L.INT  # an object reference
    if isinstance(ty, ir.TOpaque):
        return L.OPAQUE
    if isinstance(ty, ir.TEnum):
        return L.INT  # member index
    raise VCError(f"no single logical sort for {ty}")


def field_sort(ty: ir.Type) -> L.Sort:
    """A record field's sort: an optional field is a small (present, value)
    record of its own."""
    if isinstance(ty, ir.TOption):
        inner = sort_of(ty.inner)
        return L.REC(f"Opt_{_sort_tag(inner)}", (("some", L.BOOL), ("val", inner)))
    return sort_of(ty)


def _sort_tag(s: L.Sort) -> str:
    if s.name == "Rec":
        return str(s.rec)
    if s.name == "Array":
        return f"Arr{_sort_tag(s.elem)}"  # type: ignore[arg-type]
    return s.name


def flatten(v: Val) -> tuple[L.Term, ...]:
    if isinstance(v, ListVal):
        return (v.arr, v.off, v.len)
    if isinstance(v, OptVal):
        return (v.some, v.val)
    if isinstance(v, DictVal):
        return (v.vals, v.has)
    return (v,)


def ite_val(c: L.Term, a: Val, b: Val) -> Val:
    ty = val_type(a)
    if ty is not None:
        return pack(ty, [L.ite(c, x, y) for x, y in zip(flatten(a), flatten(b))])
    return L.ite(c, a, b)  # type: ignore[arg-type]


def rec_equal(a: L.Term, b: L.Term) -> L.Term:
    """Equality as the language sees it: an absent optional field equals
    another absent one, whatever junk its value slot holds."""
    s = a.sort
    if s.name != "Rec":
        return L.eq(a, b)
    if str(s.rec).startswith("Opt_"):
        sa, sb = L.field(a, "some"), L.field(b, "some")
        return L.and_(L.eq(sa, sb), L.implies(sa, rec_equal(L.field(a, "val"), L.field(b, "val"))))
    return L.and_(*[rec_equal(L.field(a, n), L.field(b, n)) for n, _ in s.fields])


def default_term(s: L.Sort) -> L.Term:
    if s == L.INT:
        return L.ZERO
    if s == L.REAL:
        return L.RealV(Fraction(0))
    if s == L.BOOL:
        return L.FALSE
    if s == L.STR:
        return L.StrV("")
    if s.name == "Array":
        assert s.elem is not None
        return L.const_array(s, default_term(s.elem))
    if s.name == "Rec":
        return L.mkrec(s, tuple(default_term(fs) for _, fs in s.fields))
    if s == L.OPAQUE:
        return L.Const("opaque!default", L.OPAQUE)
    raise VCError(f"no default value for {s}")


def coerce(v: Val, ty: ir.Type | None) -> Val:
    """Lift a plain value into an optional slot (``None`` -> absent, ``x`` ->
    present ``x``). Frontends need not insert the wrapping themselves. An
    empty literal (``[]``, ``{}``) takes the type of the variable it is
    stored in."""
    if isinstance(v, ListVal) and v.ty.elem == ir.NONE and isinstance(ty, ir.TList) and ty.elem != ir.NONE:
        return ListVal(L.const_array(sort_of(ty), default_term(sort_of(ty.elem))), L.ZERO, v.len, ty)
    if isinstance(v, DictVal) and v.ty.key == ir.NONE and isinstance(ty, ir.TDict) and ty.key != ir.NONE:
        ks, vs = sort_of(ty.key), sort_of(ty.val)
        return DictVal(L.const_array(L.ARRAY(vs, ks), default_term(vs)), L.const_array(L.ARRAY(L.BOOL, ks), L.FALSE), ty)
    if isinstance(ty, ir.TOption) and not isinstance(v, OptVal):
        if v is NONE_V:
            return OptVal(L.FALSE, default_term(sort_of(ty.inner)), ty)
        return OptVal(L.TRUE, v, ty)  # type: ignore[arg-type]
    return v


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
    aims: tuple[str, ...] = ()
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
    binders: tuple[L.Const, ...] = ()  # enclosing quantifier variables

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
            binders=self.binders,
        )
        for k, v in kw.items():
            setattr(c, k, v)
        return c

    def hyps(self) -> list[L.Term]:
        return list(self.base) + list(self.guard)

    def assume(self, t: L.Term) -> None:
        self.base.append(L.implies(L.and_(*self.guard), t) if self.guard else t)

    def assume_for_all_binders(self, t: L.Term) -> None:
        """Assume ``t`` for every value of the enclosing quantifier
        variables. Sound only when every fresh symbol in ``t`` is a
        function of them."""
        self.base.append(L.forall(self.binders, L.implies(L.and_(*self.guard), t)))


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
        # lines of the field writes to each class with an invariant
        self.written: dict[str, list[int]] = {}
        self._self_escapes: bool | None = None
        self.loop_notes: list[tuple[int, str]] = []
        # Facts valid in every state: one-level unfoldings of trusted
        # predicates and what boxing a value tells about it. Every
        # obligation assumes them.
        self.lemmas: list[L.Term] = []
        self.unfolded: set[L.Term] = set()
        self.lemma_set: set[L.Term] = set()
        self.lemma_info: list[tuple[L.Term, tuple[L.Term, ...], frozenset[str] | None, str | None]] = []
        self.unfolding_stack: list[str] = []
        self.fuel = PREDICATE_FUEL
        self.probes_contract = False
        # objects this call allocated, and the states lifecycle coverage asks
        # about: (facts, path condition, object, class, env, created)
        self.created: set = set()
        self.lc_written: list[str] = []  # classes of the non-parameter objects it writes a field of
        self.lc_sites: list[tuple[list[L.Term], L.Term, L.Term, str, dict[str, Val], bool]] = []
        self._shared: set[str] | None = None

    # -- naming -----------------------------------------------------------

    def fresh(self, base: str, ty: ir.Type, len_: L.Term | None = None) -> Val:
        n = next(self.counter)
        if isinstance(ty, ir.TList):
            arr = L.Const(f"{base}@{n}.arr", sort_of(ty))
            ln = len_ if len_ is not None else L.Const(f"{base}@{n}.len", L.INT)
            return ListVal(arr, L.ZERO, ln, ty)
        comps = components(ty)
        if len(comps) == 1:
            return L.Const(f"{base}@{n}", comps[0][1])
        return pack(ty, [L.Const(f"{base}@{n}.{suffix}", srt) for suffix, srt in comps])

    def param_val(self, name: str, ty: ir.Type) -> Val:
        if isinstance(ty, ir.TList):
            return ListVal(L.Const(f"{name}.arr", sort_of(ty)), L.ZERO, L.Const(f"{name}.len", L.INT), ty)
        comps = components(ty)
        if len(comps) == 1:
            return L.Const(name, comps[0][1])
        return pack(ty, [L.Const(f"{name}.{suffix}", srt) for suffix, srt in comps])

    # -- the heap -----------------------------------------------------------
    # Objects are integer references. Each field of each class is a map from
    # references to values (one map per logical component of the field's
    # type), kept in the environment under '@Class.field[.component]'. Two
    # references to the same object read and write the same map entries, so
    # aliasing needs no special treatment (Burstall-Bornat).

    def heap_keys(self, cls: str, fname: str, strict: bool = False) -> list[tuple[str, L.Sort]]:
        """The maps holding ``cls.fname``. A field telic cannot model has
        none: only functions that read or write it (``strict``) fail."""
        decl = self.program.classes.get(cls)
        if decl is None:
            raise VCError(f"class {cls} is not modelled")
        fty = decl.field_type(fname)
        if fty is None:
            raise VCError(f"{cls} has no field '{fname}'")
        owner = decl.field_owner(fname)
        try:
            comps = components(fty)
        except VCError:
            if strict:
                raise
            return []
        return [(f"@{owner}.{fname}" + (f".{suffix}" if suffix else ""), L.ARRAY(srt)) for suffix, srt in comps]

    def heap_init(self, env: dict[str, Val]) -> None:
        for cname, decl in self.program.classes.items():
            for fname, _ in decl.fields:
                for key, srt in self.heap_keys(cname, fname):
                    env.setdefault(key, L.Const(key[1:], srt))
        env.setdefault("@alloc", L.Const("alloc", L.ARRAY(L.BOOL)))

    def has_invariants(self, cls: str) -> bool:
        return any(self.program.classes[c].invariants for c in self.program.mro(cls))

    def written_claims(self, cls: str, env: dict[str, Val], base: list[L.Term]) -> list[tuple[ir.Clause, L.Term]]:
        """Every object of ``cls`` this function wrote a field of, other than
        the parameters (checked on their own), satisfies each invariant."""
        w = env[WRITTEN + cls]
        r = L.Const(f"r!{next(self.counter)}", L.INT)
        others = [L.not_(L.eq(r, p)) for p in self.checked_params(cls)]
        held = L.and_(L.select(w, r), *others)  # type: ignore[arg-type]
        # (a trigger only where the set is a havocked constant: in a goal it is not needed)
        pats = ((L.select(w, r),),) if isinstance(w, L.Const) else ()  # type: ignore[arg-type]
        return [(inv, L.Quant("forall", (r,), L.implies(held, t), patterns=pats)) for inv, t in self.class_invariants(cls, r, env, base)]

    def checked_params(self, cls: str) -> list[L.Term]:
        """Parameters whose own return check covers every invariant of ``cls``."""
        return [self.entry[p.name] for p in self.fn.params if isinstance(p.ty, ir.TClass) and cls in self.program.mro(p.ty.name)]  # type: ignore[misc]

    def written_in(self, names: set[str]) -> list[str]:
        return [c for c in self.program.classes if WRITTEN + c in names]

    def check_written(self, classes: list[str], st: State, site: ir.Loc, entry: bool) -> None:
        """Objects a loop writes keep their invariants from one iteration to
        the next: the loop's exit state is a havocked head, so the
        conditions under which a write happened no longer describe it."""
        for cls in classes:
            if entry and st.env[WRITTEN + cls] is NO_WRITES:
                continue
            when = "when the loop starts" if entry else "after each iteration"
            ctx = Ctx(base=st.facts, env=st.env, module=self.module, spec=True)
            for inv, t in self.written_claims(cls, st.env, st.facts):
                self.oblige("class.inv", ctx, t, inv.loc, f"invariant of {cls} ('{inv.text}') holds {when} for every object written so far", site=site, clause=inv)

    def assume_written(self, classes: list[str], st: State) -> None:
        for cls in classes:
            st.facts.extend(t for _, t in self.written_claims(cls, st.env, st.facts))
            # (an object written so far exists: calls and allocations leave it alone unless they may write it)
            w, r = st.env[WRITTEN + cls], L.Const(f"r!{next(self.counter)}", L.INT)
            st.facts.append(L.Quant("forall", (r,), L.implies(L.select(w, r), L.select(st.env["@alloc"], r)), patterns=((L.select(w, r),),)))  # type: ignore[arg-type]

    def check_objects(self, st: State, site: ir.Loc, when: str, guard: tuple[L.Term, ...] = ()) -> None:
        """The objects this function was passed, and every other object it
        wrote a field of, satisfy their invariants ``when`` control leaves it:
        on return, on raise, while it is suspended (other tasks, or a
        generator's consumer, run then), and at a call that can reach objects
        (the callee assumes the invariants of objects it reads out of lists
        and dicts)."""
        ctx = Ctx(base=st.facts, env=st.env, module=self.module, guard=guard, spec=True)
        calling = when.startswith("when calling")
        for p in self.fn.params:
            if calling and self.is_init and p.name == "self" and not self.self_escapes:
                continue  # (the object being built: nothing else can reach it yet)
            if isinstance(p.ty, ir.TClass):
                for inv, t in self.class_invariants(p.ty.name, self.entry[p.name], st.env, st.facts):  # type: ignore[arg-type]
                    self.oblige("class.inv", ctx, t, inv.loc, f"invariant of {p.ty.name} ('{inv.text}') holds for '{p.name}' {when}", site=site, clause=inv)
        for cls in self.program.classes:
            if st.env.get(WRITTEN + cls, NO_WRITES) is NO_WRITES:
                continue  # (not written on the paths that reach here)
            at = ", ".join(str(n) for n in sorted(set(self.written.get(cls, []))))
            what = f"every object written at line {at}" if at else "every object written so far"
            for inv, t in self.written_claims(cls, st.env, st.facts):
                self.oblige("class.inv", ctx, t, inv.loc, f"invariant of {cls} ('{inv.text}') holds {when} for {what}", site=site, clause=inv)

    @property
    def self_escapes(self) -> bool:
        """Can code other than this initializer reach the object it builds?"""
        if self._self_escapes is None:
            self._self_escapes = False
            for s in ir.walk_stmts(self.fn.body):
                for e in ir.stmt_exprs(s):
                    if isinstance(s, ir.FieldAssign) and e is s.obj:
                        continue
                    subs = list(ir.walk_expr(e))
                    selfs = sum(1 for x in subs if isinstance(x, ir.Var) and x.name == "self")
                    through = sum(1 for x in subs if isinstance(x, ir.Field) and isinstance(x.obj, ir.Var) and x.obj.name == "self")
                    base_init = sum(1 for x in subs if isinstance(x, ir.Call) and x.func.endswith("__init__") and x.args and isinstance(x.args[0], ir.Var) and x.args[0].name == "self")
                    if selfs > through + base_init:
                        self._self_escapes = True
        return self._self_escapes

    def held_skip(self, cls: str) -> set[tuple[str, int]]:
        """Invariants of ``cls`` (or its bases) that read a field an ancestor
        introduced: code typed as the ancestor may break them unchecked."""
        out = set()
        for c in self.program.mro(cls):
            decl = self.program.classes[c]
            for i, inv in enumerate(decl.invariants):
                read = {x.name for x in ir.walk_expr(inv.expr) if isinstance(x, ir.Field) and isinstance(x.obj, ir.Var) and x.obj.name == "self"}
                if any(decl.field_owner(f) != c for f in read):
                    out.add((c, i))
        return out

    def assume_held(self, v: Val, ty: ir.Type, ctx: Ctx) -> None:
        """An object read out of a list or dict satisfies its class invariants
        unless this function was passed it or wrote it: every other object
        was checked when last written, and callers check theirs at calls."""
        if ctx.state is None or ctx.spec or not isinstance(ty, ir.TClass) or not self.has_invariants(ty.name) or not isinstance(v, L.Term):
            return
        env = ctx.state.env
        ts = [t for _, t in self.class_invariants(ty.name, v, env, ctx.base, self.held_skip(ty.name))]
        if not ts:
            return
        exempt = [L.select(w, v) for k, w in env.items() if k.startswith(WRITTEN) and w is not NO_WRITES]  # type: ignore[arg-type]
        exempt += [L.eq(v, self.entry[p.name]) for p in self.fn.params if isinstance(p.ty, ir.TClass)]  # type: ignore[arg-type]
        ctx.assume(L.implies(L.not_(L.or_(*exempt)), L.and_(*ts)) if exempt else L.and_(*ts))

    def heap_read(self, env: dict[str, Val], cls: str, fname: str, ref: L.Term) -> Val:
        keys = self.heap_keys(cls, fname, strict=True)
        fty = self.program.classes[cls].field_type(fname)
        assert fty is not None
        return pack(fty, [L.select(env[k], ref) for k, _ in keys])  # type: ignore[arg-type]

    def heap_write(self, env: dict[str, Val], cls: str, fname: str, ref: L.Term, v: Val) -> None:
        for (k, _), comp in zip(self.heap_keys(cls, fname, strict=True), flatten(v)):
            env[k] = L.store(env[k], ref, comp)  # type: ignore[arg-type]

    def heap_env(self, env: dict[str, Val]) -> dict[str, Val]:
        return {k: v for k, v in env.items() if k.startswith("@")}

    def class_invariants(self, cls: str, ref: L.Term, env: dict[str, Val], ctx_base: list[L.Term], skip: set[tuple[str, int]] = set()) -> list[tuple[ir.Clause, L.Term]]:  # noqa: B006
        e = dict(self.heap_env(env))
        e["self"] = ref
        out = []
        for c in self.program.mro(cls):  # a subclass keeps its bases' invariants
            decl = self.program.classes[c]
            ctx = Ctx(base=ctx_base, env=e, module=self.program.class_module[c], spec=True, quiet=True)
            out += [(inv, self.ev(inv.expr, ctx)) for i, inv in enumerate(decl.invariants) if (c, i) not in skip]
        return out

    def class_lifecycles(self, cls: str, ref: L.Term, pre: dict[str, Val], post: dict[str, Val], ctx_base: list[L.Term]) -> list[tuple[ir.Lifecycle, L.Term]]:
        """Each lifecycle of ``cls`` as a relation between the object ``ref``
        in heap ``pre`` and in heap ``post``."""
        out = []
        typed = L.and_(*self.enum_facts(cls, ref, pre), *self.enum_facts(cls, ref, post))
        for owner, lc in self.program.lifecycles_for(cls):
            out.append((lc, L.implies(typed, self.two_state(lc.clause.expr, owner, ref, pre, post, ctx_base))))
        return out

    def enum_facts(self, cls: str, ref: L.Term, env: dict[str, Val]) -> list[L.Term]:
        """An enum field of an object holds one of its members."""
        out: list[L.Term] = []
        for fname, fty in self.program.classes[cls].fields:
            if (isinstance(fty, ir.TEnum) or (isinstance(fty, ir.TOption) and isinstance(fty.inner, ir.TEnum))) and self.heap_keys(cls, fname):
                out += self.alloc_facts(self.heap_read(env, cls, fname, ref), fty, env)
        return out

    def two_state(self, e: ir.Expr, owner: str, ref: L.Term, pre: dict[str, Val] | None, post: dict[str, Val], ctx_base: list[L.Term]) -> L.Term:
        """A class-scope spec over ``self`` (``old(...)`` reads ``pre``)."""
        old_env = {**self.heap_env(pre), "self": ref} if pre is not None else None
        ctx = Ctx(base=ctx_base, env={**self.heap_env(post), "self": ref}, module=self.program.class_module[owner], old_env=old_env, spec=True, quiet=True)
        return self.ev(e, ctx)  # type: ignore[return-value]

    @property
    def fresh_self(self) -> bool:
        """Is ``self`` an object this call is building?"""
        return self.fn.name.endswith((".__init__", ".__post_init__"))

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
                hyps=ctx.hyps() + self.relevant_lemmas(ctx.hyps() + [goal]),
                goal=goal,
                clause=clause,
                aims=clause.aims if clause else (),
                inputs=list(self.inputs),
                deps=set(self.deps),
                exclude_axioms=excl,
                inferred=inferred or (clause.inferred if clause else False),
            )
        )

    # -- entry point ------------------------------------------------------

    def run(self) -> list[Obligation]:
        fn = self.fn
        st = self.enter()
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
        self.ran = True
        return self.obligations

    def enter(self) -> State:
        """The entry state: inputs, the invariants of objects passed in, and
        the preconditions. ``invariant_facts`` (empty when no invariant is
        assumed) and ``entry_facts`` record what was assumed at each step."""
        fn = self.fn
        env: dict[str, Val] = {}
        facts: list[L.Term] = []
        self.heap_init(env)
        for cname in self.program.classes:
            if self.has_invariants(cname):
                env[WRITTEN + cname] = NO_WRITES
        for p in fn.params:
            v = self.input_override.get(p.name) or self.param_val(p.name, p.ty)
            env[p.name] = v
            self.inputs.append((p.name, self.input_view(v, p.ty, env, 2)))
            if isinstance(v, ListVal):
                facts.append(L.le(L.ZERO, v.len))
            facts.extend(self.alloc_facts(v, p.ty, env))
        self.entry = dict(env)
        if any(suspends(x) for st_ in ir.walk_stmts(fn.body) for e in ir.stmt_exprs(st_) for x in ir.walk_expr(e)):
            self.resume(env)
        st = State(env, facts)
        # Callers establish the invariants of the objects they pass in (a
        # constructor's own 'self' is still being built).
        n0 = len(st.facts)
        for p in fn.params:
            if isinstance(p.ty, ir.TClass) and not (self.is_init and p.name == "self"):
                skip = self.program.untrusted.get(self.ref.key, set()) if p.name == "self" else set()
                for _, t in self.class_invariants(p.ty.name, env[p.name], env, st.facts, skip):  # type: ignore[arg-type]
                    st.facts.append(t)
        self.invariant_facts = list(st.facts) if len(st.facts) > n0 else []
        ctx = self.ctx(st, spec=True)
        for r in fn.requires:
            # Preconditions must be well-defined given the earlier ones.
            t = self.ev(r.expr, ctx.sub(label="requires"))
            st.facts.append(t)
        self.entry_facts = list(st.facts) + self.relevant_lemmas(st.facts)
        return st

    def contract_probe(self) -> None:
        """For a trusted function: ``entry_facts`` become its preconditions
        and postconditions together, which must be satisfiable for what it
        promises to be assumable."""
        st = self.enter()
        fn = self.fn
        ctx = self.ctx(st, spec=True, quiet=True)
        if self.ref.key in self.program.predicates:
            # deep enough to go once round a cycle of predicates defined through
            # each other; deeper contradictions are caught where a proof unfolds them
            group = [k for k in self.program.predicates if k == self.ref.key or self.program.same_scc(self.ref.key, k)]
            self.fuel = min(len(group), 3) + 1
            flat = [t for p in fn.params for t in flatten(st.env[p.name])]
            r: Val = L.Fn(self.program.logic_names[self.ref.key], tuple(flat), sort_of(fn.ret))
            self.unfold(self.ref, {p.name: st.env[p.name] for p in fn.params}, r, ctx, fn.loc)  # type: ignore[arg-type]
        else:
            r = self.fresh("result", fn.ret) if fn.ret != ir.NONE else NONE_V
            ectx = Ctx(base=st.facts, env=st.env, module=self.module, old_env=dict(self.entry), result=None if r is NONE_V else r, spec=True, quiet=True)
            for en in fn.ensures:
                st.facts.append(self.ev(en.expr, ectx))
        self.entry_facts = list(st.facts) + self.lemmas  # every unfolding: the fuel set above is the bound
        self.probes_contract = True

    def entry_inputs(self) -> list[tuple[str, Val]]:
        """The inputs as counterexamples show them (what ``run`` records)."""
        env: dict[str, Val] = {}
        self.heap_init(env)
        for p in self.fn.params:
            v = self.input_override.get(p.name) or self.param_val(p.name, p.ty)
            env[p.name] = v
            self.inputs.append((p.name, self.input_view(v, p.ty, env, 2)))
        return self.inputs

    def ctx(self, st: State, **kw) -> Ctx:
        c = Ctx(base=st.facts, env=st.env, module=self.module, state=st)
        for k, v in kw.items():
            setattr(c, k, v)
        return c

    def input_view(self, v: Val, ty: ir.Type, env: dict[str, Val], depth: int):
        if isinstance(ty, ir.TClass) and depth <= 0:
            return ObjVal(v, ty.name, None)  # type: ignore[arg-type]
        if isinstance(ty, ir.TClass) and not (self.is_init and not self.inputs):
            decl = self.program.classes[ty.name]
            fs = tuple((f, self.input_view(self.heap_read(env, ty.name, f, v), fty, env, depth - 1)) for f, fty in decl.fields if self.heap_keys(ty.name, f))  # type: ignore[arg-type]
            return ObjVal(v, ty.name, fs)  # type: ignore[arg-type]
        if isinstance(ty, ir.TOption) and isinstance(ty.inner, (ir.TClass, ir.TEnum)) and isinstance(v, OptVal):
            return OptVal(v.some, self.input_view(v.val, ty.inner, env, depth), ty)  # type: ignore[arg-type]
        elem = ty.elem if isinstance(ty, ir.TList) else ty.val if isinstance(ty, ir.TDict) else None
        if isinstance(elem, ir.TClass) and elem.name in self.program.classes:
            decl = self.program.classes[elem.name]
            fs = tuple((f, fty, tuple(env[k] for k, _ in self.heap_keys(elem.name, f))) for f, fty in decl.fields if self.heap_keys(elem.name, f))
            return TypedView(v, ty, fs)  # type: ignore[arg-type]
        if isinstance(ty, (ir.TEnum, ir.TRecord)) or (isinstance(ty, ir.TList) and isinstance(ty.elem, (ir.TClass, ir.TEnum, ir.TRecord))):
            return TypedView(v, ty)
        return v

    @property
    def is_init(self) -> bool:
        return self.fn.name.endswith(".__init__")

    def alloc_facts(self, v: Val, ty: ir.Type, env: dict[str, Val]) -> list[L.Term]:
        #@ requires "@alloc" in env
        """Objects handed to a function already exist."""
        if isinstance(ty, ir.TEnum) and isinstance(v, L.Term):
            return [L.le(L.ZERO, v), L.lt(v, L.IntV(len(ty.members)))]
        if isinstance(ty, ir.TRecord) and isinstance(v, L.Term):
            # an enum field of a record (a union's tag) is one of its members
            return [f for n, t in ty.fields if isinstance(t, (ir.TEnum, ir.TRecord)) for f in self.alloc_facts(L.field(v, n), t, env)]
        if isinstance(ty, ir.TOption) and isinstance(ty.inner, ir.TEnum) and isinstance(v, OptVal):
            return [L.implies(v.some, L.and_(L.le(L.ZERO, v.val), L.lt(v.val, L.IntV(len(ty.inner.members)))))]
        alloc = env["@alloc"]
        if isinstance(ty, ir.TClass) and not (self.is_init and v == self.entry.get("self", None)):
            return [L.select(alloc, v)]  # type: ignore[arg-type]
        if isinstance(ty, ir.TOption) and isinstance(ty.inner, ir.TClass) and isinstance(v, OptVal):
            return [L.implies(v.some, L.select(alloc, v.val))]  # type: ignore[arg-type]
        return []

    def post_env(self, exit_env: dict[str, Val]) -> dict[str, Val]:
        """What a caller can observe: scalar parameters keep their entry
        values; list parameters show their final contents; object fields are
        read from the final heap."""
        out: dict[str, Val] = self.heap_env(exit_env)
        for p in self.fn.params:
            if isinstance(p.ty, (ir.TList, ir.TDict)):
                out[p.name] = exit_env[p.name]
            elif reaches_unchecked(p.ty) and self.ref.key in self.program.unchecked_writers:
                # the object it was passed, as the call leaves it
                out[p.name] = self.fresh(p.name, p.ty) if p.name in ir.assigned_names(self.fn.body) else exit_env[p.name]
            else:
                out[p.name] = self.entry[p.name]
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
            # Objects this function could have changed must satisfy their
            # class invariants again when it returns.
            self.check_objects(State(ex.env, st.facts), ex.loc, "on return")
            self.check_lifecycles(ex.env, st.facts, ex.loc)
            if fn.raises:
                ctx = Ctx(base=st.facts, env=self.entry, module=self.module, spec=True, quiet=True)
                cond = L.or_(*[self.ev(r.expr, ctx) for r in fn.raises])
                # (evaluated quietly; the obligation itself must not be quiet)
                self.oblige(
                    "raises",
                    ctx.sub(quiet=False),
                    L.not_(cond),
                    fn.raises[0].loc,
                    f"returns normally although '@raises {fn.raises[0].text}' holds",
                    site=ex.loc,
                    clause=fn.raises[0],
                )

    def check_lifecycles(self, env: dict[str, Val], facts: list[L.Term], site: ir.Loc, probe: bool = True, guard: tuple[L.Term, ...] = ()) -> None:
        """Objects that existed at entry changed only as their lifecycles
        allow when control leaves: the parameters, and every object of a
        class written here (quantified: a write's path condition inside a
        loop says nothing about the state after it). Control also leaves at
        an await or a yield; each stretch between two is checked on its own."""
        fn = self.fn
        pre = {**self.entry, **{k[len(SEGMENT) :]: v for k, v in env.items() if k.startswith(SEGMENT)}}
        alloc0 = pre["@alloc"]
        ctx = Ctx(base=facts, env=env, module=self.module, guard=guard, spec=True)
        for p in fn.params:
            if isinstance(p.ty, ir.TClass):
                ref = self.entry[p.name]
                created = self.fresh_self and p.name == "self"
                if probe and self.program.lifecycles_for(p.ty.name, never=True):
                    self.lc_sites.append((list(facts), L.TRUE, ref, p.ty.name, dict(env), created))  # type: ignore[arg-type]
                if created:
                    continue
                for lc, t in self.class_lifecycles(p.ty.name, ref, pre, env, facts):  # type: ignore[arg-type]
                    self.oblige("lifecycle", ctx, t, lc.clause.loc, f"'{p.name}' changes only as the lifecycle of {p.ty.name} allows ('{lc.clause.text}')", site=site, clause=lc.clause)
        for cls in self.lc_written:
            if not self.program.lifecycles_for(cls, never=True):
                continue
            if probe:
                some = L.Const(f"{cls}@some{next(self.counter)}", L.INT)
                self.lc_sites.append((list(facts), L.select(alloc0, some), some, cls, dict(env), False))  # type: ignore[arg-type]
            r = L.Const(f"r!{next(self.counter)}", L.INT)
            for lc, t in self.class_lifecycles(cls, r, pre, env, facts):
                goal = L.forall([r], L.implies(L.select(alloc0, r), t))  # type: ignore[arg-type]
                self.oblige("lifecycle", ctx, goal, lc.clause.loc, f"every {cls} written here changes only as its lifecycle allows ('{lc.clause.text}')", site=site, clause=lc.clause)

    def resume(self, env: dict[str, Val]) -> None:
        """A new stretch without suspension begins in this heap."""
        for k, v in self.heap_env(env).items():
            env[SEGMENT + k] = v

    def suspend(self, ctx: Ctx, loc: ir.Loc) -> None:
        """Other code runs while this function is suspended (other tasks, or a
        generator's consumer): the stretch so far keeps the lifecycles, the
        heap changes, and the next stretch starts from what it finds."""
        assert ctx.state is not None
        self.check_lifecycles(ctx.state.env, ctx.state.facts, loc, probe=False, guard=ctx.guard)
        self.await_havoc(ctx, loc)
        self.resume(ctx.state.env)

    # -- statements -------------------------------------------------------

    def block(self, stmts, st: State) -> State:
        for s in stmts:
            if not st.alive:
                break
            st = self.stmt(s, st)
        return st

    def stmt(self, s: ir.Stmt, st: State) -> State:
        if isinstance(s, ir.Assign):
            ctx = self.ctx(st)
            st.env[s.name] = coerce(self.ev(s.value, ctx), self.fn.locals.get(s.name))
            if self.writes_in_place(s):
                self.havoc_unchecked(ctx, keep=frozenset({s.name}))
            return st
        if isinstance(s, ir.FieldAssign):
            ctx = self.ctx(st)
            ref = self.ev(s.obj, ctx)
            v = coerce(self.ev(s.value, ctx), self.program.classes[s.cls].field_type(s.field))
            self.heap_write(st.env, s.cls, s.field, ref, v)  # type: ignore[arg-type]
            if ref not in self.created and all(ref != self.entry[p.name] for p in self.fn.params if isinstance(p.ty, ir.TClass)) and s.cls not in self.lc_written:
                self.lc_written.append(s.cls)
            if self.has_invariants(s.cls) and ref not in self.checked_params(s.cls):
                key = WRITTEN + s.cls
                st.env[key] = L.store(st.env[key], ref, L.TRUE)  # type: ignore[arg-type]
                self.written.setdefault(s.cls, []).append(s.loc.line)
            return st
        if isinstance(s, ir.DictDel):
            d = st.env[s.name]
            assert isinstance(d, DictVal)
            ctx = self.ctx(st)
            k = self.ev(s.key, ctx)
            if s.strict:
                self.oblige("key", ctx, L.select(d.has, k), s.loc, f"key being deleted from '{s.name}' is present")  # type: ignore[arg-type]
            st.env[s.name] = DictVal(d.vals, L.store(d.has, k, L.FALSE), d.ty)  # type: ignore[arg-type]
            self.wrote_view(s.name, ctx)
            return st
        if isinstance(s, ir.IndexAssign) and isinstance(st.env.get(s.name), DictVal):
            d = st.env[s.name]
            assert isinstance(d, DictVal)
            ctx = self.ctx(st)
            k = self.ev(s.idx, ctx)
            v = coerce(self.ev(s.value, ctx), d.ty.val)
            st.env[s.name] = DictVal(L.store(d.vals, k, v), L.store(d.has, k, L.TRUE), d.ty)  # type: ignore[arg-type]
            self.wrote_view(s.name, ctx)
            return st
        if isinstance(s, ir.IndexAssign):
            lst = st.env[s.name]
            assert isinstance(lst, ListVal)
            ctx = self.ctx(st)
            i = self.index_of(lst, self.ev(s.idx, ctx), s.wrap, ctx, s.loc, s.name)
            v = self.ev(s.value, ctx)
            st.env[s.name] = ListVal(L.store(lst.arr, L.add(lst.off, i), v), lst.off, lst.len, lst.ty)
            self.wrote_view(s.name, ctx)
            return st
        if isinstance(s, ir.Append):
            lst = st.env[s.name]
            assert isinstance(lst, ListVal)
            ctx = self.ctx(st)
            v = self.ev(s.value, ctx)
            st.env[s.name] = ListVal(L.store(lst.arr, L.add(lst.off, lst.len), v), lst.off, L.add(lst.len, L.ONE), lst.ty)
            self.wrote_view(s.name, ctx)
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
            v = coerce(self.ev(s.value, self.ctx(st)), self.fn.ret) if s.value is not None else None
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
        if isinstance(s, ir.Try):
            entry = st.copy()
            # Which way control goes is a free choice: merge needs each
            # branch to carry its own path condition.
            choice = L.Const(f"raised@{next(self.counter)}", L.INT)
            k = len(s.handlers)
            st.facts.append(L.eq(choice, L.ZERO))
            normal = self.block(s.body, st)
            if normal.alive:
                normal = self.block(s.orelse, normal)
            outs = [normal]
            if s.handlers:
                names, appends = self.modified(list(s.body))
                for i, h in enumerate(s.handlers):
                    hst = self.havoc(entry, names, appends)
                    for key in names:
                        if key.startswith(WRITTEN):
                            hst.env[key] = ANY_WRITES  # (the body may have broken any object it wrote before raising)
                    hst.facts.append(L.eq(choice, L.IntV(i + 1)))
                    outs.append(self.block(h, hst))
            del k
            out = self.merge(outs)
            if out.alive and s.finalbody:
                out = self.block(s.finalbody, out)
            return out
        if isinstance(s, ir.Raise) and s.caught:
            st.alive = False  # control goes to a handler (modelled from a havocked state)
            return st
        if isinstance(s, ir.Raise):
            self.raise_paths.append(list(st.facts))
            ctx = self.ctx(st)
            if self.fn.raises:
                ectx = Ctx(base=st.facts, env=self.entry, module=self.module, spec=True, quiet=True)
                cond = L.or_(*[self.ev(r.expr, ectx) for r in self.fn.raises])
                self.oblige("raise", ctx, cond, s.loc, f"raise {s.what} outside '@raises {self.fn.raises[0].text}'")
            elif self.fn.requires or self.fn.ensures:
                self.oblige("raise", ctx, L.FALSE, s.loc, f"raise {s.what} is reachable (add '@raises <condition>' if intended)")
            # (without a contract, an explicit raise is what the function does, not a failure)
            if not self.is_init:  # (an object whose initializer raises never reaches the caller)
                self.check_objects(st, s.loc, "when it raises")
                self.check_lifecycles(st.env, st.facts, s.loc, probe=False)
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
            elif isinstance(s, ir.FieldAssign):
                names.update(k for k, _ in self.heap_keys(s.cls, s.field))
                if self.has_invariants(s.cls):
                    names.add(WRITTEN + s.cls)
            for e in ir.stmt_exprs(s):
                for sub in ir.walk_expr(e):
                    if isinstance(sub, ir.New):
                        names.add("@alloc")
                        for cls_field in self.program.heap_writes.get(self._init_key(sub.cls) or "", {}):
                            c, f = cls_field.split(".", 1)
                            names.update(k for k, _ in self.heap_keys(c, f))
                        decl = self.program.classes.get(sub.cls)
                        if decl is not None and self._init_key(sub.cls) is None:
                            for f, _ in decl.fields:
                                names.update(k for k, _ in self.heap_keys(sub.cls, f))
                            post = self.program.member(sub.cls, "__post_init__")
                            for cls_field in self.program.heap_writes.get(post.key if post else "", {}):
                                c, f = cls_field.split(".", 1)
                                names.update(k for k, _ in self.heap_keys(c, f))
                    if suspends(sub):
                        names.add(SEGMENT)
                        names.update(k for c, d in self.program.classes.items() for f, _ in d.fields for k, _ in self.heap_keys(c, f))
                    if isinstance(sub, ir.Extern):
                        for a in sub.args:
                            if isinstance(a, ir.Var) and isinstance(a.ty, (ir.TList, ir.TDict)):
                                names.add(a.name)
                                appends.add(a.name)
                        if self.program.extern_writes_unchecked(sub, self.fn, self.views):
                            names.update(self.shared)
                            appends.update(self.shared)
                        if self.program.extern_touches_heap(sub):
                            names.add("@alloc")
                            names.update(k for c, d in self.program.classes.items() for f, _ in d.fields for k, _ in self.heap_keys(c, f))
                    if isinstance(sub, ir.Call):
                        tgt = self.program.resolve(self.module, sub.func)
                        if tgt is None:
                            continue
                        if tgt.key in self.program.allocates:
                            names.add("@alloc")
                        for cls_field in self.program.heap_writes.get(tgt.key, {}):
                            c, f = cls_field.split(".", 1)
                            names.update(k for k, _ in self.heap_keys(c, f))
                        for p, a in zip(tgt.fn.params, sub.args):
                            if isinstance(a, ir.Var) and p.name in self.program.mutated.get(tgt.key, ()):
                                names.add(a.name)
                                if p.name in self.program.appends.get(tgt.key, ()):
                                    appends.add(a.name)
                                if a.name in self.views:
                                    names.update(self.shared)
                                    appends.update(self.shared)
                        if tgt.key in self.program.unchecked_writers:
                            names.update(self.shared)
                            appends.update(self.shared)
            if (isinstance(s, (ir.IndexAssign, ir.Append, ir.DictDel)) and s.name in self.views) or (isinstance(s, ir.Assign) and self.writes_in_place(s)):
                names.update(self.shared)
                appends.update(self.shared)
        return names, appends

    def _init_key(self, cls: str) -> str | None:
        ref = self.program.member(cls, "__init__") if cls in self.program.classes else None
        return ref.key if ref is not None else None

    def havoc(self, st: State, names: set[str], appends: set[str]) -> State:
        h = st.copy()
        for name in sorted(names):
            if name == SEGMENT:
                for k in sorted(k for k in h.env if k.startswith(SEGMENT)):
                    h.env[k] = L.Const(f"{k[1:]}@{next(self.counter)}", h.env[k].sort)  # type: ignore[union-attr]
                continue
            if name not in h.env:
                continue
            old = h.env[name]
            if name.startswith(WRITTEN):
                assert isinstance(old, L.Term)
                h.env[name] = L.Const(f"{name[1:]}@{next(self.counter)}", old.sort)
                continue
            if name.startswith("@"):
                assert not isinstance(old, (ListVal, OptVal, DictVal))
                new = L.Const(f"{name[1:]}@{next(self.counter)}", old.sort)
                h.env[name] = new
                if name == "@alloc":
                    r = L.Const(f"r!{next(self.counter)}", L.INT)
                    h.facts.append(L.Quant("forall", (r,), L.implies(L.select(old, r), L.select(new, r)), patterns=((L.select(new, r),),)))
                continue
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

    def cut(self, names: set[str], st: State, site: ir.Loc, at_head: bool = False) -> None:
        """A loop that suspends splits its stretches at its head: each part
        keeps the lifecycles (checked on the way in and after each
        iteration), and the part after the head starts from the head's heap."""
        if SEGMENT not in names:
            return
        if at_head:
            self.resume(st.env)
        else:
            self.check_lifecycles(st.env, st.facts, site, probe=False)

    def invariants_for(self, line: int, user: tuple[ir.Clause, ...]) -> list[ir.Clause]:
        return list(user) + list(self.opts.extra_invariants.get(line, []))

    def check_invs(self, invs: list[ir.Clause], st: State, kind: str, site: ir.Loc, env_override: dict[str, Val] | None = None) -> None:
        env = dict(st.env)
        if env_override:
            env.update(env_override)
        for inv in invs:
            ctx = Ctx(base=st.facts, env=env, module=self.module, state=None, spec=True, old_env=self.entry)
            g = self.ev(inv.expr, ctx.sub(label="invariant"))
            what = "holds on entry" if kind == "inv.entry" else "is preserved"
            self.oblige(kind, ctx, g, inv.loc, f"loop invariant '{inv.text}' {what}", site=site, clause=inv)

    def assume_invs(self, invs: list[ir.Clause], st: State, env_override: dict[str, Val] | None = None) -> None:
        env = dict(st.env)
        if env_override:
            env.update(env_override)
        for inv in invs:
            ctx = Ctx(base=st.facts, env=env, module=self.module, spec=True, quiet=True, old_env=self.entry)
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
        wrote = self.written_in(names)
        self.check_written(wrote, st, s.loc, entry=True)
        self.cut(names, st, s.loc)
        head = self.havoc(st, names, appends)
        self.cut(names, head, s.loc, at_head=True)
        self.assume_invs(invs, head)
        self.assume_written(wrote, head)
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
            self.check_written(wrote, it_end, s.loc, entry=False)
            self.cut(names, it_end, s.loc)
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
        wrote = self.written_in(names)
        self.check_written(wrote, entry, s.loc, entry=True)
        self.cut(names, entry, s.loc)
        self.fn.locals.setdefault(counter, ir.INT)
        head = self.havoc(entry, names, appends)
        self.cut(names, head, s.loc, at_head=True)
        k = head.env[counter]
        assert not isinstance(k, ListVal)
        # By construction the counter stays within [lo, max(lo, hi)].
        head.facts.append(L.le(lo_v, k))
        head.facts.append(L.le(k, L.max_(lo_v, hi_v)))
        view = {idx: k}
        self.assume_invs(invs, head, view)
        self.assume_written(wrote, head)
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
            self.check_written(wrote, it_end, s.loc, entry=False)
            self.cut(names, it_end, s.loc)
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
            self.assume_held(body_st.env[s.elem], seq.ty.elem, self.ctx(body_st))

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
            return coerce(NONE_V, e.ty)
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
        if op in ("rdiv", "floordiv", "fmod", "tmod", "tdiv"):
            zero = L.lit(0, b.sort)
            sym = {"rdiv": "/", "floordiv": "//", "fmod": "%", "tmod": "%", "tdiv": "/"}[op]
            self.oblige("div", ctx, L.ne(b, zero), e.loc, f"divisor of '{sym}' is non-zero")
            if not (ctx.quiet or ctx.spec):
                ctx.assume(L.ne(b, zero))  # past this point it was not: the program would have failed
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
            if op == "tdiv":  # integer division truncating toward zero (Rust, C)
                return truncdiv(a, b)
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
        if isinstance(a, OptVal) or isinstance(b, OptVal):
            if not isinstance(a, OptVal):
                a, b = b, a
            assert isinstance(a, OptVal)
            if b is NONE_V:
                return L.not_(a.some)
            if isinstance(b, OptVal):
                return L.and_(L.eq(a.some, b.some), L.implies(a.some, L.eq(a.val, b.val)))
            return L.and_(a.some, L.eq(a.val, b))  # type: ignore[arg-type]
        if isinstance(a, DictVal) or isinstance(b, DictVal):
            raise VCError("comparing whole dicts with == is not supported")
        return rec_equal(a, b)  # type: ignore[arg-type]

    def ev_Ite(self, e: ir.Ite, ctx: Ctx) -> Val:
        c = self.ev(e.cond, ctx)
        assert not isinstance(c, ListVal)
        a = self.ev(e.then, ctx.sub(c))
        b = self.ev(e.orelse, ctx.sub(L.not_(c)))
        return ite_val(c, a, b)

    def ev_Index(self, e: ir.Index, ctx: Ctx) -> Val:
        seq = self.ev(e.seq, ctx)
        if isinstance(seq, DictVal):
            k = self.ev(e.idx, ctx)
            self.oblige("key", ctx, L.select(seq.has, k), e.loc, f"key looked up in '{_expr_name(e.seq)}' is present")  # type: ignore[arg-type]
            v = L.select(seq.vals, k)  # type: ignore[arg-type]
            self.assume_held(v, e.ty, ctx)
            return v
        assert isinstance(seq, ListVal)
        i = self.ev(e.idx, ctx)
        assert not isinstance(i, ListVal)
        j = self.index_of(seq, i, e.wrap, ctx, e.loc, _expr_name(e.seq))
        x = seq.at(j)
        self.assume_held(x, e.ty, ctx)
        return x

    def ev_Field(self, e: ir.Field, ctx: Ctx) -> Val:
        obj = self.ev(e.obj, ctx)
        assert not isinstance(obj, (ListVal, OptVal, DictVal))
        if isinstance(e.obj.ty, ir.TClass):
            env = ctx.env if ctx.state is None else ctx.state.env
            v = self.heap_read(env, e.obj.ty.name, e.name, obj)
            if ctx.state is not None and (isinstance(e.ty, ir.TClass) or isinstance(e.ty, ir.TOption) and isinstance(e.ty.inner, ir.TClass)):
                for fact in self.alloc_facts(v, e.ty, ctx.state.env):  # the heap holds only allocated objects
                    ctx.assume(fact)
            return v
        raw = L.field(obj, e.name)
        if isinstance(e.ty, ir.TOption):
            return OptVal(L.field(raw, "some"), L.field(raw, "val"), e.ty)
        return raw

    def ev_RecordLit(self, e: ir.RecordLit, ctx: Ctx) -> Val:
        vals = []
        assert isinstance(e.ty, ir.TRecord)
        for (fname, fty), (_, fe) in zip(e.ty.fields, e.fields):
            v = coerce(self.ev(fe, ctx), fty)
            if isinstance(v, OptVal):
                v = L.mkrec(field_sort(fty), (v.some, v.val))
            assert not isinstance(v, (ListVal, DictVal))
            vals.append(v)
        return L.mkrec(sort_of(e.ty), tuple(vals))

    def ev_ListLit(self, e: ir.ListLit, ctx: Ctx) -> Val:
        assert isinstance(e.ty, ir.TList)
        # an empty [] of unknown type is a placeholder until it is stored (see coerce)
        ty = ir.TList(ir.INT) if e.ty.elem == ir.NONE else e.ty
        base = self.fresh("lit", ty, len_=L.ZERO)
        assert isinstance(base, ListVal)
        if e.ty.elem == ir.NONE:
            base = ListVal(base.arr, base.off, base.len, e.ty)
        arr = base.arr
        for i, x in enumerate(e.elems):
            v = self.ev(x, ctx)
            assert not isinstance(v, ListVal)
            arr = L.store(arr, L.IntV(i), v)
        return ListVal(arr, L.ZERO, L.IntV(len(e.elems)), e.ty if e.ty.elem == ir.NONE else ty)

    def ev_Quant(self, e: ir.Quant, ctx: Ctx) -> Val:
        if e.seq is not None and isinstance(e.seq.ty, ir.TDict):
            # over a dict's keys: every k it holds
            d = self.ev(e.seq, ctx)
            assert isinstance(d, DictVal) and e.elem is not None
            k = L.Const(f"{e.elem}!{next(self.counter)}", sort_of(e.seq.ty.key))
            held = L.select(d.has, k)
            sub = ctx.sub(held, binders=ctx.binders + (k,))
            sub.bound[e.elem] = k
            body = self.ev(e.body, sub)
            assert not isinstance(body, ListVal)
            if e.kind == "forall":
                return L.forall([k], L.implies(held, body))
            return L.exists([k], L.and_(held, body))
        lo = self.ev(e.lo, ctx)
        hi = self.ev(e.hi, ctx)
        assert not isinstance(lo, ListVal) and not isinstance(hi, ListVal)
        i = L.Const(f"{e.idx.split('$')[0]}!{next(self.counter)}", L.INT)
        rng = L.and_(L.le(lo, i), L.lt(i, hi))
        sub = ctx.sub(rng, binders=ctx.binders + (i,))
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
        if name == "comp":
            return self.comprehension(e, self.ev(e.args[0], ctx), ctx)
        if name == "threw":
            return self.ev_threw(e, ctx)
        if name == "await" and ctx.state is not None and not ctx.spec:
            self.check_objects(ctx.state, e.loc, "at the await", ctx.guard)
        if name == "dict_lit" and e.ty.key == ir.NONE:  # type: ignore[union-attr]
            return DictVal(L.const_array(L.ARRAY(L.INT), L.ZERO), L.const_array(L.ARRAY(L.BOOL), L.FALSE), e.ty)  # type: ignore[arg-type]
        if name == "dict_lit":
            assert isinstance(e.ty, ir.TDict)
            ks = sort_of(e.ty.key)
            vals: L.Term = L.const_array(L.ARRAY(sort_of(e.ty.val), ks), default_term(sort_of(e.ty.val)))
            has: L.Term = L.const_array(L.ARRAY(L.BOOL, ks), L.FALSE)
            for ke, ve in zip(e.args[0::2], e.args[1::2]):
                k = self.ev(ke, ctx)
                v = coerce(self.ev(ve, ctx), e.ty.val)
                vals = L.store(vals, k, v)  # type: ignore[arg-type]
                has = L.store(has, k, L.TRUE)  # type: ignore[arg-type]
            return DictVal(vals, has, e.ty)
        args = [self.ev(a, ctx) for a in e.args]
        if name == "some":
            assert isinstance(e.ty, ir.TOption)
            return coerce(args[0], e.ty)
        if name == "is_none":
            (o,) = args
            if o is NONE_V:
                return L.TRUE
            if not isinstance(o, OptVal):
                return L.FALSE
            return L.not_(o.some)
        if name == "unwrap":
            (o,) = args
            if not isinstance(o, OptVal):
                if o is NONE_V:
                    self.oblige("none", ctx, L.FALSE, e.loc, f"'{_expr_name(e.args[0])}' is not None here")
                    raise VCError("value is always None here", e.loc)
                return o
            self.oblige("none", ctx, o.some, e.loc, f"'{_expr_name(e.args[0])}' is not None here")
            return o.val
        if name == "from_opaque":
            # A value from unchecked code, used at a checked type.
            (x,) = args
            ty = e.ty
            tag = str(ty).replace(" ", "")
            if isinstance(x, L.Fn) and x.name == f"box.{tag}":
                return pack(ty, list(x.args))  # the same object, seen at its own type again
            comps = [L.Fn(f"unbox.{tag}.{suffix}", tuple(flatten(x)), srt) for suffix, srt in components(ty)]
            v = pack(ty, comps)
            self.box_facts(x, v, ty, ctx, known=False)  # type: ignore[arg-type]
            if isinstance(v, ListVal):
                ctx.assume(L.le(L.ZERO, v.len))
            if ctx.state is not None:
                for fact in self.alloc_facts(v, ty, ctx.state.env):
                    ctx.assume(fact)
                if isinstance(ty, ir.TClass):
                    for _, t in self.class_invariants(ty.name, v, ctx.state.env, ctx.base):  # type: ignore[arg-type]
                        ctx.assume(t)
            self.note(e.loc, "values from unchecked code have the types they are used at")
            return v
        if name == "to_opaque":
            (x,) = args
            ty = e.args[0].ty
            tag = str(ty).replace(" ", "")
            flat = flatten(x)
            prefix = f"unbox.{tag}."
            if all(isinstance(c, L.Fn) and c.name.startswith(prefix) for c in flat) and len({c.args for c in flat}) == 1 and len(flat[0].args) == 1:  # type: ignore[attr-defined]
                return flat[0].args[0]  # type: ignore[attr-defined]
            b = L.Fn(f"box.{tag}", flat, L.OPAQUE)
            self.box_facts(b, x, ty, ctx, known=True)
            return b
        if name == "opaque_op":
            # An operation involving an opaque value: some deterministic,
            # otherwise unknown result.
            op = e.args[0]
            assert isinstance(op, ir.Lit)
            flat: list[L.Term] = []
            for a in args[1:]:
                flat.extend(flatten(a))
            srt = sort_of(e.ty)
            cmp = {"cmp.lt": L.lt, "cmp.le": L.le, "cmp.lte": L.le, "cmp.gt": L.gt, "cmp.ge": L.ge, "cmp.gte": L.ge, "cmp.eq": L.eq, "cmp.ne": L.ne, "cmp.noteq": L.ne}
            if op.value in cmp and len(flat) == 2 and [x.sort for x in flat] in ([L.OPAQUE, L.INT], [L.INT, L.OPAQUE]):
                # against an int: an int compares as one; anything else stays unknown
                x = flat[0] if flat[0].sort == L.OPAQUE else flat[1]
                ux = L.Fn("unbox.int.", (x,), L.INT)
                a, b = (ux, flat[1]) if flat[0].sort == L.OPAQUE else (flat[0], ux)
                return L.ite(L.Fn("opaque.isinstance.Bool", (x, L.StrV("int")), L.BOOL), cmp[op.value](a, b), L.Fn(f"opaque.{op.value}.{srt.name}", tuple(flat), srt))
            if op.value in ("cmp.eq", "cmp.ne", "cmp.noteq") and len(flat) == 2 and {x.sort for x in flat} == {L.OPAQUE, L.STR} and any(isinstance(x, L.StrV) for x in flat):
                # equal to a string literal: that very string, so no other
                x, lit = (flat[0], flat[1]) if isinstance(flat[1], L.StrV) else (flat[1], flat[0])
                boxed = L.Fn("box.str", (lit,), L.OPAQUE)
                self.lemma(L.eq(L.Fn("unbox.str.", (boxed,), L.STR), lit), ctx, (boxed,))
                self.lemma(L.Fn("opaque.isinstance.Bool", (boxed, L.StrV("str")), L.BOOL), ctx, (boxed,))
                same = L.eq(x, boxed)
                return same if op.value == "cmp.eq" else L.not_(same)
            part = str(op.value).startswith("part.")
            r = L.Fn(f"opaque.{'attr.' + str(op.value)[5:] if part else op.value}.{srt.name}", tuple(flat), srt)
            if not ctx.spec and not ctx.quiet:
                self.note(e.loc, "operations on values from unchecked code do not raise")
            if isinstance(e.ty, ir.TInt) and op.value == "len":
                ctx.assume(L.le(L.ZERO, r))
            if part and srt == L.OPAQUE and len(flat) == 1:
                ctx.assume(L.lt(depth(r), depth(flat[0])))
                if not ctx.spec and not ctx.quiet:
                    self.note(e.loc, "a frozen dataclass or NamedTuple holds values built before it")
            return r
        if name == "depth":
            (x,) = args
            ctx.assume(L.le(L.ZERO, depth(x)))  # type: ignore[arg-type]
            return depth(x)  # type: ignore[arg-type]
        if name.startswith("str_"):
            return self.string_op(name, args, e, ctx)
        if name == "await":
            if ctx.state is not None and not ctx.spec:
                self.suspend(ctx, e.loc)
            return args[0]
        if name == "enum_name" or name == "enum_value":
            (x,) = args
            et = e.args[0].ty
            assert isinstance(et, ir.TEnum)
            items = et.members if name == "enum_name" else et.values
            out: L.Term = L.StrV(items[-1]) if isinstance(items[-1], str) else L.IntV(items[-1])  # type: ignore[arg-type]
            for i in range(len(items) - 2, -1, -1):
                lit = L.StrV(items[i]) if isinstance(items[i], str) else L.IntV(items[i])  # type: ignore[arg-type]
                out = L.ite(L.eq(x, L.IntV(i)), lit, out)  # type: ignore[arg-type]
            return out
        if name in ("dict_keys", "dict_values"):
            (d,) = args
            assert isinstance(d, DictVal)
            n = next(self.counter)
            keys = L.Const(f"keys@{n}", L.ARRAY(sort_of(d.ty.key)))
            ln = L.Const(f"keys@{n}.len", L.INT)
            i = L.Const(f"i!{n}", L.INT)
            rng = L.and_(L.le(L.ZERO, i), L.lt(i, ln))
            ctx.assume(L.le(L.ZERO, ln))
            ctx.assume(L.Quant("forall", (i,), L.implies(rng, L.select(d.has, L.select(keys, i))), patterns=((L.select(keys, i),),)))
            if name == "dict_keys":
                return ListVal(keys, L.ZERO, ln, ir.TList(d.ty.key))
            vals = L.Const(f"values@{n}", L.ARRAY(sort_of(d.ty.val)))
            j = L.Const(f"j!{n}", L.INT)
            ctx.assume(L.Quant("forall", (j,), L.implies(L.and_(L.le(L.ZERO, j), L.lt(j, ln)), L.eq(L.select(vals, j), L.select(d.vals, L.select(keys, j)))), patterns=((L.select(vals, j),),)))
            return ListVal(vals, L.ZERO, ln, ir.TList(d.ty.val))

        if name == "checked":  # fixed-width arithmetic: the result must fit the type
            v, lo, hi, tyname = args[0], args[1], args[2], e.args[3]
            assert isinstance(tyname, ir.Lit)
            fits = L.and_(L.le(lo, v), L.le(v, hi))  # type: ignore[arg-type]
            self.oblige("overflow", ctx, fits, e.loc, f"{tyname.value} arithmetic does not overflow")
            ctx.assume(fits)  # (past this point it did not: the program would have panicked)
            return v
        if name == "in_range":  # a value of a fixed-width type is within its range (guaranteed by the type)
            v, lo, hi = args
            ctx.assume(L.and_(L.le(lo, v), L.le(v, hi)))  # type: ignore[arg-type]
            return v
        if name == "same_len":  # r's elements, xs's length (Array.map with an unchecked callback)
            xs, r = args
            assert isinstance(xs, ListVal) and isinstance(r, ListVal)
            return ListVal(r.arr, r.off, xs.len, r.ty)
        if name == "list_concat":
            xs, ys = args
            assert isinstance(xs, ListVal) and isinstance(ys, ListVal)
            n = next(self.counter)
            arr = L.Const(f"cat@{n}.arr", sort_of(xs.ty))
            ln = L.add(xs.len, ys.len)
            i = L.Const(f"i!{n}", L.INT)
            k = L.Const(f"k!{n}", L.INT)
            ctx.assume(L.Quant("forall", (i,), L.implies(L.and_(L.le(L.ZERO, i), L.lt(i, xs.len)), L.eq(L.select(arr, i), xs.at(i))), patterns=((L.select(arr, i),),)))
            ctx.assume(L.Quant("forall", (k,), L.implies(L.and_(L.le(xs.len, k), L.lt(k, ln)), L.eq(L.select(arr, k), ys.at(L.sub(k, xs.len)))), patterns=((L.select(arr, k),),)))
            return ListVal(arr, L.ZERO, ln, xs.ty)
        if name == "dict_copy":
            return args[0]  # dicts are values in the model; aliasing is excluded
        if name == "list_append":
            xs, v = args
            assert isinstance(xs, ListVal)
            return ListVal(L.store(xs.arr, L.add(xs.off, xs.len), v), xs.off, L.add(xs.len, L.ONE), xs.ty)  # type: ignore[arg-type]
        if name == "list_set":
            xs, i, v = args
            assert isinstance(xs, ListVal)
            j = self.index_of(xs, i, True, ctx, e.loc, _expr_name(e.args[0]))  # type: ignore[arg-type]
            return ListVal(L.store(xs.arr, L.add(xs.off, j), v), xs.off, xs.len, xs.ty)  # type: ignore[arg-type]
        if name == "dict_set":
            d, k, v = args
            assert isinstance(d, DictVal)
            v = coerce(v, d.ty.val)
            return DictVal(L.store(d.vals, k, v), L.store(d.has, k, L.TRUE), d.ty)  # type: ignore[arg-type]
        if name == "dict_remove":  # JS Map.delete: no key needed
            d, k = args
            assert isinstance(d, DictVal)
            return DictVal(d.vals, L.store(d.has, k, L.FALSE), d.ty)  # type: ignore[arg-type]
        if name == "dict_del":
            d, k = args
            assert isinstance(d, DictVal)
            self.oblige("key", ctx, L.select(d.has, k), e.loc, f"key being deleted from '{_expr_name(e.args[0])}' is present")  # type: ignore[arg-type]
            return DictVal(d.vals, L.store(d.has, k, L.FALSE), d.ty)  # type: ignore[arg-type]
        if name in ("dict_has", "dict_get_opt", "dict_get_or"):
            d, k = args[0], args[1]
            assert isinstance(d, DictVal)
            has = L.select(d.has, k)  # type: ignore[arg-type]
            v = L.select(d.vals, k)  # type: ignore[arg-type]
            if name == "dict_has":
                return has
            if name == "dict_get_opt":
                return OptVal(has, v, ir.TOption(d.ty.val))
            dflt = coerce(args[2], d.ty.val)
            return L.ite(has, v, dflt)  # type: ignore[arg-type]
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

    def string_op(self, name: str, args: list, e: ir.Builtin, ctx: Ctx) -> Val:
        if name == "str_concat":
            return L.App("str.++", tuple(args), L.STR)
        if name == "str_len":
            return L.App("str.len", (args[0],), L.INT)
        if name == "str_contains":  # sub in s
            return L.App("str.contains", (args[0], args[1]), L.BOOL)
        if name == "str_startswith":
            return L.App("str.prefixof", (args[1], args[0]), L.BOOL)
        if name == "str_endswith":
            return L.App("str.suffixof", (args[1], args[0]), L.BOOL)
        if name == "str_of_int":
            return L.App("str.from_int", (args[0],), L.STR)
        if name == "str_lt":
            return L.App("str.lt", (args[0], args[1]), L.BOOL)
        if name == "str_le":
            return L.App("str.le", (args[0], args[1]), L.BOOL)
        if name == "str_find":
            return L.App("str.indexof", (args[0], args[1], L.ZERO), L.INT)
        if name == "str_index":
            s_, i = args
            n = L.App("str.len", (s_,), L.INT)
            self.oblige("index", ctx, L.and_(L.le(L.neg(n), i), L.lt(i, n)), e.loc, f"index into '{_expr_name(e.args[0])}' is within -len..len-1")
            j = L.ite(L.lt(i, L.ZERO), L.add(i, n), i)
            return L.App("str.at", (s_, j), L.STR)
        if name == "str_slice":
            s_, lo, hi = args
            n = L.App("str.len", (s_,), L.INT)

            def norm(b, default):
                if b is NONE_V:
                    return default
                return L.ite(L.lt(b, L.ZERO), L.max_(L.add(b, n), L.ZERO), L.min_(b, n))

            lo2, hi2 = norm(lo, L.ZERO), norm(hi, n)
            return L.App("str.substr", (s_, lo2, L.max_(L.sub(hi2, lo2), L.ZERO)), L.STR)
        if name == "str_fn":
            # lower(), strip(), replace(), ...: deterministic, not interpreted
            op = e.args[0]
            assert isinstance(op, ir.Lit)
            flat: list[L.Term] = []
            for a in args[1:]:
                flat.extend(flatten(a))
            return L.Fn(f"str.{op.value}", tuple(flat), sort_of(e.ty))
        raise VCError(f"unknown string operation {name}", e.loc)

    def comprehension(self, e: ir.Builtin, seq: Val, ctx: Ctx) -> Val:
        assert isinstance(seq, ListVal) and isinstance(e.ty, ir.TList)
        elem_lit = e.args[1]
        assert isinstance(elem_lit, ir.Lit)
        elem = str(elem_lit.value)
        body, cond = e.args[2], (e.args[3] if len(e.args) > 3 else None)
        n = next(self.counter)
        pure = all(self._pure(x) for x in (body, cond) if x is not None)
        # Under a quantifier the new list depends on its variables: a
        # function of them, defined for all of them at once.
        under = bool(ctx.binders) and pure

        def sym(name: str, srt: L.Sort) -> L.Term:
            return L.Fn(name, ctx.binders, srt) if under else L.Const(name, srt)

        assume = ctx.assume_for_all_binders if under else ctx.assume
        arr = sym(f"comp@{n}.arr", sort_of(e.ty))
        if cond is None:
            ln: L.Term = seq.len
        else:
            ln = sym(f"comp@{n}.len", L.INT)
            assume(L.and_(L.le(L.ZERO, ln), L.le(ln, seq.len)))
        i = L.Const(f"{elem}!{n}", L.INT)
        rng = L.and_(L.le(L.ZERO, i), L.lt(i, seq.len))
        sub = ctx.sub(rng, spec=True) if pure else ctx.sub(rng, spec=True, quiet=True)
        sub.bound[elem] = seq.at(i)
        if not pure:
            # Effects of the body: whatever its calls may write is unknown now.
            if ctx.state is not None:
                self.havoc_heap(ctx)
            return ListVal(arr, L.ZERO, ln, e.ty)
        b = self.ev(body, sub)
        if cond is None:
            assume(L.Quant("forall", (i,), L.implies(rng, L.eq(L.select(arr, i), b)), patterns=((L.select(arr, i),),)))  # type: ignore[arg-type]
        else:
            c = self.ev(cond, sub)
            k = L.Const(f"k!{n}", L.INT)
            j = L.Const(f"j!{n}", L.INT)
            sub_j = ctx.sub(None, spec=True, quiet=True)
            sub_j.bound[elem] = seq.at(j)
            bj = self.ev(body, sub_j)
            cj = self.ev(cond, sub_j)
            # every element comes from some accepted source element
            assume(L.Quant("forall", (k,), L.implies(L.and_(L.le(L.ZERO, k), L.lt(k, ln)), L.exists([j], L.and_(L.le(L.ZERO, j), L.lt(j, seq.len), cj, L.eq(L.select(arr, k), bj)))), patterns=((L.select(arr, k),),)))  # type: ignore[arg-type]
            del c
        return ListVal(arr, L.ZERO, ln, e.ty)

    def _pure(self, e: ir.Expr) -> bool:
        for sub in ir.walk_expr(e):
            if isinstance(sub, (ir.Extern, ir.New)):
                return False
            if isinstance(sub, ir.Builtin) and sub.name in ("await", "from_opaque", "comp", "dict_keys", "dict_values"):
                return False
            if isinstance(sub, ir.Call):
                tgt = self.program.resolve(self.module, sub.func)
                if tgt is None or not (tgt.key in self.program.definitional or tgt.key in self.program.predicates):
                    return False
        return True

    def await_havoc(self, ctx: Ctx, loc: ir.Loc) -> None:
        """Other tasks run while this one awaits: objects that existed when
        this call started may change; objects it created itself do not."""
        assert ctx.state is not None
        env = ctx.state.env
        if not self.program.classes:
            return
        self.note(loc, "objects created during this call are not shared with concurrent tasks")
        alloc0 = self.entry["@alloc"]
        for key in [k for k in env if k.startswith("@") and k != "@alloc"]:
            old = env[key]
            assert isinstance(old, L.Term)
            new = L.Const(f"{key[1:]}@await{loc.line}.{next(self.counter)}", old.sort)
            r = L.Const(f"r!{next(self.counter)}", L.INT)
            ctx.assume(L.Quant("forall", (r,), L.implies(L.not_(L.select(alloc0, r)), L.eq(L.select(new, r), L.select(old, r))), patterns=((L.select(new, r),),)))  # type: ignore[arg-type]
            env[key] = new
        # Other tasks are checked code too: they leave objects satisfying
        # their class invariants whenever they yield.
        for cname, decl in self.program.classes.items():
            # (only where the field maps are the class's alone: the assumption
            # ranges over every object, and subclasses share their bases' maps)
            if not decl.invariants or self.program.in_hierarchy(cname):
                continue
            r = L.Const(f"r!{next(self.counter)}", L.INT)
            for inv, t in self.class_invariants(cname, r, env, ctx.base):
                sels = [x for x in L.iter_terms(t) if isinstance(x, L.App) and x.op == "select" and x.args[1] == r]
                if not sels:
                    continue
                self.note(loc, "other tasks do not await while an object's invariant is broken")
                ctx.assume(L.Quant("forall", (r,), L.implies(L.select(alloc0, r), t), patterns=((sels[0],),)))  # type: ignore[arg-type]

    def note(self, loc: ir.Loc, text: str) -> None:
        """Record an assumption the proof rests on (shown as trusted base).
        Inside a trusted predicate's unfolding, the predicate is the assumption."""
        if self.unfolding_stack:
            return
        text = "assumed: " + text
        if (loc, text) not in self.assumptions:
            self.assumptions.append((loc, text))

    def ev_Extern(self, e: ir.Extern, ctx: Ctx) -> Val:
        args = [self.ev(a, ctx) for a in e.args]
        if ctx.spec:
            raise VCError(f"specifications cannot call unchecked code ('{e.name}')", e.loc)
        callee = self.program.through_wrapper(self.module, e.name)
        if callee is not None and self.program.same_scc(self.ref.key, callee.key) and self.program.needs_termination(self.ref.key):
            self.recursion_check(callee, {p.name: a for p, a in zip(callee.fn.params, args)}, ctx, e.loc)
        if not e.name.startswith(("caught exception", "default of")):
            self.note(e.loc, f"call:{e.name}")
        if e.name == "yield" and ctx.state is not None:
            self.check_objects(ctx.state, e.loc, "at the yield", ctx.guard)
            self.suspend(ctx, e.loc)
        if ctx.state is not None:
            env = ctx.state.env
            # It may change any list/dict variable passed to it, and, if it
            # is handed anything that can reach objects, any object.
            # Escaped closures may run now and reassign what they captured.
            for n in sorted(self.fn.escaped):
                if n in env and n in self.fn.locals and not isinstance(env[n], (ListVal, DictVal)):
                    env[n] = self.fresh(n, self.fn.locals[n])
            touched = list(e.args) + [ir.Var(self.fn.locals[n], e.loc, n) for n in sorted(self.fn.escaped) if n in self.fn.locals]
            for a_e in touched:
                if isinstance(a_e, ir.Var) and isinstance(env.get(a_e.name), (ListVal, DictVal)):
                    ty = self.fn.locals.get(a_e.name) or a_e.ty
                    nv = self.fresh(a_e.name, ty)
                    if isinstance(nv, ListVal):
                        ctx.assume(L.le(L.ZERO, nv.len))
                    env[a_e.name] = nv
            if self.program.extern_writes_unchecked(e, self.fn, self.views, set(ctx.state.env)):
                self.havoc_unchecked(ctx)
            elif unchecked_constructor(e) and any(reaches_unchecked(a.ty) for a in e.args):
                self.note(e.loc, f"'{e.name}' leaves the values it is handed unchanged")
            if self.program.extern_touches_heap(e) or (self.program.classes and self.fn.escaped):
                self.havoc_heap(ctx)
                if any(c.invariants for c in self.program.classes.values()):
                    self.note(e.loc, "unchecked code leaves objects satisfying their class invariants")
                if any(d.lifecycles for d in self.program.classes.values()):
                    self.note(e.loc, "unchecked code changes objects only as their lifecycles allow")
        r = self.fresh(f"{e.name.split('.')[-1]}()", e.ty) if e.ty != ir.NONE else NONE_V
        if isinstance(r, ListVal):
            ctx.assume(L.le(L.ZERO, r.len))
        if ctx.state is not None and r is not NONE_V:
            for fact in self.alloc_facts(r, e.ty, ctx.state.env):
                ctx.assume(fact)
            if isinstance(e.ty, ir.TClass):
                for _, t in self.class_invariants(e.ty.name, r, ctx.state.env, ctx.base):  # type: ignore[arg-type]
                    ctx.assume(t)
        return r

    def havoc_heap(self, ctx: Ctx) -> None:
        assert ctx.state is not None
        env = ctx.state.env
        for key in [k for k in env if k.startswith("@") and k != "@alloc"]:
            old = env[key]
            assert isinstance(old, L.Term)
            env[key] = L.Const(f"{key[1:]}@{next(self.counter)}", old.sort)
        alloc_pre = env["@alloc"]
        new_alloc = L.Const(f"alloc@{next(self.counter)}", L.ARRAY(L.BOOL))
        r = L.Const(f"r!{next(self.counter)}", L.INT)
        ctx.assume(L.Quant("forall", (r,), L.implies(L.select(alloc_pre, r), L.select(new_alloc, r)), patterns=((L.select(new_alloc, r),),)))  # type: ignore[arg-type]
        env["@alloc"] = new_alloc

    def ev_Call(self, e: ir.Call, ctx: Ctx) -> Val:
        callee = self.program.resolve(ctx.module, e.func)
        if callee is None:
            raise VCError(f"unknown function '{e.func}'", e.loc)
        args = [coerce(self.ev(a, ctx), p.ty) for a, p in zip(e.args, callee.fn.params)]
        # a base constructor run on the object this constructor is building
        base_init = self.is_init and callee.fn.name.endswith(".__init__") and bool(e.args) and isinstance(e.args[0], ir.Var) and e.args[0].name == "self"
        return self.call(callee, args, list(e.args), ctx, e.loc, new_self=base_init)

    def ev_New(self, e: ir.New, ctx: Ctx) -> Val:
        if ctx.spec:
            raise VCError("specifications cannot create objects", e.loc)
        if ctx.state is None:
            raise VCError("objects can only be created in code", e.loc)
        decl = self.program.classes.get(e.cls)
        if decl is None:
            raise VCError(f"unknown class '{e.cls}'", e.loc)
        init = self._init_key(e.cls)
        ptys = [p.ty for p in self.program.funcs[init].fn.params[1:]] if init else [t for _, t in decl.fields]
        args = [coerce(self.ev(a, ctx), t) for a, t in zip(e.args, ptys)]
        env = ctx.state.env
        alloc = env["@alloc"]
        r = L.Const(f"{e.cls}@new{next(self.counter)}", L.INT)
        self.created.add(r)
        ctx.assume(L.not_(L.select(alloc, r)))  # type: ignore[arg-type]
        env["@alloc"] = L.store(alloc, r, L.TRUE)  # type: ignore[arg-type]
        if init is not None:
            self.call(self.program.ref(init), [r] + args, [None] + list(e.args), ctx, e.loc, new_self=True)
            if not init.endswith(f"::{e.cls}.__init__"):
                # an inherited constructor establishes its own class's
                # invariants; this class's must be shown here
                self.new_invariants(e.cls, r, env, ctx, e.loc)
            return r
        # Generated constructor (dataclass-style): fields in declaration order,
        # then __post_init__ if there is one.
        for (fname, _), v in zip(decl.fields, args):
            self.heap_write(env, e.cls, fname, r, v)
        post = self.program.member(e.cls, "__post_init__")
        if post is not None:
            self.call(post, [r], [None], ctx, e.loc, new_self=True)
            return r
        self.new_invariants(e.cls, r, env, ctx, e.loc)
        if self.program.lifecycles_for(e.cls, never=True):
            self.lc_sites.append((list(ctx.base), L.and_(*ctx.guard), r, e.cls, dict(env), True))
        return r

    def new_invariants(self, cls: str, r: L.Term, env: dict[str, Val], ctx: Ctx, loc: ir.Loc) -> None:
        for inv, t in self.class_invariants(cls, r, env, ctx.base):
            self.oblige("class.inv", ctx, t, inv.loc, f"new {cls} satisfies its invariant '{inv.text}'", site=loc, clause=inv)
            ctx.assume(t)

    def call(self, callee: FuncRef, args: list[Val], arg_exprs: list[ir.Expr | None], ctx: Ctx, loc: ir.Loc, new_self: bool = False) -> Val:
        fn = callee.fn
        # A list argument is a reference: a later argument that mutates the
        # same list changes what the callee sees. Re-read list variables.
        if ctx.state is not None:
            args = [ctx.state.env.get(a_e.name, a) if isinstance(a_e, ir.Var) and isinstance(a, (ListVal, DictVal)) else a for a_e, a in zip(arg_exprs, args)]
        muts = self.program.mutated.get(callee.key, set())
        list_vars = [a_e.name for a_e, p in zip(arg_exprs, fn.params) if isinstance(a_e, ir.Var) and isinstance(p.ty, (ir.TList, ir.TDict))]
        if muts and len(list_vars) != len(set(list_vars)):
            raise VCError(f"the same list is passed twice to '{fn.name}', which mutates a list parameter; the two parameters would alias", loc)
        for p, a_e in zip(fn.params, arg_exprs):
            if p.name in muts and not isinstance(a_e, ir.Var) and not _fresh_expr(a_e):
                raise VCError(f"'{fn.name}' mutates its list parameter '{p.name}'; pass a variable (or a copy) so the change is tracked", loc)
        pmap: dict[str, Val] = {p.name: a for p, a in zip(fn.params, args)}
        heap_pre = self.heap_env(ctx.env) if ctx.state is None else self.heap_env(ctx.state.env)
        predicate = callee.key in self.program.predicates
        definitional = callee.key in self.program.definitional or predicate
        if ctx.spec and not definitional:
            raise VCError(f"specs may only call pure (loop-free, mutation-free) functions; '{fn.name}' is not", loc)
        # Callee preconditions (which may read object fields).
        cctx = Ctx(base=ctx.base, env={**heap_pre, **pmap}, module=callee.module, guard=ctx.guard, spec=True, quiet=True)
        for rq in fn.requires:
            g = self.ev(rq.expr, cctx)
            self.oblige("call", ctx, g, loc, f"call to '{fn.name}' satisfies '@requires {rq.text}'", clause=rq)
        # Objects passed in must satisfy their invariants (the callee assumes them).
        if not ctx.spec:
            for i, p in enumerate(fn.params):
                if isinstance(p.ty, ir.TClass) and not (new_self and i == 0):
                    for inv, t in self.class_invariants(p.ty.name, args[i], {**heap_pre}, ctx.base):  # type: ignore[arg-type]
                        self.oblige("call", ctx, t, loc, f"'{p.name}' satisfies the invariant of {p.ty.name} ('{inv.text}') when calling '{fn.name}'", clause=inv)
        if ctx.state is not None and not ctx.spec and not new_self and any(ir.reaches_object(p.ty) for p in fn.params):
            self.check_objects(ctx.state, loc, f"when calling '{fn.name}'", ctx.guard)
        if fn.raises and not ctx.spec:
            rc = L.or_(*[self.ev(r.expr, cctx) for r in fn.raises])
            self.oblige("call", ctx, L.not_(rc), loc, f"call to '{fn.name}' cannot raise ('@raises {fn.raises[0].text}')")
        if self.program.same_scc(self.ref.key, callee.key) and self.program.needs_termination(self.ref.key):
            self.recursion_check(callee, pmap, ctx, loc)
        self.deps.add(callee.key)
        # Result.
        if predicate:
            flat = [t for a in args for t in flatten(a)]
            r: Val = L.Fn(self.program.logic_names[callee.key], tuple(flat), sort_of(fn.ret))
            self.unfold(callee, pmap, r, ctx, loc)
        elif definitional:
            r = self.apply_def(callee, args, heap_pre)
        elif fn.ret == ir.NONE:
            r = NONE_V
        else:
            r = self.fresh(f"{fn.name.split('.')[-1]}()", fn.ret)
            if ctx.state is not None:
                for fact in self.alloc_facts(r, fn.ret, ctx.state.env):
                    ctx.assume(fact)
        post = dict(pmap)
        if ctx.state is not None and not ctx.spec:
            post.update(self.call_effects(callee, args, arg_exprs, ctx, new_self))
        # Assume the postcondition (code context; spec calls use lemma axioms).
        if not ctx.spec and fn.ensures and not self.definitional_mode and not predicate:
            ectx = Ctx(base=ctx.base, env=post, module=callee.module, guard=ctx.guard, old_env={**heap_pre, **pmap}, result=r if r is not NONE_V else None, spec=True, quiet=True)
            for en in fn.ensures:
                ctx.assume(self.ev(en.expr, ectx))
        return r

    def call_effects(self, callee: FuncRef, args: list[Val], arg_exprs: list[ir.Expr | None], ctx: Ctx, new_self: bool = False, returned: bool = True) -> dict[str, Val]:
        """What a call leaves in the caller's state whether it returns or
        raises: mutated list arguments get fresh contents, the fields it may
        write change, and the objects it was passed satisfy their invariants
        (an object under construction only if it returns). Returns the
        changed arguments and the heap."""
        assert ctx.state is not None
        fn = callee.fn
        muts = self.program.mutated.get(callee.key, set())
        post: dict[str, Val] = {}
        env = ctx.state.env
        heap_pre = self.heap_env(env)
        for p, a_expr in zip(fn.params, arg_exprs):
            if p.name in muts and isinstance(a_expr, ir.Var) and isinstance(env[a_expr.name], DictVal):
                nd = self.fresh(a_expr.name, p.ty)
                env[a_expr.name] = nd
                post[p.name] = nd
                continue
            if p.name in muts and isinstance(a_expr, ir.Var):
                old = env[a_expr.name]
                assert isinstance(old, ListVal)
                keep = None if p.name in self.program.appends.get(callee.key, ()) else old.len
                nv = self.fresh(a_expr.name, p.ty, len_=keep)
                assert isinstance(nv, ListVal)
                if keep is not None:
                    nv = ListVal(nv.arr, old.off, keep, nv.ty)
                else:
                    ctx.assume(L.le(L.ZERO, nv.len))
                env[a_expr.name] = nv
                post[p.name] = nv
        views = [a.name for p, a in zip(fn.params, arg_exprs) if p.name in muts and isinstance(a, ir.Var) and a.name in self.views]
        if callee.key in self.program.unchecked_writers or views:
            self.havoc_unchecked(ctx, keep=frozenset(views))
            for p, a_expr in zip(fn.params, arg_exprs):
                if reaches_unchecked(p.ty) and p.name not in post:
                    post[p.name] = env[a_expr.name] if isinstance(a_expr, ir.Var) and a_expr.name in self.shared else self.fresh(p.name, p.ty)
        self.havoc_call(callee, args, new_self, ctx)
        post.update(self.heap_env(env))
        for i, p in enumerate(fn.params):
            if isinstance(p.ty, ir.TClass) and (returned or not (new_self and i == 0)):
                for _, t in self.class_invariants(p.ty.name, args[i], env, ctx.base):  # type: ignore[arg-type]
                    ctx.assume(t)
            # ... changed only as their lifecycles allow (an initializer
            # rebuilds its object, whether or not it is new: no lifecycle binds it)
            if isinstance(p.ty, ir.TClass) and not (i == 0 and fn.name.endswith((".__init__", ".__post_init__"))):
                for _, t in self.class_lifecycles(p.ty.name, args[i], heap_pre, env, ctx.base):  # type: ignore[arg-type]
                    ctx.assume(t)
        return post

    def ev_threw(self, e: ir.Builtin, ctx: Ctx) -> Val:
        """The state a call leaves when it raises: its contract describes
        normal returns only, so only what it may change, and the invariants
        of the objects it was passed, are known."""
        c = e.args[0]
        assert isinstance(c, ir.Call)
        callee = self.program.resolve(ctx.module, c.func)
        if callee is None:
            raise VCError(f"unknown function '{c.func}'", e.loc)
        if ctx.state is not None and not ctx.spec:
            args = [coerce(self.ev(a, ctx), p.ty) for a, p in zip(c.args, callee.fn.params)]
            self.deps.add(callee.key)
            exprs: list[ir.Expr | None] = list(c.args)
            self.call_effects(callee, args, exprs, ctx, new_self=callee.fn.name.endswith(".__init__"), returned=False)
        return NONE_V

    def unfold(self, callee: FuncRef, pmap: dict[str, Val], r: L.Term, ctx: Ctx, loc: ir.Loc) -> None:
        """A trusted predicate's '@ensures' at this one application, as a
        lemma. Inside it, applications of predicates in its own recursion
        group are unfolded only ``fuel`` deep (others always: they form a
        DAG), so the facts stay finite and need no recursive axiom."""
        depth = sum(1 for k in self.unfolding_stack if k == callee.key or self.program.same_scc(k, callee.key))
        if depth >= self.fuel or r in self.unfolded:
            return
        self.unfolded.add(r)
        self.note(loc, f"trusted predicate '{callee.fn.name}' holds exactly as its @ensures says")
        self.unfolding_stack.append(callee.key)
        try:
            scratch: list[L.Term] = []
            ectx = Ctx(base=scratch, env=dict(pmap), module=callee.module, old_env=dict(pmap), result=r, spec=True, quiet=True)
            req = [self.ev(rq.expr, ectx) for rq in callee.fn.requires]
            goals = [self.ev(en.expr, ectx) for en in callee.fn.ensures]
        finally:
            self.unfolding_stack.pop()
        self.lemma(L.implies(L.and_(*req), L.and_(*scratch, *goals)), ctx, (r,), pred=callee.key)

    def lemma(self, fact: L.Term, ctx: Ctx, about: tuple[L.Term, ...], pred: str | None = None) -> None:
        """Record a fact valid in every state, about the terms ``about``.
        Inside a quantifier it is about the bound variables, so it holds for
        all of them, triggered by ``about``."""
        bound = {c for v in ctx.bound.values() if isinstance(v, L.Term) for c in L.consts(v) if "!" in c.name}
        vs = tuple(sorted({c for t in about for c in L.consts(t)} & bound, key=lambda c: c.name))
        if vs:
            fact = L.Quant("forall", vs, fact, patterns=(about,) if _triggerable(about) else ())
        if fact not in self.lemma_set:
            self.lemma_set.add(fact)
            self.lemmas.append(fact)
            heads = frozenset(x.name for t in about for x in L.iter_terms(t) if isinstance(x, L.Fn)) if vs else None
            self.lemma_info.append((fact, about, heads, pred))

    def relevant_lemmas(self, terms: list[L.Term]) -> list[L.Term]:
        """The lemmas about terms the obligation mentions, and what those
        lemmas mention in turn, except applications of predicates in the
        unfolded one's own recursion group (the fuel bound, per obligation)."""
        if not self.lemma_info:
            return []
        present: set[L.Term] = set()
        heads: set[str] = set()
        preds = {self.program.logic_names[k]: k for k in self.program.predicates}

        def mention(t: L.Term, pred: str | None) -> None:
            for x in L.iter_terms(t):
                if isinstance(x, L.Fn):
                    k = preds.get(x.name)
                    if pred is not None and k is not None and (k == pred or self.program.same_scc(k, pred)):
                        continue
                    heads.add(x.name)
                present.add(x)

        for t in terms:
            mention(t, None)
        todo = list(range(len(self.lemma_info)))
        chosen: set[int] = set()
        changed = True
        while changed:
            changed = False
            for i in list(todo):
                fact, about, hs, pred = self.lemma_info[i]
                if (hs is not None and (not hs or hs & heads)) or (hs is None and any(a in present for a in about)):
                    todo.remove(i)
                    chosen.add(i)
                    mention(fact, pred)
                    changed = True
        return [self.lemma_info[i][0] for i in sorted(chosen)]

    def box_facts(self, b: L.Term, v: Val, ty: ir.Type, ctx: Ctx, known: bool) -> None:
        """How a checked value ``v`` of type ``ty`` looks through the
        operations telic leaves uninterpreted on its unchecked view ``b``
        (the same object): membership, indexing, length, isinstance. Unless
        ``known``, only where ``b`` is an instance of that type."""
        n = next(self.counter)
        facts: list[L.Term] = []
        kind = None
        if isinstance(v, DictVal) and isinstance(ty, ir.TDict) and isinstance(ty.val, ir.TOpaque):
            kind = "dict"
            k = L.Const(f"k!{n}", sort_of(ty.key))
            has = L.select(v.has, k)
            # Python's 'in' is key membership; JavaScript's also sees inherited
            # properties, and a Map's entries are not properties at all
            mems = [("opaque.cmp.in.Bool", has), ("opaque.cmp.notin.Bool", L.not_(has))] if not ty.js else [("opaque.in.Bool", None)] if ty.js == "object" else []
            for op, held in mems:
                mem = L.Fn(op, (k, b), L.BOOL)
                facts.append(L.Quant("forall", (k,), L.eq(mem, held) if held is not None else L.implies(has, mem), patterns=((mem,),) if _triggerable((mem,)) else ()))
            if ty.js != "map":
                get = L.Fn("opaque.getitem.Opaque", (b, k), L.OPAQUE)
                facts.append(L.Quant("forall", (k,), L.implies(has, L.eq(get, L.select(v.vals, k))), patterns=((get,),) if _triggerable((get,)) else ()))
        elif isinstance(v, ListVal) and isinstance(ty, ir.TList) and isinstance(ty.elem, ir.TOpaque):
            kind = "list"
            i = L.Const(f"i!{n}", L.INT)
            facts.append(L.eq(L.Fn("opaque.len.Int", (b,), L.INT), v.len))
            get = L.Fn("opaque.getitem.Opaque", (b, i), L.OPAQUE)
            facts.append(L.Quant("forall", (i,), L.implies(L.and_(L.le(L.ZERO, i), L.lt(i, v.len)), L.eq(get, v.at(i))), patterns=((get,),) if _triggerable((get,)) else ()))
        elif isinstance(ty, ir.TStr):
            kind = "str"
        elif isinstance(ty, ir.TInt):
            kind = "int"
        elif isinstance(ty, ir.TBool):
            kind = "bool"
        if kind is None:
            return
        is_kind = L.Fn("opaque.isinstance.Bool", (b, L.StrV(kind)), L.BOOL)
        if known:
            facts.append(is_kind)
            fact = L.and_(*facts)
        else:
            fact = L.implies(is_kind, L.and_(*facts)) if facts else L.TRUE
        if fact != L.TRUE:
            self.lemma(fact, ctx, (b,))

    @property
    def views(self) -> set[str]:
        return self.program.views.get(self.ref.key, set())

    @property
    def shared(self) -> set[str]:
        """Variables that may hold an object unchecked values can reach."""
        if self._shared is None:
            tys = {**{p.name: p.ty for p in self.fn.params}, **self.fn.locals}
            self._shared = {n for n, t in tys.items() if reaches_unchecked(t)} | self.views
        return self._shared

    def writes_in_place(self, s: ir.Assign) -> bool:
        return in_place(s) and (s.name in self.views or isinstance(self.fn.locals.get(s.name), ir.TOpaque))

    def wrote_view(self, name: str, ctx: Ctx) -> None:
        if name in self.views:
            self.havoc_unchecked(ctx, keep=frozenset({name}))

    def havoc_unchecked(self, ctx: Ctx, keep: frozenset[str] = frozenset()) -> None:
        """An object unchecked values can reach may have changed: forget
        what is known about every variable that may share one. Two variables
        holding the same unchecked value still hold the same one."""
        assert ctx.state is not None
        env = ctx.state.env
        tys = {**{p.name: p.ty for p in self.fn.params}, **self.fn.locals}
        renamed: dict[L.Term, Val] = {}
        for n in sorted(self.shared - keep):
            if n not in env or n not in tys:
                continue
            old = env[n]
            if isinstance(old, L.Term) and old.sort == L.OPAQUE:
                if old not in renamed:
                    renamed[old] = self.fresh(n, tys[n])
                env[n] = renamed[old]
                continue
            nv = self.fresh(n, tys[n])
            if isinstance(nv, ListVal):
                ctx.assume(L.le(L.ZERO, nv.len))
            env[n] = nv

    def havoc_call(self, callee: FuncRef, args: list[Val], new_self: bool, ctx: Ctx) -> None:
        """The heap after a call: only the fields the callee may write change,
        and only on the objects it may write them on."""
        assert ctx.state is not None
        env = ctx.state.env
        alloc_pre = env["@alloc"]
        names = [p.name for p in callee.fn.params]
        for cls_field, targets in self.program.heap_writes.get(callee.key, {}).items():
            c, f = cls_field.split(".", 1)
            refs = []
            for t in targets:
                if t in names:
                    refs.append(args[names.index(t)])
            for key, srt in self.heap_keys(c, f):
                old = env[key]
                new = L.Const(f"{key[1:]}@{next(self.counter)}", srt)
                env[key] = new
                if "*" in targets:
                    continue
                r = L.Const(f"r!{next(self.counter)}", L.INT)
                untouched = L.and_(L.select(alloc_pre, r), *[L.ne(r, x) for x in refs])  # type: ignore[arg-type]
                ctx.assume(L.Quant("forall", (r,), L.implies(untouched, L.eq(L.select(new, r), L.select(old, r))), patterns=((L.select(new, r),),)))  # type: ignore[arg-type]
        if callee.key in self.program.allocates:
            new_alloc = L.Const(f"alloc@{next(self.counter)}", L.ARRAY(L.BOOL))
            r = L.Const(f"r!{next(self.counter)}", L.INT)
            ctx.assume(L.Quant("forall", (r,), L.implies(L.select(alloc_pre, r), L.select(new_alloc, r)), patterns=((L.select(new_alloc, r),),)))  # type: ignore[arg-type]
            env["@alloc"] = new_alloc

    def apply_def(self, callee: FuncRef, args: list[Val], heap: dict[str, Val] | None = None) -> L.Term:
        #@ requires callee.key in self.program.logic_names
        flat: list[L.Term] = []
        for a in args:
            flat.extend(flatten(a))
        for key in self.program.def_heap_keys(callee.key):
            if heap is None or key not in heap:
                raise VCError(f"'{callee.fn.name}' reads object fields that are not available here")
            flat.append(heap[key])  # type: ignore[arg-type]
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
        m0 = [self.ev(e, mctx) for e in measure_parts(me)]
        cctx = Ctx(base=ctx.base, env=pmap, module=callee.module, guard=ctx.guard, spec=True, quiet=True)
        m1 = [self.ev(e, cctx) for e in measure_parts(them)]
        if len(m0) != len(m1):
            raise VCError(f"'{self.fn.name}' and '{callee.fn.name}' recurse into each other but their '@decreases' have different lengths", loc)
        inferred = self.fn.decreases is None
        self.oblige("variant", ctx, L.and_(*[L.le(L.ZERO, t) for t in m0]), loc, "recursion measure is non-negative", inferred=inferred)
        self.oblige("variant", ctx, lex_lt(m1, m0), loc, f"recursive call to '{callee.fn.name}' decreases the measure", inferred=inferred)


def depth(x: L.Term) -> L.Term:
    """How deep an immutable structure is: every part of it is shallower."""
    return L.Fn("struct.depth", (x,), L.INT)


def measure_parts(m: ir.Expr) -> tuple[ir.Expr, ...]:
    """A list literal is a lexicographic measure, compared left to right."""
    return m.elems if isinstance(m, ir.ListLit) else (m,)


def lex_lt(a: list[L.Term], b: list[L.Term]) -> L.Term:
    #@ requires len(a) >= 1 and len(a) == len(b)
    out = L.lt(a[-1], b[-1])
    for x, y in zip(reversed(a[:-1]), reversed(b[:-1])):
        out = L.or_(L.lt(x, y), L.and_(L.eq(x, y), out))
    return out


# ---------------------------------------------------------------------------
# Language arithmetic in terms of Euclidean division


PREDICATE_FUEL = 1


def _triggerable(ts: tuple[L.Term, ...]) -> bool:
    """Can these terms be an SMT trigger (no connectives or ite inside)?"""
    return not any(isinstance(x, L.Quant) or (isinstance(x, L.App) and x.op not in ("select", "add", "sub", "field")) for t in ts for x in L.iter_terms(t))


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
    if isinstance(e, ir.Field):
        return f"{_expr_name(e.obj)}.{e.name}"
    if isinstance(e, ir.Call):
        return f"{e.func.split('.')[-1]}(...)"
    return "value"


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


def _fresh_expr(e: ir.Expr | None) -> bool:
    return isinstance(e, (ir.ListLit, ir.Call, ir.New)) or (isinstance(e, ir.Builtin) and e.name in ("slice", "dict_lit"))


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
    # Object fields the body reads are parameters of the definition too.
    g.heap_init(env)
    for key in program.def_heap_keys(ref.key):
        c = env[key]
        assert isinstance(c, L.Const)
        params.append(c)
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
        m = tuple(g.ev(e, mctx) for e in measure_parts(measure))
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
    if s == L.OPAQUE:
        return L.Const("opaque!default", L.OPAQUE)
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
        v: Val = pack(p.ty, [next(it) for _ in components(p.ty)])
        env[p.name] = v
        args.append(v)
    for key in program.def_heap_keys(ref.key):
        env[key] = next(it)
    call = L.Fn(fundef.name, fundef.params, fundef.sort)
    base: list[L.Term] = []
    ctx = Ctx(base=base, env=env, module=ref.module, spec=True, quiet=True)
    # The body was proved assuming the invariants of the objects passed in,
    # so the lemma assumes them too (over any heap maps they read beyond the
    # definition's own, quantified as well).
    extra: list[L.Const] = []
    hyps = []
    for p in ref.fn.params:
        if isinstance(p.ty, ir.TClass) and not (g.is_init and p.name == "self"):
            for c in program.mro(p.ty.name):
                for f, _ in program.classes[c].fields:
                    for key, srt in g.heap_keys(c, f):
                        if key not in env:
                            env[key] = L.Const(f"{key[1:]}!lemma", srt)
                            extra.append(env[key])  # type: ignore[arg-type]
            try:
                hyps += [t for _, t in g.class_invariants(p.ty.name, env[p.name], env, base)]  # type: ignore[arg-type]
            except (VCError, KeyError):
                return []  # without its invariant hypotheses the lemma could be false
    hyps += [g.ev(r.expr, ctx) for r in ref.fn.requires]
    for p in ref.fn.params:
        v = env[p.name]
        if isinstance(v, ListVal):
            hyps.append(L.le(L.ZERO, v.len))
    ectx = Ctx(base=base, env=env, module=ref.module, old_env=env, result=call, spec=True, quiet=True)
    goals = [g.ev(en.expr, ectx) for en in ref.fn.ensures]
    formula = L.forall(tuple(fundef.params) + tuple(extra), L.implies(L.and_(*base, *hyps), L.and_(*goals)))
    return [L.Axiom(f"{fundef.name}_spec", formula, about=ref.key, doc=f"@ensures of {ref.fn.name}")]
