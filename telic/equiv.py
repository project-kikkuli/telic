"""Cross-implementation equivalence: ``@mirrors``.

Business rules get implemented twice -- once on the server, once in the UI --
and drift apart one "harmless" port at a time. A function that declares

    //@ mirrors ../server/pricing.py::quote

must return the same result as the function it mirrors for every input both
accept. telic proves it for loop-free code by running both bodies through the
same symbolic executor (so Python's ``//`` and JavaScript's ``Math.trunc``
really are different operators) and asking Z3 for a disagreement. A
disagreement is then executed in both real runtimes before it is reported.
Code with loops is proved equal from the two proved contracts when they pin
the result, and otherwise compared by differential testing, labelled as such.
"""

from __future__ import annotations

import itertools
import os
import random
from dataclasses import dataclass, field
from fractions import Fraction
from typing import Any

from . import ir
from . import logic as L
from .program import FuncRef, Program
from .replay import encode_value, format_value, run_python, run_typescript, ts_contracts, type_desc
from .smt import RLIMIT, Theory, solve
from .vcgen import Ctx, ListVal, Obligation, State, Val, VCError, VCGen, sort_of


@dataclass
class MirrorReport:
    a: FuncRef
    b: FuncRef
    loc: ir.Loc
    aims: list[str]
    status: str  # proved | refuted | vacuous | open
    method: str = ""  # smt | testing
    witness: dict[str, Any] | None = None
    reason: str = ""
    explanation: str = ""
    verdicts: list[str] = field(default_factory=list)

    def to_json(self) -> dict[str, Any]:
        return {
            "a": self.a.key,
            "b": self.b.key,
            "status": self.status,
            "method": self.method,
            "witness": self.witness,
            "reason": self.reason,
            "explanation": self.explanation,
            "aims": self.aims,
        }


class Incomparable(Exception):
    pass


# ---------------------------------------------------------------------------


def _shared_inputs(a: ir.Function, b: ir.Function) -> tuple[dict[str, Val], dict[str, Val], list[tuple[str, Val]], list[str]]:
    if len(a.params) != len(b.params):
        raise Incomparable(f"{a.name} takes {len(a.params)} parameters, {b.name} takes {len(b.params)}")
    ina: dict[str, Val] = {}
    inb: dict[str, Val] = {}
    shown: list[tuple[str, Val]] = []
    notes: list[str] = []
    for pa, pb in zip(a.params, b.params):
        ta, tb = pa.ty, pb.ty
        name = f"in.{pa.name}"
        if ta == tb:
            if isinstance(ta, ir.TList):
                v: Val = ListVal(L.Const(f"{name}.arr", sort_of(ta)), L.ZERO, L.Const(f"{name}.len", L.INT), ta)
            else:
                v = L.Const(name, sort_of(ta))
            ina[pa.name] = v
            inb[pb.name] = v
        elif {type(ta), type(tb)} == {ir.TInt, ir.TReal}:
            v = L.Const(name, L.INT)
            ina[pa.name] = v if isinstance(ta, ir.TInt) else L.to_real(v)
            inb[pb.name] = v if isinstance(tb, ir.TInt) else L.to_real(v)
            notes.append(f"'{pa.name}' is compared on integers ({a.name} takes {ta}, {b.name} takes {tb})")
        else:
            raise Incomparable(f"parameter '{pa.name}' is {ta} in {a.name} but {tb} in {b.name}")
        shown.append((pa.name, ina[pa.name] if isinstance(ta, ir.TInt) or ta == tb else v))
    return ina, inb, shown, notes


def _has_str(ty: ir.Type) -> bool:
    if isinstance(ty, ir.TStr):
        return True
    if isinstance(ty, ir.TList):
        return _has_str(ty.elem)
    if isinstance(ty, ir.TOption):
        return _has_str(ty.inner)
    if isinstance(ty, ir.TDict):
        return _has_str(ty.key) or _has_str(ty.val)
    if isinstance(ty, ir.TRecord):
        return any(_has_str(t) for _, t in ty.fields)
    return False


def _strings_differ(a: FuncRef, b: FuncRef) -> str:
    """One symbolic string means code points in Python, UTF-16 code units in
    JavaScript and bytes in Rust, so across languages strings are only tested."""
    if a.module.language != b.module.language and any(_has_str(t) for t in [p.ty for p in a.fn.params + b.fn.params] + [a.fn.ret, b.fn.ret]):
        return f"strings are encoded differently in {a.module.language} and {b.module.language}"
    return ""


def _has_loops(fn: ir.Function) -> bool:
    return any(isinstance(s, (ir.While, ir.ForRange, ir.ForEach)) for s in ir.walk_stmts(fn.body))


def result_term(program: Program, ref: FuncRef, inputs: dict[str, Val], side: str = "a") -> tuple[L.Term, list[L.Term], L.Term, set[str], list[tuple[ir.Loc, str]]]:
    """The function's result, defining facts, exits, dependencies and
    assumptions for a loop-free symbolic run."""
    g = VCGen(program, ref, inputs=inputs)
    g.counter = itertools.count(1 if side == "a" else 1_000_000)
    g.definitional_mode = True
    env = dict(inputs)
    g.heap_init(env)  # both sides start from the same heap; a call havocs it
    g.entry = dict(env)
    rctx = Ctx(base=[], env=env, module=ref.module, spec=True, quiet=True)
    reqs = [g.ev(r.expr, rctx) for r in ref.fn.requires]
    st = State(env, [])
    st = g.block(ref.fn.body, st)
    exits = [ex for ex in g.exits if ex.value is not None]
    if not exits:
        raise Incomparable(f"'{ref.fn.name}' returns no value")
    if any(isinstance(ex.value, ListVal) for ex in exits):
        raise Incomparable("comparing list results symbolically is not supported yet")
    if not all(isinstance(ex.value, L.Term) for ex in exits):
        raise Incomparable(f"'{ref.fn.name}' returns a value telic cannot compare symbolically")
    r = L.Const(f"mirror.{side}.result", exits[0].value.sort)  # type: ignore[union-attr]
    # The run follows exactly one path, and every fact on it holds there
    # (including the definitions of symbols it made).
    paths = [L.and_(*ex.facts) for ex in exits]
    raises = L.or_(*[L.and_(*facts) for facts in g.raise_paths])
    defs = [L.or_(*paths, raises)] + [L.implies(p, L.eq(r, ex.value)) for p, ex in zip(paths, exits)]  # type: ignore[arg-type]
    return r, list(rctx.base) + reqs + defs, raises, g.deps, g.assumptions


SCALARS = (ir.TInt, ir.TReal, ir.TBool, ir.TStr)


def contract_result(program: Program, ref: FuncRef, inputs: dict[str, Val], side: str) -> tuple[Val, list[L.Term]]:
    """A result the function's proved contract allows: a fresh value, its
    preconditions over ``inputs`` and its postconditions over both."""
    g = VCGen(program, ref, inputs=inputs)
    g.counter = itertools.count(1 if side == "a" else 1_000_000)
    g.definitional_mode = True
    env = dict(inputs)
    g.heap_init(env)
    g.entry = dict(env)
    r = g.fresh(f"mirror.{side}.result", ref.fn.ret)
    ctx = Ctx(base=[], env=env, module=ref.module, spec=True, quiet=True, old_env=dict(env), result=r)
    facts = [g.ev(c.expr, ctx) for c in ref.fn.requires] + [g.ev(c.expr, ctx) for c in ref.fn.ensures]
    if isinstance(r, ListVal):
        facts.append(L.le(L.ZERO, r.len))
    return r, list(ctx.base) + facts  # type: ignore[return-value]


def mirror_lemma(program: Program, a: FuncRef, b: FuncRef) -> L.Term | None:
    """A proved mirror between two logical definitions, as a fact: on every
    input both accept, they are equal."""
    if a.key not in program.logic_names or b.key not in program.logic_names:
        return None
    try:
        ina, inb, shown, _ = _shared_inputs(a.fn, b.fn)
    except Incomparable:
        return None
    if _strings_differ(a, b):
        return None
    if any(isinstance(v, ListVal) for _, v in shown):
        return None
    reqs: list[L.Term] = []
    apps: list[L.Term] = []
    for ref, ins in ((a, ina), (b, inb)):
        g = VCGen(program, ref, inputs=ins)
        g.definitional_mode = True
        ctx = Ctx(base=[], env=dict(ins), module=ref.module, spec=True, quiet=True)
        reqs += [g.ev(r.expr, ctx) for r in ref.fn.requires]
        if ctx.base:
            return None
        apps.append(g.apply_def(ref, [ins[p.name] for p in ref.fn.params]))
    x, y = _coerce_pair(apps[0], apps[1])
    fresh = {v: L.Const(f"eq!{a.fn.name}.{n}", v.sort) for n, v in shown}  # type: ignore[misc]
    return L.substitute(L.Quant("forall", tuple(fresh.values()), L.implies(L.and_(*reqs), L.eq(x, y)), patterns=((L.substitute(apps[0], fresh),),)), fresh)


def agree_by_contracts(program: Program, theory: Theory, a: FuncRef, b: FuncRef, ina: dict[str, Val], inb: dict[str, Val], loc: ir.Loc, timeout_ms: int, rlimit: int, lemmas: list[L.Term] = ()) -> bool:  # type: ignore[assignment]
    """Do the two proved contracts pin the same result on every input both
    accept? Only for scalar parameters (nothing to mutate) and functions
    that never raise. ``lemmas``: proved mirrors of the helpers they use."""
    if a.fn.raises or b.fn.raises or not all(isinstance(p.ty, SCALARS) for p in a.fn.params + b.fn.params):
        return False
    ra, ha = contract_result(program, a, ina, "a")
    rb, hb = contract_result(program, b, inb, "b")
    if isinstance(ra, ListVal) != isinstance(rb, ListVal):
        return False
    if isinstance(ra, ListVal) and isinstance(rb, ListVal):
        i = L.Const("mirror.i", L.INT)  # any index: free, so the goal needs no quantifier
        x, y = _coerce_pair(ra.at(i), rb.at(i))
        goal = L.and_(L.eq(ra.len, rb.len), L.implies(L.and_(L.le(L.ZERO, i), L.lt(i, ra.len)), L.eq(x, y)))
        # element-wise @ensures, instantiated at that index
        ha = ha + [L.substitute(h.body, {h.vars[0]: i}) for h in ha if isinstance(h, L.Quant) and h.kind == "forall" and len(h.vars) == 1]
        hb = hb + [L.substitute(h.body, {h.vars[0]: i}) for h in hb if isinstance(h, L.Quant) and h.kind == "forall" and len(h.vars) == 1]
    else:
        x, y = _coerce_pair(ra, rb)  # type: ignore[arg-type]
        goal = L.eq(x, y)
    ob = Obligation(id=f"{a.fn.name}~{b.fn.name}/contracts", func=a.key, kind="mirror", loc=loc, site=None, message=f"the contracts of {a.fn.name} and {b.fn.name} pin the same result", hyps=ha + hb + list(lemmas), goal=goal, inputs=[])
    return solve(ob, theory, timeout_ms, rlimit).status == "proved"


def _coerce_pair(ra: L.Term, rb: L.Term) -> tuple[L.Term, L.Term]:
    if ra.sort == L.INT and rb.sort == L.REAL:
        return L.to_real(ra), rb
    if ra.sort == L.REAL and rb.sort == L.INT:
        return ra, L.to_real(rb)
    return ra, rb


# ---------------------------------------------------------------------------
# Running the real implementations


def _full(root: str, path: str) -> str:
    return path if os.path.isabs(path) else os.path.join(root, path)


def run_one(ref: FuncRef, root: str, args: list[Any]) -> dict[str, Any]:
    path = _full(root, ref.module.path)
    if ref.module.language == "swift":
        from .frontend.swift_replay import run_swift_batch

        (out,) = run_swift_batch(path, ref.fn, [_model(ref.fn, args)])
        return _swift_result(out)
    if ref.module.language == "rust":
        from .frontend.rust_replay import run_rust

        return run_rust(path, ref.fn, _model(ref.fn, args)) or {"harness_error": "rustc cannot run this function"}
    if ref.module.language == "python":
        return run_python(path, ref.fn.name, args)
    return run_typescript(path, ref.fn.name, args, extra={"contracts": ts_contracts(ref.module)})


def _model(fn: ir.Function, args: list[Any]) -> dict[str, Any]:
    """Encoded arguments as a model (what the Swift harness reads)."""
    return {p.name: _decode_arg(a) for p, a in zip(fn.params, args)}


def _decode_arg(a: Any) -> Any:
    if isinstance(a, dict) and "__real__" in a:
        return Fraction(*a["__real__"])
    if isinstance(a, dict) and "__float__" in a:
        return float(a["__float__"])
    if isinstance(a, list):
        return [_decode_arg(x) for x in a]
    return a


def _swift_result(out: dict[str, Any]) -> dict[str, Any]:
    if out.get("rejected"):
        return {"rejected": True}
    if "value" in out and "violation" not in out:
        return {"ok": True, "value": out["value"], "returned_repr": out.get("returned_repr", "")}
    return {**out, "ok": False}


def _rust_result(out: dict[str, Any]) -> dict[str, Any]:
    """Rust reports a returned value as its Debug text."""
    if "returned_repr" in out and "violation" not in out:
        return {"ok": True, "value": out["returned_repr"], "returned_repr": out["returned_repr"]}
    return _swift_result(out)


def run_batch(ref: FuncRef, root: str, batch: list[list[Any]]) -> list[dict[str, Any]]:
    path = _full(root, ref.module.path)
    if ref.module.language == "swift":
        from .frontend.swift_replay import run_swift_batch

        return [_swift_result(o) for o in run_swift_batch(path, ref.fn, [_model(ref.fn, a) for a in batch])]
    if ref.module.language == "rust":
        from .frontend.rust_replay import run_rust_batch

        return [_rust_result(o) for o in run_rust_batch(path, ref.fn, [_model(ref.fn, a) for a in batch])]
    extra = {"batch": batch}
    if ref.module.language == "python":
        out = run_python(path, ref.fn.name, [], timeout=30, extra=extra)
    else:
        extra["contracts"] = ts_contracts(ref.module)
        out = run_typescript(path, ref.fn.name, [], timeout=30, extra=extra)
    return out.get("results") or [{"error": out.get("harness_error", "timeout" if out.get("timeout") else "no result")}] * len(batch)


def same_value(x: Any, y: Any) -> bool:
    if isinstance(x, bool) or isinstance(y, bool):
        return x == y
    if isinstance(x, (int, float)) and isinstance(y, (int, float)):
        return float(x) == float(y)
    if isinstance(x, list) and isinstance(y, list):
        return len(x) == len(y) and all(same_value(a, b) for a, b in zip(x, y))
    if isinstance(x, dict) and isinstance(y, dict):
        return x.keys() == y.keys() and all(same_value(x[k], y[k]) for k in x)
    return x == y


def _value_of(out: dict[str, Any]) -> tuple[bool, Any, str]:
    if "value" in out:
        return True, out["value"], out.get("returned_repr", str(out["value"]))
    if "returned_repr" in out:
        return True, out["returned_repr"], out["returned_repr"]
    if "violation" in out:
        return False, None, f"@{out['violation']} {out.get('text', '')} failed"
    if "crash" in out:
        return False, None, f"{out['crash']}: {out.get('msg', '')}"
    return False, None, out.get("harness_error", "no result")


def gen_value(ty: ir.Type, rnd: random.Random) -> Any:
    if isinstance(ty, ir.TInt):
        r = rnd.random()
        if r < 0.5:
            return rnd.choice([0, 1, -1, 2, 3, 5, 7, 10, 50, 99, 100, 101, 150, 250, -3])
        return rnd.randint(-1000, 1000)
    if isinstance(ty, ir.TReal):
        return Fraction(rnd.randint(-2000, 2000), rnd.choice([1, 2, 4, 10, 100]))
    if isinstance(ty, ir.TBool):
        return rnd.random() < 0.5
    if isinstance(ty, ir.TStr):
        return rnd.choice(["", "a", "b", "x", "\u00e9", "\ue000", "\U0001f600"])
    if isinstance(ty, ir.TList):
        return [gen_value(ty.elem, rnd) for _ in range(rnd.choice([0, 1, 2, 3, 4, 6]))]
    if isinstance(ty, ir.TRecord):
        return {n: gen_value(t, rnd) for n, t in ty.fields}
    return None


# ---------------------------------------------------------------------------


OP_NOTES = [
    ({"round_even"}, {"round_up"}, "Python's round() rounds halves to even (banker's rounding); JavaScript's Math.round rounds halves up"),
    ({"floordiv"}, {"trunc"}, "Python's // rounds toward negative infinity; Math.trunc(a / b) rounds toward zero"),
    ({"fmod"}, {"tmod"}, "Python's % takes the sign of the divisor; JavaScript's % takes the sign of the dividend"),
    ({"floor"}, {"trunc"}, "floor rounds toward negative infinity; trunc rounds toward zero"),
]


def _ops(fn: ir.Function) -> set[str]:
    out: set[str] = set()
    exprs: list[ir.Expr] = []
    for s in ir.walk_stmts(fn.body):
        exprs.extend(ir.stmt_exprs(s))
    for e in exprs:
        for x in ir.walk_expr(e):
            if isinstance(x, ir.Binary):
                out.add(x.op)
            elif isinstance(x, ir.Builtin):
                out.add(x.name)
    return out


def explain_difference(a: ir.Function, b: ir.Function, notes: list[str]) -> str:
    oa, ob = _ops(a), _ops(b)
    for xa, xb, text in OP_NOTES:
        if (xa & oa and xb & ob) or (xa & ob and xb & oa):
            return text
    return notes[0] if notes else ""


def check_pair(program: Program, theory: Theory, a: FuncRef, b: FuncRef, root: str, loc: ir.Loc, timeout_ms: int = 60000, rlimit: int = RLIMIT, n_tests: int = 300, aims: list[str] | None = None, proved: set[str] | None = None, lemmas: list[L.Term] = ()) -> MirrorReport:  # type: ignore[assignment]
    """``aims``: the tags on the ``@mirrors`` line; untagged, the mirror
    serves every aim either function cites. ``proved``: functions whose
    every obligation is proved, whose contracts may stand in for them."""
    rep = MirrorReport(a, b, loc, aims or sorted(set(a.fn.aims) | set(b.fn.aims)), "open", verdicts=["mirror"])
    try:
        ina, inb, shown, notes = _shared_inputs(a.fn, b.fn)
    except Incomparable as e:
        rep.reason = str(e)
        return rep
    rep.explanation = explain_difference(a.fn, b.fn, notes)
    rep.reason = _strings_differ(a, b)
    symbolic = not rep.reason
    if symbolic and not _has_loops(a.fn) and not _has_loops(b.fn) and not a.fn.unsupported and not b.fn.unsupported:
        try:
            ra, reqa, xa, depsa, assuma = result_term(program, a, ina, "a")
            rb, reqb, xb, depsb, assumb = result_term(program, b, inb, "b")
            unproved = depsa | depsb
            if assuma or assumb or (proved is None and unproved) or (proved is not None and not unproved <= proved):
                raise Incomparable("symbolic comparison depends on unchecked assumptions or functions without proved evidence")
            ra, rb = _coerce_pair(ra, rb)
            hyps = reqa + reqb
            for _, v in shown:
                if isinstance(v, ListVal):
                    hyps.append(L.le(L.ZERO, v.len))
            ob = Obligation(
                id=f"{a.fn.name}~{b.fn.name}",
                func=a.key,
                kind="mirror",
                loc=loc,
                site=None,
                message=f"{a.fn.name} and {b.fn.name} agree",
                hyps=hyps,
                # same outcome: both raise, or neither does and the values agree
                goal=L.and_(L.eq(xa, xb), L.implies(L.not_(xa), L.eq(ra, rb))),
                inputs=shown,
            )
            res = solve(ob, theory, timeout_ms, rlimit)
            rep.method = "smt"
            if res.status == "proved":
                rep.status = "proved"
                if hyps:
                    probe = Obligation(id=f"{ob.id}/vacuity", func=a.key, kind="vacuity", loc=loc, site=None, message="some input satisfies both", hyps=hyps, goal=L.FALSE)
                    if solve(probe, theory, timeout_ms, rlimit).status == "proved":
                        rep.status = "vacuous"
                        rep.reason = f"no input satisfies the @requires of both {a.fn.name} and {b.fn.name}, so they never run on the same input; align the preconditions"
                return rep
            if res.status == "refuted":
                args_a = [encode_value(res.model.get(p.name), p.ty) for p in a.fn.params]
                args_b = [encode_value(res.model.get(pa.name), pb.ty) for pa, pb in zip(a.fn.params, b.fn.params)]
                return _witness(rep, a, b, root, args_a, args_b, from_solver=True)
            rep.reason = f"solver: {res.reason}"
        except (Incomparable, VCError) as e:
            rep.reason = str(e)
    if symbolic and proved is not None and a.key in proved and b.key in proved:
        try:
            if agree_by_contracts(program, theory, a, b, ina, inb, loc, timeout_ms, rlimit, lemmas):
                rep.status, rep.method, rep.reason = "proved", "contracts", ""
                return rep
        except (Incomparable, VCError):
            pass
    # Differential testing (loops, or the solver gave up).
    rnd = random.Random(0x7E11C)
    batch_a, batch_b = [], []
    for _ in range(n_tests):
        vals = [gen_value(p.ty if not ({type(p.ty), type(q.ty)} == {ir.TInt, ir.TReal}) else ir.INT, rnd) for p, q in zip(a.fn.params, b.fn.params)]
        batch_a.append([encode_value(v, p.ty) for v, p in zip(vals, a.fn.params)])
        batch_b.append([encode_value(v, q.ty) for v, q in zip(vals, b.fn.params)])
    ra_out = run_batch(a, root, batch_a)
    rb_out = run_batch(b, root, batch_b)
    rep.method = "testing"
    compared = 0
    for xa, xb, oa, ob_ in zip(batch_a, batch_b, ra_out, rb_out):
        if oa.get("rejected") or ob_.get("rejected"):
            continue
        compared += 1
        if oa.get("ok") and ob_.get("ok") and same_value(oa["value"], ob_["value"]):
            continue
        if not oa.get("ok") and not ob_.get("ok"):
            continue
        return _witness(rep, a, b, root, xa, xb, from_solver=False)
    rep.status = "open"
    rep.reason = (rep.reason + "; " if rep.reason else "") + f"agreed on {compared} random inputs (testing, not proof)"
    return rep


def _witness(rep: MirrorReport, a: FuncRef, b: FuncRef, root: str, args_a: list[Any], args_b: list[Any], from_solver: bool) -> MirrorReport:
    oa = run_one(a, root, args_a)
    ob = run_one(b, root, args_b)
    oka, va, sa = _value_of(oa)
    okb, vb, sb = _value_of(ob)
    la, lb = a.module.language, b.module.language
    args_text = ", ".join(f"{p.name}={format_value(v, p.ty, la)}" for p, v in zip(a.fn.params, args_a))
    ran = all("harness_error" not in o and not o.get("timeout") for o in (oa, ob))
    differ = ran and not (oka and okb and same_value(va, vb))
    rep.witness = {
        "args_text": args_text,
        "a_text": f"{a.fn.name}(...) → {sa}",
        "b_text": f"{b.fn.name}(...) → {sb}",
        "replay": {
            "ran": ran,
            "confirmed": differ,
            "summary": f"ran both: {la} returned {sa}, {lb} returned {sb}" if differ else f"ran both: both returned {sa} (the solver's model disagrees with the runtimes)" if ran else f"could not run both: {sa if 'harness_error' in oa or oa.get('timeout') else sb}",
        },
    }
    rep.status = "refuted" if differ else "open"
    if not from_solver:
        rep.method = "testing"
    if not differ:
        rep.reason = "the solver's disagreement did not reproduce when run" if ran else rep.witness["replay"]["summary"]
    return rep


def resolve_mirror(program: Program, owner: FuncRef, spec: str) -> FuncRef | None:
    if "::" not in spec:
        return None
    rel, name = spec.rsplit("::", 1)
    base = os.path.dirname(owner.module.path)
    target = os.path.normpath(os.path.join(base, rel))
    for m in program.modules:
        if os.path.normpath(m.path) == target and name in m.functions:
            return FuncRef(m, m.functions[name])
    return None


def mirror_targets(modules: list[ir.Module]) -> list[str]:
    out = []
    for m in modules:
        for f in m.functions.values():
            for spec, _, _ in f.mirrors:
                if "::" in spec:
                    rel = spec.rsplit("::", 1)[0]
                    out.append(os.path.normpath(os.path.join(os.path.dirname(m.path), rel)))
    return out


def check_mirrors(program: Program, theory: Theory, opts, root: str | None = None, proved: set[str] | None = None) -> list[MirrorReport]:
    root = root or getattr(program, "root", os.getcwd())
    out: list[MirrorReport] = []
    pairs = []
    for m in program.modules:
        for f in m.functions.values():
            if opts.only and f.name not in opts.only:
                continue
            for spec, loc, tags in f.mirrors:
                owner = FuncRef(m, f)
                target = resolve_mirror(program, owner, spec)
                if target is None:
                    rep = MirrorReport(owner, owner, loc, list(tags or f.aims), "open", verdicts=["mirror"])
                    rep.reason = f"cannot find '{spec}' (path is relative to {m.path}; the file must be checkable)"
                    out.append(rep)
                    continue
                pairs.append((target, owner, loc, tags))
    # Loop-free pairs first: once proved, a pair of helpers is a lemma for
    # the mirrors of functions that use them.
    pairs.sort(key=lambda p: _has_loops(p[0].fn) or _has_loops(p[1].fn))
    lemmas: list[L.Term] = []
    for target, owner, loc, tags in pairs:
        rep = check_pair(program, theory, target, owner, root, loc, opts.timeout_ms, opts.rlimit, aims=list(tags), proved=proved, lemmas=lemmas)
        out.append(rep)
        if rep.status == "proved":
            lemma = mirror_lemma(program, target, owner)
            if lemma is not None:
                lemmas.append(lemma)
    return out
