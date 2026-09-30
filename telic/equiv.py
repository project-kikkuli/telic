"""Cross-implementation equivalence: ``@mirrors``.

Business rules get implemented twice -- once on the server, once in the UI --
and drift apart one "harmless" port at a time. A function that declares

    //@ mirrors ../server/pricing.py::quote

must return the same result as the function it mirrors for every input both
accept. telic proves it for loop-free code by running both bodies through the
same symbolic executor (so Python's ``//`` and JavaScript's ``Math.trunc``
really are different operators) and asking Z3 for a disagreement. A
disagreement is then executed in both real runtimes before it is reported.
Code with loops is compared by differential testing and labelled as such.
"""

from __future__ import annotations

import os
import random
from dataclasses import dataclass, field
from fractions import Fraction
from typing import Any

from . import ir
from . import logic as L
from .program import FuncRef, Program
from .replay import encode_value, format_value, run_python, run_typescript, ts_contracts, type_desc
from .smt import Theory, solve
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


def _has_loops(fn: ir.Function) -> bool:
    return any(isinstance(s, (ir.While, ir.ForRange, ir.ForEach)) for s in ir.walk_stmts(fn.body))


def result_term(program: Program, ref: FuncRef, inputs: dict[str, Val]) -> tuple[L.Term, list[L.Term], L.Term]:
    """The function's result as one term over ``inputs`` (loop-free only),
    its preconditions over the same inputs, and the condition under which it
    raises instead of returning."""
    g = VCGen(program, ref, inputs=inputs)
    g.definitional_mode = True
    env = dict(inputs)
    g.entry = dict(env)
    rctx = Ctx(base=[], env=env, module=ref.module, spec=True, quiet=True)
    reqs = [g.ev(r.expr, rctx) for r in ref.fn.requires]
    st = State(env, [])
    st = g.block(ref.fn.body, st)
    exits = [ex for ex in g.exits if ex.value is not None]
    if not exits:
        raise Incomparable(f"'{ref.fn.name}' returns no value")
    body = exits[-1].value
    for ex in reversed(exits[:-1]):
        body = L.ite(L.and_(*ex.facts), ex.value, body)  # type: ignore[arg-type]
    if isinstance(body, ListVal):
        raise Incomparable("comparing list results symbolically is not supported yet")
    raises = L.or_(*[L.and_(*facts) for facts in g.raise_paths])
    return body, reqs, raises


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
    if ref.module.language == "python":
        return run_python(path, ref.fn.name, args)
    return run_typescript(path, ref.fn.name, args, extra={"contracts": ts_contracts(ref.module)})


def run_batch(ref: FuncRef, root: str, batch: list[list[Any]]) -> list[dict[str, Any]]:
    path = _full(root, ref.module.path)
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
        return rnd.choice(["", "a", "b", "x"])
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


def check_pair(program: Program, theory: Theory, a: FuncRef, b: FuncRef, root: str, loc: ir.Loc, timeout_ms: int = 8000, n_tests: int = 300) -> MirrorReport:
    rep = MirrorReport(a, b, loc, sorted(set(a.fn.aims) | set(b.fn.aims)), "open", verdicts=["mirror"])
    try:
        ina, inb, shown, notes = _shared_inputs(a.fn, b.fn)
    except Incomparable as e:
        rep.reason = str(e)
        return rep
    rep.explanation = explain_difference(a.fn, b.fn, notes)
    if not _has_loops(a.fn) and not _has_loops(b.fn) and not a.fn.unsupported and not b.fn.unsupported:
        try:
            ra, reqa, xa = result_term(program, a, ina)
            rb, reqb, xb = result_term(program, b, inb)
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
            res = solve(ob, theory, timeout_ms)
            rep.method = "smt"
            if res.status == "proved":
                rep.status = "proved"
                if hyps:
                    probe = Obligation(id=f"{ob.id}/vacuity", func=a.key, kind="vacuity", loc=loc, site=None, message="some input satisfies both", hyps=hyps, goal=L.FALSE)
                    if solve(probe, theory, timeout_ms).status == "proved":
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
    differ = not (oka and okb and same_value(va, vb))
    rep.witness = {
        "args_text": args_text,
        "a_text": f"{a.fn.name}(...) → {sa}",
        "b_text": f"{b.fn.name}(...) → {sb}",
        "replay": {
            "confirmed": differ,
            "summary": f"ran both: {la} returned {sa}, {lb} returned {sb}" if differ else f"ran both: both returned {sa} (the solver's model disagrees with the runtimes)",
        },
    }
    rep.status = "refuted" if differ else "open"
    if not from_solver:
        rep.method = "testing"
    if not differ:
        rep.reason = "the solver's disagreement did not reproduce when run"
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
            for spec, _ in f.mirrors:
                if "::" in spec:
                    rel = spec.rsplit("::", 1)[0]
                    out.append(os.path.normpath(os.path.join(os.path.dirname(m.path), rel)))
    return out


def check_mirrors(program: Program, theory: Theory, opts, root: str | None = None) -> list[MirrorReport]:
    root = root or getattr(program, "root", os.getcwd())
    out: list[MirrorReport] = []
    for m in program.modules:
        for f in m.functions.values():
            if opts.only and f.name not in opts.only:
                continue
            for spec, loc in f.mirrors:
                owner = FuncRef(m, f)
                target = resolve_mirror(program, owner, spec)
                if target is None:
                    rep = MirrorReport(owner, owner, loc, list(f.aims), "open", verdicts=["mirror"])
                    rep.reason = f"cannot find '{spec}' (path is relative to {m.path}; the file must be checkable)"
                    out.append(rep)
                    continue
                out.append(check_pair(program, theory, target, owner, root, loc, opts.timeout_ms))
    return out
