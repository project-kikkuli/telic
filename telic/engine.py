"""The native engine (core/, OxCaml): VC generation and solving outside Python.

``telic check --engine ox`` sends the program, what the Python side knows
about it (call resolution, mutation, pure definitions, inferred invariants)
and the theory to ``telic-core``, which generates the obligations of each
function and solves them on every core, each worker driving its own z3. The
answers come back as full obligations (formulas included), so replay, Lean
and explain work as usual. Functions the engine does not model yet come back
as "fallback" and are checked by the Python core.
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
from fractions import Fraction
from pathlib import Path
from typing import Any

from . import ir
from . import irjson
from . import logic as L
from .jobs import take as take_jobs
from .program import FuncRef, Program
from .smt import solve
from .vcgen import ListVal, Obligation, Options, VCGen

CORE_DIR = Path(__file__).resolve().parent.parent / "core"


def binary() -> str | None:
    env = os.environ.get("TELIC_CORE")
    if env and os.path.exists(env):
        return env
    local = CORE_DIR / "telic-core"
    if local.exists():
        return str(local)
    return shutil.which("telic-core")


def _calls(fn: ir.Function, extra: list[ir.Clause]) -> set[str]:
    names: set[str] = set()
    exprs: list[ir.Expr] = []
    for s in ir.walk_stmts(fn.body):
        exprs.extend(ir.stmt_exprs(s))
        if isinstance(s, (ir.While, ir.ForRange, ir.ForEach)):
            exprs.extend(c.expr for c in s.invariants)
            if isinstance(s, ir.While) and s.decreases is not None:
                exprs.append(s.decreases.expr)
        if isinstance(s, (ir.AssertStmt, ir.AssumeStmt)):
            exprs.append(s.clause.expr)
    for c in fn.requires + fn.ensures + fn.raises + ([fn.decreases] if fn.decreases else []) + extra:
        exprs.append(c.expr)
    for e in exprs:
        for sub in ir.walk_expr(e):
            if isinstance(sub, ir.Call):
                names.add(sub.func)
    return names


def request(program: Program, theory, tasks: list[tuple[FuncRef, Options]], timeout_ms: int, jobs: int | None) -> tuple[dict[str, Any], irjson.TermWriter]:
    extra_by_key = {ref.key: [c for cs in opts.extra_invariants.values() for c in cs] for ref, opts in tasks}
    req, tw = _base(program, theory, extra_by_key, timeout_ms, jobs)
    req["tasks"] = [
        {
            "key": ref.key,
            "options": {
                "extra_invariants": {str(line): [irjson.clause(c) for c in cs] for line, cs in opts.extra_invariants.items()},
                "variants": {str(line): irjson.expr(e) for line, e in opts.variants.items()},
                "measures": {k: irjson.expr(e) for k, e in opts.measures.items()},
            },
        }
        for ref, opts in tasks
    ]
    return req, tw


def _base(program: Program, theory, extra_by_key: dict[str, list[ir.Clause]], timeout_ms: int, jobs: int | None) -> tuple[dict[str, Any], irjson.TermWriter]:
    """The program, what the Python side knows about it, and the theory."""
    tw = irjson.TermWriter()
    fundefs = []
    for name, fd in theory.fundefs.items():
        fundefs.append({"name": name, "params": [tw.term(p) for p in fd.params], "body": tw.term(fd.body) if fd.body is not None else None, "sort": tw.term(L.Const("sort!", fd.sort))})
    axioms = [{"name": a.name, "formula": tw.term(a.formula), "about": a.about, "symbol": a.symbol} for a in theory.axioms]
    # Every name any module can call, resolved from every module: the engine
    # resolves callee contracts and class invariants where they live.
    names: set[str] = set()
    for key, ref in program.funcs.items():
        names |= _calls(ref.fn, extra_by_key.get(key, []))
    for decl in program.classes.values():
        for c in decl.invariants:
            names |= {x.func for x in ir.walk_expr(c.expr) if isinstance(x, ir.Call)}
    for cname in program.classes:
        names |= {f"{cname}.__init__", f"{cname}.__post_init__"}
    resolve_tbl: dict[str, dict[str, str]] = {}
    for m in program.modules:
        tbl = resolve_tbl.setdefault(m.path, {})
        for name in sorted(names):
            tgt = program.resolve(m, name)
            if tgt is not None:
                tbl[name] = tgt.key

    def member(cname: str, meth: str) -> str | None:
        tgt = program.member(cname, meth)
        return tgt.key if tgt is not None else None

    classes = [
        {
            "name": cname,
            "module": program.class_module[cname].path,
            "fields": [[f, irjson.ty(t)] for f, t in decl.fields],
            "invariants": [irjson.clause(c) for c in decl.invariants],
            "bases": list(decl.bases),
            "owner": dict(decl.owner),
            "init": member(cname, "__init__"),
            "post_init": member(cname, "__post_init__"),
        }
        for cname, decl in program.classes.items()
    ]
    info: dict[str, Any] = {}
    for key, ref in program.funcs.items():
        resolve = {}
        for name in _calls(ref.fn, extra_by_key.get(key, [])):
            tgt = program.resolve(ref.module, name)
            if tgt is not None:
                resolve[name] = tgt.key
        info[key] = {
            "mutated": sorted(program.mutated.get(key, ())),
            "appends": sorted(program.appends.get(key, ())),
            "definitional": key in program.definitional,
            "logic_name": program.logic_names.get(key, ref.fn.name),
            "scc": sorted(k for k in program.funcs if k != key and program.same_scc(key, k)),
            "recursive": key in program.recursive,
            "termination": program.needs_termination(key),
            "resolve": resolve,
            "untrusted": sorted([c, i] for c, i in program.untrusted.get(key, ())),
        }
    req = {
        "modules": [irjson.module(m) for m in program.modules],
        "program": info,
        "classes": classes,
        "resolve": resolve_tbl,
        "heap_writes": {k: {cf: sorted(ts) for cf, ts in w.items()} for k, w in program.heap_writes.items()},
        "allocates": sorted(program.allocates),
        "def_heap": {k: program.def_heap_keys(k) for k in program.definitional},
        "theory": {**tw.dump(), "fundefs": fundefs, "axioms": axioms},
        "timeout_ms": timeout_ms,
        "jobs": jobs or 0,
    }
    return req, tw


def _call(req: dict[str, Any]) -> dict[str, Any]:
    exe = binary()
    assert exe is not None
    with take_jobs(req["jobs"] or None) as workers:
        req["jobs"] = workers
        p = subprocess.run([exe], input=json.dumps(req), capture_output=True, text=True)
    if p.returncode != 0:
        raise RuntimeError(f"telic-core failed: {p.stderr.strip()[-800:]}")
    if p.stderr and os.environ.get("TELIC_CORE_DEBUG"):
        print(p.stderr, end="", file=sys.stderr)
    return json.loads(p.stdout)


def infer(program: Program, theory, refs: list[FuncRef], timeout_ms: int, jobs: int | None) -> dict[str, Any]:
    """Houdini invariants, loop variants and recursion measures for ``refs``,
    from the same candidates ``telic.infer`` proposes. Returns key ->
    Inferred, or None where the engine could not decide (the caller infers
    those in Python)."""
    from .infer import Inferred, invariant_candidates, loop_sites, measure_candidates, variant_candidates
    from .render_expr import render

    if binary() is None or not refs:
        return {}
    cands: dict[str, tuple[dict[int, list[ir.Clause]], dict[int, list[ir.Expr]], list[ir.Expr]]] = {}
    for ref in refs:
        fn = ref.fn
        sites = loop_sites(fn.body)
        inv = {s.stmt.loc.line: cs for s in sites if (cs := invariant_candidates(fn, s))}
        var = {s.stmt.loc.line: vs for s in sites if isinstance(s.stmt, ir.While) and s.stmt.decreases is None and (vs := variant_candidates(fn, s.stmt))}
        meas = measure_candidates(fn) if ref.key in program.recursive and fn.decreases is None else []
        cands[ref.key] = (inv, var, meas)
    extra = {k: [c for cs in inv.values() for c in cs] for k, (inv, _, _) in cands.items()}
    req, _ = _base(program, theory, extra, timeout_ms, jobs)
    req["mode"] = "infer"
    req["tasks"] = [
        {
            "key": k,
            "invariants": {str(l): [irjson.clause(c) for c in cs] for l, cs in inv.items()},
            "variants": {str(l): [irjson.expr(e) for e in vs] for l, vs in var.items()},
            "measures": [irjson.expr(e) for e in meas],
        }
        for k, (inv, var, meas) in cands.items()
    ]
    ans = _call(req)
    out: dict[str, Any] = {}
    for r in ans["results"]:
        key = r["key"]
        if r["status"] != "ok":
            out[key] = None
            continue
        inv, var, meas = cands[key]
        res = Inferred()
        res.invariants = {int(l): [inv[int(l)][i] for i in idx] for l, idx in r["invariants"].items() if idx}
        res.options.extra_invariants = res.invariants
        for l, i in r["variants"].items():
            res.options.variants[int(l)] = var[int(l)][i]
            res.variants[int(l)] = render(var[int(l)][i])
        if r["measure"] is not None:
            res.options.measures[key] = meas[r["measure"]]
            res.measure = render(meas[r["measure"]])
        res.solver_calls = r["solver_calls"]
        out[key] = res
    return out


def _value(v: Any) -> Any:
    """Engine JSON values -> the Python values smt.decode produces."""
    if isinstance(v, dict) and "__real__" in v:
        n, d = v["__real__"]
        return Fraction(n, d)
    if isinstance(v, list):
        return [_value(x) for x in v]
    if isinstance(v, dict) and "__opaque__" not in v:
        return {k: _value(x) for k, x in v.items()}
    return v


def run(program: Program, theory, tasks: list[tuple[FuncRef, Options]], timeout_ms: int, jobs: int | None, cached: list[str] = (), salt: str = "") -> dict[str, dict[str, Any]] | None:
    """``cached``: engine keys of obligations proved before (skipped, and
    answered 'proved' by 'cache'); every obligation comes back with its key.
    ``salt`` binds the keys to the toolchain."""
    exe = binary()
    if exe is None or not tasks:
        return None
    req, _ = request(program, theory, tasks, timeout_ms, jobs)
    req["cached"], req["salt"] = list(cached), salt
    ans = _call(req)
    reader = irjson.TermReader(ans["terms"])
    out: dict[str, dict[str, Any]] = {}
    by_key = {ref.key: (ref, opts) for ref, opts in tasks}
    # obligations can be about other functions' clauses (a callee's
    # @requires) and class invariants
    shared: dict[tuple, ir.Clause] = {}
    for other in program.funcs.values():
        shared.update(_clause_index(other.fn, Options()))
    for decl in program.classes.values():
        for c in decl.invariants:
            shared[(c.kind, c.loc.line, c.loc.col, c.text)] = c
    for r in ans["results"]:
        key = r["key"]
        if r["status"] != "ok":
            out[key] = r
            continue
        ref, opts = by_key[key]
        clauses = {**shared, **_clause_index(ref.fn, opts)}
        # Inputs are named the same in both cores; the Python side knows how
        # to show them (objects, optionals, enums), so it builds them.
        inputs = VCGen(program, ref).entry_inputs()
        plain = all(isinstance(v, (L.Term, ListVal)) for _, v in inputs)
        obs = []
        for o in r["obligations"]:
            c = o["clause"]
            clause = None
            if c is not None:
                clause = clauses.get((c["kind"], c["loc"][0], c["loc"][1], c["text"]))
            ob = Obligation(
                id=o["id"],
                func=key,
                kind=o["kind"],
                loc=ir.Loc(*o["loc"]),
                site=ir.Loc(*o["site"]) if o["site"] else None,
                message=o["message"],
                hyps=[reader.terms[i] for i in o["hyps"]],
                goal=reader.terms[o["goal"]],
                clause=clause,
                aims=tuple(o["aims"]),
                inputs=list(inputs),
                deps=set(o["deps"]),
                exclude_axioms=set(o["exclude"]),
                inferred=o["inferred"],
            )
            entry = {"ob": ob, "key": o["key"], "status": o["status"], "seconds": o["seconds"], "reason": o["reason"], "model": {k: _value(v) for k, v in o["model"].items()}, "state": {k: _value(v) for k, v in o["state"].items()}}
            if o["status"] == "refuted" and not plain:
                # Objects/optionals in the model: decode them with the Python backend.
                res = solve(ob, theory, timeout_ms)
                entry.update(status=res.status, model=res.model, state=res.state, reason=res.reason)
            obs.append(entry)
        out[key] = {"status": "ok", "obligations": obs, "assumptions": [(ir.Loc(line), text) for line, text in r["assumptions"]], "deps": set(r["deps"]), "loop_notes": [tuple(x) for x in r["loop_notes"]]}
    return out


def _clause_index(fn: ir.Function, opts: Options) -> dict[tuple, ir.Clause]:
    out: dict[tuple, ir.Clause] = {}

    def add(c: ir.Clause | None) -> None:
        if c is not None:
            out[(c.kind, c.loc.line, c.loc.col, c.text)] = c

    for c in fn.requires + fn.ensures + fn.raises:
        add(c)
    add(fn.decreases)
    for s in ir.walk_stmts(fn.body):
        if isinstance(s, (ir.While, ir.ForRange, ir.ForEach)):
            for c in s.invariants:
                add(c)
            if isinstance(s, ir.While):
                add(s.decreases)
        if isinstance(s, (ir.AssertStmt, ir.AssumeStmt)):
            add(s.clause)
    for cs in opts.extra_invariants.values():
        for c in cs:
            add(c)
    return out
