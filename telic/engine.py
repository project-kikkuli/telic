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
from fractions import Fraction
from pathlib import Path
from typing import Any

from . import ir
from . import irjson
from . import logic as L
from .program import FuncRef, Program
from .vcgen import ListVal, Obligation, Options

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
    tw = irjson.TermWriter()
    fundefs = []
    for name, fd in theory.fundefs.items():
        fundefs.append({"name": name, "params": [tw.term(p) for p in fd.params], "body": tw.term(fd.body) if fd.body is not None else None, "sort": tw.term(L.Const("sort!", fd.sort))})
    axioms = [{"name": a.name, "formula": tw.term(a.formula), "about": a.about, "symbol": a.symbol} for a in theory.axioms]
    extra_by_key: dict[str, list[ir.Clause]] = {}
    for ref, opts in tasks:
        extra_by_key[ref.key] = [c for cs in opts.extra_invariants.values() for c in cs]
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
            "resolve": resolve,
        }
    req = {
        "modules": [irjson.module(m) for m in program.modules],
        "program": info,
        "theory": {**tw.dump(), "fundefs": fundefs, "axioms": axioms},
        "tasks": [
            {
                "key": ref.key,
                "options": {
                    "extra_invariants": {str(line): [irjson.clause(c) for c in cs] for line, cs in opts.extra_invariants.items()},
                    "variants": {str(line): irjson.expr(e) for line, e in opts.variants.items()},
                    "measures": {k: irjson.expr(e) for k, e in opts.measures.items()},
                },
            }
            for ref, opts in tasks
        ],
        "timeout_ms": timeout_ms,
        "jobs": jobs or 0,
    }
    return req, tw


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


def run(program: Program, theory, tasks: list[tuple[FuncRef, Options]], timeout_ms: int, jobs: int | None) -> dict[str, dict[str, Any]] | None:
    exe = binary()
    if exe is None or not tasks:
        return None
    req, _ = request(program, theory, tasks, timeout_ms, jobs)
    p = subprocess.run([exe], input=json.dumps(req), capture_output=True, text=True)
    if p.returncode != 0:
        raise RuntimeError(f"telic-core failed: {p.stderr.strip()[-800:]}")
    ans = json.loads(p.stdout)
    reader = irjson.TermReader(ans["terms"])
    out: dict[str, dict[str, Any]] = {}
    by_key = {ref.key: (ref, opts) for ref, opts in tasks}
    for r in ans["results"]:
        key = r["key"]
        if r["status"] != "ok":
            out[key] = r
            continue
        ref, opts = by_key[key]
        clauses = _clause_index(ref.fn, opts)
        obs = []
        for o in r["obligations"]:
            inputs = []
            params = {p.name: p.ty for p in ref.fn.params}
            for name, enc in o["inputs"]:
                if enc is None:
                    continue
                if "list" in enc:
                    a, off, ln = (reader.terms[i] for i in enc["list"])
                    inputs.append((name, ListVal(a, off, ln, params[name])))  # type: ignore[arg-type]
                else:
                    inputs.append((name, reader.terms[enc["t"]]))
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
                intents=tuple(o["intents"]),
                inputs=inputs,
                deps=set(o["deps"]),
                exclude_axioms=set(o["exclude"]),
                inferred=o["inferred"],
            )
            obs.append({"ob": ob, "status": o["status"], "seconds": o["seconds"], "reason": o["reason"], "model": {k: _value(v) for k, v in o["model"].items()}, "state": {k: _value(v) for k, v in o["state"].items()}})
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
