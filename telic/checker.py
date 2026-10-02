"""The pipeline: source files in, a verdict for every obligation out."""

from __future__ import annotations

import hashlib
import json
import os
import sys
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Callable

from . import ir, irjson
from .evidence import evidence_status
from . import logic as L
from .infer import Inferred, cached_measures, infer, infer_measures, infer_rlimit
from .jobs import exit_with_parent
from .jobs import take as take_jobs
from .program import ANY, FuncRef, Program
from .render_expr import render
from .smt import RLIMIT, SmtResult, Theory, solve
from .vcgen import Obligation, VCError, VCGen, build_axioms, build_fundef

# ---------------------------------------------------------------------------
# Loading


def language_of(path: str) -> str | None:
    if path.endswith(".py"):
        return "python"
    if path.endswith((".ts", ".tsx", ".mts", ".cts")) and not path.endswith(".d.ts"):
        return "typescript"
    if path.endswith(".rs"):
        return "rust"
    if path.endswith(".swift"):
        return "swift"
    return None


def load_modules(paths: list[str], root: str | None = None) -> list[ir.Module]:
    from .frontend.aim_file import DIR, aim_files, is_aim_file

    files: list[str] = []
    for p in paths:
        if os.path.isdir(p) and os.path.basename(os.path.normpath(p)) == DIR:
            files += aim_files(p)
        elif os.path.isdir(p):
            for dirpath, dirnames, filenames in os.walk(p):
                dirnames[:] = [d for d in dirnames if not d.startswith(".") and d not in ("node_modules", "__pycache__", "venv", ".venv", "dist", "build", "target")]
                for f in sorted(filenames):
                    full = os.path.join(dirpath, f)
                    if language_of(full):
                        files.append(full)
                if DIR in dirnames:  # read, not walked: it also holds what does not belong
                    dirnames.remove(DIR)
                    files += aim_files(os.path.join(dirpath, DIR))
        else:
            files.append(p)
    root = root or os.getcwd()
    aims_files = [f for f in files if is_aim_file(f)]
    files = [f for f in files if not is_aim_file(f)]
    # Files named by '@mirrors' come along automatically.
    seen = {os.path.normpath(os.path.abspath(f)) for f in files}
    pending = list(files)
    while pending:
        f = pending.pop()
        try:
            src = Path(f).read_text()
        except OSError:
            continue
        for line in src.splitlines():
            s = line.strip()
            if s.startswith(("#@", "//@")) and " mirrors " in s + " ":
                spec = s.split("mirrors", 1)[1].strip()
                if "::" in spec:
                    tgt = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(f)), spec.rsplit("::", 1)[0]))
                    if tgt not in seen and os.path.exists(tgt):
                        seen.add(tgt)
                        files.append(tgt)
                        pending.append(tgt)
    mods: list[ir.Module] = []
    ts_files = [f for f in files if language_of(f) == "typescript"]
    ts_mods: dict[str, ir.Module] = {}
    if ts_files:
        from .frontend.typescript import lower_typescript_files

        ts_mods = lower_typescript_files(ts_files, root)
    from .frontend.python import lower_python_project, project_imports

    py_files = [f for f in files if language_of(f) == "python"]
    # Checked modules they import come along as context (declarations and
    # contracts only): a call into them uses their contracts.
    context: set[str] = set()
    todo = list(py_files)
    known = {os.path.normpath(os.path.abspath(f)) for f in py_files}
    while todo:
        f = todo.pop()
        for dep in project_imports(f, root):
            d = os.path.normpath(os.path.abspath(dep))
            if d not in known:
                known.add(d)
                context.add(d)
                py_files.append(dep)
                todo.append(dep)
    py_mods = dict(zip(py_files, lower_python_project([(os.path.relpath(f, root), Path(f).read_text()) for f in py_files]))) if py_files else {}
    for f in py_files:
        if os.path.normpath(os.path.abspath(f)) in context:
            py_mods[f].context = True
            mods.append(py_mods[f])
    swift_files = [f for f in files if language_of(f) == "swift"]
    swift_mods: dict[str, ir.Module] = {}
    if swift_files:
        from .frontend.swift import lower_swift_files

        swift_mods = lower_swift_files(swift_files, root)
    rust_seen = {os.path.normpath(os.path.abspath(f)) for f in files if language_of(f) == "rust"}
    for f in files:
        lang = language_of(f)
        if lang == "swift":
            mods.append(swift_mods[f])
        elif lang == "python":
            mods.append(py_mods[f])
        elif lang == "typescript":
            mods.append(ts_mods[f])
        elif lang == "rust":
            from .frontend.rust import lower_rust
            from .frontend.rust_crate import crate_for

            mods.append(lower_rust(os.path.relpath(f, root), Path(f).read_text(), f, root))
            # the other files of its crate come along as context: calls into them use their contracts
            for g in sorted(crate_for(f).sources):
                if g not in rust_seen:
                    rust_seen.add(g)
                    ctx = lower_rust(os.path.relpath(g, root), Path(g).read_text(), g, root)
                    ctx.context = True
                    mods.append(ctx)
    return mods + aims_modules(paths, aims_files, root)


def aims_modules(paths: list[str], named: list[str], root: str) -> list[ir.Module]:
    """The aims/<ID>.md files named or walked, plus those in the aims/
    directories of ancestors up to the root. Ancestors come as context: their
    aims are reported only where the checked code cites them."""
    from .frontend.aim_file import DIR, aim_files, lower_aim_entry

    own = {os.path.normpath(os.path.abspath(f)) for f in named}
    top = os.path.normpath(os.path.abspath(root))
    ancestors: set[str] = set()
    for p in paths:
        full = os.path.normpath(os.path.abspath(p))
        d = os.path.dirname(full)  # a walked directory's own aims/ is already named
        while d == top or d.startswith(top + os.sep):
            above = os.path.join(d, DIR)
            if os.path.isdir(above):
                ancestors.update(aim_files(above))
            if d == top:
                break
            d = os.path.dirname(d)
    # an aims/ reached through two links is read once, at the widest scope
    one: dict[str, str] = {}
    for f in sorted(own | ancestors, key=lambda f: (f.count(os.sep), f)):
        one.setdefault(os.path.realpath(f), f)
    out = []
    for f in sorted(one.values()):
        m = lower_aim_entry(os.path.relpath(f, root), f)
        m.context = f not in own
        out.append(m)
    return out


# ---------------------------------------------------------------------------
# Results


@dataclass
class Replay:
    """What happened when a counterexample was actually executed."""

    ran: bool
    confirmed: bool  # the real program misbehaved on these inputs
    summary: str  # one line, human readable
    returned: Any = None
    violation: str | None = None  # which contract / crash
    runtime: str = ""  # "python 3.11" / "node 22"
    fuzz_witness: str | None = None  # a real failing call found by random testing
    fuzz_summary: str | None = None
    fuzz_desc: str | None = None
    timed_out: bool = False  # cut short by the wall-clock safety net: decided nothing
    shrunk: str | None = None  # the same failure on a smaller input


@dataclass
class Verdict:
    ob: Obligation
    status: str  # proved | refuted | unknown
    method: str  # z3 | lean | cache | trivial
    seconds: float = 0.0
    model: dict[str, Any] = field(default_factory=dict)
    state: dict[str, Any] = field(default_factory=dict)
    reason: str = ""
    replay: Replay | None = None
    lean: Any = None  # LeanOutcome


@dataclass
class FunctionReport:
    ref: FuncRef
    status: str  # proved | refuted | vacuous | open | unsupported | trusted | error
    verdicts: list[Verdict] = field(default_factory=list)
    inferred: Inferred | None = None
    problems: list[tuple[str, ir.Loc]] = field(default_factory=list)
    assumptions: list[tuple[ir.Loc, str]] = field(default_factory=list)
    deps: set[str] = field(default_factory=set)
    open_deps: set[str] = field(default_factory=set)
    context_deps: set[str] = field(default_factory=set)
    trusted_deps: set[str] = field(default_factory=set)  # trusted contracts the proof assumes, transitively
    seconds: float = 0.0
    from_receipt: bool = False

    @property
    def fn(self) -> ir.Function:
        return self.ref.fn

    def count(self, status: str) -> int:
        return sum(1 for v in self.verdicts if v.status == status)

    @property
    def timed_out(self) -> bool:
        """A solver or a replay hit a wall-clock safety net, so this run decided nothing about it."""
        return any((v.status == "unknown" and v.reason.startswith("timeout")) or (v.replay is not None and v.replay.timed_out) for v in self.verdicts)


from .aim import AimReport  # noqa: E402  (re-exported)


@dataclass
class Report:
    modules: list[ir.Module]
    program: Program
    functions: list[FunctionReport]
    aims: list[AimReport]
    mirrors: list[Any] = field(default_factory=list)  # EquivReport
    seconds: float = 0.0
    cache_hits: int = 0
    solved: int = 0
    ui: Any = None  # ui.run.UiReport
    lifecycles: list[Any] = field(default_factory=list)  # history.LifecycleReport

    def all_verdicts(self) -> list[Verdict]:
        return [v for f in self.functions for v in f.verdicts]

    @property
    def ok(self) -> bool:
        claimed = self.program.claimed()
        claims = [f for f in self.functions if f.ref.key in claimed]
        return (
            not any(f.status in ("refuted", "error") for f in self.functions)
            and all(evidence_status(f) == "proved" for f in claims)
            and all(m.status == "proved" for m in self.mirrors)
            and all(lc.status == "proved" for lc in self.lifecycles)
            and all(i.status == "backed" for i in self.aims if i.text is not None)
            and not any(p for m in self.modules for p in m.problems)
            and (self.ui is None or not self.ui.problems and all(r.status == "proved" for r in self.ui.results))
        )


# ---------------------------------------------------------------------------
# Cache: proofs are keyed by the exact formula, so they survive any edit that
# does not change what has to be proved.


ENGINE_KEY = "ox:"  # cache keys the native engine computes for its own obligations


class ProofCache:
    VERSION = 3

    def __init__(self, path: str | None):
        self.path = path
        self.data: dict[str, dict[str, Any]] = {}
        if path and os.path.exists(path):
            try:
                raw = json.loads(Path(path).read_text())
                if raw.get("version") == self.VERSION:
                    self.data = raw.get("proofs", {})
            except (OSError, ValueError):
                self.data = {}
        self.used: set[str] = set()
        self.initial = set(self.data)

    def get(self, key: str) -> dict[str, Any] | None:
        hit = self.data.get(key)
        if hit is not None:
            self.used.add(key)
        return hit

    def fresh(self, key: str) -> bool:
        """True if the entry was produced during this run."""
        return key not in self.initial

    def put(self, key: str, value: dict[str, Any]) -> None:
        self.data[key] = value
        self.used.add(key)

    def save(self) -> None:
        if not self.path:
            return
        os.makedirs(os.path.dirname(self.path) or ".", exist_ok=True)
        Path(self.path).write_text(json.dumps({"version": self.VERSION, "proofs": self.data}, indent=1, sort_keys=True))


def make_receipt(rep: "FunctionReport") -> dict[str, Any]:
    return {
        "method": "function",
        "status": rep.status,
        "deps": sorted(rep.deps),
        "assumptions": [[loc.line, text] for loc, text in rep.assumptions],
        "obs": [
            {
                "id": v.ob.id,
                "kind": v.ob.kind,
                "loc": [v.ob.loc.line, v.ob.loc.col, v.ob.loc.end_col],
                "site": [v.ob.site.line, v.ob.site.col, v.ob.site.end_col] if v.ob.site else None,
                "message": v.ob.message,
                "aims": list(v.ob.aims),
                "method": v.reason if v.method == "cache" else v.method,
                "inferred": v.ob.inferred,
            }
            for v in rep.verdicts
        ],
    }


def restore_receipt(rep: "FunctionReport", r: dict[str, Any]) -> None:
    #@ requires "status" in r and "obs" in r
    """Rebuild a proved function's report from its receipt (no formulas are
    kept; `telic explain` recomputes them)."""
    rep.status = r["status"]
    if "deps" in r:
        rep.deps = set(r["deps"])
    if "assumptions" in r:
        rep.assumptions = [(ir.Loc(line), text) for line, text in r["assumptions"]]
    for o in r["obs"]:
        ob = Obligation(
            id=o["id"],
            func=rep.ref.key,
            kind=o["kind"],
            loc=ir.Loc(*o["loc"]),
            site=ir.Loc(*o["site"]) if o.get("site") else None,
            message=o["message"],
            hyps=[],
            goal=L.TRUE,
            aims=tuple(o.get("aims", ())),
            inferred=o.get("inferred", False),
        )
        rep.verdicts.append(Verdict(ob, "proved", "cache", 0.0, reason=o.get("method", "")))


_sidecars: dict[str, dict] = {}


def sidecar_proof_hash(ref: FuncRef, oid: str, root: str | None) -> str | None:
    from .lean import _phash, read_sidecar, sidecar_path

    path = ref.module.path
    full = os.path.join(root or os.getcwd(), path) if not os.path.isabs(path) else path
    side = sidecar_path(full)
    if side not in _sidecars:
        _sidecars[side] = read_sidecar(side)
    sp = _sidecars[side].get(oid)
    return _phash(sp.proof) if sp is not None else None


def inference_key(program: Program, key: str, rlimit: int) -> str:
    """Inference results depend on a function and everything it calls."""
    from . import __version__

    seen: set[str] = set()
    todo = [key]
    while todo:
        k = todo.pop()
        if k in seen:
            continue
        seen.add(k)
        todo.extend(program.callees.get(k, ()))
    h = hashlib.sha256(f"infer {__version__} {toolchain_id()} {key} {rlimit}".encode())
    for k in sorted(seen):
        if k not in program.funcs:
            h.update(f"{k}\n{program.units[k][3] if k in program.units else ''}".encode())
            continue
        ref = program.ref(k)
        h.update(f"{k}\n{ref.fn.source}\n{sorted(ref.module.records)}".encode())
    return "infer:" + h.hexdigest()[:24]


_TOOLCHAIN: str | None = None


def toolchain_id() -> str:
    """Evidence is only as good as the verifier that produced it, so every
    receipt is bound to the exact telic sources and Z3 version (a telic fix
    or a solver upgrade invalidates old receipts instead of trusting them)."""
    global _TOOLCHAIN
    if _TOOLCHAIN is None:
        import z3

        h = hashlib.sha256(f"z3 {z3.get_version_string()}".encode())
        pkg = Path(__file__).resolve().parent
        for f in sorted(pkg.rglob("*")):
            if f.suffix in (".py", ".mjs", ".lean") and "node_modules" not in f.parts and "demo" not in f.parts:
                h.update(f.relative_to(pkg).as_posix().encode())
                h.update(f.read_bytes())
        for f in sorted(f for f in (pkg.parent / "core").glob("*.ml") if f.name != "source_hash.ml"):
            h.update(f.name.encode())
            h.update(f.read_bytes())
        _TOOLCHAIN = h.hexdigest()[:16]
    return _TOOLCHAIN


def _lowered(program: Program, key: str) -> str:
    """A function as telic reads it, module constants inlined, without
    positions: an edit outside the function that changes its meaning changes this."""
    memo = program.__dict__.setdefault("_lowered", {})
    if key not in memo:
        memo[key] = json.dumps(irjson.without_locs(irjson.function(program.ref(key).fn)), sort_keys=True, default=str)
    return memo[key]


def _classes(program: Program) -> str:
    memo = program.__dict__.setdefault("_lowered", {})
    if "" not in memo:
        decls = {n: {"fields": [[f, irjson.ty(t)] for f, t in c.fields], "invariants": [i.text for i in c.invariants], "lifecycles": [lc.clause.text for lc in c.lifecycles], "bases": c.bases, "owner": c.owner} for n, c in program.classes.items()}
        memo[""] = json.dumps(decls, sort_keys=True, default=str)
    return memo[""]


def function_key(program: Program, key: str, root: str | None, rlimit: int) -> str:
    """A function's verdict depends on its own source, everything it calls
    (contracts, and bodies of pure callees used as definitions), the records
    and class invariants it uses, the module constants it reads, its Lean
    sidecar proofs, the toolchain and the solver's resource limit. Nothing else."""
    seen: set[str] = set()
    todo = [key]
    while todo:
        k = todo.pop()
        if k in seen:
            continue
        seen.add(k)
        todo.extend(program.callees.get(k, ()))
    h = hashlib.sha256(f"fn {toolchain_id()} {key} {rlimit}".encode())
    h.update(_classes(program).encode())
    for k in sorted(seen):
        if k not in program.funcs:
            h.update(f"{k}\n{program.units[k][3] if k in program.units else ''}".encode())
            continue
        ref = program.ref(k)
        h.update(f"{k}\n{ref.module.language}\n{ref.fn.source}\n{sorted((n, str(t)) for n, t in ref.module.records.items())}\n{_lowered(program, k)}".encode())
    ref = program.ref(key)
    from .lean import sidecar_path

    side = sidecar_path(os.path.join(root or os.getcwd(), ref.module.path))
    if os.path.exists(side):
        h.update(Path(side).read_bytes())
    return "fn:" + h.hexdigest()[:24]


def code_value_calls(program: Program, rep: "FunctionReport") -> None:
    """A call through a function value runs code no ``Call`` names: the
    proof rests on the functions it reaches, and recursion through it needs
    a termination proof telic cannot give, as it cannot see the call."""
    key = rep.ref.key
    seen: set[str] = set()

    def reach(k: str) -> None:
        if k in seen:
            return
        seen.add(k)
        if k in program.funcs:
            rep.deps.add(k)
            return
        if k in program.recursive:
            rep.deps.add(k)
        if k != ANY:
            for c in program.callees.get(k, ()):
                reach(c)

    for loc, label, keys in program.code_calls.get(key, ()):
        for k in keys:
            reach(k)
        again = sorted(k for k in keys if program.same_scc(key, k))
        if again:
            me = program.describe(key)
            how = f"may run {me} again" if key in again else f"may run {program.describe(again[0])}, which leads back to {me}"
            rep.problems.append((f"termination not proved: '{label}' {how}; no '@decreases' bounds recursion through a function value, so call it directly", loc))


def obligation_key(ob: Obligation, theory: Theory, rlimit: int) -> str:
    defs, axioms = theory.closure(list(ob.hyps) + [ob.goal], ob.exclude_axioms)
    h = hashlib.sha256(f"{toolchain_id()} {rlimit}".encode())
    h.update(L.canonical(ob.formula()).encode())
    for d in defs:
        h.update(f"def {d.name}({' '.join(L.canonical(p) for p in d.params)})={L.canonical(d.body) if d.body else '?'}".encode())
    for a in axioms:
        h.update(f"ax {L.canonical(a.formula)}".encode())
    return h.hexdigest()[:24]


# ---------------------------------------------------------------------------


@dataclass
class CheckOptions:
    rlimit: int = RLIMIT  # the proof budget, in Z3 resource units: the same on every machine
    timeout_ms: int = 60000  # a wall-clock safety net per solver stage; hitting it is "unknown (timeout)"
    replay: bool = True
    lean: bool = True
    infer: bool = True
    cache_path: str | None = None
    only: set[str] | None = None  # function names to check
    progress: Callable[[str], None] | None = None
    receipts: bool = True  # reuse whole-function verdicts for unchanged functions
    jobs: int | None = None  # solver workers (default: TELIC_JOBS, else min(4, cores // 2))
    # "ox": the native engine (core/), where it applies
    engine: str = field(default_factory=lambda: os.environ.get("TELIC_ENGINE", "python"))
    ui: bool = True  # run ui lemmas against the app (cached verdicts are shown either way)
    claims_only: bool = False
    lean_auto: bool = True
    infer_auto: bool = True


_POOL: dict[str, Any] = {}


def _pool_call(item: Any) -> Any:
    return _POOL["fn"](item)


def run_parallel(fn: Callable[[Any], Any], items: list[Any], jobs: int | None) -> list[Any]:
    """Map ``fn`` over ``items`` on the run's worker slots (fork: the function
    and what it closes over are inherited, only items and results are
    pickled)."""
    with take_jobs(jobs, len(items)) as workers:
        if workers == 1 or len(items) < 2:
            return [fn(x) for x in items]
        import multiprocessing as mp
        from concurrent.futures import ProcessPoolExecutor, ThreadPoolExecutor

        if "fork" in mp.get_all_start_methods():
            _POOL["fn"] = fn
            try:
                with ProcessPoolExecutor(max_workers=workers, mp_context=mp.get_context("fork"), initializer=exit_with_parent) as pool:
                    return list(pool.map(_pool_call, items, chunksize=max(1, len(items) // (workers * 4))))
            except Exception:  # pragma: no cover
                pass
            finally:
                _POOL.pop("fn", None)
        with ThreadPoolExecutor(max_workers=workers) as tp:
            return list(tp.map(fn, items))


def _pool_solve(ob: Obligation) -> SmtResult:
    return solve(ob, _POOL["theory"], _POOL["timeout"], _POOL["rlimit"])


def solve_all(obs: list[Obligation], theory: Theory, timeout_ms: int, rlimit: int, jobs: int | None) -> list[SmtResult]:
    """Solve independent obligations on the run's worker slots. Worker
    processes (fork) sidestep the GIL, which the Python half of each solve
    holds; threads are the fallback where fork is unavailable."""
    with take_jobs(jobs, len(obs)) as workers:
        if workers == 1 or len(obs) < 4:
            return [solve(ob, theory, timeout_ms, rlimit) for ob in obs]
        import multiprocessing as mp
        from concurrent.futures import ProcessPoolExecutor, ThreadPoolExecutor

        if "fork" in mp.get_all_start_methods():
            _POOL["theory"], _POOL["timeout"], _POOL["rlimit"] = theory, timeout_ms, rlimit
            try:
                with ProcessPoolExecutor(max_workers=workers, mp_context=mp.get_context("fork"), initializer=exit_with_parent) as pool:
                    return list(pool.map(_pool_solve, obs, chunksize=max(1, len(obs) // (workers * 4))))
            except Exception:  # pragma: no cover - e.g. a sandbox without fork
                pass
            finally:
                _POOL.clear()
        with ThreadPoolExecutor(max_workers=workers) as tp:
            return list(tp.map(lambda ob: solve(ob, theory, timeout_ms, rlimit), obs))


class Vacuity:
    """Is each function's entry state (the invariants of the objects passed
    in, then the preconditions) satisfiable? Where it is not, every
    obligation holds trivially and the function is reported ``vacuous``.
    An undecided check leaves the verdict alone."""

    def __init__(self) -> None:
        self.todo: list[tuple[tuple[FunctionReport, VCGen], Obligation, str]] = []
        self.unsat: list[tuple[FunctionReport, VCGen]] = []

    def record(self, results: list[SmtResult], cache: "ProofCache") -> None:
        for (item, _, key), res in zip(self.todo, results):
            if res.status == "proved":
                self.unsat.append(item)
                cache.put(key, {"method": "unsat"})
            elif res.status == "refuted":
                cache.put(key, {"method": "sat"})

    def explain(self, theory: Theory, opts: "CheckOptions", cache: "ProofCache") -> dict[str, str]:
        out: dict[str, str] = {}
        for rep, gen in self.unsat:
            fn = rep.fn
            classes = sorted({p.ty.name for p in fn.params if isinstance(p.ty, ir.TClass)})
            inv_unsat = False
            if gen.probes_contract:
                out[rep.ref.key] = f"its @requires and @ensures can never hold together, so every proof that uses '{fn.name}' is vacuous; fix its contract"
                continue
            if gen.lemmas and _unsat(_unsat_probe(gen, gen.lemmas), theory, opts, cache):
                preds = sorted(gen.program.funcs[k].fn.name for k in gen.deps if k in gen.program.predicates)
                out[rep.ref.key] = f"the @ensures of trusted {', '.join(preds)} cannot hold at every value '{fn.name}' applies {'it' if len(preds) == 1 else 'them'} to, so every claim about '{fn.name}' is vacuous; fix the contract"
                continue
            if gen.invariant_facts and fn.requires:
                inv_unsat = _unsat(_unsat_probe(gen, gen.invariant_facts), theory, opts, cache)
            elif gen.invariant_facts:
                inv_unsat = True
            if inv_unsat:
                why = f"the invariants of {', '.join(classes)} can never hold, so every claim about '{fn.name}' is vacuous; fix the invariant"
            elif gen.invariant_facts:
                why = f"its @requires can never hold together with the invariants of {', '.join(classes)}, so every claim about '{fn.name}' is vacuous; weaken the preconditions"
            else:
                why = f"its @requires can never hold, so every claim about '{fn.name}' is vacuous; weaken the preconditions"
            out[rep.ref.key] = why
        return out


def _unsat(ob: Obligation, theory: Theory, opts: "CheckOptions", cache: "ProofCache") -> bool:
    key = "sat:" + obligation_key(ob, theory, opts.rlimit)
    hit = cache.get(key)
    if hit is None:
        res = solve(ob, theory, opts.timeout_ms, opts.rlimit)
        hit = {"method": {"proved": "unsat", "refuted": "sat"}.get(res.status, "unknown")}
        if hit["method"] != "unknown":
            cache.put(key, hit)
    return hit.get("method") == "unsat"


def _body_lemmas(gen: VCGen) -> list[L.Term]:
    """The trusted-predicate unfoldings the body's obligations assume on top
    of the entry's: together they hold for any consistent contracts, however
    deep the unfoldings reach."""
    if gen.probes_contract:
        return []
    seen = set(gen.entry_facts)
    return [t for t in gen.lemmas if t not in seen]


def _unsat_probe(gen: VCGen, facts: list[L.Term]) -> Obligation:
    """``facts ⊢ false``: proved exactly when ``facts`` are unsatisfiable."""
    excl = {k for k in gen.program.funcs if gen.program.same_scc(gen.ref.key, k)}
    return Obligation(id=f"{gen.fn.name}/vacuity", func=gen.ref.key, kind="vacuity", loc=gen.fn.loc, site=None, message="the entry state is satisfiable", hyps=list(facts), goal=L.FALSE, exclude_axioms=excl)


def vacuity_checks(entries: list[tuple[FunctionReport, VCGen]], theory: Theory, cache: "ProofCache", rlimit: int) -> Vacuity:
    v = Vacuity()
    for rep, gen in entries:
        lemmas = _body_lemmas(gen)
        if not (gen.fn.requires or gen.invariant_facts or gen.probes_contract or lemmas):
            continue
        ob = _unsat_probe(gen, gen.entry_facts + lemmas)
        key = "sat:" + obligation_key(ob, theory, rlimit)
        hit = cache.get(key)
        if hit is None:
            v.todo.append(((rep, gen), ob, key))
        elif hit.get("method") == "unsat":
            v.unsat.append((rep, gen))
    return v


def build_theory(program: Program, measures: dict[str, ir.Expr]) -> tuple[Theory, list[tuple[str, str]]]:
    theory = Theory()
    problems: list[tuple[str, str]] = []
    for d in (L.seqsum_def(L.INT), L.seqsum_def(L.REAL), L.seqsum_def(L.FLOAT32), L.seqsum_def(L.FLOAT64), L.seqcount_def(L.INT), L.seqcount_def(L.REAL), L.seqcount_def(L.BOOL), L.seqcount_def(L.STR)):
        theory.fundefs[d.name] = d
    if sys.version_info >= (3, 12):
        for d in L.python_float_sum_defs(sys.version_info.major, sys.version_info.minor):
            theory.fundefs[d.name] = d
    for d in L.python_numeric_sum_defs(sys.version_info.major, sys.version_info.minor):
        theory.fundefs[d.name] = d
    for elem in (L.INT, L.REAL):
        theory.axioms.extend(L.theory_lemmas(elem))
    for key in sorted(program.definitional):
        ref = program.ref(key)
        m = measures.get(key) or (ref.fn.decreases.expr if ref.fn.decreases else None)
        try:
            fd = build_fundef(program, ref, m)
        except VCError as e:
            problems.append((key, str(e)))
            program.definitional.discard(key)
            continue
        theory.fundefs[fd.name] = fd
    for key in sorted(program.definitional):
        ref = program.ref(key)
        fd = theory.fundefs.get(program.logic_names[key])
        if fd is None:
            continue
        try:
            theory.axioms.extend(build_axioms(program, ref, fd))
        except VCError as e:
            problems.append((key, str(e)))
    return theory, problems


def check(paths: list[str], opts: CheckOptions | None = None, root: str | None = None) -> Report:
    from .ui.spec import scan

    opts = opts or CheckOptions()
    t0 = time.perf_counter()
    modules = load_modules(paths, root)
    rep = check_modules(modules, opts, t0=t0, root=root, ui=scan(paths, root or os.getcwd()))
    if rep.aims:
        from .aim import flag_vacuous_risk

        flag_vacuous_risk(rep, opts)
        rep.seconds = time.perf_counter() - t0
    return rep


def check_modules(modules: list[ir.Module], opts: CheckOptions, t0: float | None = None, root: str | None = None, ui: Any = None) -> Report:
    t0 = t0 or time.perf_counter()
    program = Program.build([m for m in modules if m.language != "aims"])
    selected = program.claimed() if opts.claims_only else set(program.funcs)
    _sidecars.clear()
    program.root = root or os.getcwd()  # type: ignore[attr-defined]
    cache = ProofCache(opts.cache_path)
    theory, theory_problems = build_theory(program, {})
    reports: list[FunctionReport] = []
    hits = solved = 0

    # Recursion measures must be known before definitions are built (Lean
    # needs them), so infer them first for recursive definitional functions.
    measures: dict[str, ir.Expr] = {}
    inferred: dict[str, Inferred] = {}
    todo_inf = [
        (key, ref)
        for key, ref in program.funcs.items()
        if key in selected and opts.infer and (opts.infer_auto or (cache.get(inference_key(program, key, opts.rlimit)) or {}).get("method") == "inference") and not (opts.only and ref.fn.name not in opts.only) and not (ref.fn.unsupported or ref.fn.trusted or ref.module.context)
    ]

    def infer_one(item):
        key, ref = item
        ikey = inference_key(program, key, opts.rlimit)
        try:
            return key, ikey, infer(program, ref, theory, opts.timeout_ms, infer_rlimit(opts.rlimit), cached=cache.get(ikey))
        except VCError:
            return key, None, Inferred()

    use_engine = opts.engine == "ox"
    if use_engine:
        from . import engine as _engine

        use_engine = _engine.binary() is not None
    if use_engine:
        # Cached inferences are rebuilt locally; the rest run in the engine,
        # and whatever it cannot decide falls back to Python.
        fresh = [(k, r) for k, r in todo_inf if opts.infer_auto and (cache.get(inference_key(program, k, opts.rlimit)) or {}).get("method") != "inference" and not program.python_only(k)]
        by_engine = _engine.infer(program, theory, [r for _, r in fresh], opts.timeout_ms, infer_rlimit(opts.rlimit), opts.jobs)
        inf_results = [(k, inference_key(program, k, opts.rlimit), by_engine[k]) for k, _ in fresh if by_engine.get(k) is not None]
        done = {k for k, _, _ in inf_results}
        inf_results += run_parallel(infer_one, [x for x in todo_inf if x[0] not in done], opts.jobs)
    else:
        inf_results = run_parallel(infer_one, todo_inf, opts.jobs)
    ikeys: dict[str, str] = {}
    for key, ikey, res in inf_results:
        inferred[key] = res
        if ikey is not None:
            ikeys[key] = ikey
    # Recursion measures, one recursion group at a time (every function in it
    # inferable and none with '@decreases').
    groups: dict[int, list[str]] = {}
    for key in inferred:
        if key in program.recursive:
            groups.setdefault(program.scc_of[key], []).append(key)
    todo_groups = []
    for keys in groups.values():
        members = [k for k in program.funcs if program.same_scc(keys[0], k)]
        if set(members) != set(keys) or any(program.ref(k).fn.decreases is not None for k in members):
            continue
        hit = cached_measures(program, members, inferred)
        if hit is None and opts.infer_auto:
            todo_groups.append(members)
        elif hit is not None:
            for k in members:
                inferred[k].options.measures.update(hit)

    def measure_one(keys: list[str]) -> tuple[list[str], dict[str, ir.Expr], int]:
        calls = inferred[keys[0]].solver_calls
        found = infer_measures(program, keys, theory, inferred, opts.timeout_ms, infer_rlimit(opts.rlimit))
        spent = inferred[keys[0]].solver_calls - calls
        inferred[keys[0]].solver_calls = calls
        return keys, found, spent

    for keys, found, calls in run_parallel(measure_one, todo_groups, opts.jobs):
        inferred[keys[0]].solver_calls += calls
        for k in keys:
            inferred[k].measured = True
            inferred[k].options.measures.update(found)
            if k in found:
                inferred[k].measure = render(found[k])
    for key, res in inferred.items():
        if key in ikeys:
            cache.put(ikeys[key], res.summary())
        measures.update(res.options.measures)
    if measures:
        theory, theory_problems = build_theory(program, measures)

    pending: list[tuple[Verdict, str]] = []
    staged: list[tuple[FunctionReport, str | None, float]] = []
    engine_tasks: list[tuple[FunctionReport, FuncRef, Inferred, str | None, float]] = []
    entry_checks: list[tuple[FunctionReport, VCGen]] = []

    def python_gather(rep: FunctionReport, ref: FuncRef, inf: Inferred) -> bool:
        """Generate and triage one function's obligations with the Python core.
        False when the function could not be verified (the report says why)."""
        nonlocal hits, solved
        why = program.ambiguity(ref)
        if why is not None:
            rep.status = "unsupported"
            rep.problems.append((why, ref.fn.loc))
            return False
        try:
            gen = VCGen(program, ref, inf.options)
            obs = gen.run()
        except VCError as e:
            rep.status = "error"
            rep.problems.append((str(e), e.loc or ref.fn.loc))
            return False
        except Exception as e:  # noqa: BLE001 - a bug in telic must not block the other functions
            if os.environ.get("TELIC_DEBUG"):
                raise
            rep.status = "error"
            rep.problems.append((f"internal error in telic ({type(e).__name__}: {e or 'no message'}); this is a telic bug, set TELIC_DEBUG=1 for the trace", ref.fn.loc))
            return False
        rep.assumptions = gen.assumptions
        rep.deps = set(gen.deps)
        code_value_calls(program, rep)
        entry_checks.append((rep, gen))
        for line, note in gen.loop_notes:
            if note == "no-variant" and ref.fn.has_contract:
                # (a claim about what a function returns needs it to return;
                # without a contract telic only looks for crashes)
                rep.problems.append(("termination not proved: add '@decreases <measure>' to this loop", ir.Loc(line)))
        for ob in obs:
            key_ = obligation_key(ob, theory, opts.rlimit)
            hit = cache.get(key_)
            if hit is not None and hit.get("method") == "unknown":
                hits += 1
                rep.verdicts.append(Verdict(ob, "unknown", "z3", 0.0, reason=f"{hit.get('reason', 'unknown')} (cached)"))
                continue
            if hit is not None and hit.get("method") == "lean:proof" and hit.get("proof_hash") != sidecar_proof_hash(ref, ob.id, root):
                # The sidecar proof was edited or removed: Z3 already failed
                # on this exact formula, so go straight back to Lean.
                rep.verdicts.append(Verdict(ob, "unknown", "z3", 0.0, reason="needs Lean"))
                continue
            if hit is not None:
                if cache.fresh(key_):
                    solved += 1  # a duplicate obligation proved earlier in this run
                else:
                    hits += 1
                rep.verdicts.append(Verdict(ob, "proved", "cache", 0.0, reason=hit.get("method", "")))
                continue
            solved += 1
            v = Verdict(ob, "pending", "z3", 0.0)
            pending.append((v, key_))
            rep.verdicts.append(v)
        return True


    for key, ref in program.funcs.items():
        fn = ref.fn
        if key not in selected:
            continue
        if opts.only and fn.name not in opts.only:
            continue
        if ref.module.context:
            continue
        if opts.progress:
            opts.progress(f"{ref.module.path}::{fn.name}")
        ft = time.perf_counter()
        rep = FunctionReport(ref, status="proved")
        rep.problems = [(m, loc) for (m, loc) in fn.unsupported]
        for tkey, msg in theory_problems:
            if tkey == key:
                rep.problems.append((msg, fn.loc))
        if fn.unsupported:
            rep.status = "unsupported"
            reports.append(rep)
            continue
        if fn.trusted:
            rep.status = "trusted"
            reports.append(rep)
            if fn.ensures:
                probe = VCGen(program, ref)
                try:
                    probe.contract_probe()
                    entry_checks.append((rep, probe))
                except VCError:
                    pass  # its callers report the same error when they evaluate the contract
            continue
        inf = inferred.get(key) or Inferred()
        rep.inferred = inf
        fkey = function_key(program, key, root, opts.rlimit) if opts.receipts else None
        receipt = cache.get(fkey) if fkey else None
        if receipt is not None and receipt.get("method") == "function":
            restore_receipt(rep, receipt)
            hits += len(rep.verdicts)
            rep.from_receipt = True
            reports.append(rep)
            continue
        if use_engine and program.ambiguity(ref) is None and not program.python_only(key):
            engine_tasks.append((rep, ref, inf, fkey, ft))
            reports.append(rep)
            continue
        if not python_gather(rep, ref, inf):
            reports.append(rep)
            continue
        staged.append((rep, fkey, ft))
        reports.append(rep)

    # The native engine: VC generation and solving for its functions; the
    # ones it does not model yet go through the Python core.
    if engine_tasks:
        cached = [k[len(ENGINE_KEY) :] for k, v in cache.data.items() if k.startswith(ENGINE_KEY) and v.get("method") == "z3"]
        answers = _engine.run(program, theory, [(ref, inf.options) for _, ref, inf, _, _ in engine_tasks], opts.timeout_ms, opts.rlimit, opts.jobs, cached, f"{toolchain_id()} {opts.rlimit}") or {}
        for rep, ref, inf, fkey, ft in engine_tasks:
            a = answers.get(ref.key)
            if a is None or a["status"] != "ok":
                if python_gather(rep, ref, inf):
                    staged.append((rep, fkey, ft))
                continue
            rep.assumptions = a["assumptions"]
            rep.deps = a["deps"]
            code_value_calls(program, rep)
            gen = VCGen(program, ref, inf.options)
            try:
                gen.enter()
                entry_checks.append((rep, gen))
            except VCError:
                pass  # the engine already reported whatever makes the entry state ill-formed
            for line, note in a["loop_notes"]:
                if note == "no-variant" and ref.fn.has_contract:
                    rep.problems.append(("termination not proved: add '@decreases <measure>' to this loop", ir.Loc(line)))
            for o in a["obligations"]:
                ob = o["ob"]
                if o["status"] == "proved" and o["reason"] == "cache":
                    hits += 1
                    rep.verdicts.append(Verdict(ob, "proved", "cache", 0.0, reason="z3"))
                    continue
                solved += 1
                v = Verdict(ob, o["status"], "z3", o["seconds"], o["model"], o["state"], o["reason"])
                rep.verdicts.append(v)
                if o["status"] == "proved":
                    cache.put(ENGINE_KEY + o["key"], {"method": "z3"})
                    cache.put(obligation_key(ob, theory, opts.rlimit), {"method": "z3"})
            staged.append((rep, fkey, ft))

    # Solve everything pending at once: each obligation gets its own Z3
    # context, and Z3 releases the GIL while it works, so threads use every
    # core.
    vacuity = vacuity_checks(entry_checks, theory, cache, opts.rlimit)
    if pending or vacuity.todo:
        results = solve_all([v.ob for v, _ in pending] + [ob for _, ob, _ in vacuity.todo], theory, opts.timeout_ms, opts.rlimit, opts.jobs)
        vacuity.record(results[len(pending) :], cache)
        results = results[: len(pending)]
        for (v, key_), res in zip(pending, results):
            v.status, v.seconds, v.model, v.state, v.reason = res.status, res.seconds, res.model, res.state, res.reason
            if res.status == "proved":
                cache.put(key_, {"method": "z3"})
            elif res.status == "unknown" and not res.reason.startswith("timeout"):
                cache.put(key_, {"method": "unknown", "reason": res.reason})

    # Escalate: counterexamples get executed (each replay is a subprocess,
    # so they run side by side), unknowns go to Lean.
    if opts.replay:
        from concurrent.futures import ThreadPoolExecutor

        from .replay import replay_verdicts

        to_replay = [rep for rep, _, _ in staged if any(v.status == "refuted" or (v.status == "unknown" and v.ob.kind in ("ensures", "inv.entry", "inv.step", "lifecycle")) for v in rep.verdicts)]
        if to_replay:
            with take_jobs(opts.jobs, len(to_replay)) as workers, ThreadPoolExecutor(max_workers=workers) as ex:
                list(ex.map(lambda r: replay_verdicts(program, r), to_replay))
    vacuous = vacuity.explain(theory, opts, cache)
    for rep, fkey, ft in staged:
        ref = rep.ref
        if opts.lean and any(v.status == "unknown" for v in rep.verdicts):
            from .lean import escalate

            escalate(program, theory, rep, cache, lambda ob, th: obligation_key(ob, th, opts.rlimit), root=root, auto=opts.lean_auto)
        if any(v.status == "refuted" for v in rep.verdicts):
            rep.status = "refuted"
        elif ref.key in vacuous:
            rep.status = "vacuous"
            rep.problems.append((vacuous[ref.key], ref.fn.loc))
        elif any(v.status != "proved" for v in rep.verdicts) or any("termination" in p for p, _ in rep.problems):
            rep.status = "open"
        rep.seconds = time.perf_counter() - ft
        if fkey and rep.status == "proved" and not rep.problems:
            cache.put(fkey, make_receipt(rep))

    for r in reports:
        if r.status == "trusted" and r.ref.key in vacuous:
            r.status = "vacuous"
            r.problems.append((vacuous[r.ref.key], r.fn.loc))

    # Transitive dependency status: a proof that assumes an unproved contract
    # is only as good as that contract.
    by_key = {r.ref.key: r for r in reports}
    for r in reports:
        seen: set[str] = set()
        todo = list(r.deps)
        while todo:
            d = todo.pop()
            if d in seen or d == r.ref.key:
                continue
            seen.add(d)
            dr = by_key.get(d)
            if dr is None and d in program.funcs and program.funcs[d].module.context:
                r.context_deps.add(d)  # checked on its own; its contract is what this proof uses
                continue
            if dr is not None:
                r.context_deps.update(dr.context_deps)
                status = evidence_status(dr)
            else:
                status = "open"
            if status == "trusted":
                r.trusted_deps.add(d)
            elif status != "proved":
                r.open_deps.add(d)
            if dr is not None:
                todo.extend(dr.deps)
            todo.extend(program.dispatch.get(d, ()))  # a call through a base may run any override

    from . import history

    gens = {r.ref.key: g for r, g in entry_checks}
    lifecycles = history.check(program, reports, gens, lambda obs: solve_all(obs, theory, opts.timeout_ms, opts.rlimit, opts.jobs), cache, lambda ob: obligation_key(ob, theory, opts.rlimit))

    mirrors = []
    if any(f.mirrors for m in modules for f in m.functions.values()):
        from .equiv import check_mirrors

        proved = {r.ref.key for r in reports if evidence_status(r) == "proved"}
        mirrors = check_mirrors(program, theory, opts, root=root, proved=proved)

    cache.save()
    rep = Report(modules, program, reports, [], mirrors, time.perf_counter() - t0, hits, solved)
    rep.lifecycles = lifecycles
    rep.root = program.root  # type: ignore[attr-defined]
    if ui is not None and (ui.lemmas or ui.aims):
        from .ui.run import run as run_ui

        rep.ui = run_ui(ui, program.root, enabled=opts.ui)
        rep.seconds = time.perf_counter() - t0
    rep.aims = aim_reports(rep)
    return rep


# ---------------------------------------------------------------------------


def aim_reports(rep: Report) -> list[AimReport]:
    from . import aim

    out = aim.build(rep)
    aim.attach_cached_judgments(getattr(rep, "root", None) or ".", out)
    return out
