"""The pipeline: source files in, a verdict for every obligation out."""

from __future__ import annotations

import hashlib
import json
import os
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Callable

from . import ir
from . import logic as L
from .infer import Inferred, infer
from .program import FuncRef, Program
from .smt import SmtResult, Theory, solve
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
    return None


def load_modules(paths: list[str], root: str | None = None) -> list[ir.Module]:
    from .frontend.python import lower_python

    files: list[str] = []
    for p in paths:
        if os.path.isdir(p):
            for dirpath, dirnames, filenames in os.walk(p):
                dirnames[:] = [d for d in dirnames if not d.startswith(".") and d not in ("node_modules", "__pycache__", "venv", ".venv", "dist", "build", "target")]
                for f in sorted(filenames):
                    full = os.path.join(dirpath, f)
                    if language_of(full):
                        files.append(full)
        else:
            files.append(p)
    root = root or os.getcwd()
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
    for f in files:
        lang = language_of(f)
        if lang == "python":
            mods.append(py_mods[f])
        elif lang == "typescript":
            mods.append(ts_mods[f])
        elif lang == "rust":
            from .frontend.rust import lower_rust

            mods.append(lower_rust(os.path.relpath(f, root), Path(f).read_text()))
    return mods


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
    status: str  # proved | refuted | open | unsupported | trusted | error
    verdicts: list[Verdict] = field(default_factory=list)
    inferred: Inferred | None = None
    problems: list[tuple[str, ir.Loc]] = field(default_factory=list)
    assumptions: list[tuple[ir.Loc, str]] = field(default_factory=list)
    deps: set[str] = field(default_factory=set)
    open_deps: set[str] = field(default_factory=set)
    context_deps: set[str] = field(default_factory=set)
    seconds: float = 0.0
    from_receipt: bool = False

    @property
    def fn(self) -> ir.Function:
        return self.ref.fn

    def count(self, status: str) -> int:
        return sum(1 for v in self.verdicts if v.status == status)


from .intent import IntentReport  # noqa: E402  (re-exported)


@dataclass
class Report:
    modules: list[ir.Module]
    program: Program
    functions: list[FunctionReport]
    intents: list[IntentReport]
    mirrors: list[Any] = field(default_factory=list)  # EquivReport
    seconds: float = 0.0
    cache_hits: int = 0
    solved: int = 0

    def all_verdicts(self) -> list[Verdict]:
        return [v for f in self.functions for v in f.verdicts]

    @property
    def ok(self) -> bool:
        return not any(f.status in ("refuted", "error") for f in self.functions) and not any(
            m.status == "refuted" for m in self.mirrors
        ) and not any(p for m in self.modules for p in m.problems)


# ---------------------------------------------------------------------------
# Cache: proofs are keyed by the exact formula, so they survive any edit that
# does not change what has to be proved.


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
        keep = {k: v for k, v in self.data.items() if k in self.used}
        Path(self.path).write_text(json.dumps({"version": self.VERSION, "proofs": keep}, indent=1, sort_keys=True))


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
                "intents": list(v.ob.intents),
                "method": v.reason if v.method == "cache" else v.method,
                "inferred": v.ob.inferred,
            }
            for v in rep.verdicts
        ],
    }


def restore_receipt(rep: "FunctionReport", r: dict[str, Any]) -> None:
    """Rebuild a proved function's report from its receipt (no formulas are
    kept; `telic explain` recomputes them)."""
    rep.status = r["status"]
    rep.deps = set(r.get("deps", []))
    rep.assumptions = [(ir.Loc(line), text) for line, text in r.get("assumptions", [])]
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
            intents=tuple(o.get("intents", ())),
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


def inference_key(program: Program, key: str) -> str:
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
    h = hashlib.sha256(f"infer {__version__} {toolchain_id()}".encode())
    for k in sorted(seen):
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
        _TOOLCHAIN = h.hexdigest()[:16]
    return _TOOLCHAIN


def function_key(program: Program, key: str, root: str | None) -> str:
    """A function's verdict depends on its own source, everything it calls
    (contracts, and bodies of pure callees used as definitions), the records
    it uses, its Lean sidecar proofs, and the toolchain. Nothing else."""
    seen: set[str] = set()
    todo = [key]
    while todo:
        k = todo.pop()
        if k in seen:
            continue
        seen.add(k)
        todo.extend(program.callees.get(k, ()))
    h = hashlib.sha256(f"fn {toolchain_id()}".encode())
    for k in sorted(seen):
        ref = program.ref(k)
        h.update(f"{k}\n{ref.module.language}\n{ref.fn.source}\n{sorted((n, str(t)) for n, t in ref.module.records.items())}".encode())
    ref = program.ref(key)
    from .lean import sidecar_path

    side = sidecar_path(os.path.join(root or os.getcwd(), ref.module.path))
    if os.path.exists(side):
        h.update(Path(side).read_bytes())
    return "fn:" + h.hexdigest()[:24]


def obligation_key(ob: Obligation, theory: Theory) -> str:
    defs, axioms = theory.closure(list(ob.hyps) + [ob.goal], ob.exclude_axioms)
    h = hashlib.sha256(toolchain_id().encode())
    h.update(L.canonical(ob.formula()).encode())
    for d in defs:
        h.update(f"def {d.name}({' '.join(L.canonical(p) for p in d.params)})={L.canonical(d.body) if d.body else '?'}".encode())
    for a in axioms:
        h.update(f"ax {L.canonical(a.formula)}".encode())
    return h.hexdigest()[:24]


# ---------------------------------------------------------------------------


@dataclass
class CheckOptions:
    timeout_ms: int = 8000
    replay: bool = True
    lean: bool = True
    infer: bool = True
    cache_path: str | None = None
    only: set[str] | None = None  # function names to check
    progress: Callable[[str], None] | None = None
    receipts: bool = True  # reuse whole-function verdicts for unchanged functions
    jobs: int | None = None  # solver threads (default: every core)
    # "ox": the native engine (core/), where it applies
    engine: str = field(default_factory=lambda: os.environ.get("TELIC_ENGINE", "python"))


_POOL: dict[str, Any] = {}


def _pool_call(item: Any) -> Any:
    return _POOL["fn"](item)


def run_parallel(fn: Callable[[Any], Any], items: list[Any], jobs: int | None) -> list[Any]:
    """Map ``fn`` over ``items`` on every core (fork: the function and what it
    closes over are inherited, only items and results are pickled)."""
    workers = max(1, min(jobs or (os.cpu_count() or 1), len(items)))
    if workers == 1 or len(items) < 2:
        return [fn(x) for x in items]
    import multiprocessing as mp
    from concurrent.futures import ProcessPoolExecutor, ThreadPoolExecutor

    if "fork" in mp.get_all_start_methods():
        _POOL["fn"] = fn
        try:
            with ProcessPoolExecutor(max_workers=workers, mp_context=mp.get_context("fork")) as pool:
                return list(pool.map(_pool_call, items, chunksize=max(1, len(items) // (workers * 4))))
        except Exception:  # pragma: no cover
            pass
        finally:
            _POOL.pop("fn", None)
    with ThreadPoolExecutor(max_workers=workers) as tp:
        return list(tp.map(fn, items))


def _pool_solve(ob: Obligation) -> SmtResult:
    return solve(ob, _POOL["theory"], _POOL["timeout"])


def solve_all(obs: list[Obligation], theory: Theory, timeout_ms: int, jobs: int | None) -> list[SmtResult]:
    """Solve independent obligations on every core. Worker processes (fork)
    sidestep the GIL, which the Python half of each solve holds; threads are
    the fallback where fork is unavailable."""
    workers = max(1, min(jobs or (os.cpu_count() or 1), len(obs)))
    if workers == 1 or len(obs) < 4:
        return [solve(ob, theory, timeout_ms) for ob in obs]
    import multiprocessing as mp
    from concurrent.futures import ProcessPoolExecutor, ThreadPoolExecutor

    if "fork" in mp.get_all_start_methods():
        _POOL["theory"], _POOL["timeout"] = theory, timeout_ms
        try:
            with ProcessPoolExecutor(max_workers=workers, mp_context=mp.get_context("fork")) as pool:
                return list(pool.map(_pool_solve, obs, chunksize=max(1, len(obs) // (workers * 4))))
        except Exception:  # pragma: no cover - e.g. a sandbox without fork
            pass
        finally:
            _POOL.clear()
    with ThreadPoolExecutor(max_workers=workers) as tp:
        return list(tp.map(lambda ob: solve(ob, theory, timeout_ms), obs))


def build_theory(program: Program, measures: dict[str, ir.Expr]) -> tuple[Theory, list[tuple[str, str]]]:
    theory = Theory()
    problems: list[tuple[str, str]] = []
    for d in (L.seqsum_def(L.INT), L.seqsum_def(L.REAL), L.seqcount_def(L.INT), L.seqcount_def(L.REAL), L.seqcount_def(L.BOOL), L.seqcount_def(L.STR)):
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
    opts = opts or CheckOptions()
    t0 = time.perf_counter()
    modules = load_modules(paths, root)
    return check_modules(modules, opts, t0=t0, root=root)


def check_modules(modules: list[ir.Module], opts: CheckOptions, t0: float | None = None, root: str | None = None) -> Report:
    t0 = t0 or time.perf_counter()
    program = Program.build(modules)
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
        if opts.infer and not (opts.only and ref.fn.name not in opts.only) and not (ref.fn.unsupported or ref.fn.trusted or ref.module.context)
    ]

    def infer_one(item):
        key, ref = item
        ikey = inference_key(program, key)
        try:
            return key, ikey, infer(program, ref, theory, timeout_ms=min(opts.timeout_ms, 1000), cached=cache.get(ikey))
        except VCError:
            return key, None, Inferred()

    use_engine = opts.engine == "ox"
    if use_engine:
        from . import engine as _engine

        use_engine = _engine.binary() is not None
    if use_engine:
        # Cached inferences are rebuilt locally; the rest run in the engine,
        # and whatever it cannot decide falls back to Python.
        fresh = [(k, r) for k, r in todo_inf if (cache.get(inference_key(program, k)) or {}).get("method") != "inference"]
        by_engine = _engine.infer(program, theory, [r for _, r in fresh], min(opts.timeout_ms, 1000), opts.jobs)
        inf_results = [(k, inference_key(program, k), by_engine[k]) for k, _ in fresh if by_engine.get(k) is not None]
        done = {k for k, _, _ in inf_results}
        inf_results += run_parallel(infer_one, [x for x in todo_inf if x[0] not in done], opts.jobs)
    else:
        inf_results = run_parallel(infer_one, todo_inf, opts.jobs)
    for key, ikey, res in inf_results:
        inferred[key] = res
        if ikey is not None:
            cache.put(ikey, res.summary())
        if key in res.options.measures:
            measures[key] = res.options.measures[key]
    if measures:
        theory, theory_problems = build_theory(program, measures)

    pending: list[tuple[Verdict, str]] = []
    staged: list[tuple[FunctionReport, str | None, float]] = []
    engine_tasks: list[tuple[FunctionReport, FuncRef, Inferred, str | None, float]] = []

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
        for line, note in gen.loop_notes:
            if note == "no-variant" and ref.fn.has_contract:
                # (a claim about what a function returns needs it to return;
                # without a contract telic only looks for crashes)
                rep.problems.append(("termination not proved: add '@decreases <measure>' to this loop", ir.Loc(line)))
        for ob in obs:
            key_ = obligation_key(ob, theory)
            hit = cache.get(key_)
            if hit is not None and hit.get("method") == "unknown":
                if hit.get("timeout", 0) >= opts.timeout_ms:
                    hits += 1
                    rep.verdicts.append(Verdict(ob, "unknown", "z3", 0.0, reason=f"{hit.get('reason', 'timeout')} (cached)"))
                    continue
                hit = None
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
            continue
        inf = inferred.get(key) or Inferred()
        rep.inferred = inf
        fkey = function_key(program, key, root) if opts.receipts else None
        receipt = cache.get(fkey) if fkey else None
        if receipt is not None and receipt.get("method") == "function":
            restore_receipt(rep, receipt)
            hits += len(rep.verdicts)
            rep.from_receipt = True
            reports.append(rep)
            continue
        if use_engine and program.ambiguity(ref) is None:
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
        answers = _engine.run(program, theory, [(ref, inf.options) for _, ref, inf, _, _ in engine_tasks], opts.timeout_ms, opts.jobs) or {}
        for rep, ref, inf, fkey, ft in engine_tasks:
            a = answers.get(ref.key)
            if a is None or a["status"] != "ok":
                if python_gather(rep, ref, inf):
                    staged.append((rep, fkey, ft))
                continue
            rep.assumptions = a["assumptions"]
            rep.deps = a["deps"]
            for line, note in a["loop_notes"]:
                if note == "no-variant" and ref.fn.has_contract:
                    rep.problems.append(("termination not proved: add '@decreases <measure>' to this loop", ir.Loc(line)))
            for o in a["obligations"]:
                ob = o["ob"]
                solved += 1
                v = Verdict(ob, o["status"], "z3", o["seconds"], o["model"], o["state"], o["reason"])
                rep.verdicts.append(v)
                if o["status"] == "proved":
                    cache.put(obligation_key(ob, theory), {"method": "z3"})
            staged.append((rep, fkey, ft))

    # Solve everything pending at once: each obligation gets its own Z3
    # context, and Z3 releases the GIL while it works, so threads use every
    # core.
    if pending:
        results = solve_all([v.ob for v, _ in pending], theory, opts.timeout_ms, opts.jobs)
        for (v, key_), res in zip(pending, results):
            v.status, v.seconds, v.model, v.state, v.reason = res.status, res.seconds, res.model, res.state, res.reason
            if res.status == "proved":
                cache.put(key_, {"method": "z3"})
            elif res.status == "unknown":
                cache.put(key_, {"method": "unknown", "timeout": opts.timeout_ms, "reason": res.reason})

    # Escalate: counterexamples get executed (each replay is a subprocess,
    # so they run side by side), unknowns go to Lean.
    if opts.replay:
        from concurrent.futures import ThreadPoolExecutor

        from .replay import replay_verdicts

        to_replay = [rep for rep, _, _ in staged if any(v.status == "refuted" for v in rep.verdicts)]
        if to_replay:
            with ThreadPoolExecutor(max_workers=min(len(to_replay), opts.jobs or os.cpu_count() or 4)) as ex:
                list(ex.map(lambda r: replay_verdicts(program, r), to_replay))
    for rep, fkey, ft in staged:
        ref = rep.ref
        if opts.lean and any(v.status == "unknown" for v in rep.verdicts):
            from .lean import escalate

            escalate(program, theory, rep, cache, obligation_key, root=root)
        if any(v.status == "refuted" for v in rep.verdicts):
            rep.status = "refuted"
        elif any(v.status != "proved" for v in rep.verdicts) or any("termination" in p for p, _ in rep.problems):
            rep.status = "open"
        rep.seconds = time.perf_counter() - ft
        if fkey and rep.status == "proved" and not rep.problems:
            cache.put(fkey, make_receipt(rep))

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
            if dr is None or dr.status not in ("proved",):
                if dr is None or dr.status != "trusted":
                    r.open_deps.add(d)
            if dr is not None:
                todo.extend(dr.deps)
            todo.extend(program.dispatch.get(d, ()))  # a call through a base may run any override

    mirrors = []
    if any(f.mirrors for m in modules for f in m.functions.values()):
        from .equiv import check_mirrors

        mirrors = check_mirrors(program, theory, opts, root=root)

    cache.save()
    rep = Report(modules, program, reports, [], mirrors, time.perf_counter() - t0, hits, solved)
    rep.root = program.root  # type: ignore[attr-defined]
    rep.intents = intent_reports(rep)
    return rep


# ---------------------------------------------------------------------------


def intent_reports(rep: Report) -> list[IntentReport]:
    from . import intent

    out = intent.build(rep)
    intent.attach_cached_judgments(getattr(rep, "root", None) or ".", out)
    return out
