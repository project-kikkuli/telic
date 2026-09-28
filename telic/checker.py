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
    return None


def load_modules(paths: list[str], root: str | None = None) -> list[ir.Module]:
    from .frontend.python import lower_python

    files: list[str] = []
    for p in paths:
        if os.path.isdir(p):
            for dirpath, dirnames, filenames in os.walk(p):
                dirnames[:] = [d for d in dirnames if not d.startswith(".") and d not in ("node_modules", "__pycache__", "venv", ".venv", "dist", "build")]
                for f in sorted(filenames):
                    full = os.path.join(dirpath, f)
                    if language_of(full):
                        files.append(full)
        else:
            files.append(p)
    root = root or os.getcwd()
    mods: list[ir.Module] = []
    ts_files = [f for f in files if language_of(f) == "typescript"]
    ts_mods: dict[str, ir.Module] = {}
    if ts_files:
        from .frontend.typescript import lower_typescript_files

        ts_mods = lower_typescript_files(ts_files, root)
    for f in files:
        rel = os.path.relpath(f, root)
        lang = language_of(f)
        if lang == "python":
            src = Path(f).read_text()
            if "@" not in src:  # fast path: nothing to check unless contracts exist?
                pass
            mods.append(lower_python(rel, src))
        elif lang == "typescript":
            mods.append(ts_mods[f])
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
    seconds: float = 0.0

    @property
    def fn(self) -> ir.Function:
        return self.ref.fn

    def count(self, status: str) -> int:
        return sum(1 for v in self.verdicts if v.status == status)


@dataclass
class IntentReport:
    id: str
    text: str | None
    loc: tuple[str, int] | None
    functions: list[str]
    status: str  # proved | refuted | open | unformalized | undeclared
    clauses: int = 0
    proved: int = 0
    refuted: int = 0
    open: int = 0


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

    def get(self, key: str) -> dict[str, Any] | None:
        hit = self.data.get(key)
        if hit is not None:
            self.used.add(key)
        return hit

    def put(self, key: str, value: dict[str, Any]) -> None:
        self.data[key] = value
        self.used.add(key)

    def save(self) -> None:
        if not self.path:
            return
        os.makedirs(os.path.dirname(self.path) or ".", exist_ok=True)
        keep = {k: v for k, v in self.data.items() if k in self.used}
        Path(self.path).write_text(json.dumps({"version": self.VERSION, "proofs": keep}, indent=1, sort_keys=True))


def obligation_key(ob: Obligation, theory: Theory) -> str:
    defs, axioms = theory.closure(list(ob.hyps) + [ob.goal], ob.exclude_axioms)
    h = hashlib.sha256()
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


def build_theory(program: Program, measures: dict[str, ir.Expr]) -> tuple[Theory, list[tuple[str, str]]]:
    theory = Theory()
    problems: list[tuple[str, str]] = []
    for d in (L.seqsum_def(L.INT), L.seqsum_def(L.REAL), L.seqcount_def(L.INT), L.seqcount_def(L.REAL), L.seqcount_def(L.BOOL), L.seqcount_def(L.STR)):
        theory.fundefs[d.name] = d
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
    program.root = root or os.getcwd()  # type: ignore[attr-defined]
    cache = ProofCache(opts.cache_path)
    theory, theory_problems = build_theory(program, {})
    reports: list[FunctionReport] = []
    hits = solved = 0

    # Recursion measures must be known before definitions are built (Lean
    # needs them), so infer them first for recursive definitional functions.
    measures: dict[str, ir.Expr] = {}
    inferred: dict[str, Inferred] = {}
    for key, ref in program.funcs.items():
        if opts.only and ref.fn.name not in opts.only:
            continue
        if ref.fn.unsupported or ref.fn.trusted:
            continue
        if opts.infer:
            try:
                inferred[key] = infer(program, ref, theory, timeout_ms=min(opts.timeout_ms, 3000))
            except VCError:
                inferred[key] = Inferred()
            if key in inferred[key].options.measures:
                measures[key] = inferred[key].options.measures[key]
    if measures:
        theory, theory_problems = build_theory(program, measures)

    for key, ref in program.funcs.items():
        fn = ref.fn
        if opts.only and fn.name not in opts.only:
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
        try:
            gen = VCGen(program, ref, inf.options)
            obs = gen.run()
        except VCError as e:
            rep.status = "error"
            rep.problems.append((str(e), e.loc or fn.loc))
            reports.append(rep)
            continue
        rep.assumptions = gen.assumptions
        rep.deps = set(gen.deps)
        for line, note in gen.loop_notes:
            if note == "no-variant":
                rep.problems.append(("termination not proved: add '@decreases <measure>' to this loop", ir.Loc(line)))
        for ob in obs:
            key_ = obligation_key(ob, theory)
            hit = cache.get(key_)
            if hit is not None:
                hits += 1
                rep.verdicts.append(Verdict(ob, "proved", "cache", 0.0, reason=hit.get("method", "")))
                continue
            solved += 1
            res: SmtResult = solve(ob, theory, opts.timeout_ms)
            v = Verdict(ob, res.status, "z3", res.seconds, res.model, res.state, res.reason)
            if res.status == "proved":
                cache.put(key_, {"method": "z3"})
            rep.verdicts.append(v)
        # Escalate: counterexamples get executed, unknowns go to Lean.
        if opts.replay:
            from .replay import replay_verdicts

            replay_verdicts(program, rep)
        if opts.lean and any(v.status == "unknown" for v in rep.verdicts):
            from .lean import escalate

            escalate(program, theory, rep, cache, obligation_key, root=root)
        if any(v.status == "refuted" for v in rep.verdicts):
            rep.status = "refuted"
        elif any(v.status != "proved" for v in rep.verdicts) or any("termination" in p for p, _ in rep.problems):
            rep.status = "open"
        rep.seconds = time.perf_counter() - ft
        reports.append(rep)

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
            if dr is None or dr.status not in ("proved",):
                if dr is None or dr.status != "trusted":
                    r.open_deps.add(d)
            if dr is not None:
                todo.extend(dr.deps)

    mirrors = []
    if any(f.mirrors for m in modules for f in m.functions.values()):
        from .equiv import check_mirrors

        mirrors = check_mirrors(program, theory, opts, root=root)

    cache.save()
    rep = Report(modules, program, reports, [], mirrors, time.perf_counter() - t0, hits, solved)
    rep.intents = intent_reports(rep)
    return rep


# ---------------------------------------------------------------------------


def intent_reports(rep: Report) -> list[IntentReport]:
    decls: dict[str, tuple[str, tuple[str, int]]] = {}
    for m in rep.modules:
        for d in m.intents:
            decls.setdefault(d.id, (d.text, (m.path, d.loc.line)))
    linked: dict[str, list[FunctionReport]] = {}
    for f in rep.functions:
        for i in f.fn.intents:
            linked.setdefault(i, []).append(f)
    mirror_by_intent: dict[str, list[Any]] = {}
    for mr in rep.mirrors:
        for i in mr.intents:
            mirror_by_intent.setdefault(i, []).append(mr)
    out: list[IntentReport] = []
    for iid in sorted(set(decls) | set(linked)):
        text, loc = decls.get(iid, (None, None))
        fns = linked.get(iid, [])
        clauses = sum(
            1
            for f in fns
            for c in f.fn.requires + f.fn.ensures + f.fn.raises
            if iid in c.intents and c.kind != "requires"
        )
        verdicts = [v for f in fns for v in f.verdicts]
        ir_ = IntentReport(iid, text, loc, [f.ref.key for f in fns], "open", clauses)
        ir_.proved = sum(1 for v in verdicts if v.status == "proved")
        ir_.refuted = sum(1 for v in verdicts if v.status == "refuted")
        ir_.open = sum(1 for v in verdicts if v.status not in ("proved", "refuted"))
        mirrors = mirror_by_intent.get(iid, [])
        statuses = [f.status for f in fns] + [m.status for m in mirrors]
        if text is None:
            ir_.status = "undeclared"
        elif not fns or (clauses == 0 and not mirrors):
            ir_.status = "unformalized"
        elif "refuted" in statuses:
            ir_.status = "refuted"
        elif all(s in ("proved", "trusted") for s in statuses) and not any(f.open_deps for f in fns):
            ir_.status = "proved"
        else:
            ir_.status = "open"
        out.append(ir_)
    return out
