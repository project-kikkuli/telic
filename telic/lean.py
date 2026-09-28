"""Lean 4 backend: the proof ladder's upper rungs.

When Z3 cannot decide an obligation (induction, nonlinear arithmetic, ...),
telic renders the *same* verification condition as a Lean 4 theorem and
tries, in order:

1. a proof already written for it in the source file's sidecar
   (``pricing.py`` -> ``pricing.py.proof.lean``), if its statement still
   matches the current code;
2. an automatic tactic ladder (omega, grind, simp, induction...);
3. with ``telic prove --agent CMD``, an agent that writes the proof, with
   Lean's error messages fed back to it until the kernel accepts one.

A proof counts only if Lean accepts it *and* ``#print axioms`` shows nothing
beyond Lean's three standard axioms -- no ``sorry``, no ``native_decide``,
no smuggled axioms. Proof statements are regenerated from code on every run,
so a proof silently going stale is impossible: when the code changes the
obligation, its sidecar proof is reported as stale, alone.

Lemmas (``@ensures`` of pure functions) enter a theorem as explicit
hypotheses, never as Lean axioms: each Lean proof is conditional on exactly
the contracts it uses, and those contracts carry their own obligations.
"""

from __future__ import annotations

import glob
import hashlib
import json
import os
import re
import shutil
import subprocess
import tempfile
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from . import logic as L
from .smt import Theory
from .vcgen import Obligation

STANDARD_AXIOMS = {"propext", "Classical.choice", "choice", "Quot.sound"}
LEAN_TIMEOUT_S = 120
HEARTBEATS = 400000

AUTO_TACTICS = [
    "omega",
    "grind",
    "(simp_all <;> omega)",
    "(simp_all <;> grind)",
    "decide",
]

LEAN_KEYWORDS = {
    "fun", "let", "if", "then", "else", "have", "show", "from", "at", "by", "do", "match", "with", "end",
    "def", "theorem", "lemma", "open", "namespace", "section", "instance", "structure", "class", "where",
    "deriving", "in", "import", "variable", "universe", "Type", "Prop", "Sort", "example", "abbrev",
    "calc", "suffices", "obtain", "return", "for", "unless", "mut", "true", "false", "True", "False",
    "axiom", "private", "protected", "noncomputable", "partial", "unsafe", "macro", "syntax", "set_option",
}


class LeanUnsupported(Exception):
    pass


# ---------------------------------------------------------------------------
# Toolchain


def find_lean() -> str | None:
    env = os.environ.get("TELIC_LEAN")
    if env and os.path.exists(env):
        return env
    found = shutil.which("lean")
    if found:
        return found
    candidates = sorted(glob.glob("/opt/lean/*/bin/lean")) + sorted(glob.glob(os.path.expanduser("~/.elan/toolchains/*/bin/lean")))
    return candidates[-1] if candidates else None


def lean_version(lean: str) -> str:
    try:
        out = subprocess.run([lean, "--version"], capture_output=True, text=True, timeout=20).stdout
        m = re.search(r"version ([\d.]+[^,\s]*)", out)
        return m.group(1) if m else out.strip()
    except (OSError, subprocess.TimeoutExpired):
        return "unknown"


# ---------------------------------------------------------------------------
# Translation


class Namer:
    def __init__(self) -> None:
        self.names: dict[str, str] = {}
        self.used: set[str] = set()

    def __call__(self, raw: str) -> str:
        if raw in self.names:
            return self.names[raw]
        base = re.sub(r"[^A-Za-z0-9_]", "_", raw.replace("@", "_").replace(".", "_").replace("!", "_").replace("?", "_q").replace("$", "_").replace("()", "_ret"))
        base = re.sub(r"_+", "_", base).strip("_") or "v"
        if base[0].isdigit():
            base = "v" + base
        if base in LEAN_KEYWORDS:
            base = base + "'"
        name = base
        k = 1
        while name in self.used:
            k += 1
            name = f"{base}_{k}"
        self.used.add(name)
        self.names[raw] = name
        return name


def lean_sort(s: L.Sort) -> str:
    if s == L.INT:
        return "Int"
    if s == L.REAL:
        return "Rat"
    if s == L.BOOL:
        return "Prop"
    if s == L.STR:
        return "String"
    if s.name == "Array":
        assert s.elem is not None
        return f"(Int → {lean_sort(s.elem)})"
    if s.name == "Rec":
        return s.rec or "Rec"
    raise LeanUnsupported(f"no Lean type for {s}")


class LeanPrinter:
    def __init__(self, namer: Namer, fn_names: dict[str, str]):
        self.n = namer
        self.fn_names = fn_names
        self.dependent_ite = False
        self.hyp_counter = 0

    def t(self, x: L.Term, prec: int = 0) -> str:
        s, p = self._t(x)
        return f"({s})" if p < prec else s

    def _t(self, x: L.Term) -> tuple[str, int]:
        if isinstance(x, L.Const):
            return self.n(x.name), 1000
        if isinstance(x, L.IntV):
            return (str(x.value), 1000) if x.value >= 0 else (f"({x.value})", 1000)
        if isinstance(x, L.RealV):
            v = x.value
            if v.denominator == 1:
                return (f"({v.numerator} : Rat)", 100)
            return (f"(({v.numerator} : Rat) / {v.denominator})", 100)
        if isinstance(x, L.BoolV):
            return ("True" if x.value else "False"), 100
        if isinstance(x, L.StrV):
            return json.dumps(x.value), 100
        if isinstance(x, L.Quant):
            q = "∀" if x.kind == "forall" else "∃"
            vs = " ".join(f"({self.n(v.name)} : {lean_sort(v.sort)})" for v in x.vars)
            return f"{q} {vs}, {self.t(x.body)}", 0
        if isinstance(x, L.Fn):
            name = self.fn_names.get(x.name, x.name)
            if not x.args:
                return name, 100
            return f"{name} {' '.join(self.t(a, 101) for a in x.args)}", 90
        assert isinstance(x, L.App)
        a = x.args
        op = x.op
        bin_ops = {
            "add": ("+", 65),
            "sub": ("-", 65),
            "mul": ("*", 70),
            "rdiv": ("/", 70),
            "ediv": ("/", 70),
            "emod": ("%", 70),
            "lt": ("<", 50),
            "le": ("≤", 50),
        }
        if op in bin_ops:
            sym, p = bin_ops[op]
            return f"{self.t(a[0], p)} {sym} {self.t(a[1], p + 1)}", p
        if op == "neg":
            return f"-{self.t(a[0], 75)}", 75
        if op == "eq":
            if a[0].sort == L.BOOL:
                return f"({self.t(a[0], 21)} ↔ {self.t(a[1], 21)})", 100
            return f"{self.t(a[0], 51)} = {self.t(a[1], 51)}", 50
        if op == "not":
            return f"¬{self.t(a[0], 40)}", 40
        if op == "and":
            return " ∧ ".join(self.t(y, 36) for y in a), 35
        if op == "or":
            return " ∨ ".join(self.t(y, 31) for y in a), 30
        if op == "implies":
            return f"{self.t(a[0], 26)} → {self.t(a[1], 25)}", 25
        if op == "ite":
            if self.dependent_ite:
                self.hyp_counter += 1
                return f"if h{self.hyp_counter} : {self.t(a[0])} then {self.t(a[1])} else {self.t(a[2])}", 1
            return f"if {self.t(a[0])} then {self.t(a[1])} else {self.t(a[2])}", 1
        if op == "to_real":
            return f"(({self.t(a[0])} : Int) : Rat)", 100
        if op == "floor":
            return f"Rat.floor {self.t(a[0], 101)}", 90
        if op == "is_int":
            return f"({self.t(a[0], 100)}.den = 1)", 100
        if op == "select":
            return f"{self.t(a[0], 101)} {self.t(a[1], 101)}", 90
        if op == "store":
            return f"Telic.upd {self.t(a[0], 101)} {self.t(a[1], 101)} {self.t(a[2], 101)}", 90
        if op.startswith("field:"):
            return f"{self.t(a[0], 101)}.{op[6:]}", 100
        if op.startswith("mk:"):
            return f"{{ {', '.join(f'{fn} := {self.t(v)}' for (fn, _), v in zip(x.sort.fields, a))} }}", 100
        raise LeanUnsupported(f"no Lean rendering for '{op}'")


PRELUDE = """set_option linter.unusedVariables false
set_option maxHeartbeats {heartbeats}
open Classical

namespace Telic
/-- Functional array update. -/
def upd {{α : Type}} (a : Int → α) (i : Int) (v : α) : Int → α := fun j => if j = i then v else a j
@[simp] theorem upd_same {{α : Type}} (a : Int → α) (i : Int) (v : α) : upd a i v i = v := by simp [upd]
@[simp] theorem upd_other {{α : Type}} (a : Int → α) (i j : Int) (v : α) (h : j ≠ i) : upd a i v j = a j := by simp [upd, h]
theorem upd_apply {{α : Type}} (a : Int → α) (i j : Int) (v : α) : upd a i v j = if j = i then v else a j := rfl
end Telic
"""


@dataclass
class LeanDoc:
    """A self-contained Lean file proving one or more obligations."""

    header: str
    theorems: list[tuple[str, str]]  # (name, statement)


def collect_records(terms: list[L.Term]) -> list[L.Sort]:
    out: dict[str, L.Sort] = {}

    def visit_sort(s: L.Sort) -> None:
        if s.name == "Rec" and s.rec not in out:
            for _, fs in s.fields:
                visit_sort(fs)
            out[s.rec] = s  # type: ignore[index]
        elif s.name == "Array" and s.elem is not None:
            visit_sort(s.elem)

    for t in terms:
        for x in L.iter_terms(t):
            visit_sort(x.sort)
            if isinstance(x, L.Quant):
                for v in x.vars:
                    visit_sort(v.sort)
    return list(out.values())


def render_defs(defs: list[L.FunDef], records: list[L.Sort], fn_names: dict[str, str]) -> str:
    lines: list[str] = []
    for r in records:
        fields = " ".join(f"({n} : {lean_sort(s)})" for n, s in r.fields)
        lines.append(f"structure {r.rec} where\n  mk ::\n" + "".join(f"  {n} : {lean_sort(s)}\n" for n, s in r.fields))
        del fields
    # Definitions in dependency order (callees first).
    order: list[L.FunDef] = []
    by = {d.name: d for d in defs}
    seen: set[str] = set()

    def dfs(d: L.FunDef) -> None:
        if d.name in seen:
            return
        seen.add(d.name)
        if d.body is not None:
            for callee in sorted(L.fns(d.body)):
                if callee in by and callee != d.name:
                    dfs(by[callee])
        order.append(d)

    for d in defs:
        dfs(d)
    for d in order:
        namer = Namer()
        pr = LeanPrinter(namer, fn_names)
        params = " ".join(f"({namer(p.name)} : {lean_sort(p.sort)})" for p in d.params)
        name = fn_names.get(d.name, d.name)
        if d.body is None:
            raise LeanUnsupported(f"'{d.name}' has no definition")
        pr.dependent_ite = d.recursive
        body = pr.t(d.body)
        doc = f"/-- {d.doc} -/\n" if d.doc else ""
        lemma = ""
        if d.inner is not None:
            lnamer = Namer()
            lpr = LeanPrinter(lnamer, fn_names)
            lparams = " ".join(f"({lnamer(p.name)} : {lean_sort(p.sort)})" for p in d.params)
            hyp = f" (h : {lpr.t(d.guard)})" if d.guard is not None else ""
            lemma = (
                f"/-- Unfolds one step of `{name}`{' under its precondition' if d.guard is not None else ''}. -/\n"
                f"theorem {name}_def {lparams}{hyp} :\n    {name} {' '.join(lnamer(p.name) for p in d.params)} = {lpr.t(d.inner)} := by\n"
                f"  first | (rw [{name}]; simp [{'h' if hyp else ''}]) | (rw [{name}]; simp_all) | (unfold {name}; simp_all) | grind [{name}]\n"
            )
        if d.recursive:
            if d.measure is None:
                raise LeanUnsupported(f"recursive '{d.name}' has no termination measure; add '@decreases'")
            meas = pr.t(d.measure, 101)
            lines.append(f"{doc}def {name} {params} : {lean_sort(d.sort)} :=\n  {body}\ntermination_by {meas}.toNat\ndecreasing_by all_goals (first | omega | (simp_all; omega) | grind)\n")
        else:
            lines.append(f"{doc}def {name} {params} : {lean_sort(d.sort)} :=\n  {body}\n")
        if lemma:
            lines.append(LEMMA_MARK + d.name + "\n" + lemma)
    return "\n".join(lines)


LEMMA_MARK = "-- telic-lemma: "
_validated: dict[str, str] = {}


def validated_defs(lean: str, defs_text: str) -> str:
    """Drop any generated helper lemma that Lean does not accept, so one
    unlucky lemma never takes the definitions (and every proof) down."""
    if defs_text in _validated:
        return _validated[defs_text]
    if LEMMA_MARK not in defs_text:
        _validated[defs_text] = defs_text
        return defs_text
    pre = PRELUDE.format(heartbeats=HEARTBEATS)
    run = run_lean(lean, pre + "\n" + defs_text + "\n")
    offset = len(pre.splitlines()) + 1
    bad_lines = {m.line - offset for m in run.messages if m.severity == "error"}
    chunks = defs_text.split(LEMMA_MARK)
    out = [chunks[0]]
    line = chunks[0].count("\n")
    for ch in chunks[1:]:
        n = ch.count("\n")
        span = range(line + 1, line + n + 2)
        if not any(l in span for l in bad_lines):
            out.append(LEMMA_MARK + ch)
        line += n
    text = "".join(out)
    _validated[defs_text] = text
    return text


def theorem_statement(ob: Obligation, axioms: list[L.Axiom], fn_names: dict[str, str]) -> str:
    namer = Namer()
    pr = LeanPrinter(namer, fn_names)
    terms = list(ob.hyps) + [ob.goal]
    consts = sorted(set().union(*(L.consts(t) for t in terms)), key=lambda c: c.name)
    binders = [f"({namer(c.name)} : {lean_sort(c.sort)})" for c in consts]
    lemmas = [f"({re.sub(r'[^A-Za-z0-9_]', '_', ax.name)} : {pr.t(ax.formula)})" for ax in axioms]
    hyps = [f"(h{i + 1} : {pr.t(h)})" for i, h in enumerate(ob.hyps) if h != L.TRUE]
    goal = pr.t(ob.goal)
    parts = binders + lemmas + hyps
    body = "\n    ".join(parts)
    return f"\n    {body} :\n    {goal}" if parts else f" : {goal}"


def theorem_name(ob: Obligation) -> str:
    return "vc_" + re.sub(r"[^A-Za-z0-9_]", "_", ob.id).strip("_")


def statement_hash(statement: str, defs_text: str) -> str:
    return hashlib.sha256((defs_text + "\n" + statement).encode()).hexdigest()[:12]


def build_context(ob: Obligation, theory: Theory, fn_names: dict[str, str]) -> tuple[str, str]:
    """(definitions text, theorem statement) for one obligation."""
    terms = list(ob.hyps) + [ob.goal]
    defs, axioms = theory.closure(terms, ob.exclude_axioms)
    records = collect_records(terms + [a.formula for a in axioms] + [d.body for d in defs if d.body is not None])
    defs_text = render_defs(defs, records, fn_names)
    stmt = theorem_statement(ob, axioms, fn_names)
    return defs_text, stmt


# ---------------------------------------------------------------------------
# Running Lean


@dataclass
class LeanMessage:
    severity: str
    line: int
    text: str


@dataclass
class LeanRun:
    ok: bool
    messages: list[LeanMessage]
    seconds: float
    error: str = ""


def run_lean(lean: str, text: str, timeout: float = LEAN_TIMEOUT_S) -> LeanRun:
    t0 = time.perf_counter()
    with tempfile.TemporaryDirectory(prefix="telic-lean-") as d:
        path = os.path.join(d, "Obligations.lean")
        Path(path).write_text(text)
        try:
            p = subprocess.run([lean, "--json", path], capture_output=True, text=True, timeout=timeout, cwd=d)
        except subprocess.TimeoutExpired:
            return LeanRun(False, [], time.perf_counter() - t0, error=f"Lean timed out after {timeout:.0f}s")
    msgs: list[LeanMessage] = []
    for line in p.stdout.splitlines():
        try:
            m = json.loads(line)
        except ValueError:
            continue
        msgs.append(LeanMessage(m.get("severity", ""), (m.get("pos") or {}).get("line", 0), m.get("data", "")))
    ok = p.returncode == 0 and not any(m.severity == "error" for m in msgs)
    err = "" if ok or msgs else (p.stderr.strip() or "lean failed")
    return LeanRun(ok, msgs, time.perf_counter() - t0, error=err)


@dataclass
class Attempt:
    name: str
    statement: str
    proof: str
    first_line: int = 0
    last_line: int = 0
    print_line: int = 0


@dataclass
class AttemptResult:
    ok: bool
    errors: list[str] = field(default_factory=list)
    axioms: list[str] = field(default_factory=list)


def check_attempts(lean: str, defs_text: str, attempts: list[Attempt]) -> tuple[list[AttemptResult], LeanRun]:
    """Elaborate many theorems in one Lean process; attribute messages back."""
    lines = PRELUDE.format(heartbeats=HEARTBEATS).splitlines() + [""] + defs_text.splitlines() + [""]
    for at in attempts:
        at.first_line = len(lines) + 1
        body = at.proof.strip("\n")
        block = f"theorem {at.name}{at.statement} := by\n" + "\n".join("  " + l if l.strip() else l for l in body.splitlines())
        lines += block.splitlines()
        at.last_line = len(lines)
        lines.append(f"#print axioms {at.name}")
        at.print_line = len(lines)
        lines.append("")
    run = run_lean(lean, "\n".join(lines) + "\n")
    defs_end = len(PRELUDE.format(heartbeats=HEARTBEATS).splitlines()) + 1 + len(defs_text.splitlines()) + 1
    def_errors = [m for m in run.messages if m.severity == "error" and m.line <= defs_end]
    results = []
    for at in attempts:
        r = AttemptResult(True)
        if def_errors:
            r.ok = False
            r.errors = [f"(definitions) line {m.line}: {m.text}" for m in def_errors]
        for m in run.messages:
            if at.first_line <= m.line <= at.last_line and m.severity == "error":
                r.ok = False
                r.errors.append(m.text)
            if at.first_line <= m.line <= at.last_line and m.severity == "warning" and "sorry" in m.text:
                r.ok = False
                r.errors.append(m.text)
            if m.line == at.print_line and "depends on axioms" in m.text:
                r.axioms = re.findall(r"[\w.]+", m.text.split(":", 1)[1])
        if run.error and not run.messages:
            r.ok = False
            r.errors.append(run.error)
        bad = [a for a in r.axioms if a not in STANDARD_AXIOMS]
        if bad:
            r.ok = False
            r.errors.append(f"proof depends on non-standard axioms: {', '.join(bad)}")
        results.append(r)
    return results, run


# ---------------------------------------------------------------------------
# Sidecar proof files


def sidecar_path(source_path: str) -> str:
    return source_path + ".proof.lean"


BLOCK_RE = re.compile(r"^-- telic: (?P<id>\S+) statement=(?P<hash>[0-9a-f]+)\s*$", re.M)


@dataclass
class StoredProof:
    id: str
    hash: str
    proof: str  # tactic text after ':= by'


def read_sidecar(path: str) -> dict[str, StoredProof]:
    if not os.path.exists(path):
        return {}
    text = Path(path).read_text()
    out: dict[str, StoredProof] = {}
    matches = list(BLOCK_RE.finditer(text))
    for i, m in enumerate(matches):
        end = matches[i + 1].start() if i + 1 < len(matches) else len(text)
        block = text[m.end():end]
        k = block.find(":= by")
        if k < 0:
            continue
        proof = block[k + len(":= by"):]
        proof = "\n".join(l[2:] if l.startswith("  ") else l for l in proof.strip("\n").splitlines()).rstrip()
        out[m.group("id")] = StoredProof(m.group("id"), m.group("hash"), proof)
    return out


def write_sidecar(path: str, source_rel: str, entries: dict[str, tuple[str, str, str, str]]) -> None:
    """entries: id -> (hash, theorem name, statement, proof)."""
    head = (
        f"-- Lean proofs for {source_rel}, checked by telic.\n"
        "-- Each block proves one obligation. telic regenerates the statements from the\n"
        "-- code on every run; edit only the tactic proofs. A block whose statement no\n"
        "-- longer matches the code is reported as stale and ignored.\n"
    )
    parts = [head]
    for oid in sorted(entries):
        h, name, stmt, proof = entries[oid]
        body = "\n".join("  " + l if l.strip() else l for l in proof.strip("\n").splitlines())
        parts.append(f"-- telic: {oid} statement={h}\ntheorem {name}{stmt} := by\n{body}\n")
    Path(path).write_text("\n".join(parts))


# ---------------------------------------------------------------------------
# Escalation from `telic check`


@dataclass
class LeanOutcome:
    status: str  # proved | stale | failed | unavailable | unsupported
    summary: str
    method: str = ""
    errors: list[str] = field(default_factory=list)


def _fn_names(program) -> dict[str, str]:
    return {}


def escalate(program, theory: Theory, rep, cache, key_fn, root: str | None = None) -> None:
    """Try Lean on every 'unknown' verdict of one function report."""
    lean = find_lean()
    unknown = [v for v in rep.verdicts if v.status == "unknown"]
    if not unknown:
        return
    if lean is None:
        for v in unknown:
            v.lean = LeanOutcome("unavailable", "Lean 4 not found (set TELIC_LEAN or put 'lean' on PATH)")
        return
    root = root or getattr(program, "root", os.getcwd())
    src = rep.ref.module.path
    side = sidecar_path(os.path.join(root, src) if not os.path.isabs(src) else src)
    stored = read_sidecar(side)
    attempts: list[tuple[Any, Attempt, str, str]] = []  # (verdict, attempt, hash, source)
    groups: dict[str, list] = {}
    for v in unknown:
        try:
            defs_text, stmt = build_context(v.ob, theory, {})
        except LeanUnsupported as e:
            v.lean = LeanOutcome("unsupported", f"cannot express in Lean: {e}")
            continue
        h = statement_hash(stmt, defs_text)
        k = key_fn(v.ob, theory)
        sp = stored.get(v.ob.id)
        hit = cache.get(k)
        if hit is not None and hit.get("method", "").startswith("lean") and (sp is None or hit.get("proof_hash") == _phash(sp.proof)):
            v.status = "proved"
            v.method = "cache"
            v.reason = hit["method"]
            v.lean = LeanOutcome("proved", hit["method"], method=hit["method"])
            continue
        if sp is not None and sp.hash != h:
            v.lean = LeanOutcome("stale", f"the proof in {os.path.basename(side)} is stale: the obligation changed (re-prove with 'telic prove')")
            # still try automation below
        name = theorem_name(v.ob)
        if sp is not None and sp.hash == h:
            attempts.append((v, Attempt(name, stmt, sp.proof), h, "sidecar"))
        else:
            auto = "first\n  | " + "\n  | ".join(AUTO_TACTICS + _def_tactics(theory, v.ob))
            attempts.append((v, Attempt(name, stmt, auto), h, "auto"))
        groups.setdefault(defs_text, []).append(len(attempts) - 1)
    for defs_text, idxs in groups.items():
        batch = [attempts[i][1] for i in idxs]
        results, run = check_attempts(lean, validated_defs(lean, defs_text), batch)
        for i, res in zip(idxs, results):
            v, at, h, how = attempts[i]
            if res.ok:
                method = "lean:proof" if how == "sidecar" else "lean:auto"
                v.status = "proved"
                v.method = method
                v.lean = LeanOutcome("proved", "proved in Lean" + (" (sidecar proof)" if how == "sidecar" else " (automatic tactics)"), method=method, errors=[])
                entry = {"method": method}
                if how == "sidecar":
                    entry["proof_hash"] = _phash(at.proof)
                cache.put(key_fn(v.ob, theory), entry)
            else:
                prev = v.lean
                if prev is not None and prev.status == "stale":
                    v.lean = LeanOutcome("stale", prev.summary, errors=res.errors)
                elif how == "sidecar":
                    v.lean = LeanOutcome("failed", "the sidecar proof does not check: " + _first_error(res.errors), errors=res.errors)
                else:
                    v.lean = LeanOutcome("failed", f"automatic tactics failed; write a proof with 'telic lean {v.ob.id}' or 'telic prove --agent CMD'", errors=res.errors)


def _phash(proof: str) -> str:
    return hashlib.sha256(proof.strip().encode()).hexdigest()[:12]


def _first_error(errors: list[str]) -> str:
    if not errors:
        return "unknown error"
    return errors[0].strip().splitlines()[0][:160]


def _def_tactics(theory: Theory, ob: Obligation) -> list[str]:
    defs, _ = theory.closure(list(ob.hyps) + [ob.goal], ob.exclude_axioms)
    names = [d.name for d in defs]
    if not names:
        return []
    ns = ", ".join(names)
    return [f"(grind [{ns}])", f"(simp_all [{ns}] <;> omega)", f"(simp_all [{ns}] <;> grind)"]


# ---------------------------------------------------------------------------
# Commands: telic lean / telic prove


def obligation_document(ob: Obligation, theory: Theory, proof: str = "sorry") -> str:
    defs_text, stmt = build_context(ob, theory, {})
    lean = find_lean()
    if lean is not None:
        defs_text = validated_defs(lean, defs_text)
    h = statement_hash(stmt, defs_text)
    return (
        PRELUDE.format(heartbeats=HEARTBEATS)
        + "\n"
        + defs_text
        + f"\n-- telic: {ob.id} statement={h}\n-- {ob.message}\ntheorem {theorem_name(ob)}{stmt} := by\n  {proof}\n"
    )


def _find(report, oid: str):
    for f in report.functions:
        for v in f.verdicts:
            if v.ob.id == oid:
                return f, v
    return None, None


def cmd_lean(args) -> int:
    from .checker import check

    root = os.path.abspath(args.root or os.getcwd())
    fname = args.id.split("/")[0]
    opts = args._options(args, root)
    opts.only = {fname}
    opts.lean = False
    opts.replay = False
    rep = check(args.paths, opts, root=root)
    f, v = _find(rep, args.id)
    if v is None:
        ids = [v.ob.id for f in rep.functions for v in f.verdicts]
        print(f"no obligation '{args.id}'. Obligations of {fname}:\n  " + "\n  ".join(ids))
        return 1
    from .checker import build_theory

    theory, _ = build_theory(rep.program, {k: m for f in rep.functions if f.inferred for k, m in f.inferred.options.measures.items()})
    print(obligation_document(v.ob, theory))
    return 0


AGENT_PROMPT = """You are proving one verification condition in Lean 4 (version {version}, core library only: no Mathlib).

The obligation comes from this {language} function ({path}):

```{language}
{source}
```

Obligation {oid}: {message}

Here is the complete Lean file. Everything above the final theorem is fixed:

```lean
{document}
```

Replace `sorry` with a tactic proof. Useful tactics in core Lean: omega (linear integer arithmetic),
grind, simp, simp_all, decide, induction, cases, unfold, rw, exact, constructor, intro, by_cases.

Hints:
- Each definition `f` comes with a proved lemma `f_def` that unfolds one step of `f`
  (under its precondition, if it has one). Prefer `rw [f_def _ h]` / `have := f_def x h` to unfolding by hand.
- `Telic.upd_apply` unfolds array updates.
- To prove `P x` for an `x : Int` with `0 ≤ x` by induction, prove `∀ k : Nat, P (k : Int)` with
  `induction k`, then finish with `have := key x.toNat; rwa [Int.toNat_of_nonneg hx] at this`.
- Casts: `((k + 1 : Nat) : Int) = (k : Int) + 1` is `by omega`; rewrite argument shapes with
  `have e : a = b := by omega` then `rw [e]` before applying a lemma.

Reply with ONLY the tactic proof inside one ```lean code block (the text that goes after `:= by`), nothing else.
{feedback}"""


def extract_proof(text: str) -> str | None:
    blocks = re.findall(r"```(?:lean4?|)\s*\n(.*?)```", text, re.S)
    if not blocks:
        return None
    proof = blocks[-1].strip("\n")
    # Accept a full theorem by mistake: keep only what follows its ':= by'
    if re.match(r"\s*(theorem|lemma|example)\b", proof) and ":= by" in proof:
        proof = proof.split(":= by", 1)[1]
    lines = proof.splitlines()
    indents = [len(l) - len(l.lstrip()) for l in lines if l.strip()]
    cut = min(indents) if indents else 0
    return "\n".join(l[cut:] for l in lines).strip("\n")


def run_agent(cmd: str, prompt: str, timeout: float = 600) -> str:
    import shlex

    p = subprocess.run(shlex.split(cmd), input=prompt, capture_output=True, text=True, timeout=timeout)
    return p.stdout


def cmd_prove(args) -> int:
    from .checker import build_theory, check, obligation_key
    from .render import Paint

    paint = Paint()
    root = os.path.abspath(args.root or os.getcwd())
    lean = find_lean()
    if lean is None:
        print("telic prove: Lean 4 not found (set TELIC_LEAN or put 'lean' on PATH)")
        return 2
    opts = args._options(args, root)
    opts.replay = False
    rep = check(args.paths, opts, root=root)
    measures = {k: m for f in rep.functions if f.inferred for k, m in f.inferred.options.measures.items()}
    theory, _ = build_theory(rep.program, measures)
    todo = [(f, v) for f in rep.functions for v in f.verdicts if v.status == "unknown"]
    if args.id:
        todo = [(f, v) for f, v in todo if v.ob.id in args.id]
    if not todo:
        print(paint.green("✓") + " nothing to prove: no open obligation is waiting on Lean")
        return 0
    version = lean_version(lean)
    proved = 0
    for f, v in todo:
        ob = v.ob
        print(f"{paint.bold(ob.id)}  {paint.dim(ob.message)}")
        if not args.agent:
            reason = v.lean.summary if v.lean else "open"
            print(f"  {paint.yellow('?')} {reason}")
            continue
        try:
            defs_text, stmt = build_context(ob, theory, {})
        except LeanUnsupported as e:
            print(f"  {paint.gray('⊘')} {e}")
            continue
        h = statement_hash(stmt, defs_text)
        doc = obligation_document(ob, theory)
        feedback = ""
        ok_proof = None
        for attempt in range(1, args.attempts + 1):
            prompt = AGENT_PROMPT.format(
                version=version,
                language=f.ref.module.language,
                path=f.ref.module.path,
                source=f.fn.source,
                oid=ob.id,
                message=ob.message,
                document=doc,
                feedback=feedback,
            )
            try:
                reply = run_agent(args.agent, prompt)
            except (OSError, subprocess.TimeoutExpired) as e:
                print(f"  {paint.red('!')} agent failed: {e}")
                break
            proof = extract_proof(reply)
            if not proof:
                feedback = "\nYour previous reply had no ```lean code block. Reply with only the proof in one."
                print(f"  {paint.dim(f'attempt {attempt}: no proof in reply')}")
                continue
            res, _ = check_attempts(lean, validated_defs(lean, defs_text), [Attempt(theorem_name(ob), stmt, proof)])
            if res[0].ok:
                ok_proof = proof
                print(f"  {paint.green('✓')} attempt {attempt}: Lean accepted the proof  {paint.dim('axioms: ' + ', '.join(res[0].axioms) if res[0].axioms else '')}")
                break
            err = "\n".join(res[0].errors)[:3000]
            print(f"  {paint.dim(f'attempt {attempt}: rejected — ' + _first_error(res[0].errors))}")
            feedback = f"\nYour previous proof was:\n```lean\n{proof}\n```\nLean rejected it with:\n```\n{err}\n```\nFix the proof."
        if ok_proof is None:
            continue
        proved += 1
        src = f.ref.module.path
        side = sidecar_path(os.path.join(root, src))
        stored = read_sidecar(side)
        entries = {}
        # keep other proofs (re-render their statements verbatim from the file)
        existing_text = Path(side).read_text() if os.path.exists(side) else ""
        for sid, sp in stored.items():
            if sid == ob.id:
                continue
            m = re.search(rf"-- telic: {re.escape(sid)} statement={sp.hash}\ntheorem (\S+)(.*?) := by", existing_text, re.S)
            if m:
                entries[sid] = (sp.hash, m.group(1), m.group(2), sp.proof)
        entries[ob.id] = (h, theorem_name(ob), stmt, ok_proof)
        write_sidecar(side, src, entries)
        opts.cache_path and None
        print(f"  {paint.dim('saved to ' + os.path.relpath(side, root))}")
    del obligation_key
    print()
    print(f"{proved} of {len(todo)} proved")
    return 0 if proved == len(todo) else 1


def add_commands(sub, common, options) -> None:
    l = sub.add_parser("lean", help="print the Lean 4 theorem for one obligation")
    l.add_argument("id", help="obligation id, e.g. triangle/ensures@4>9")
    common(l)
    l.set_defaults(func=cmd_lean, _options=options)

    p = sub.add_parser("prove", help="discharge open obligations in Lean")
    common(p)
    p.add_argument("--agent", metavar="CMD", help="command that reads a prompt on stdin and prints a proof, e.g. \"claude -p\"")
    p.add_argument("--attempts", type=int, default=4, help="attempts per obligation (default 4)")
    p.add_argument("--id", action="append", help="only these obligation ids")
    p.set_defaults(func=cmd_prove, _options=options)
