"""Lean 4 backend: the proof ladder's upper rungs.

When Z3 cannot decide an obligation (induction, nonlinear arithmetic, ...),
telic renders the *same* verification condition as a Lean 4 theorem and
tries, in order:

1. a proof already written for it in the source file's sidecar
   (``pricing.py`` -> ``pricing.py.proof.lean``), if its statement still
   matches the current code;
2. an automatic tactic ladder (omega, grind, simp, induction...);
3. with ``telic prove --agent SPEC``, an agent that writes the proof, with
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


TOOLCHAIN = Path(__file__).parent / "lean" / "lean-toolchain"


def pinned_toolchain() -> str:
    return TOOLCHAIN.read_text().strip()


def find_lean() -> str | None:
    env = os.environ.get("TELIC_LEAN")
    if env and os.path.exists(env):
        return env
    elan = os.environ.get("ELAN_HOME", os.path.expanduser("~/.elan"))
    pinned = os.path.join(elan, "toolchains", pinned_toolchain().replace("/", "--").replace(":", "---"), "bin", "lean")
    if os.path.exists(pinned):
        return pinned
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
        return f"({lean_sort(L.index_sort(s))} → {lean_sort(s.elem)})"
    if s.name == "Rec":
        return s.rec or "Rec"
    raise LeanUnsupported(f"no Lean type for {s}")


class LeanPrinter:
    def __init__(self, namer: Namer, fn_names: dict[str, str], free_fns: set[str] = frozenset()):  # type: ignore[assignment]
        self.n = namer
        self.fn_names = fn_names
        self.free_fns = free_fns  # uninterpreted symbols: variables of the theorem
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
            name = self.n(x.name) if x.name in self.free_fns else self.fn_names.get(x.name, x.name)
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
        if op == "K":
            return f"(fun _ => {self.t(a[0])})", 100
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
def upd {{ι α : Type}} [DecidableEq ι] (a : ι → α) (i : ι) (v : α) : ι → α := fun j => if j = i then v else a j
@[simp] theorem upd_same {{ι α : Type}} [DecidableEq ι] (a : ι → α) (i : ι) (v : α) : upd a i v i = v := by simp [upd]
@[simp] theorem upd_other {{ι α : Type}} [DecidableEq ι] (a : ι → α) (i j : ι) (v : α) (h : j ≠ i) : upd a i v j = a j := by simp [upd, h]
theorem upd_apply {{ι α : Type}} [DecidableEq ι] (a : ι → α) (i j : ι) (v : α) : upd a i v j = if j = i then v else a j := rfl
end Telic
"""


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
        lines.append(f"structure {r.rec} where\n  mk ::\n" + "".join(f"  {n} : {lean_sort(s)}\n" for n, s in r.fields))
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
            if any("struct.depth" in L.fns(m) for m in d.measure):
                raise LeanUnsupported(f"'{d.name}' terminates because its argument is a smaller part each time, which Lean does not model")
            parts = [f"{pr.t(m, 101)}.toNat" for m in d.measure]
            meas = parts[0] if len(parts) == 1 else f"({', '.join(parts)})"
            # (a lexicographic measure: lower the first part, or keep it and lower the next)
            lex = "" if len(parts) == 1 else " | (apply Prod.Lex.left; first | omega | (simp_all; omega)) | (apply Prod.Lex.right; first | omega | (simp_all; omega)) | decreasing_tactic"
            lines.append(f"{doc}def {name} {params} : {lean_sort(d.sort)} :=\n  {body}\ntermination_by {meas}\ndecreasing_by all_goals (first | omega | (simp_all; omega) | grind{lex})\n")
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


def theorem_statement(ob: Obligation, axioms: list[L.Axiom], fn_names: dict[str, str], defined: set[str] | None = None) -> str:
    """``defined``: the functions the definitions text declares; any other
    function symbol is uninterpreted and becomes a variable."""
    namer = Namer()
    terms = list(ob.hyps) + [ob.goal]
    free: dict[str, L.Fn] = {}
    if defined is not None:
        for t in terms + [ax.formula for ax in axioms]:
            for x in L.iter_terms(t):
                if isinstance(x, L.Fn) and x.args and x.name not in defined and x.name not in fn_names:
                    free.setdefault(x.name, x)
    pr = LeanPrinter(namer, fn_names, set(free))
    consts = sorted(set().union(*(L.consts(t) for t in terms)), key=lambda c: c.name)
    binders = [f"({namer(c.name)} : {lean_sort(c.sort)})" for c in consts]
    binders += [f"({namer(f.name)} : {' → '.join(lean_sort(a.sort) for a in f.args)} → {lean_sort(f.sort)})" for _, f in sorted(free.items())]
    lemmas = [f"({re.sub(r'[^A-Za-z0-9_]', '_', ax.name)} : {pr.t(ax.formula)})" for ax in axioms]
    hyps = [f"(h{i + 1} : {pr.t(h)})" for i, h in enumerate(ob.hyps) if h != L.TRUE]
    goal = pr.t(ob.goal)
    parts = binders + lemmas + hyps
    body = "\n    ".join(parts)
    return f"\n    {body} :\n    {goal}" if parts else f" : {goal}"


def theorem_name(ob: Obligation) -> str:
    return "vc_" + re.sub(r"[^A-Za-z0-9_]", "_", ob.id).strip("_")


def statement_hash(statement: str, defs_text: str) -> str:
    # Doc comments carry file paths; moving a file must not invalidate proofs.
    defs = re.sub(r"/--.*?-/\n?", "", defs_text, flags=re.S)
    return hashlib.sha256((defs + "\n" + statement).encode()).hexdigest()[:12]


def build_context(ob: Obligation, theory: Theory, fn_names: dict[str, str]) -> tuple[str, str]:
    """(definitions text, theorem statement) for one obligation."""
    terms = list(ob.hyps) + [ob.goal]
    defs, axioms = theory.closure(terms, ob.exclude_axioms)
    records = collect_records(terms + [a.formula for a in axioms] + [d.body for d in defs if d.body is not None])
    defs_text = render_defs(defs, records, fn_names)
    stmt = theorem_statement(ob, axioms, fn_names, {d.name for d in defs})
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


@dataclass
class AttemptResult:
    ok: bool
    errors: list[str] = field(default_factory=list)
    axioms: list[str] = field(default_factory=list)


COMMAND_RE = re.compile(
    r"^\s*(axiom|theorem|lemma|def|abbrev|instance|example|namespace|section|end|open|set_option|attribute|"
    r"macro|macro_rules|syntax|elab|elab_rules|notation|infix|infixl|infixr|prefix|postfix|universe|variable|import|"
    r"opaque|structure|class|inductive|mutual|noncomputable|private|protected|partial|unsafe|initialize|"
    r"builtin_initialize|export|local|scoped|deriving|declare_syntax_cat|run_cmd|run_elab|run_meta)\b|^\s*(@\[|#[a-z_])",
    re.M,
)


def proof_is_tactics_only(proof: str) -> str | None:
    """A proof must be a tactic block. A line that starts a Lean command
    could end the theorem and add declarations (an axiom, a namespace that
    hides the real theorem from the audit), so such proofs are refused."""
    m = COMMAND_RE.search(proof)
    if m:
        return f"proof text may only contain tactics; line starting with '{m.group(0).strip()}' is a Lean command"
    return None


def _check_one(lean: str, defs_text: str, at: Attempt) -> AttemptResult:
    bad = proof_is_tactics_only(at.proof)
    if bad:
        return AttemptResult(False, [bad])
    pre = PRELUDE.format(heartbeats=HEARTBEATS)
    body = "\n".join("  " + l if l.strip() else l for l in at.proof.strip("\n").splitlines())
    text = f"{pre}\n{defs_text}\n\ntheorem {at.name}{at.statement} := by\n{body}\n\n#print axioms _root_.{at.name}\n"
    run = run_lean(lean, text)
    r = AttemptResult(True)
    if run.error and not run.messages:
        return AttemptResult(False, [run.error])
    audited = False
    for m in run.messages:
        # Every error anywhere in the file counts: nothing may fail around the proof.
        if m.severity == "error":
            r.ok = False
            r.errors.append(m.text)
        elif m.severity == "warning" and "sorry" in m.text:
            r.ok = False
            r.errors.append(m.text)
        if f"'{at.name}' depends on axioms" in m.text:
            audited = True
            r.axioms = re.findall(r"[\w.]+", m.text.split(":", 1)[1])
        elif f"'{at.name}' does not depend on any axioms" in m.text:
            audited = True
    if r.ok and not run.ok:
        r.ok = False
        r.errors.append("Lean exited abnormally")
    if r.ok and not audited:
        r.ok = False
        r.errors.append("could not audit the axioms of the proved theorem")
    bad_axioms = [a for a in r.axioms if a not in STANDARD_AXIOMS]
    if bad_axioms:
        r.ok = False
        r.errors.append(f"proof depends on non-standard axioms: {', '.join(bad_axioms)}")
    return r


def check_attempts(lean: str, defs_text: str, attempts: list[Attempt]) -> tuple[list[AttemptResult], None]:
    """Check each proof in its own Lean file (in parallel), so one proof can
    never see, or interfere with, another."""
    from concurrent.futures import ThreadPoolExecutor

    from .jobs import take

    with take(None, len(attempts)) as workers, ThreadPoolExecutor(max_workers=workers) as pool:
        results = list(pool.map(lambda at: _check_one(lean, defs_text, at), attempts))
    return results, None


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
    proof_bytes: str


def read_sidecar(path: str) -> dict[str, StoredProof]:
    if not os.path.exists(path):
        return {}
    text = Path(path).read_bytes().decode()
    out: dict[str, StoredProof] = {}
    matches = list(BLOCK_RE.finditer(text))
    for i, m in enumerate(matches):
        end = matches[i + 1].start() if i + 1 < len(matches) else len(text)
        block = text[m.end():end]
        k = block.find(":= by")
        if k < 0:
            continue
        proof_bytes = block[k + len(":= by"):]
        proof = "\n".join(l[2:] if l.startswith("  ") else l for l in proof_bytes.strip("\n").splitlines()).rstrip()
        out[m.group("id")] = StoredProof(m.group("id"), m.group("hash"), proof, proof_bytes)
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


def _lean_receipt_key(context: str, statement: str, theorem: str, proof: str | None, proof_bytes: str | None, identity: Any) -> str:
    renderer = hashlib.sha256()
    for path in (Path(__file__), Path(__file__).with_name("toolchain.py")):
        renderer.update(path.name.encode())
        renderer.update(path.read_bytes())
    payload = json.dumps(
        [PRELUDE.format(heartbeats=HEARTBEATS), context, theorem, statement, proof, proof_bytes, identity, renderer.hexdigest()],
        sort_keys=True,
    )
    return "lean:" + hashlib.sha256(payload.encode()).hexdigest()


def escalate(program, theory: Theory, rep, cache, root: str | None = None, auto: bool = True) -> None:
    """Try Lean on every 'unknown' verdict of one function report."""
    lean = find_lean()
    unknown = [v for v in rep.verdicts if v.status == "unknown"]
    if not unknown:
        return
    if lean is None:
        for v in unknown:
            v.lean = LeanOutcome("unavailable", "Lean 4 not found (set TELIC_LEAN or put 'lean' on PATH)")
        return
    from .toolchain import lean as lean_identity

    identity = lean_identity()
    root = root or getattr(program, "root", os.getcwd())
    src = rep.ref.module.path
    side = sidecar_path(os.path.join(root, src) if not os.path.isabs(src) else src)
    stored = read_sidecar(side)
    if not auto and not stored:
        return
    attempts: list[tuple[Any, Attempt, str, str, str]] = []  # (verdict, attempt, hash, source, cache key)
    groups: dict[str, list] = {}
    for v in unknown:
        try:
            defs_text, stmt = build_context(v.ob, theory, {})
        except LeanUnsupported as e:
            v.lean = LeanOutcome("unsupported", f"cannot express in Lean: {e}")
            continue
        h = statement_hash(stmt, defs_text)
        rendered_defs = validated_defs(lean, defs_text)
        sp = stored.get(v.ob.id)
        if sp is None or sp.hash != h:
            # The obligation id carries line numbers; a proof whose statement
            # is unchanged still applies after the code above it moved.
            fn_prefix = v.ob.id.split("/")[0] + "/"
            moved = [x for x in stored.values() if x.hash == h and x.id.startswith(fn_prefix)]
            if moved:
                sp = moved[0]
        has_sidecar_proof = sp is not None and sp.hash == h
        proof = sp.proof if has_sidecar_proof else None
        proof_bytes = sp.proof_bytes if has_sidecar_proof else None
        k = _lean_receipt_key(rendered_defs, stmt, theorem_name(v.ob), proof, proof_bytes, identity)
        hit = cache.get(k)
        valid = hit is not None and hit.get("method") == "lean:auto"
        valid = valid or hit is not None and hit.get("method") == "lean:proof" and has_sidecar_proof and hit.get("proof_hash") == _phash(sp.proof)
        if valid:
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
            attempts.append((v, Attempt(name, stmt, sp.proof), h, "sidecar", k))
        else:
            if not auto:
                continue
            tactics = "first\n  | " + "\n  | ".join(AUTO_TACTICS + _def_tactics(theory, v.ob))
            attempts.append((v, Attempt(name, stmt, tactics), h, "auto", k))
        groups.setdefault(rendered_defs, []).append(len(attempts) - 1)
    for defs_text, idxs in groups.items():
        batch = [attempts[i][1] for i in idxs]
        results, _ = check_attempts(lean, defs_text, batch)
        for i, res in zip(idxs, results):
            v, at, h, how, k = attempts[i]
            if res.ok:
                method = "lean:proof" if how == "sidecar" else "lean:auto"
                v.status = "proved"
                v.method = method
                v.lean = LeanOutcome("proved", "proved in Lean" + (" (sidecar proof)" if how == "sidecar" else " (automatic tactics)"), method=method, errors=[])
                entry = {"method": method}
                if how == "sidecar":
                    entry["proof_hash"] = _phash(at.proof)
                cache.put(k, entry)
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
    lines = errors[0].strip().splitlines() if errors else []
    return lines[0][:160] if lines else "unknown error"


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
    opts.receipts = False
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
The proof must be tactics only: no top-level commands (no `theorem`, `lemma`, `open ... in`, `set_option`,
`namespace`, `#print`); state helper facts with `have` inside the proof.
{feedback}"""


def cmd_prove(args) -> int:
    from . import prover as P
    from .checker import build_theory, check
    from .render import Paint

    paint = Paint()
    try:
        agent = P.resolve(args.agent)
    except (P.ProverError, ImportError, AttributeError) as e:
        print(f"telic prove: {e}")
        return 2
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
        if agent is None:
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
            request = {
                "prompt": prompt,
                "document": doc,
                "theorem": theorem_name(ob),
                "statement": stmt,
                "lean_version": version,
                "obligation": ob.id,
                "message": ob.message,
                "attempt": attempt,
                "feedback": feedback,
            }
            try:
                proof = agent.prove(request)
            except P.ProverError as e:
                print(f"  {paint.red('!')} {agent.name} failed: {e}")
                break
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
        print(f"  {paint.dim('saved to ' + os.path.relpath(side, root))}")
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
    p.add_argument("--agent", metavar="SPEC", help="prover: a command that reads a prompt on stdin (\"claude -p\"), http:URL or py:MODULE:FUNC; default $TELIC_PROVER")
    p.add_argument("--attempts", type=int, default=4, help="attempts per obligation (default 4)")
    p.add_argument("--id", action="append", help="only these obligation ids")
    p.set_defaults(func=cmd_prove, _options=options)
