import re
import subprocess
from pathlib import Path

from telic import logic as L
from telic.lean import extract_proof, find_lean, read_sidecar

from conftest import needs_lean, run_check

THEORY = Path(__file__).resolve().parent.parent / "telic" / "lean" / "Theory.lean"

POW = """
def pow2(n: int) -> int:
    #@ requires n >= 0
    #@ ensures result >= 1
    #@ decreases n
    if n == 0:
        return 1
    return 2 * pow2(n - 1)


def pow2_add(a: int, b: int) -> bool:
    #@ requires a >= 0 and b >= 0
    #@ ensures result
    return pow2(a + b) == pow2(a) * pow2(b)
"""

PROOF = """  have key : ∀ k : Nat, pow2 ((k : Int) + b) = pow2 (k : Int) * pow2 b := by
    intro k
    induction k with
    | zero =>
      have h0 : pow2 0 = 1 := by rw [pow2_def 0 (by omega)]; simp
      have e : ((0 : Nat) : Int) + b = b := by omega
      have e2 : ((0 : Nat) : Int) = 0 := by omega
      rw [e, e2, h0]; omega
    | succ k ih =>
      have e1 : ((k + 1 : Nat) : Int) + b = ((k : Int) + b) + 1 := by omega
      have e2 : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by omega
      rw [e1, e2, pow2_def ((k : Int) + b + 1) (by omega), pow2_def ((k : Int) + 1) (by omega)]
      have e3 : (k : Int) + b + 1 - 1 = (k : Int) + b := by omega
      have e4 : (k : Int) + 1 - 1 = k := by omega
      have n1 : ¬((k : Int) + b + 1 = 0) := by omega
      have n2 : ¬((k : Int) + 1 = 0) := by omega
      rw [if_neg n1, if_neg n2, e3, e4, ih, Int.mul_assoc]
  have := key a.toNat
  rw [Int.toNat_of_nonneg h1.1] at this
  exact this"""


@needs_lean
def test_theory_lemmas_are_proved_in_lean():
    lean = find_lean()
    out = subprocess.run([lean, str(THEORY)], capture_output=True, text=True, timeout=300)
    assert out.returncode == 0, out.stdout + out.stderr
    assert "sorry" not in out.stdout
    text = THEORY.read_text()
    # every lemma handed to Z3 has a Lean proof of the same name
    for elem, prefix in ((L.INT, "seqsum"), (L.REAL, "seqsumR")):
        for ax in L.theory_lemmas(elem):
            name = ax.name
            name = name.replace("seqsum_r_", "seqsumR_").replace("seqcount_int_", "seqcount_").replace("seqcount_real_", "seqcount_")
            assert re.search(rf"theorem {re.escape(name)}\b", text), f"no Lean proof for {ax.name}"


def _sidecar(tmp_path, proof):
    (tmp_path / "hard.py.proof.lean").write_text("")
    rep = run_check(tmp_path, {"hard.py": POW}, replay=False, timeout_ms=1500)
    v = next(v for f in rep.functions for v in f.verdicts if v.status != "proved")
    from telic.checker import build_theory
    from telic.lean import build_context, statement_hash, theorem_name, write_sidecar

    theory, _ = build_theory(rep.program, {})
    defs_text, stmt = build_context(v.ob, theory, {})
    write_sidecar(str(tmp_path / "hard.py.proof.lean"), "hard.py", {v.ob.id: (statement_hash(stmt, defs_text), theorem_name(v.ob), stmt, proof)})
    return v.ob.id


@needs_lean
def test_sidecar_proof_is_checked_and_used(tmp_path):
    oid = _sidecar(tmp_path, PROOF)
    rep = run_check(tmp_path, {"hard.py": POW}, replay=False, timeout_ms=1500)
    f = next(f for f in rep.functions if f.fn.name == "pow2_add")
    assert f.status == "proved", [(v.ob.id, v.status, v.lean and v.lean.summary) for v in f.verdicts]
    assert any(v.method == "lean:proof" for v in f.verdicts)
    assert oid in read_sidecar(str(tmp_path / "hard.py.proof.lean"))


@needs_lean
def test_sorry_is_rejected(tmp_path):
    _sidecar(tmp_path, "sorry")
    rep = run_check(tmp_path, {"hard.py": POW}, replay=False, timeout_ms=1500)
    f = next(f for f in rep.functions if f.fn.name == "pow2_add")
    assert f.status == "open"
    v = next(v for v in f.verdicts if v.status != "proved")
    assert v.lean.status == "failed" and "sorry" in v.lean.summary


@needs_lean
def test_smuggled_axiom_is_rejected(tmp_path):
    _sidecar(tmp_path, "exact cheat\naxiom cheat : False")
    rep = run_check(tmp_path, {"hard.py": POW}, replay=False, timeout_ms=1500)
    f = next(f for f in rep.functions if f.fn.name == "pow2_add")
    assert f.status == "open"


@needs_lean
def test_changed_code_makes_exactly_that_proof_stale(tmp_path):
    _sidecar(tmp_path, PROOF)
    changed = POW.replace("pow2(a + b) == pow2(a) * pow2(b)", "pow2(b + a) == pow2(a) * pow2(b)")
    rep = run_check(tmp_path, {"hard.py": changed}, replay=False, timeout_ms=1500)
    f = next(f for f in rep.functions if f.fn.name == "pow2_add")
    v = next(v for v in f.verdicts if v.status != "proved")
    assert v.lean.status == "stale"
    assert next(f for f in rep.functions if f.fn.name == "pow2").status == "proved"


@needs_lean
def test_auto_tactics_close_nonlinear_goal(tmp_path):
    src = """
def square_sum(a: int, b: int) -> int:
    #@ requires a >= 0 and b >= 0
    #@ ensures result >= a * b
    return a * a + b * b
"""
    rep = run_check(tmp_path, {"sq.py": src}, replay=False, timeout_ms=1000)
    f = rep.functions[0]
    assert f.status == "proved"


def test_extract_proof_keeps_inner_have_blocks():
    reply = "```lean\nhave k : 1 = 1 := by\n  rfl\nexact k\n```"
    assert extract_proof(reply) == "have k : 1 = 1 := by\n  rfl\nexact k"
    full = "```lean\ntheorem x : True := by\n  trivial\n```"
    assert extract_proof(full).strip() == "trivial"
