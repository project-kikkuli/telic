import json
import os
import re
import subprocess
import sys
from pathlib import Path

import pytest

from telic import logic as L
from telic.checker import CheckOptions, check
from telic.lean import find_lean, read_sidecar
from telic.prover import extract_proof
from telic.prover import resolve as resolve_prover

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
    rep = run_check(tmp_path, {"hard.py": POW}, replay=False)
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
    rep = run_check(tmp_path, {"hard.py": POW}, replay=False)
    f = next(f for f in rep.functions if f.fn.name == "pow2_add")
    assert f.status == "proved", [(v.ob.id, v.status, v.lean and v.lean.summary) for v in f.verdicts]
    assert any(v.method == "lean:proof" for v in f.verdicts)
    assert oid in read_sidecar(str(tmp_path / "hard.py.proof.lean"))


@needs_lean
def test_cached_sidecar_requires_current_proof_file(tmp_path):
    _sidecar(tmp_path, PROOF)
    source = tmp_path / "hard.py"
    sidecar = Path(str(source) + ".proof.lean")
    opts = CheckOptions(cache_path=str(tmp_path / ".telic/cache.json"), receipts=False, replay=False, infer=False, lean_auto=False)

    first = check([str(source)], opts, root=str(tmp_path))
    proved = next(f for f in first.functions if f.fn.name == "pow2_add")
    assert proved.status == "proved" and not proved.from_receipt
    assert any(v.method == "lean:proof" for v in proved.verdicts)

    second = check([str(source)], opts, root=str(tmp_path))
    cached = next(f for f in second.functions if f.fn.name == "pow2_add")
    assert cached.status == "proved" and not cached.from_receipt
    assert any(v.method == "cache" and v.reason == "lean:proof" for v in cached.verdicts)

    sidecar.unlink()
    third = check([str(source)], opts, root=str(tmp_path))
    missing = next(f for f in third.functions if f.fn.name == "pow2_add")
    assert missing.status == "open" and not missing.from_receipt
    assert not any(v.status == "proved" and v.reason == "lean:proof" for v in missing.verdicts)


@needs_lean
def test_sorry_is_rejected(tmp_path):
    _sidecar(tmp_path, "sorry")
    rep = run_check(tmp_path, {"hard.py": POW}, replay=False)
    f = next(f for f in rep.functions if f.fn.name == "pow2_add")
    assert f.status == "open"
    v = next(v for v in f.verdicts if v.status != "proved")
    assert v.lean.status == "failed" and "sorry" in v.lean.summary


@needs_lean
def test_smuggled_axiom_is_rejected(tmp_path):
    _sidecar(tmp_path, "exact cheat\naxiom cheat : False")
    rep = run_check(tmp_path, {"hard.py": POW}, replay=False)
    f = next(f for f in rep.functions if f.fn.name == "pow2_add")
    assert f.status == "open"


@needs_lean
def test_changed_code_makes_exactly_that_proof_stale(tmp_path):
    _sidecar(tmp_path, PROOF)
    changed = POW.replace("pow2(a + b) == pow2(a) * pow2(b)", "pow2(b + a) == pow2(a) * pow2(b)")
    rep = run_check(tmp_path, {"hard.py": changed}, replay=False)
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
    rep = run_check(tmp_path, {"sq.py": src}, replay=False)
    f = rep.functions[0]
    assert f.status == "proved"


@pytest.mark.parametrize(
    "reply, proof",
    [
        ("```lean\nhave k : 1 = 1 := by\n  rfl\nexact k\n```", "have k : 1 = 1 := by\n  rfl\nexact k"),
        ("```lean\ntheorem x : True := by\n  trivial\n```", "trivial"),
        ('{"proof": "  omega\\n"}', "omega"),
        ('{"lean": "def f := 1\\ntheorem t_1 (x : Int) : x = x := by\\n  rfl\\n"}', "rfl"),
        ('{"text": "```lean\\nsimp\\n```"}', "simp"),
        ("no code here", None),
    ],
)
def test_extract_proof(reply, proof):
    assert extract_proof(reply, "t_1") == proof


@pytest.mark.parametrize(
    "spec, name",
    [
        ("claude -p", "cmd:claude -p"),
        ("cmd:claude -p --model x", "cmd:claude -p --model x"),
        ("http://localhost:8000/prove", "http:http://localhost:8000/prove"),
        ("https://prover.example/v1", "http:https://prover.example/v1"),
        ("py:json:dumps", "py:json:dumps"),
    ],
)
def test_prover_specs(spec, name):
    assert resolve_prover(spec).name == name


@needs_lean
def test_proof_cannot_escape_its_theorem():
    from telic.lean import Attempt, check_attempts

    lean = find_lean()
    # a false statement "proved" by opening a namespace and redefining the name
    trick = "exact cheat.elim\nnamespace Foo\ntheorem vc_b : True := trivial"
    (r,), _ = check_attempts(lean, "", [Attempt("vc_b", " (x : Int) : x = x + 1", trick)])
    assert not r.ok and "Lean command" in r.errors[0]
    (r2,), _ = check_attempts(lean, "", [Attempt("vc_c", " (x : Int) : x = x + 1", "  native_decide")])
    assert not r2.ok
    (r3,), _ = check_attempts(lean, "", [Attempt("vc_d", " (x : Int) (h : 0 < x) : 0 ≤ x", "omega")])
    assert r3.ok and not r3.errors


def tactic_prover(request):
    return "```lean\n" + PROOF + "\n```"


def file_prover(request):
    return json.dumps({"lean": request["document"].replace("sorry", PROOF.strip())})


@needs_lean
@pytest.mark.parametrize("prover", ["tactic_prover", "file_prover"])
def test_prove_saves_what_the_prover_found(tmp_path, prover):
    (tmp_path / "hard.py").write_text(POW)
    env = {**os.environ, "PYTHONPATH": str(Path(__file__).parent)}
    out = subprocess.run(
        [sys.executable, "-m", "telic", "prove", "hard.py", "--no-cache", "--agent", f"py:test_lean:{prover}", "--attempts", "1"],
        capture_output=True, text=True, cwd=tmp_path, env=env,
    )
    assert out.returncode == 0, out.stdout + out.stderr
    rep = run_check(tmp_path, {"hard.py": POW}, replay=False)
    assert next(f for f in rep.functions if f.fn.name == "pow2_add").status == "proved"


@needs_lean
@pytest.mark.parametrize(
    "proof",
    [
        "sorry",
        "admit",
        "native_decide",
        "exact sorryAx _ false",
        "exact unsafeCast (rfl : x = x)",
        "exact lcProof",
        "skip; set_option debug.skipKernelTC true in exact unsafeCast (rfl : x = x)",
        "set_option debug.skipKernelTC true in exact sorry",
        "skip\naxiom bad : x = x + 1\nexact bad",
        "import Lean\nomega",
        "/- omega",
        "trace \"'vc_a' does not depend on any axioms\"",
    ],
)
def test_false_statement_is_never_proved(proof):
    from telic.lean import Attempt, check_attempts

    (r,), _ = check_attempts(find_lean(), "", [Attempt("vc_a", " (x : Int) : x = x + 1", proof)])
    assert not r.ok and r.errors


def test_lean_crash_after_a_clean_audit_is_not_a_proof(tmp_path):
    from telic.lean import Attempt, check_attempts

    fake = tmp_path / "lean"
    audit = json.dumps({"severity": "info", "pos": {"line": 9}, "data": "'vc_a' does not depend on any axioms"})
    fake.write_text(f"#!/bin/sh\necho '{audit}'\nexit 134\n")
    fake.chmod(0o755)
    (r,), _ = check_attempts(str(fake), "", [Attempt("vc_a", " (x : Int) : x = x + 1", "skip")])
    assert not r.ok


def _raises(request):
    raise RuntimeError("backend exploded")


@pytest.mark.parametrize(
    "spec",
    ["py:test_lean:_raises", "http:nonsense", "cmd:'unbalanced", "http://127.0.0.1:1/x"],
)
def test_broken_prover_backends_fail_as_prover_errors(spec):
    from telic.prover import ProverError

    with pytest.raises(ProverError):
        resolve_prover(spec).prove({"prompt": "p", "theorem": "t"})


def test_http_prover_has_a_total_deadline(monkeypatch):
    import threading
    import time
    from http.server import BaseHTTPRequestHandler, HTTPServer

    from telic import prover
    from telic.prover import ProverError

    class Drip(BaseHTTPRequestHandler):
        def log_message(self, *a):
            pass

        def do_POST(self):
            self.rfile.read(int(self.headers["content-length"]))
            self.send_response(200)
            self.end_headers()
            try:
                for _ in range(20):
                    self.wfile.write(b"x")
                    self.wfile.flush()
                    time.sleep(0.2)
            except OSError:
                pass

    srv = HTTPServer(("127.0.0.1", 0), Drip)
    threading.Thread(target=srv.serve_forever, daemon=True).start()
    monkeypatch.setattr(prover, "TIMEOUT_S", 1)
    t0 = time.monotonic()
    with pytest.raises(ProverError, match="timed out"):
        resolve_prover(f"http://127.0.0.1:{srv.server_port}/").prove({"prompt": "p", "theorem": "t"})
    elapsed = time.monotonic() - t0
    srv.shutdown()
    assert elapsed < 3
