"""The CI ratchet: regressions fail, acceptances and improvements pass."""

import json
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
SRC = """#@ intent CAP: A result never exceeds the cap.

def capped(x: int, cap: int) -> int:
    #@ requires cap >= 0
    #@ intent CAP
    #@ ensures result <= cap
    return min(x, cap)


def other(x: int) -> int:
    #@ ensures result >= x
    return x + 1
"""


def sh(cwd, *cmd):
    return subprocess.run(list(cmd), cwd=cwd, capture_output=True, text=True)


def telic(cwd, *args):
    return sh(cwd, sys.executable, "-m", "telic", *args)


@pytest.fixture
def repo(tmp_path):
    (tmp_path / "lib").mkdir()
    (tmp_path / "lib" / "cap.py").write_text(SRC)
    (tmp_path / "lib" / "unrelated.py").write_text("def f(x: int) -> int:\n    #@ ensures result == x\n    return x\n")
    sh(tmp_path, "git", "init", "-q", "-b", "main")
    sh(tmp_path, "git", "config", "user.email", "t@example.com")
    sh(tmp_path, "git", "config", "user.name", "t")
    assert telic(tmp_path, "init", "--no-hook").returncode == 0
    sh(tmp_path, "git", "add", "-A")
    sh(tmp_path, "git", "commit", "-qm", "init")
    sh(tmp_path, "git", "checkout", "-qb", "feature")
    return tmp_path


def commit(repo, msg):
    sh(repo, "git", "commit", "-qam", msg)


def test_ledger_records_intents_and_clauses(repo):
    data = json.loads((repo / "telic.ledger.json").read_text())
    assert data["intents"]["CAP"]["status"] == "backed"
    assert data["intents"]["CAP"]["clauses"] == ["capped: ensures result <= cap"]
    assert data["functions"]["lib/cap.py::capped"]["status"] == "proved"


def test_no_change_is_free(repo):
    out = telic(repo, "ci", "--since", "main")
    assert out.returncode == 0 and "no checkable files changed" in out.stdout


def test_regression_fails_and_scope_is_exact(repo):
    p = repo / "lib" / "cap.py"
    p.write_text(SRC.replace("return min(x, cap)", "return x"))
    commit(repo, "oops")
    out = telic(repo, "ci", "--since", "main", "--color", "never")
    assert out.returncode == 1
    assert "intent CAP: backed → broken" in out.stdout
    assert "1 affected file" in out.stdout  # unrelated.py is not re-checked


def test_dropping_a_clause_needs_acceptance(repo):
    p = repo / "lib" / "cap.py"
    p.write_text(SRC.replace("    #@ ensures result <= cap\n", ""))
    commit(repo, "weaken")
    out = telic(repo, "ci", "--since", "main", "--color", "never")
    assert out.returncode == 1 and "lost a clause" in out.stdout
    sh(repo, "git", "commit", "-q", "--allow-empty", "-m", "ack\n\nTelic-accept: CAP the cap moved to the caller")
    out = telic(repo, "ci", "--since", "main", "--color", "never")
    assert out.returncode == 0 and "accepted: the cap moved to the caller" in out.stdout


def test_improvement_updates_ledger(repo):
    p = repo / "lib" / "unrelated.py"
    p.write_text("#@ intent SAME: f is the identity.\n\ndef f(x: int) -> int:\n    #@ intent SAME\n    #@ ensures result == x\n    return x\n")
    commit(repo, "formalize")
    out = telic(repo, "ci", "--since", "main", "--update", "--color", "never")
    assert out.returncode == 0 and "intent SAME (backed)" in out.stdout
    data = json.loads((repo / "telic.ledger.json").read_text())
    assert data["intents"]["SAME"]["status"] == "backed" and "CAP" in data["intents"]


def test_github_annotations(repo):
    p = repo / "lib" / "cap.py"
    p.write_text(SRC.replace("return min(x, cap)", "return x"))
    commit(repo, "oops")
    out = telic(repo, "ci", "--since", "main", "--format", "github", "--color", "never")
    assert "::error file=lib/cap.py,line=" in out.stdout


def test_receipts_are_bound_to_the_toolchain(repo, monkeypatch):
    import telic.checker as C

    first = C.toolchain_id()
    monkeypatch.setattr(C, "_TOOLCHAIN", None)
    assert C.toolchain_id() == first  # stable across processes for the same sources


BASE = "class Shape:\n    def area(self) -> int:\n        #@ ensures result >= 0\n        return 0\n"
MID = "from base import Shape\n\n\nclass Poly(Shape):\n    pass\n"
SUB = "from {parent} import {cls}\n\n\nclass Square({cls}):\n    def area(self) -> int:\n        return {body}\n"
CALLER = "#@ intent POS: Every area is non-negative.\n\nfrom base import Shape\n\n\ndef total(s: Shape) -> int:\n    #@ intent POS\n    #@ ensures result >= 0\n    return s.area()\n"


@pytest.mark.parametrize("parent,cls", [("base", "Shape"), ("mid", "Poly")])
def test_changed_override_rechecks_callers_through_the_base(tmp_path, parent, cls):
    (tmp_path / "base.py").write_text(BASE)
    (tmp_path / "mid.py").write_text(MID)
    (tmp_path / "square.py").write_text(SUB.format(parent=parent, cls=cls, body="1"))
    (tmp_path / "caller.py").write_text(CALLER)
    sh(tmp_path, "git", "init", "-q", "-b", "main")
    sh(tmp_path, "git", "config", "user.email", "t@example.com")
    sh(tmp_path, "git", "config", "user.name", "t")
    assert telic(tmp_path, "init", "--no-hook").returncode == 0
    sh(tmp_path, "git", "add", "-A")
    sh(tmp_path, "git", "commit", "-qm", "init")
    (tmp_path / "square.py").write_text(SUB.format(parent=parent, cls=cls, body="-1"))
    commit(tmp_path, "negative area")
    out = telic(tmp_path, "ci", "--since", "HEAD~1", "--color", "never")
    assert out.returncode == 1, out.stdout
    assert "intent POS: backed →" in out.stdout
