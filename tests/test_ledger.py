"""The CI ratchet: regressions fail, acceptances and improvements pass."""

import json
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
SRC = """#@ aim CAP: A result never exceeds the cap.

def capped(x: int, cap: int) -> int:
    #@ requires cap >= 0
    #@ aim CAP
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


CITES_OTHER = "def f(x: int) -> int:\n    #@ aim {iid}\n    #@ ensures result == x\n    return x\n"


@pytest.mark.parametrize(
    "files, problem",
    [
        ({"lib/cap.py": SRC.replace("the cap.", "the cap. by: capped, gone")}, "'gone' is listed in by:"),
        ({"lib/unrelated.py": "#@ aim CAP: A result never exceeds the cap.\n\n" + CITES_OTHER.format(iid="CAP")}, "declared more than once"),
        ({"lib/aims/ORPH.md": "The shop shall log.\n"}, "nothing backs it"),
        ({"lib/sub/aims/SUBX.md": "The shop shall log.\n", "lib/unrelated.py": CITES_OTHER.format(iid="SUBX")}, "is outside lib/sub/"),
        ({"lib/aims/Overview.md": "prose\n"}, "not an aim ID"),
    ],
)
def test_aim_link_problems_fail_ci_and_cannot_be_accepted(repo, files, problem):
    for rel, text in files.items():
        (repo / rel).parent.mkdir(parents=True, exist_ok=True)
        (repo / rel).write_text(text)
    sh(repo, "git", "add", "-A")
    iids = " ".join(["CAP", "ORPH", "SUBX"])
    commit(repo, f"rot\n\nTelic-accept: {iids} trying to wave it through")
    out = telic(repo, "ci", "--since", "main", "--update", "--color", "never")
    assert out.returncode == 1 and problem in out.stdout, out.stdout
    assert "updated telic.ledger.json" not in out.stdout


def test_ledger_records_aims_and_clauses(repo):
    data = json.loads((repo / "telic.ledger.json").read_text())
    assert data["aims"]["CAP"]["status"] == "backed"
    assert data["aims"]["CAP"]["clauses"] == ["capped: ensures result <= cap"]
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
    assert "aim CAP: backed → broken" in out.stdout
    assert "1 affected file" in out.stdout  # unrelated.py is not re-checked


def test_dropping_a_clause_needs_acceptance(repo):
    p = repo / "lib" / "cap.py"
    p.write_text(SRC.replace("    #@ aim CAP\n    #@ ensures result <= cap\n", ""))  # a cite left without its clause is a link problem
    commit(repo, "weaken")
    out = telic(repo, "ci", "--since", "main", "--color", "never")
    assert out.returncode == 1 and "lost a clause" in out.stdout
    sh(repo, "git", "commit", "-q", "--allow-empty", "-m", "ack\n\nTelic-accept: CAP the cap moved to the caller")
    out = telic(repo, "ci", "--since", "main", "--color", "never")
    assert out.returncode == 0 and "accepted: the cap moved to the caller" in out.stdout


def test_improvement_updates_ledger(repo):
    p = repo / "lib" / "unrelated.py"
    p.write_text("#@ aim SAME: f is the identity.\n\ndef f(x: int) -> int:\n    #@ aim SAME\n    #@ ensures result == x\n    return x\n")
    commit(repo, "formalize")
    out = telic(repo, "ci", "--since", "main", "--update", "--color", "never")
    assert out.returncode == 0 and "aim SAME (backed)" in out.stdout
    data = json.loads((repo / "telic.ledger.json").read_text())
    assert data["aims"]["SAME"]["status"] == "backed" and "CAP" in data["aims"]


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
CALLER = "#@ aim POS: Every area is non-negative.\n\nfrom base import Shape\n\n\ndef total(s: Shape) -> int:\n    #@ aim POS\n    #@ ensures result >= 0\n    return s.area()\n"


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
    assert "aim POS: backed →" in out.stdout


@pytest.mark.parametrize(
    "change",
    [
        [("git", "mv", "lib/aims/PAY.md", "lib/aims/PAYS.md")],
        [("mkdir", "aims"), ("git", "mv", "lib/aims/PAY.md", "aims/PAY.md")],
        [("git", "rm", "-q", "lib/aims/PAY.md")],
        [("write", "lib/aims/NEW.md", "The shop shall log.\nby: f\n")],
        [("write", "lib/aims/NOTES.txt", "The shop shall log.\n")],
        [("mkdir", "lib/aims/sub"), ("write", "lib/aims/sub/NEW.md", "The shop shall log.\n")],
    ],
)
def test_since_judges_aim_file_changes_as_a_full_check_does(repo, change):
    sh(repo, "git", "checkout", "-q", "main")
    (repo / "lib" / "aims").mkdir()
    (repo / "lib" / "aims" / "PAY.md").write_text("The shop shall pay.\nby: f\n")
    (repo / "lib" / "unrelated.py").write_text(CITES_OTHER.format(iid="PAY"))
    assert telic(repo, "ledger").returncode == 0
    sh(repo, "git", "add", "-A")
    sh(repo, "git", "commit", "-qm", "pay")
    sh(repo, "git", "checkout", "-qb", "change")
    for cmd, *rest in change:
        if cmd == "write":
            (repo / rest[0]).write_text(rest[1])
        else:
            sh(repo, cmd, *rest)
    sh(repo, "git", "add", "-A")
    sh(repo, "git", "commit", "-qm", "change")
    since, full = telic(repo, "ci", "--since", "main", "--color", "never"), telic(repo, "ci", "--color", "never")
    assert (since.returncode, since.stdout.splitlines()[1:]) == (full.returncode, full.stdout.splitlines()[1:])
