"""The CI ratchet: regressions fail, acceptances and improvements pass."""

import json
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
SRC = """#@ aim CAP: The result shall be at most the cap.

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
        ({"lib/unrelated.py": "#@ aim CAP: The result shall be at most the cap.\n\n" + CITES_OTHER.format(iid="CAP")}, "declared more than once"),
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


def test_receipts_are_bound_to_the_toolchain(monkeypatch):
    import telic.checker as C

    # Both ids are computed now, from the same files: the one cached earlier in
    # this process may predate an edit made while the suite runs.
    monkeypatch.setattr(C, "_TOOLCHAIN", None)
    here = C.toolchain_id()
    there = sh(ROOT, sys.executable, "-c", "from telic.checker import toolchain_id; print(toolchain_id())").stdout.strip()
    assert here == there  # stable across processes for the same sources


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


TRANSITIVE = {
    "python": (
        {"pkg/__init__.py": "", "pkg/a.py": "def g(x: int) -> int:\n    return x\n", "pkg/b.py": "from pkg.a import g\n\n\ndef f(x: int) -> int:\n    return g(x)\n", "pkg/c.py": "from pkg.b import f\n\n\ndef h(x: int) -> int:\n    #@ ensures result == x\n    return f(x)\n"},
        ("pkg/a.py", "return x\n", "return x + 1\n"),
    ),
    "typescript": (
        {"a.ts": "export function g(x: number): number {\n  //@ ensures result === x\n  return x;\n}\n", "c.ts": 'import { g } from "./a";\n\nexport function h(x: number): number {\n  //@ ensures result === x\n  return g(x);\n}\n'},
        ("a.ts", "result === x\n  return x;", "result === x + 1\n  return x + 1;"),
    ),
    "typescript importer": (
        {"a.ts": "export function g(x: number): number {\n  //@ ensures result === x\n  return x;\n}\n", "c.ts": 'import { g } from "./a";\n\nexport function h(x: number): number {\n  //@ ensures result === x\n  return g(x);\n}\n'},
        ("c.ts", "return g(x);", "return g(x) + 0;"),
    ),
}


@pytest.mark.parametrize("case", sorted(TRANSITIVE))
def test_since_follows_imports_as_a_full_check_does(tmp_path, case):
    if "typescript" in case:
        import shutil

        if shutil.which("node") is None:
            pytest.skip("Node.js not available")
    files, (path, old, new) = TRANSITIVE[case]
    for name, text in files.items():
        (tmp_path / name).parent.mkdir(parents=True, exist_ok=True)
        (tmp_path / name).write_text(text)
    sh(tmp_path, "git", "init", "-q", "-b", "main")
    sh(tmp_path, "git", "config", "user.email", "t@example.com")
    sh(tmp_path, "git", "config", "user.name", "t")
    assert telic(tmp_path, "init", "--no-hook").returncode == 0
    sh(tmp_path, "git", "add", "-A")
    sh(tmp_path, "git", "commit", "-qm", "init")
    (tmp_path / path).write_text((tmp_path / path).read_text().replace(old, new))
    commit(tmp_path, "change")
    since, full = telic(tmp_path, "ci", "--since", "HEAD~1", "--color", "never"), telic(tmp_path, "ci", "--color", "never")
    assert since.returncode == full.returncode, since.stdout
    assert [l for l in since.stdout.splitlines() if "→" in l] == [l for l in full.stdout.splitlines() if "→" in l]


TS_BASE = "export class Shape {\n  area(): number {\n    //@ ensures result >= 0\n    return 0;\n  }\n}\n"
TS_SUB = 'import { Shape } from "./base";\n\nexport class Square extends Shape {\n  area(): number {\n    return -1;\n  }\n}\n'
TS_CALLER = '//@ aim POS: Every area is non-negative.\n\nimport { Shape } from "./base";\n\nexport function total(s: Shape): number {\n  //@ aim POS\n  //@ ensures result >= 0\n  return s.area();\n}\n'


def test_a_new_ts_subclass_rechecks_callers_through_the_base(tmp_path):
    import shutil

    if shutil.which("node") is None:
        pytest.skip("Node.js not available")
    (tmp_path / "base.ts").write_text(TS_BASE)
    (tmp_path / "caller.ts").write_text(TS_CALLER)
    sh(tmp_path, "git", "init", "-q", "-b", "main")
    sh(tmp_path, "git", "config", "user.email", "t@example.com")
    sh(tmp_path, "git", "config", "user.name", "t")
    assert telic(tmp_path, "init", "--no-hook").returncode == 0
    sh(tmp_path, "git", "add", "-A")
    sh(tmp_path, "git", "commit", "-qm", "init")
    (tmp_path / "square.ts").write_text(TS_SUB)
    sh(tmp_path, "git", "add", "-A")
    commit(tmp_path, "a subclass")
    since, full = telic(tmp_path, "ci", "--since", "HEAD~1", "--color", "never"), telic(tmp_path, "ci", "--color", "never")
    assert "aim POS: backed →" in full.stdout, full.stdout
    assert [l for l in since.stdout.splitlines() if "→" in l] == [l for l in full.stdout.splitlines() if "→" in l]


@pytest.mark.parametrize(
    "files,has,lacks",
    [
        ({"a.py": ""}, ["pip install git+"], ["playwright", "npm", "elan"]),
        ({"web/telic.toml": "[ui]\ncommand = 'x'\n", "web/package.json": "{}", "web/package-lock.json": "{}"}, ["telic[ui]", "playwright install", "npm ci\n        working-directory: web"], ["elan"]),
        ({"a.py": "", "a.py.proof.lean": ""}, ["elan", "lean-toolchain"], ["playwright"]),
    ],
)
def test_init_installs_what_the_project_needs(tmp_path, files, has, lacks):
    from telic.ledger import workflow

    for name, text in files.items():
        (tmp_path / name).parent.mkdir(parents=True, exist_ok=True)
        (tmp_path / name).write_text(text)
    w = workflow(str(tmp_path))
    assert all(h in w for h in has) and not any(x in w for x in lacks)


def test_a_timeout_is_never_a_verdict_change(tmp_path, monkeypatch):
    import time

    import z3

    from telic.checker import CheckOptions, check
    from telic.ledger import compare, merge, snapshot

    (tmp_path / "cap.py").write_text(SRC)
    run = lambda **kw: snapshot(check([str(tmp_path / "cap.py")], CheckOptions(cache_path=None, lean=False, **kw), root=str(tmp_path)))  # noqa: E731
    old = run()
    check_sat = z3.Solver.check
    monkeypatch.setattr(z3.Solver, "check", lambda self, *a: (time.sleep(0.3), check_sat(self, *a))[1])
    new = run(timeout_ms=50)
    assert all(f.get("timeout") for f in new["functions"].values()) and new["aims"]["CAP"].get("timeout")
    assert compare(old, new, None) == []
    kept = merge(old, new, None)
    assert kept["functions"] == old["functions"] and kept["aims"] == old["aims"]
