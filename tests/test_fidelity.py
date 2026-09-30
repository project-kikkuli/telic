"""Spec fidelity: realistic mutants the contract accepts, verified proposals
that close them, safety aims an empty implementation would meet, and
coverage judgments carried to the JSON and HTML reports."""

import json
import shutil
import sys
from pathlib import Path

import pytest

from telic.aim import _aim_json, judge
from telic.checker import CheckOptions, check
from telic.gaps import find_gaps, render_gaps
from telic.html import render_html
from telic.oracle import resolve

WITHDRAW = """
def withdraw(balance: int, amount: int, owner: bool) -> int:
    #@ requires balance >= 0 and 0 <= amount <= balance
    #@ ensures 0 <= result <= balance
    if not owner:
        return balance
    return balance - amount
"""

REFUND = """#@ aim CAP: WHEN a refund is requested, the shop shall refund at most what is left.

def refund(paid: int, refunded: int, requested: int) -> int:
    #@ requires 0 <= refunded <= paid and requested >= 0
    #@ aim CAP
    #@ ensures 0 <= result <= paid - refunded
    remaining = paid - refunded
    if requested > remaining:
        return remaining
    return requested
"""

# a model's answers: one realistic mutant, one that edits the contract (unusable),
# and for the gaps, one clause that holds and one that does not
MODEL = r'''
import json, sys
prompt = sys.stdin.read()
if "task: mutate" in prompt:
    wrong = """def refund(paid: int, refunded: int, requested: int) -> int:
    #@ requires 0 <= refunded <= paid and requested >= 0
    #@ aim CAP
    #@ ensures 0 <= result <= paid - refunded
    remaining = paid - refunded
    if requested >= remaining:
        return 0
    return requested"""
    print(json.dumps({"guard_clause": {"text": wrong},
                      "validation": {"text": wrong.replace("0 <= result", "-1 <= result").replace("return 0", "return -1")},
                      "auth": None}))
else:
    print(json.dumps({"ensures": {"text": "result == 0\nresult == min(requested, paid - refunded)"},
                      "aim": {"text": "WHEN a refund is requested, the shop shall refund what was asked, capped at what is left."}}))
'''


def gaps(tmp_path, files, **kw):
    for name, text in files.items():
        (tmp_path / name).write_text(text)
    return find_gaps([str(tmp_path / n) for n in files], CheckOptions(cache_path=None), str(tmp_path), **kw)


def test_deleting_an_authorization_check_is_a_deterministic_gap(tmp_path):
    (fg,) = gaps(tmp_path, {"w.py": WITHDRAW}, propose=False)
    (g,) = [g for g in fg.gaps if g.mutant.what == "auth"]
    assert not g.mutant.by  # an operator, no model involved
    assert "owner=False" in g.args_text and g.original != g.mutated


def test_model_mutants_count_only_when_the_contract_accepts_them(tmp_path):
    (tmp_path / "model.py").write_text(MODEL)
    (fg,) = gaps(tmp_path, {"r.py": REFUND}, oracle=f"llm-cmd:{sys.executable} {tmp_path / 'model.py'}", llm=True)
    written = [g for g in fg.gaps if g.mutant.by.startswith("llm-cmd:")]
    assert [g.mutant.what for g in written] == ["guard clause"]
    assert fg.invalid == 1  # the mutant that edited the contract is neither a gap nor a kill
    (fix,) = [p for p in fg.proposals if p.kind == "ensures"]
    assert fix.text == "result == min(requested, paid - refunded)" and fix.kills == len(fg.gaps)
    assert all(g.closed_by == fix.text for g in fg.gaps)
    assert fg.rejected == 1  # 'result == 0' does not hold of the original
    (aim,) = [p for p in fg.proposals if p.kind == "aim"]
    assert "capped" in aim.text
    assert "== min(" not in (tmp_path / "r.py").read_text()  # proposed, never applied
    out = render_gaps([fg], 1.0)
    assert "written by llm-cmd:" in out and "not applied" in out and f"rejects {len(fg.gaps)} of {len(fg.gaps)}" in out


def test_generative_tasks_use_the_claude_cli_and_judgments_use_jev_first(monkeypatch):
    for v in ("TELIC_ORACLE", "TELIC_ORACLE_MUTATE", "TELIC_ORACLE_STRENGTHEN", "TELIC_JUDGE_CMD", "JEV_API_KEY", "TYPESAFE_API_KEY", "ANTHROPIC_API_KEY"):
        monkeypatch.delenv(v, raising=False)
    monkeypatch.setattr("telic.oracle.shutil.which", lambda name: "/bin/" + name)
    assert resolve(task="mutate").name == "llm-cmd:claude -p then builtin"
    assert resolve(task="strengthen").name == "llm-cmd:claude -p then builtin"
    assert resolve(task="coverage").name == "builtin"
    monkeypatch.setenv("JEV_API_KEY", "k")
    assert resolve(task="coverage").name == "jev then llm-cmd:claude -p then builtin"
    assert resolve(task="mutate").name == "llm-cmd:claude -p then builtin"
    monkeypatch.delenv("JEV_API_KEY")
    monkeypatch.setattr("telic.oracle.shutil.which", lambda name: None)
    assert resolve(task="mutate").name == "builtin"


@pytest.mark.parametrize(
    "aim, lemmas, status",
    [
        ("The shop shall never compute a negative total.", ["result >= 0"], "vacuous-risk"),
        ("The shop shall not charge a negative total.", ["result >= 0"], "vacuous-risk"),
        ("The shop shall never compute a negative total.", ["result >= 0", "result == a + b"], "backed"),
        ("The shop shall compute a non-negative total.", ["result >= 0"], "backed"),
    ],
)
def test_safety_aim_needs_more_than_a_stub_meets(tmp_path, aim, lemmas, status):
    ens = "".join(f"    #@ ensures {c}\n" for c in lemmas)
    (tmp_path / "t.py").write_text(f"#@ aim TOTAL: {aim}\n\n\ndef total(a: int, b: int) -> int:\n    #@ requires a >= 0 and b >= 0\n    #@ aim TOTAL\n{ens}    return a + b\n")
    rep = check([str(tmp_path / "t.py")], CheckOptions(cache_path=None, lean=False, replay=False), root=str(tmp_path))
    (r,) = rep.aims
    assert r.status == status
    assert bool(r.stubs) == (status == "vacuous-risk")
    if r.stubs:
        assert "return 0" in r.stubs[0]


def test_a_stub_that_raises_is_ruled_out_by_the_contract(tmp_path):
    src = "#@ aim SAFE: The service shall never return a negative balance.\n\n\ndef bal(x: int) -> int:\n    #@ requires x >= 0\n    #@ aim SAFE\n    #@ ensures result >= 0\n    #@ ensures result != 0\n    return x + 1\n"
    (tmp_path / "b.py").write_text(src)
    rep = check([str(tmp_path / "b.py")], CheckOptions(cache_path=None, lean=False, replay=False), root=str(tmp_path))
    assert rep.aims[0].status == "backed"  # `return 0` breaks result != 0, and an undeclared raise is an error


def test_judgments_reach_the_json_and_the_html_report(tmp_path):
    shutil.copy(Path(__file__).parent / "cases" / "aim" / "app.py", tmp_path / "app.py")
    script = tmp_path / "judge.py"
    script.write_text("import json, sys\nreq = json.load(sys.stdin)\nprint(json.dumps({'answers': {k: {'noul': 0.9 if k == 'covers' else 0.3} for k in req['questions']}}))\n")
    opts = CheckOptions(cache_path=None, lean=False, replay=False)
    rep = check([str(tmp_path / "app.py")], opts, root=str(tmp_path))
    judge(str(tmp_path), rep.aims, oracle=f"cmd:{sys.executable} {script}")
    cap = next(r for r in rep.aims if r.id == "CAP")
    data = json.loads(json.dumps(_aim_json(cap)))
    (part,) = data["coverage"]["parts"]
    assert part["condition"] == "the shop shall refund at most what was paid" and part["p"] == 0.3 and part["by"].startswith("cmd:")
    page = render_html(check([str(tmp_path / "app.py")], opts, root=str(tmp_path)))  # a fresh run shows the cached judgment
    assert "judged sufficient by cmd:" in page and "p=0.90" in page and "not proof" in page
    assert "the shop shall refund at most what was paid" in page and "p=0.30" in page
