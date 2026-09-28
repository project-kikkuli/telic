"""Objects, optionals and dicts: verdicts, aliasing, frames, replay."""

from pathlib import Path

from telic.checker import CheckOptions, check
from telic.replay import call_text

CASES = Path(__file__).parent / "cases" / "objects"


def run(name: str):
    rep = check([str(CASES / name)], CheckOptions(cache_path=None, lean=False), root=str(CASES))
    return {f.fn.name: f for f in rep.functions}


def refuted_confirmed(f) -> bool:
    return f.status == "refuted" and all(v.replay is None or v.replay.confirmed for v in f.verdicts if v.status == "refuted")


def test_bank():
    got = run("bank.py")
    for name in ("transfer", "find", "safe_total", "Account.__init__", "Account.deposit", "Account.withdraw"):
        assert got[name].status == "proved", (name, got[name].status, got[name].problems)
    for name in ("total", "lookup", "open_account", "Account.bad_withdraw"):
        assert refuted_confirmed(got[name]), (name, got[name].status)


def test_heap_aliasing_and_frames():
    got = run("heap.py")
    assert got["fresh_distinct"].status == "proved"
    assert got["loop_bump"].status == "proved"
    for name in ("alias_write", "alias_call", "break_child", "break_local"):
        assert refuted_confirmed(got[name]), (name, got[name].status)
    # The counterexample makes the aliasing visible.
    f = got["alias_write"]
    v = next(v for v in f.verdicts if v.status == "refuted")
    assert call_text(f.fn, v.model, "python") == "alias_write(a=<Box v=0 next=None>, b=a)"
    f = got["break_child"]
    v = next(v for v in f.verdicts if v.status == "refuted")
    assert "next=a" in call_text(f.fn, v.model, "python")
