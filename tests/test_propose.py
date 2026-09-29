"""telic propose: proved facts, crash-free preconditions, drafted intents."""

import json
import os
import stat
from pathlib import Path

from telic.checker import CheckOptions, check
from telic.propose import draft_intents, propose, write_back

SHOP = '''
def average(xs: list[int]) -> float:
    return sum(xs) / len(xs)


def evens(xs: list[int]) -> list[int]:
    return [x for x in xs if x % 2 == 0]


def discount(total: int, pct: int) -> int:
    if pct < 0 or pct > 100:
        return total
    return total - total * pct // 100


class Wallet:
    def __init__(self, balance: int):
        self.balance = balance
        self.owner = "me"

    def spend(self, amount: int) -> bool:
        if amount <= self.balance:
            self.balance -= amount
            return True
        return False


def pick(items: list[str], i: int) -> str:
    return items[i]
'''


def opts():
    return CheckOptions(cache_path=None, lean=False, timeout_ms=4000)


def test_facts_and_fixes(tmp_path):
    (tmp_path / "shop.py").write_text(SHOP)
    got = {p.func: p for p in propose([str(tmp_path / "shop.py")], str(tmp_path), opts())}
    assert "ensures len(result) <= len(xs)" in got["evens"].facts
    assert "ensures self.owner == old(self.owner)" in got["Wallet.spend"].facts
    # a negative total or amount breaks the obvious candidates: nothing false is proposed
    assert not got["discount"].facts
    assert not any("balance <= old" in f for f in got["Wallet.spend"].facts)
    assert [r for r, _ in got["average"].fixes] == ["requires len(xs) > 0"]
    assert got["pick"].fixes and got["pick"].fixes[0][0] == "requires 0 <= i < len(items)"


def test_written_facts_are_proved(tmp_path):
    (tmp_path / "shop.py").write_text(SHOP)
    props = propose([str(tmp_path / "shop.py")], str(tmp_path), opts())
    n = write_back(str(tmp_path), props, with_fixes=True)
    assert n >= 5
    rep = check([str(tmp_path / "shop.py")], opts(), root=str(tmp_path))
    by = {f.fn.name: f for f in rep.functions}
    for name in ("average", "evens", "Wallet.spend", "pick"):
        assert by[name].status == "proved", (name, by[name].status, [(v.ob.id, v.status) for v in by[name].verdicts])


def test_drafted_intents_only_cite_proved_facts(tmp_path, monkeypatch):
    (tmp_path / "shop.py").write_text(SHOP)
    props = propose([str(tmp_path / "shop.py")], str(tmp_path), opts())
    fake = tmp_path / "judge.sh"
    fake.write_text(
        "#!/bin/sh\ncat > /dev/null\ncat <<'J'\n"
        + json.dumps({"intents": [
            {"id": "SAFE-AVG", "text": "WHEN an average is requested, the system shall compute it over a non-empty list.", "facts": ["F1"]},
            {"id": "MADE-UP", "text": "The system shall be fast.", "facts": ["F999"]},
            {"id": "SLOPPY", "text": "averages are fine", "facts": ["F1"]}]})
        + "\nJ\n"
    )
    fake.chmod(fake.stat().st_mode | stat.S_IEXEC)
    d = draft_intents(props, str(tmp_path), command=str(fake))
    ids = [i["id"] for i in d["intents"]]
    assert "MADE-UP" not in ids  # nothing proved supports it: shown as unbacked, never as backed
    assert "MADE-UP" in [i["id"] for i in d["unbacked"]]
    assert "SAFE-AVG" in ids
    sloppy = next(i for i in d["intents"] if i["id"] == "SLOPPY")
    assert sloppy["lint"]  # not EARS: flagged
