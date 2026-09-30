"""telic propose: proved facts, crash-free preconditions, drafted aims."""

import json
import os
import stat
import sys
from pathlib import Path

from telic.checker import CheckOptions, check
from telic.propose import draft_aims, propose, write_back

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


def test_drafted_aims_only_cite_proved_facts(tmp_path):
    (tmp_path / "shop.py").write_text(SHOP)
    props = propose([str(tmp_path / "shop.py")], str(tmp_path), opts())
    # a generative oracle: classifies, rephrases (once badly), and names a gap
    fake = tmp_path / "oracle.py"
    fake.write_text(
        "import json, sys\n"
        "req = json.load(sys.stdin)\n"
        "out = {}\n"
        "for k, q in req['questions'].items():\n"
        "    if k.endswith('_kind'):\n"
        "        c = req['state']['candidates'][k[:-5]]\n"
        "        out[k] = {'choice': 'bug' if 'evens' in c['function'] else 'requirement', 'confidence': 0.9}\n"
        "    elif k == 'F1_phrase':\n"
        "        out[k] = {'text': 'averages are fine'}\n"
        "    elif k == 'gaps':\n"
        "        out[k] = {'text': json.dumps(['The shop shall be fast.'])}\n"
        "print(json.dumps({'answers': out}))\n"
    )
    d = draft_aims(props, str(tmp_path), oracle=f"cmd:{sys.executable} {fake}")
    for it in d["aims"]:
        assert it["facts"] and all(f in d["facts"] for f in it["facts"])  # backed drafts cite proved facts only
        assert not it["lint"]  # a rephrasing that is not EARS is dropped for the literal one
    assert "averages are fine" not in [i["text"] for i in d["aims"]]
    assert [i["text"] for i in d["unbacked"]] == ["The shop shall be fast."]
    assert d["suspicious"] and all("evens" in d["facts"][s["fact"]]["func"] for s in d["suspicious"])
    assert d["oracle"].startswith("cmd:")


def test_drafted_aims_with_builtin_oracle(tmp_path, monkeypatch):
    for v in ("TELIC_ORACLE", "JEV_API_KEY", "TYPESAFE_API_KEY", "ANTHROPIC_API_KEY", "TELIC_JUDGE_CMD"):
        monkeypatch.delenv(v, raising=False)
    (tmp_path / "shop.py").write_text(SHOP)
    props = propose([str(tmp_path / "shop.py")], str(tmp_path), opts())
    d = draft_aims(props, str(tmp_path))
    assert d["oracle"] == "builtin" and d["aims"] and not d["unbacked"]
    assert all(not i["lint"] for i in d["aims"])
    assert not any("old(self.owner)" in d["facts"][i["facts"][0]]["clause"] for i in d["aims"])  # frame facts are details


STATED = """
def double(xs: list[int]) -> list[int]:
    #@ ensures len(result)   == len(xs)
    #@ ensures all(v >= 0 for v in result) or not all(w >= 0 for w in xs)
    return [x * 2 for x in xs]


class Tab:
    #@ invariant self.total >= 0
    def __init__(self) -> None:
        self.total = 0

    def add(self, n: int) -> None:
        #@ requires n >= 0
        self.total = self.total + n
"""


def test_facts_the_contract_states_are_not_proposed_again(tmp_path):
    (tmp_path / "s.py").write_text(STATED)
    got = {p.func: p.facts for p in propose([str(tmp_path / "s.py")], str(tmp_path), opts())}
    assert not any("len(result)" in f for f in got["double"])  # == is stated, so <= says nothing new
    assert "ensures self.total >= 0" not in got["Tab.add"]
    assert "ensures self.total >= old(self.total)" in got["Tab.add"]
