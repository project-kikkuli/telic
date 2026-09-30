"""Proved clauses in words: the literal first draft of an aim."""

import pytest

from telic.aim import ears_conditions, ears_problems
from telic.phrase import requirement

CASES = [
    ("saturating", "ensures result <= a"),
    ("checked", "ensures result.is_none() || result.unwrap() == a + b"),
    ("Account.deposit", "ensures self.balance == old(self.balance) + amount"),
    ("try_withdraw", "ensures result == (old(self.balance) >= amount)"),
    ("average", "requires len(xs) > 0"),
    ("find", "ensures result === null || xs[result] === target"),
    ("doubled", "ensures result.len() == xs.len()"),
    ("odd", "ensures frobnicate(x)"),
]


@pytest.mark.parametrize("func,clause", CASES)
def test_rendering_is_valid_ears(func, clause):
    assert ears_problems(requirement(func, clause)) == []


def test_quantifiers_in_all_three_syntaxes():
    for c in ("ensures all(x <= result for x in xs)", "ensures xs.iter().all(|x| x <= result)", "ensures xs.every((x) => x <= result)"):
        assert "for every x in xs, x is at most the result" in requirement("max_of", c)


def test_ears_conditions_split_the_response():
    trig, parts = ears_conditions("WHEN a refund is issued, the shop shall refund at most what was paid and log it.")
    assert trig == "WHEN a refund is issued"
    assert parts == ["the shop shall refund at most what was paid", "the shop shall log it"]
