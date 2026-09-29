"""Proved clauses in words: the literal first draft of an intent."""

import pytest

from telic.intent import ears_conditions, ears_problems
from telic.phrase import requirement

CASES = [
    ("saturating", "ensures result <= a", "WHEN saturating returns, the result shall be at most a."),
    ("checked", "ensures result.is_none() || result.unwrap() == a + b", "WHEN checked returns, the result shall equal a plus b whenever the result is present."),
    ("Account.deposit", "ensures self.balance == old(self.balance) + amount", "WHEN deposit returns, the balance shall equal the balance before the call plus amount."),
    ("try_withdraw", "ensures result == (old(self.balance) >= amount)", "WHEN try_withdraw returns, the result shall be true exactly when the balance before the call is at least amount."),
    ("average", "requires len(xs) > 0", "The callers of average shall ensure that the length of xs is greater than 0."),
    ("find", "ensures result === null || xs[result] === target", "WHEN find returns, xs[result] shall equal target whenever the result is present."),
    ("doubled", "ensures result.len() == xs.len()", "WHEN doubled returns, the length of the result shall equal the length of xs."),
    ("odd", "ensures frobnicate(x)", "WHEN odd returns, the result shall satisfy `frobnicate(x)`."),
]


@pytest.mark.parametrize("func,clause,want", CASES)
def test_rendering(func, clause, want):
    got = requirement(func, clause)
    assert got == want
    assert ears_problems(got) == []


def test_quantifiers_in_all_three_syntaxes():
    for c in ("ensures all(x <= result for x in xs)", "ensures xs.iter().all(|x| x <= result)", "ensures xs.every((x) => x <= result)"):
        assert "for every x in xs, x is at most the result" in requirement("max_of", c)


def test_ears_conditions_split_the_response():
    trig, parts = ears_conditions("WHEN a refund is issued, the shop shall refund at most what was paid and log it.")
    assert trig == "WHEN a refund is issued"
    assert parts == ["the shop shall refund at most what was paid", "the shop shall log it"]
