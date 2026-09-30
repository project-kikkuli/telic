# The other half: a proof needing both levels stays open (never refuted: the
# model leaves the second level free), one needing a single level is proved.
from typing import Any

from a import even


#@ trusted
#@ ensures result == (isinstance(t, dict) and "n" in t and even(t["n"]))
def odd(t: Any) -> bool:
    return isinstance(t, dict) and "n" in t and even(t["n"])


#@ requires even(t)
#@ ensures result
def one_level(t: Any) -> bool:
    return "n" in t


#@ requires even(t)
#@ ensures result
def two_levels(t: Any) -> bool:
    return "n" in t["n"]
