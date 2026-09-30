# Counterexamples over unchecked values are rebuilt as JSON and run: a false
# claim is refuted with a real input, a true one is proved.
from typing import Any


#@ requires isinstance(t, dict) and "k" in t
#@ ensures result is not None
def present_is_not_null(t: Any) -> Any:
    return t["k"]


#@ requires isinstance(t, list) and len(t) == 1 and t[0] == "a"
#@ ensures result == False
def contains(t: Any) -> bool:
    return "a" in t


#@ requires isinstance(t, dict) and "x" not in t
#@ ensures "x" not in t
def adds(t: Any) -> None:
    t["x"] = 1


#@ requires isinstance(t, dict) and "x" not in t
#@ ensures "x" not in t
def reads(t: Any) -> None:
    s = str(t)
    k = t.get("y")
