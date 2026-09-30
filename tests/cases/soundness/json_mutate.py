# Unchecked values are objects: every way of changing one must drop what was
# known about it (and about every value that may share it).
from typing import Any


#@ trusted
#@ ensures result == (isinstance(t, dict) and "kind" in t and t["kind"] == "leaf")
def is_leaf(t: Any) -> bool:
    return isinstance(t, dict) and t.get("kind") == "leaf"


def put(t: Any) -> None:
    t["x"] = 1


#@ requires is_leaf(t)
#@ ensures is_leaf(t)
def through_view(t: Any) -> None:
    d: dict[str, Any] = t
    d["kind"] = "node"


#@ requires isinstance(t, dict) and "x" not in t
#@ ensures result == False
def view_reread(t: Any) -> bool:
    d: dict[str, Any] = t
    d["x"] = 1
    e: dict[str, Any] = t
    return "x" in e


#@ requires isinstance(t, dict) and "x" not in t
#@ ensures "x" not in t
def setitem(t: Any) -> None:
    t["x"] = 1


#@ requires isinstance(t, dict) and "x" in t
#@ ensures "x" in t
def method(t: Any) -> None:
    t.pop("x")


#@ requires isinstance(t, dict) and "x" not in t
#@ ensures "x" not in t
def callee(t: Any) -> None:
    put(t)


#@ requires isinstance(t, dict) and isinstance(t["c"], list) and len(t["c"]) == 0
#@ ensures len(t["c"]) == 0
def nested(t: Any) -> None:
    c: list[Any] = t["c"]
    c.append(1)


#@ requires isinstance(t, dict) and isinstance(t["xs"], list) and len(t["xs"]) == 0
#@ ensures len(t["xs"]) == 0
def in_place(t: Any) -> None:
    xs = t["xs"]
    xs += [1]


#@ requires isinstance(t, dict) and "x" not in t
#@ ensures "x" not in t
def in_loop(t: Any, n: int) -> None:
    for i in range(n):
        t["x"] = i


#@ requires isinstance(t, dict) and "x" not in t
#@ ensures "x" not in t
def rebound(t: Any) -> None:
    u = t
    t = 5
    u["x"] = 1
