# A trusted predicate proves only what its @ensures implies: each function
# below claims more than that, and must not be proved.
from typing import Any


#@ trusted
#@ ensures implies(result, isinstance(t, dict) and "a" in t)
def has_a(t: Any) -> bool:
    return isinstance(t, dict) and "a" in t


#@ trusted
#@ ensures result == (isinstance(t, dict) and "kind" in t and (t["kind"] == "leaf"
#@     or t["kind"] == "node" and "left" in t and wf_tree(t["left"])))
def wf_tree(t: Any) -> bool:
    if not (isinstance(t, dict) and "kind" in t):
        return False
    return t["kind"] == "leaf" or t["kind"] == "node" and "left" in t and wf_tree(t["left"])


#@ trusted
#@ ensures result == (isinstance(t, list) and len(t) == 2)
def is_pair(t: Any) -> bool:
    return isinstance(t, list) and len(t) == 2


#@ requires has_a(t)
def other_key(t: dict[str, Any]) -> Any:
    return t["b"]


#@ requires not has_a(t)
def negated(t: dict[str, Any]) -> Any:
    return t["a"]


#@ requires wf_tree(t)
def two_levels(t: dict[str, Any]) -> Any:
    left: dict[str, Any] = t["left"]
    return left["left"]


#@ requires wf_tree(t) and t["kind"] == "leaf"
def wrong_branch(t: dict[str, Any]) -> Any:
    return t["left"]


#@ requires is_pair(t)
def third(t: list[Any]) -> Any:
    return t[2]


#@ ensures result
def any_dict(d: dict[str, Any]) -> bool:
    return has_a(d)


#@ ensures result
def literal_eq(x: Any) -> bool:
    return x != "a" or x == "b"


#@ requires all(has_a(x) for x in xs)
def elements(xs: list[Any]) -> Any:
    first: dict[str, Any] = xs[0]
    return first["b"]
