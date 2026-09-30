# A recursive config tree, as parsed from JSON: sections nest, leaves hold ints.
from typing import Any


#@ trusted
#@ ensures result >= 0
def depth(v: Any) -> int:
    if isinstance(v, dict):
        return 1 + max((depth(x) for x in v.values()), default=0)
    if isinstance(v, list):
        return 1 + max((depth(x) for x in v), default=0)
    return 0


#@ trusted
#@ ensures result == (isinstance(node, dict) and "kind" in node and (
#@     node["kind"] == "value" and "value" in node and isinstance(node["value"], int) and node["value"] >= 0
#@     or node["kind"] == "section" and "name" in node and isinstance(node["name"], str)
#@         and "children" in node and isinstance(node["children"], list)
#@         and all(wf_config(c) and depth(c) < depth(node) for c in node["children"])))
def wf_config(node: Any) -> bool:
    if not (isinstance(node, dict) and "kind" in node):
        return False
    if node["kind"] == "value":
        return isinstance(node.get("value"), int) and node["value"] >= 0
    return (
        node["kind"] == "section"
        and isinstance(node.get("name"), str)
        and isinstance(node.get("children"), list)
        and all(wf_config(c) for c in node["children"])
    )


#@ requires wf_config(node)
#@ decreases depth(node)
#@ ensures result >= 0
def total(node: dict[str, Any]) -> int:
    if node["kind"] == "value":
        v: int = node["value"]
        return v
    children: list[Any] = node["children"]
    out = 0
    for k in range(len(children)):
        #@ invariant out >= 0
        out += total(children[k])
    return out


#@ requires wf_config(node)
def label(node: dict[str, Any]) -> str:
    if node["kind"] == "section":
        name: str = node["name"]
        return name
    return "value"


#@ requires wf_config(node)
def section_name(node: dict[str, Any]) -> str:
    name: str = node["name"]
    return name


#@ requires wf_config(node) and node["kind"] == "section"
#@ ensures result >= 1
def grandchildren(node: dict[str, Any]) -> int:
    children: list[Any] = node["children"]
    first: dict[str, Any] = children[0]
    inner: list[Any] = first["children"]
    return len(inner)
