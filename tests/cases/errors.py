"""Code that once made telic fail with an internal error instead of a
verdict. The comment '# expect: STATUS' before each function is the verdict
telic must reach."""

import json
from typing import Any, Callable, Optional


def grow(ys: list[int]) -> None:
    ys.append(1)


# expect: proved
def visit_all(nodes: list, check: Callable[[Any], bool]) -> int:
    #@ ensures result >= 0
    n = 0
    for node in nodes:
        check(node)
        n += 1
    return n


# expect: proved
def map_all(fn: Callable[[Any], Any], items: list[Any]) -> list[Any]:
    return [fn(x) for x in items]


# expect: proved
def kids(node: Any) -> int:
    xs = node.children if node is not None else []
    return len(xs)


# expect: proved
def empty_json() -> int:
    #@ ensures result == 0
    json.dumps([])
    json.dumps({})
    json.dumps({"a": [1], "b": {"c": [2]}})
    return 0


# expect: proved
def shares_body(n: int) -> dict:
    #@ requires n >= 0
    return {"shares": [n, n]}


# expect: unsupported
def count_labels(labels: list[Optional[str]]) -> int:
    #@ ensures result >= 0
    return len(labels)


# expect: proved
def grow_attr(args: Any) -> int:
    #@ ensures result == 0
    grow(args.paths)
    return 0


# expect: proved
def grow_each(xss: list[list[int]]) -> int:
    #@ ensures result == 0
    _ = [grow(x) for x in xss]
    return 0


# expect: proved
def shadowed(xs: list[list[int]]) -> int:
    for node in xs:
        pass

    def size(node: list[int]) -> int:
        return len(node)

    total = 0
    for x in xs:
        total = size(x)
    return total
