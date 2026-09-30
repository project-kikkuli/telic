# A frozen dataclass tied into a cycle from outside the class: the inferred depth measure must not prove.
from dataclasses import dataclass
from typing import Union


@dataclass(frozen=True)
class Node:
    nxt: "Nodes"


@dataclass(frozen=True)
class Stop:
    v: int


Nodes = Union[Node, Stop]


def walk(x: Nodes) -> int:
    if isinstance(x, Stop):
        return 0
    return walk(x.nxt)


def knot() -> Node:
    n = Node(Stop(0))
    object.__setattr__(n, "nxt", n)
    return n
