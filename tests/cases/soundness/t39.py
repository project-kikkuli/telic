# A subclass defined inside a function decides what reading a field returns.
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
    class Sneak(Node):
        def __getattribute__(self, name: str) -> object:
            return self

    return Sneak(Stop(0))
