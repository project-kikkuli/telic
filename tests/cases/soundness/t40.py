# A NamedTuple subclass built with type(), whose field is a property returning the tuple itself.
from typing import NamedTuple, Union


class Pair(NamedTuple):
    nxt: "Pairs"


class Stop(NamedTuple):
    v: int


Pairs = Union[Pair, Stop]


def walk(x: Pairs) -> int:
    if isinstance(x, Stop):
        return 0
    return walk(x.nxt)


def knot() -> Pair:
    Late = type("Late", (Pair,), {"nxt": property(lambda self: self)})
    return Late(Stop(0))
