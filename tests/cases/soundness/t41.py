# A NamedTuple whose class is swapped after it is built, for one whose field reads back the tuple.
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


class Loop(tuple):
    __slots__ = ()

    @property
    def nxt(self) -> "Loop":
        return self


def knot() -> Pair:
    p = Pair(Stop(0))
    p.__class__ = Loop
    return p
