# Recursion that never ends, for some input: no inferred measure may prove it terminates.
from dataclasses import dataclass
from typing import Any, Union


def stays(n: int) -> int:
    if n == 0:
        return 0
    return stays(n)


def grows(n: int) -> int:
    if n == 0:
        return 0
    return grows(n + 1)


def below(n: int) -> int:
    # decreases, but nothing stops it below 10
    if n == 10:
        return 0
    return below(n - 1)


def down_forever(xs: list[int]) -> int:
    # shrinks the list, and keeps going once it is empty
    return down_forever(xs[1:])


def ping(n: int) -> int:
    return pong(n - 1)


def pong(n: int) -> int:
    return ping(n - 1)


def tick(n: int) -> int:
    if n <= 0:
        return 0
    return tock(n)


def tock(n: int) -> int:
    return tick(n)


def seesaw(a: int, b: int) -> int:
    # each call lowers one argument and raises the other: (2, 1) -> (1, 2) -> (2, 1)
    if a <= 0 or b <= 0:
        return 0
    if a > b:
        return seesaw(a - 1, b + 1)
    return seesaw(a + 1, b - 1)


def shrink_s(s: str) -> int:
    # a string that does not get shorter
    if s == "":
        return 0
    return shrink_s(s + "")


@dataclass
class Link:
    nxt: "Link | None" = None


@dataclass(frozen=True)
class Stop:
    v: int


Chain = Union[Link, Stop]


def walk(x: Chain) -> int:
    # a mutable Link can point back at itself
    if isinstance(x, Stop):
        return 0
    return walk(x.nxt)


@dataclass(frozen=True)
class Knot:
    v: int

    @property
    def me(self) -> "Knot":
        return self


Knotty = Union[Knot, Stop]


def spin_knot(k: Knotty) -> int:
    # a property is not a field: it can return the object itself
    return spin_knot(k.me)


@dataclass(frozen=True)
class Loop:
    other: "Loopy"

    def __post_init__(self) -> None:
        object.__setattr__(self, "other", self)


Loopy = Union[Loop, Stop]


def around(x: Loopy) -> int:
    # __post_init__ ties the knot after the object is built
    if isinstance(x, Stop):
        return 0
    return around(x.other)


@dataclass(frozen=True)
class Base:
    nxt: "Based"


class Sneaky(Base):
    def __getattribute__(self, name: str) -> object:
        return self


Based = Union[Base, Stop]


def descend(x: Based) -> int:
    # a subclass decides what reading a field returns
    if isinstance(x, Stop):
        return 0
    return descend(x.nxt)


#@ trusted
#@ ensures result >= 0
def size(v: Any) -> int: ...


#@ trusted
#@ ensures result == (isinstance(t, dict) and "next" in t and size(t["next"]) < size(t))
def chain(t: Any) -> bool: ...


def stuck(t: dict[str, Any]) -> int:
    #@ requires chain(t)
    # every JSON value here has a smaller "next", but the call does not follow it
    return stuck(t)
