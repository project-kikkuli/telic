from typing import Optional


class Box:
    #@ invariant self.v >= 0
    def __init__(self, v: int):
        #@ requires v >= 0
        #@ ensures self.v == v
        self.v = v
        self.next: Optional[Box] = None

    def bump(self) -> None:
        #@ ensures self.v == old(self.v) + 1
        self.v += 1


def alias_write(a: Box, b: Box) -> int:
    #@ ensures result == 1
    a.v = 1
    b.v = 2
    return a.v


def alias_call(a: Box, b: Box) -> int:
    #@ ensures result == 0
    x = a.v
    b.bump()
    return a.v - x


def fresh_distinct(a: Box) -> int:
    #@ ensures result == old(a.v)
    n = Box(3)
    n.bump()
    return a.v


def break_child(a: Box) -> None:
    if a.next is not None:
        a.next.v = -1


def break_local() -> Box:
    n = Box(0)
    n.v = -5
    return n


def loop_bump(a: Box, k: int) -> None:
    #@ requires k >= 0
    #@ ensures a.v == old(a.v) + k
    for i in range(k):
        #@ invariant a.v == old(a.v) + i
        a.bump()
