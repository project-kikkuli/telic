# A lifecycle binds every stretch other code can observe: a call from start
# to end, and each piece between two awaits or yields (other tasks, or the
# generator's consumer, run in the gaps). An initializer run again on a live
# object, or a trusted body, keeps nothing.
import asyncio
from typing import Iterator


class Tab:
    #@ lifecycle monotonic self.paid
    def __init__(self) -> None:
        self.paid = 0

    def pay(self, n: int) -> None:
        #@ requires n >= 0
        self.paid = self.paid + n


def restart(t: Tab) -> None:
    t.__init__()


class Gauge:
    #@ lifecycle monotonic self.level
    def __init__(self) -> None:
        self.level = 0


def dip(g: Gauge) -> Iterator[int]:
    # the consumer sees the level drop between two next() calls
    old = g.level
    g.level = 0
    yield 1
    g.level = old


class Latch:
    #@ lifecycle once self.shut
    def __init__(self) -> None:
        self.shut = False

    def close(self) -> None:
        self.shut = True


def reopen_later(a: Latch) -> Iterator[int]:
    # the consumer may close the latch at the yield
    if not a.shut:
        yield 1
        a.shut = False


async def reopen_after(a: Latch, n: int) -> None:
    # other tasks may close it at any of the awaits
    if not a.shut:
        i = 0
        while i < n:
            await asyncio.sleep(0)
            i = i + 1
        a.shut = False


class Meter:
    #@ lifecycle monotonic self.v
    def __init__(self) -> None:
        self.v = 0

    def tick(self) -> None:
        self.v = self.v + 1


#@ trusted
def wipe(m: Meter) -> None:
    m.v = 0
