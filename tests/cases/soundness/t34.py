# A class invariant that reads another object's fields breaks when code that
# never touches the object writes that other one; other tasks assume it
# whenever they resume.
import asyncio
from typing import Optional


class Acct:
    def __init__(self):
        self.bal = 0


def nonneg(a: Optional[Acct]) -> bool:
    return a is None or a.bal >= 0


class Link:
    #@ invariant nonneg(self.nxt)

    def __init__(self):
        self.nxt: Optional[Acct] = None


class Pool:
    #@ invariant all(self.bal >= 0 for self in self.accts)

    def __init__(self):
        self.accts: list[Acct] = []


async def dip(a: Acct):
    a.bal = -1
    await asyncio.sleep(0.01)
    a.bal = 0


async def sees(k: Link) -> int:
    #@ ensures result >= 0
    await asyncio.sleep(0)
    if k.nxt is not None:
        return k.nxt.bal
    return 0


async def sees_pool(p: Pool) -> int:
    #@ ensures result >= 0
    await asyncio.sleep(0)
    if len(p.accts) > 0:
        return p.accts[0].bal
    return 0
