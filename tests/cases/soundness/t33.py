# A task suspended at 'await', or a generator at 'yield', lets other code run:
# other tasks assume every object satisfies its invariant there, and a
# consumer receives the yielded object as a checked one.
import asyncio


class Acct:
    #@ invariant self.bal >= 0

    def __init__(self):
        self.bal = 0


async def dip(a: Acct):
    a.bal = -1
    await asyncio.sleep(0)
    a.bal = 5


async def dip_listed(accts: list[Acct]):
    if len(accts) > 0:
        accts[0].bal = -1
        await asyncio.sleep(0)
        accts[0].bal = 5


async def dip_each(accts: list[Acct]):
    for a in accts:
        a.bal = -1
        await asyncio.sleep(0)
        a.bal = 5


async def sees(a: Acct) -> int:
    #@ ensures result >= 0
    await asyncio.sleep(0)
    return a.bal


def peek(accts: list[Acct]):
    if len(accts) > 0:
        accts[0].bal = -1
        yield accts[0]
        accts[0].bal = 5

