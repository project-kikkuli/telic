# A call to an async function that is not awaited runs none of it yet.


class Counter:
    def __init__(self):
        self.n = 0


async def bump(c: Counter) -> None:
    #@ ensures c.n == old(c.n) + 1
    c.n = c.n + 1


def kick(c: Counter) -> int:
    #@ ensures result == old(c.n) + 1
    bump(c)
    return c.n
