# An object escapes with the exception: whoever catches it still holds the
# object, so a raise must leave its invariant intact, like a return.


class Acct:
    #@ invariant self.lo <= self.hi

    def __init__(self):
        self.lo = 0
        self.hi = 0

    def risky(self, x: int):
        #@ raises x < 0
        self.lo = self.hi + 1
        if x < 0:
            raise ValueError("negative")
        self.hi = self.lo


def spoil(accts: list[Acct], x: int):
    #@ raises x < 0 and len(accts) > 0
    if len(accts) > 0:
        accts[0].lo = accts[0].hi + 1
        if x < 0:
            raise ValueError("negative")
        accts[0].hi = accts[0].lo


class Checked:
    #@ invariant self.n >= 0

    def __init__(self, n: int):
        if n < 0:
            raise ValueError("negative")
        self.n = n
