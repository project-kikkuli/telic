# An object written inside a loop must satisfy its class invariant on return.
# The write's path condition names the loop's havocked counter, which the
# exit contradicts: guarding the invariant with it made every claim vacuous.


class Acct:
    #@ invariant self.bal >= 0

    def __init__(self):
        self.bal = 0


def drain(accts: list[Acct]):
    for a in accts:
        a.bal = -1


def drain_range(accts: list[Acct]):
    for i in range(len(accts)):
        accts[i].bal = -1


def drain_while(accts: list[Acct]):
    i = 0
    while i < len(accts):
        accts[i].bal = -1
        i += 1


def drain_nested(accts: list[Acct], n: int):
    for a in accts:
        for _ in range(n):
            a.bal = a.bal - 1


def drain_alias(accts: list[Acct]):
    for a in accts:
        b = a
        b.bal = -1


def drain_some(accts: list[Acct], cut: int):
    for a in accts:
        if a.bal > cut:
            a.bal = cut


def drain_then_fix_one(accts: list[Acct]):
    for a in accts:
        a.bal = -1
    if len(accts) > 0:
        accts[0].bal = 0


def drain_in_try(accts: list[Acct]):
    for a in accts:
        try:
            a.bal = -1
            a.bal = int("7")
        except ValueError:
            pass


def drain_last(accts: list[Acct]):
    for a in accts:
        a.bal = 1
        a.bal = -1
        break


def refill(accts: list[Acct]):
    for a in accts:
        a.bal = 5


def clamp(accts: list[Acct], cut: int):
    for a in accts:
        if a.bal > cut and cut >= 0:
            a.bal = a.bal - cut


def refill_nested(accts: list[Acct], n: int):
    for a in accts:
        for j in range(n):
            a.bal = j
