# An object read out of a list or dict is assumed to satisfy its invariant.
# That holds only if nobody the reader can't see has it broken: the reader
# itself, a caller waiting on a call, a raise into a handler, code typed as a
# base class, or an initializer that let the object escape.


class Acct:
    #@ invariant self.bal >= 0

    def __init__(self):
        self.bal = 0


def peek(accts: list[Acct]) -> int:
    #@ ensures result >= 0
    if len(accts) > 0:
        return accts[0].bal
    return 0


def aliased(a: Acct, accts: list[Acct]) -> int:
    #@ ensures result >= 0
    a.bal = -1
    r = 0
    if len(accts) > 0:
        r = accts[0].bal
    a.bal = 0
    return r


def across_call(a: Acct, accts: list[Acct]) -> int:
    #@ ensures result >= 0
    a.bal = -1
    r = peek(accts)
    a.bal = 0
    return r


def in_handler(accts: list[Acct]) -> int:
    #@ ensures result >= 0
    if len(accts) == 0:
        return 0
    try:
        accts[0].bal = -1
        raise ValueError("x")
    except ValueError:
        return accts[0].bal


class Base:
    def __init__(self):
        self.x = 0


class Capped(Base):
    #@ invariant self.x <= 100

    def __init__(self):
        self.x = 0


def lift(b: Base):
    b.x = 1000


def capped_first(cs: list[Capped]) -> int:
    #@ ensures result <= 100
    if len(cs) > 0:
        return cs[0].x
    return 0


class Node:
    #@ invariant self.v >= 0 and self.w >= 0

    def __init__(self, reg: list["Node"]):
        self.v = -1
        self.w = 0
        reg.append(self)
        self.w = first_v(reg)
        self.v = 0


def first_v(reg: list[Node]) -> int:
    #@ ensures result >= 0
    if len(reg) > 0:
        return reg[len(reg) - 1].v
    return 0
