# Recursion telic cannot see as a call: through a rebound name, a lambda, a
# decorator's wrapper, a local alias, a function passed as an argument. Each
# claim raises RecursionError.
import functools
from typing import Callable


def rebound(n: int) -> int:
    return again(n + 1)


again = rebound


def claim_rebound(n: int) -> int:
    #@ ensures result == 42
    rebound(n)
    return 42


spin = lambda n: spin(n + 1)  # noqa: E731


def claim_lambda(n: int) -> int:
    #@ ensures result == 42
    spin(n)
    return 42


def wraps_deco(f):
    @functools.wraps(f)
    def w(*a):
        return f(*a)

    return w


@wraps_deco
def wrapped(n: int) -> int:
    return wrapped(n + 1)


def claim_wraps(n: int) -> int:
    #@ ensures result == 42
    wrapped(n)
    return 42


def plain_deco(f):
    def w(n: int) -> int:
        return f(n)

    return w


@plain_deco
def decorated(n: int) -> int:
    return decorated(n + 1)


def claim_decorated(n: int) -> int:
    #@ ensures result == 42
    decorated(n)
    return 42


def aliased(n: int) -> int:
    g = aliased
    return g(n + 1)


def claim_aliased(n: int) -> int:
    #@ ensures result == 42
    aliased(n)
    return 42


def apply(f: Callable[[int], int], n: int) -> int:
    return f(n)


def passed(n: int) -> int:
    return apply(passed, n + 1)


def claim_passed(n: int) -> int:
    #@ ensures result == 42
    passed(n)
    return 42


class Node:
    def __init__(self, n: int) -> None:
        self.n = n
        self.nxt = Node(n + 1).n


def claim_constructor(n: int) -> int:
    #@ ensures result == 42
    Node(n)
    return 42
