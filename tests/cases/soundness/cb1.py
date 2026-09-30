# Functions handed on as values run where telic cannot see the call: a lambda
# given to sorted/min/list.sort by key, to map/filter or functools.reduce, a
# checked function given to map, and callbacks given to unchecked code. Each
# callback fails on some element or argument.
import functools
import itertools
import threading


def pos(x: int) -> int:
    #@ requires x > 0
    return 10 // x


def by_key(xs: list[int]) -> int:
    #@ ensures result == 0
    _ = sorted(xs, key=lambda x: 10 // x)
    return 0


def min_key(xs: list[int]) -> int:
    #@ requires len(xs) > 0
    #@ ensures result == 0
    _ = min(xs, key=lambda x: 10 // x)
    return 0


def sort_in_place(xs: list[int]) -> int:
    #@ ensures result == 0
    xs.sort(key=lambda x: 10 // x)
    return 0


def mapped(xs: list[int]) -> int:
    #@ ensures result == 0
    _ = list(map(pos, xs))
    return 0


def filtered(xs: list[int]) -> int:
    #@ ensures result == 0
    _ = list(filter(lambda x: 10 // x > 1, xs))
    return 0


def reduced(xs: list[int]) -> int:
    #@ ensures result == 0
    _ = functools.reduce(lambda acc, x: acc + 10 // x, xs, 0)
    return 0


def through_library(xs: list[int]) -> int:
    #@ ensures result == 0
    _ = list(itertools.filterfalse(lambda x: pos(x) > 1, xs))
    return 0


def named_through_library(xs: list[int]) -> int:
    #@ ensures result == 0
    _ = list(itertools.filterfalse(pos, xs))
    return 0


def later(n: int) -> int:
    #@ ensures result == 0
    threading.Timer(0.01, lambda: pos(n)).start()
    return 0
