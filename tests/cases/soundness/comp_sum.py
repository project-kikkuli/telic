from dataclasses import dataclass


@dataclass
class T:
    who: int
    amount: int


def after_write(xs: list[T], m: int) -> int:
    # the same comprehension before and after a field write is not the same list
    #@ requires len(xs) > 0
    before = sum(t.amount for t in xs if t.who == m)
    xs[0].amount = xs[0].amount + 1
    after = sum(t.amount for t in xs if t.who == m)
    #@ assert before == after
    return after


def other_member(xs: list[T], m: int, p: int) -> list[T]:
    # appending for one member changes no other member's sum, but it does change this one's
    #@ requires p != 0
    #@ ensures sum(t.amount for t in result if t.who == m + 1) == sum(t.amount for t in xs if t.who == m + 1)
    #@ ensures sum(t.amount for t in result if t.who == m) == sum(t.amount for t in xs if t.who == m)
    out = xs[:]
    out.append(T(m, p))
    return out


def shorter_list(xs: list[T], m: int) -> list[T]:
    # a prefix's sum is not the whole list's
    #@ requires len(xs) > 0
    #@ ensures sum(t.amount for t in result if t.who == m) == sum(t.amount for t in xs if t.who == m)
    return xs[1:]
