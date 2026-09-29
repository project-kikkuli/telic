# Vacuity: preconditions or invariants that can never hold make every claim
# trivially true. None of these may be reported proved.

#@ aim NEVER: The system shall return 42 for every input.


def is_neg(x: int) -> bool:
    #@ ensures result == (x < 0)
    return x < 0


def contradictory(x: int) -> int:
    #@ requires x > 0 and x < 0
    #@ aim NEVER
    #@ ensures result == 42
    return x


def through_helper(x: int) -> int:
    #@ requires is_neg(x) and x > 5
    #@ ensures result == 42
    return x


def empty_below_zero(xs: list[int]) -> int:
    #@ requires len(xs) < 0
    #@ ensures result == 42
    return 0


def split_across(x: int, y: int) -> int:
    #@ requires x < y
    #@ requires y < x
    #@ ensures result == 42
    return x + y


class Impossible:
    #@ invariant self.v > 0
    #@ invariant self.v < 0

    def __init__(self, v: int):
        self.v = v

    def get(self) -> int:
        #@ ensures result == 42
        return self.v


class Counter:
    #@ invariant self.n >= 0

    def __init__(self):
        self.n = 0

    def below_zero(self) -> int:
        #@ requires self.n < 0
        #@ ensures result == 42
        return self.n


def fine(x: int) -> int:
    #@ requires x > 0
    #@ ensures result > 0
    return x
