# A trusted contract that only three unfoldings show to be contradictory:
# f(n) == f(n + 1) + 1 with 0 <= f <= 1. A proof that unfolds it that deep
# assumes false.


#@ trusted
#@ ensures 0 <= result and result <= 1 and result == f(n + 1) + 1
def f(n: int) -> int:
    return 0


#@ ensures result == 99
def sums(n: int) -> int:
    return f(n) + f(n + 1) + f(n + 2)


#@ requires n >= 0
#@ ensures result == 99
def sums_from(n: int) -> int:
    return f(n) + f(n + 1) + f(n + 2)
