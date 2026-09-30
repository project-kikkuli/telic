# The two preconditions share no input, so "agree on every input" is vacuous.

#@ aim SAME: The web and server prices shall always agree.


def price(x: int) -> int:
    #@ requires x > 0
    #@ aim SAME
    return x
