# A callee that changes a list argument in place: when the argument is a new
# list (a literal, a copy), what the callee's contract says about it after
# the call must not be read off its value before the call.


def grow(ys: list[int]) -> None:
    #@ ensures len(ys) == len(old(ys)) + 1
    ys.append(0)


def grow_literal() -> int:
    #@ ensures result == 1
    grow([1])
    return 0


def grow_copy(xs: list[int]) -> int:
    #@ ensures result == 1
    grow(xs[:])
    return 0
