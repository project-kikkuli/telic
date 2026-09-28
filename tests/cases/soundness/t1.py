def loopvar() -> int:
    #@ ensures result == 2
    i = 0
    for i in range(3):
        i = 10
    return i


def alias_ifexp(xs: list[int]) -> int:
    #@ requires len(xs) == 1
    #@ requires xs[0] == 0
    #@ ensures result == 0
    ys = xs if len(xs) > 0 else xs
    ys[0] = 5
    return xs[0]


def alias_ann(xs: list[int]) -> int:
    #@ requires len(xs) == 1
    #@ requires xs[0] == 0
    #@ ensures result == 0
    ys: list[int] = xs
    ys[0] = 5
    return xs[0]


def alias_tuple(xs: list[int]) -> int:
    #@ requires len(xs) == 1
    #@ requires xs[0] == 0
    #@ ensures result == 0
    ys, k = xs, 0
    ys[0] = 5
    return xs[0]


def rebind_ann(xs: list[int]) -> None:
    #@ ensures len(xs) == 0
    xs: list[int] = []


def rebind_tuple(xs: list[int]) -> None:
    #@ ensures len(xs) == 0
    xs, k = [0][0:0], 0
