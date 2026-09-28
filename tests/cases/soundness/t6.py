def inc(ys: list[int]) -> bool:
    #@ requires len(ys) >= 1
    #@ ensures len(ys) == len(old(ys))
    #@ ensures ys[0] == old(ys[0]) + 1
    #@ ensures result == (ys[0] < 3)
    ys[0] = ys[0] + 1
    return ys[0] < 3


def while_cond_mut(xs: list[int]) -> int:
    #@ requires len(xs) == 1 and xs[0] == 0
    #@ ensures result == 1
    n = 5
    #@ decreases n
    while inc(xs) and n > 0:
        n = n - 1
    return xs[0]
