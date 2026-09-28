def inc2(ys: list[int]) -> bool:
    #@ requires len(ys) >= 1
    #@ ensures len(ys) == len(old(ys))
    #@ ensures ys[0] == old(ys[0]) + 1
    #@ ensures result
    ys[0] = ys[0] + 1
    return True


def printed(xs: list[int]) -> int:
    #@ requires len(xs) == 1 and xs[0] == 0
    #@ ensures result == 0
    print(inc2(xs))
    return xs[0]
