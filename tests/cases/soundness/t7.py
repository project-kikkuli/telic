def setz(ys: list[int]) -> int:
    #@ requires len(ys) >= 1
    #@ ensures len(ys) == len(old(ys))
    #@ ensures ys[0] == 0
    #@ ensures result == 0
    ys[0] = 0
    return 0


def first(a: list[int], k: int) -> int:
    #@ requires len(a) >= 1
    #@ ensures result == a[0] + k
    return a[0] + k


def stale_arg(xs: list[int]) -> int:
    #@ requires len(xs) >= 1 and xs[0] == 7
    #@ ensures result == 7
    return first(xs, setz(xs))


def arith(x: float, n: int) -> int:
    #@ ensures result == 0
    a = round(2.5) - 2
    b = int(-2.7) + 2
    c = (-7) // 2 + 4
    d = (-7.5) % 2 - 0.5
    e = (7.0 // -2.0) + 4.0
    f = 1 + 0.5 - 1.5
    g = (-7) % -2 + 1
    h = round(-0.5)
    return a + b + c + int(d) + int(e) + int(f) + g + h


def chained(x: int) -> bool:
    #@ ensures result == (0 < x and x < 10)
    return 0 < x < 10
