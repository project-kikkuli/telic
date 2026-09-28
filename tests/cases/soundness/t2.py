def bump(ys: list[int]) -> None:
    #@ requires len(ys) >= 2
    #@ ensures len(ys) == len(old(ys))
    #@ ensures ys[1] == 100
    ys[1] = 100


def iter_mut_call(xs: list[int]) -> int:
    #@ requires len(xs) == 2
    #@ requires xs[1] == 5
    #@ ensures result == 5
    last = 0
    #@ index k
    #@ invariant implies(k >= 2, last == 5)
    for x in xs:
        bump(xs)
        last = x
    return last


def grow(ys: list[int]) -> None:
    #@ ensures len(ys) == len(old(ys)) + 1
    ys.append(0)


def iter_grow(xs: list[int]) -> int:
    #@ requires len(xs) == 1
    #@ ensures result == 1
    n = 0
    #@ index k
    #@ invariant n == k
    for x in xs:
        grow(xs)
        n = n + 1
    return n


def abs(x: int) -> int:
    return 0 - x


def uses_abs(x: int) -> int:
    #@ ensures result >= 0
    return abs(x)


def orval(a: int, b: int) -> bool:
    #@ requires a == 3
    #@ ensures result == True
    return a or b


def ret_alias(a: list[int]) -> list[int]:
    while False:
        pass
    return a


def via_ret(xs: list[int]) -> int:
    #@ requires len(xs) == 1
    #@ requires xs[0] == 0
    #@ ensures result == 0
    ys = ret_alias(xs)
    ys[0] = 5
    return xs[0]


def two(a: list[int], b: list[int]) -> None:
    #@ requires len(a) == 1 and len(b) == 1
    #@ ensures a[0] == 1 and b[0] == 2
    b[0] = 2
    a[0] = 1


def same_twice(xs: list[int]) -> int:
    #@ requires len(xs) == 1
    #@ ensures result == 2
    two(xs, xs)
    return xs[0]
