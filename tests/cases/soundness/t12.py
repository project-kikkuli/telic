def maybe(c: bool) -> int:
    #@ ensures result == 1
    if c:
        y = 1
    return y


def after_loop(xs: list[int]) -> int:
    #@ ensures result == 0
    for i in range(len(xs)):
        pass
    return i - i
