def maybe2(c: bool) -> int:
    #@ ensures result * result >= 0
    if c:
        y = 1
    return y
