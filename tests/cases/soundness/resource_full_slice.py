def wrong(xs: list[int]) -> list[int]:
    #@ requires len(xs) > 0
    #@ ensures cost("alloc") == 0
    return xs[:]
