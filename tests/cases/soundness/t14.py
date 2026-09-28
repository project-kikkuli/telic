def idx_clash(xs: list[int]) -> int:
    #@ requires len(xs) == 3
    #@ ensures result == 2
    k = 100
    t = 0
    #@ index k
    #@ invariant k == 0 or t == k - 1
    for x in xs:
        t = k
    return t
