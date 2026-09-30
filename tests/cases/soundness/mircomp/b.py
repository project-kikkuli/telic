def g(xs: list[int]) -> int:
    #@ mirrors a.py::f
    return sum([x * 3 for x in xs])


def h(n: int) -> int:
    #@ mirrors a.py::f2
    if n > 0:
        return len([0 for _ in range(n)])
    return 0
