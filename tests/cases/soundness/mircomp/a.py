# Both sides build a list with a comprehension; the two lists must not be
# taken for the same one.
def f(xs: list[int]) -> int:
    return sum([x * 2 for x in xs])


def f2(n: int) -> int:
    return len([1 for _ in range(n + 1)])
