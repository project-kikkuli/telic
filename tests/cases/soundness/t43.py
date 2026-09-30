# Comprehensions and all()/any() generators: every element's obligations
# and effects must survive, whatever shape telic models the result with.
# Every function below except the helpers must NOT prove.
import lib


def pos(x: int) -> int:
    #@ requires x > 0
    #@ ensures result == x
    return x


def boom(x: int) -> int:
    #@ ensures result == x
    if x == 3:
        raise ValueError("three")
    return x


class Counter:
    def __init__(self) -> None:
        #@ ensures self.n == 0
        self.n = 0

    def bump(self) -> bool:
        #@ ensures self.n == old(self.n) + 1
        #@ ensures result == True
        self.n = self.n + 1
        return True


def grow(ys: list[int]) -> int:
    #@ ensures result == 0
    ys.append(1)
    return 0


def pre_in_comp(xs: list[int]) -> list[int]:
    #@ ensures len(result) == len(xs)
    return [pos(x) for x in xs]


def raise_in_comp(xs: list[int]) -> list[int]:
    #@ ensures len(result) == len(xs)
    return [boom(x) for x in xs]


def div_in_comp(xs: list[int]) -> list[int]:
    #@ ensures len(result) == len(xs)
    return [10 // x for x in xs]


def index_in_comp(xs: list[int], ys: list[int]) -> list[int]:
    #@ ensures len(result) == len(xs)
    return [ys[x] for x in xs]


def effect_in_comp(c: Counter, xs: list[int]) -> int:
    #@ requires c.n == 0
    #@ ensures result == 0
    _ = [c.bump() for x in xs]
    return c.n


def effect_in_all(c: Counter, xs: list[int]) -> int:
    #@ requires c.n == 0
    #@ ensures result == 0
    _ = all(c.bump() for x in xs)
    return c.n


def list_effect_in_comp(xs: list[int], ys: list[int]) -> int:
    #@ requires len(ys) == 0
    #@ ensures result == 0
    _ = [grow(ys) for x in xs]
    return len(ys)


def grows_its_source(xs: list[int]) -> int:
    #@ ensures result == 0
    _ = [grow(xs) for x in xs if x < 0]
    return 0


def div_in_nested(xs: list[int], ys: list[int]) -> int:
    #@ ensures result == 0
    _ = [a // b for a in xs for b in ys]
    return 0


def div_in_setcomp(xs: list[int]) -> int:
    #@ ensures result == 0
    _ = {10 // x for x in xs}
    return 0


def div_in_dictcomp(xs: list[int]) -> int:
    #@ ensures result == 0
    _ = {x: 10 // x for x in xs}
    return 0


def pre_in_list_element(xs: list[int]) -> int:
    #@ ensures result == 0
    _ = [[pos(x)] for x in xs]
    return 0


def pre_in_unchecked_source(n: int) -> int:
    #@ ensures result == 0
    _ = [pos(x) for x in lib.items(n)]
    return 0


def pre_in_range(n: int) -> int:
    #@ ensures result == 0
    _ = [pos(i) for i in range(n)]
    return 0


def pre_in_items(d: dict[str, int]) -> int:
    #@ ensures result == 0
    _ = {k: pos(v) for k, v in d.items()}
    return 0


def pre_in_enumerate(xs: list[int]) -> int:
    #@ ensures result == 0
    _ = [pos(i) + x for i, x in enumerate(xs)]
    return 0


def pre_in_generator(xs: list[int]) -> int:
    #@ ensures result == 0
    _ = sum(pos(x) for x in xs)
    return 0


def distinct_dicts(xs: list[int]) -> bool:
    #@ requires len(xs) == 1
    #@ ensures result == True
    return f"{ {x: 1 for x in xs} }" == f"{ {x: 2 for x in xs} }"
