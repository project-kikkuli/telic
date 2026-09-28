from dataclasses import dataclass


@dataclass
class P:
    x: int

    def __post_init__(self) -> None:
        self.x = 0


def mk(v: int) -> int:
    #@ ensures result == v
    p = P(v)
    return p.x


def print(xs: list[int]) -> None:
    xs[0] = 99


def shadow_print(xs: list[int]) -> int:
    #@ requires len(xs) == 1 and xs[0] == 0
    #@ ensures result == 0
    print(xs)
    return xs[0]
