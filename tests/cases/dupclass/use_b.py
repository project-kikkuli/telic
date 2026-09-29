# Every contract here would be proved if b's Box were confused with a's.
from b.shapes import Box


def read_b(b: Box) -> int:
    #@ ensures result >= 0
    return b.get()


def field_b(b: Box) -> int:
    #@ ensures result >= 0
    return b.v


def build_b() -> int:
    #@ ensures result >= 0
    return Box(0).get() - 1
