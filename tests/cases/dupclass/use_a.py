from a.shapes import Box


def read_a(b: Box) -> int:
    #@ ensures result >= 0
    return b.get()


def field_a(b: Box) -> int:
    #@ ensures result >= 0
    return b.v


def make_a() -> Box:
    return Box(3)
