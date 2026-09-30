import json


def total(xs: list[int]) -> int:
    #@ requires all(x >= 0 for x in xs)
    #@ ensures result >= 0
    out = 0
    for x in xs:
        #@ invariant out >= 0
        out += x
    return out


def unvalidated(body: dict) -> int:
    return total(body["xs"])


def half_validated(body: dict) -> int:
    xs = body["xs"]
    if not isinstance(xs, list) or not all(isinstance(x, int) for x in xs):
        raise ValueError("ints")
    return total(xs)


def later_view(body: dict) -> int:
    # an element that is not an int is not made one by a later conversion
    #@ ensures result == 1
    xs = body["xs"]
    if isinstance(xs, list) and len(xs) > 0 and not isinstance(xs[0], int):
        return 2
    ys: list[int] = xs
    return 1 + 0 * len(ys)


class Box:
    def __init__(self, v: int) -> None:
        self.v = v


def handed_out(body: dict) -> int:
    # an object handed to unchecked code may be changed by later unchecked calls
    b = Box(1)
    json.dumps(b)
    json.loads(body["x"])
    #@ assert b.v == 1
    return b.v
