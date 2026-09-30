# isinstance with a tuple of classes is a disjunction, never a conjunction;
# quantifiers over a dict range over the keys it holds, not every key.
from typing import Any


class A:
    pass


class B:
    pass


def first_of_two(x: Any) -> bool:
    #@ ensures result
    if isinstance(x, (A, B)):
        return isinstance(x, A)
    return True


def every_key(d: dict[str, int]) -> int:
    #@ requires all(d[k] > 0 for k in d)
    #@ ensures result > 0
    return d["missing"] if "missing" in d else d.get("x", 0)
