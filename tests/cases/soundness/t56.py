from dataclasses import dataclass


def list_alias(a: list[int], b: list[int]) -> int:
    #@ requires len(a) > 0 and len(b) > 0
    #@ ensures result == old(b[0])
    a[0] += 1
    return b[0]


def dict_alias(a: dict[str, int], b: dict[str, int]) -> int:
    #@ requires "x" in a and "x" in b
    #@ ensures result == old(b["x"])
    a["x"] += 1
    return b["x"]


def dict_delete_alias(a: dict[str, int], b: dict[str, int]) -> bool:
    #@ requires "x" in a and "x" in b
    #@ ensures result
    del a["x"]
    return "x" in b


@dataclass(eq=False)
class Holder:
    xs: list[int]


def field_parameter_alias(a: Holder, b: list[int]) -> int:
    #@ requires len(a.xs) > 0 and len(b) > 0
    #@ ensures result == old(b[0])
    a.xs[0] += 1
    return b[0]


def two_field_alias(a: Holder, b: Holder) -> int:
    #@ requires a != b
    #@ requires len(a.xs) > 0 and len(b.xs) > 0
    #@ ensures result == old(b.xs[0])
    a.xs[0] += 1
    return b.xs[0]


def cross_schema_alias(a: list[int], b: list[float]) -> float:
    #@ requires len(a) > 0 and len(b) > 0
    #@ ensures result == old(b[0])
    a[0] += 1
    return b[0]


class FieldA:
    def __init__(self) -> None:
        self.x: int = 0


class FieldB:
    def __init__(self) -> None:
        self.x: int = 0


class FieldC(FieldA, FieldB):
    pass


def shared_property_alias(a: FieldA, b: FieldB) -> int:
    #@ ensures result == old(b.x)
    a.x += 1
    return b.x
