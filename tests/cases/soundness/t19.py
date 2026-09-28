# Gradual verification: unchecked code must never be trusted beyond the
# listed assumptions. Every function below except the helpers must NOT prove.
from typing import Any, Optional

import lib


class Box:
    def __init__(self, v: int):
        #@ ensures self.v == v
        self.v = v


def ext_list(xs: list[int]) -> int:
    #@ requires len(xs) == 1 and xs[0] == 0
    #@ ensures result == 0
    lib.refill(xs)
    return xs[0]


def ext_obj(b: Box) -> int:
    #@ ensures result == old(b.v)
    lib.touch(b)
    return b.v


def ext_obj_later(b: Box, sink: Any) -> int:
    #@ ensures result == old(b.v)
    sink.keep(b)
    sink.flush()
    return b.v


def opaque_int(x: Any) -> int:
    #@ ensures result == 1
    return int(x)


def opaque_is_none(x: Any) -> int:
    #@ ensures result == 0
    if x is None:
        return 1
    return 0


def handler_path(n: int) -> int:
    #@ ensures result == 1
    y = 1
    try:
        y = lib.compute(n)
        y = 1
    except Exception:
        pass
    return y


def filtered_len(xs: list[int]) -> list[int]:
    #@ ensures len(result) == len(xs)
    return [x for x in xs if x > 0]


def opaque_cmp(a: Any, b: Any) -> int:
    #@ ensures result == 0
    if a == b:
        return 0
    return 1


def global_read() -> int:
    #@ ensures result == 5
    return lib.LIMIT


def str_ops(s: str) -> int:
    #@ ensures result == len(s)
    return len(s.strip())


async def racy(b: Box) -> int:
    #@ requires b.v == 1
    #@ ensures result == 1
    await lib.sleep(0)
    return b.v


def closure_mutates(xs: list[int]) -> int:
    #@ requires len(xs) == 1 and xs[0] == 0
    #@ ensures result == 0
    def bump() -> None:
        xs[0] = 5
    bump()
    return xs[0]


def closure_escapes(xs: list[int], sink: Any) -> int:
    #@ requires len(xs) == 1 and xs[0] == 0
    #@ ensures result == 0
    def bump() -> None:
        xs[0] = 5
    sink.register(bump)
    lib.run_callbacks()
    return xs[0]


def lambda_escapes(xs: list[int]) -> int:
    #@ requires len(xs) == 1 and xs[0] == 0
    #@ ensures result == 0
    lib.later(lambda: xs.append(1))
    lib.tick()
    return len(xs) - 1


def wrapped_contract(x: int) -> int:
    #@ ensures result == 1
    return decorated(x)


import functools


def weird(f: Any) -> Any:
    return f


@weird
def decorated(x: int) -> int:
    #@ ensures result == 1
    return 1
