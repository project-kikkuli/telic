def right(x: bool) -> bool:
    #@ requires not x
    #@ ensures cost("work") == 3
    return x and True


def wrong(x: bool) -> bool:
    #@ requires not x
    #@ ensures cost("work") == 4
    return x and True


def bounded_callback(x: bool) -> bool:
    #@ requires x
    #@ ensures cost("work") <= 20
    return x and True


def callback_upper(xs: list[bool]) -> list[bool]:
    #@ requires all(x for x in xs)
    #@ ensures cost("work") <= 30 * len(xs) + 100
    return [bounded_callback(x) for x in xs]


def callback_false_exact(xs: list[bool]) -> list[bool]:
    #@ requires all(x for x in xs)
    #@ ensures cost("work") == 23 * len(xs) + 3
    return [bounded_callback(x) for x in xs]


def any_upper(xs: list[int]) -> bool:
    #@ ensures cost("work") <= 10 * len(xs) + 100
    return any(x > 0 for x in xs)


def any_false_lower(xs: list[int]) -> bool:
    #@ ensures cost("work") >= 10 * len(xs)
    return any(x > 0 for x in xs)


def membership_singleton() -> bool:
    #@ ensures cost("work") == 8
    xs = [1]
    return 1 in xs


def membership_false_full_scan() -> bool:
    #@ ensures cost("work") >= 12
    xs = [1, 2, 3]
    return 1 in xs
