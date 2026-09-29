# Unpacking in a for loop: the items of a tuple are opaque, never guessed.


def swapped() -> int:
    #@ ensures result == 1
    t = 0
    for a, b in [(2, 1)]:
        t = a
    return t


def all_same(pairs: list[tuple[int, int]]) -> int:
    #@ ensures result == 0
    t = 0
    for a, b in pairs:
        t = a - b
    return t
