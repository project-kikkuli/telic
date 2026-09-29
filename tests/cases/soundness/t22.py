# Moving a local list into a field/another name is only safe if it is dead after.


class Bag:
    def __init__(self, items: list[int]):
        self.items: list[int] = items[:]


def moved_ok() -> int:
    #@ ensures result == 2
    xs = [1, 2]
    ys = xs  # xs is never used again: a move
    ys.append(3)
    return ys[1]


def used_after() -> int:
    #@ ensures result == 2
    xs = [1, 2]
    ys = xs  # not a move: xs is read below
    ys.append(3)
    return len(xs)


def in_loop() -> int:
    #@ ensures result == 0
    xs = [0]
    total = 0
    for i in range(3):
        ys = xs  # the next iteration sees xs again
        ys.append(i)
        total = total + ys[0]
    return len(ys) - 4
