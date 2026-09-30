# Lifecycles are claims across calls: a relation each call keeps must be
# transitive, 'never' must follow from what every call keeps, and every
# function that can change the object must be checked against it.


class Counter:
    # true of each call (bump adds one), false across two calls
    #@ lifecycle self.n <= old(self.n) + 1 and old(self.n) <= self.n
    def __init__(self) -> None:
        self.n = 0

    def bump(self) -> None:
        self.n = self.n + 1


class Job:
    #@ lifecycle state: 0 -> 1 -> 2
    # every call keeps 'not 0 -> 2', but start then finish goes 0 -> 2
    #@ lifecycle never state: 0 -> 2
    def __init__(self) -> None:
        self.state = 0

    def start(self) -> None:
        if self.state == 0:
            self.state = 1

    def finish(self) -> None:
        if self.state == 1:
            self.state = 2


class Base:
    def __init__(self) -> None:
        self.level = 0

    def reset(self) -> None:
        # also runs on a Sub, whose level may never go down
        self.level = 0


class Sub(Base):
    #@ lifecycle monotonic self.level
    def up(self) -> None:
        self.level = self.level + 1


class Door:
    #@ lifecycle once self.locked
    def __init__(self) -> None:
        self.locked = False

    def lock(self) -> None:
        self.locked = True


def unlock_all(doors: list[Door]) -> None:
    for d in doors:
        d.locked = False


def unlock_first(doors: list[Door]) -> None:
    if doors:
        doors[0].locked = False


class Valve:
    #@ lifecycle monotonic self.opened
    def __init__(self) -> None:
        self.opened = 0

    def twist(self, k: int) -> None:
        # not modelled (a nested function): the lifecycle cannot rest on it
        def half(x: int) -> int:
            return x // 2

        self.opened = half(k)
