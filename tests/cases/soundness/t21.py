# Inheritance: subclasses share their bases' fields.


class B:
    #@ invariant self.x >= 0
    def __init__(self, x: int):
        #@ requires x >= 0
        self.x = x

    def value(self) -> int:
        return 1

    def shrink(self) -> None:
        self.x = 0


class C(B):
    #@ invariant self.x >= 10
    def value(self) -> int:
        return 2


def via_base(b: B) -> int:
    #@ ensures result == 1
    return b.value()  # may run C.value


def inherited_init(x: int) -> C:
    #@ requires x >= 0
    return C(x)  # B.__init__ allows x = 0, C's invariant does not


def shrink_c(c: C) -> int:
    #@ ensures result >= 10
    c.shrink()  # B.shrink keeps B's invariant, not C's
    return c.x


async def other_task() -> None:
    pass


async def after_await(b: B) -> int:
    #@ ensures result >= 10
    await other_task()
    return b.x  # C's invariant must not be assumed of every object
