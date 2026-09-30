# A subclass invariant over an inherited field: code typed as the base may
# break it, then a call through the base runs the override that assumed it.


class Base:
    def __init__(self, x: int):
        self.x = x

    def setx(self, v: int) -> None:
        self.x = v

    def helper(self) -> int:
        #@ ensures result <= 100
        return min(self.x, 100)


class Sub(Base):
    #@ invariant self.x <= 100
    def __init__(self, x: int):
        #@ requires x <= 100
        self.x = x

    def helper(self) -> int:
        return self.x


def through_base(b: Base) -> int:
    #@ ensures result <= 100
    b.setx(1000)
    return b.helper()
