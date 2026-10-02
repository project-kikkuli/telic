class Base:
    def __init__(self, x: int):
        self.x = x

    def m(self) -> int:
        self.x = -1
        return self.x


class Sub(Base):
    #@ invariant self.x >= 0

    def m(self) -> int:
        #@ ensures result >= 0
        return self.x
