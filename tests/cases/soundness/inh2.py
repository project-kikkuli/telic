# A constructor that calls a method on self before a subclass has set its
# fields runs the override on a half-built object.


class Base:
    #@ invariant self.z >= 0
    def __init__(self):
        self.z = 0
        self.z = self.size()

    def size(self) -> int:
        #@ ensures result >= 0
        return 0


class Sub(Base):
    #@ invariant self.n >= 0
    def __init__(self, n: int):
        #@ requires n >= 0
        super().__init__()
        self.n = n

    def size(self) -> int:
        return self.n


def made() -> int:
    #@ ensures result >= 0
    return Sub(1).z
