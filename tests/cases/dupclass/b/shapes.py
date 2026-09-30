class Box:
    #@ invariant self.v <= 0
    #@ lifecycle monotonic -self.v

    def __init__(self, v: int):
        #@ requires v <= 0
        self.v = v

    def get(self) -> int:
        #@ ensures result <= 0
        return self.v

    def shrink(self) -> None:
        self.v = self.v - 1
