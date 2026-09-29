# A method's @ensures, used as a lemma, holds only for objects satisfying
# the class invariant; assumed for every heap it made the theory inconsistent.

class Box:
    #@ invariant self.v <= 0

    def __init__(self):
        self.v = 0

    def get(self) -> int:
        #@ ensures result <= 0
        return self.v


def anything(b: Box, x: int) -> int:
    #@ ensures result == x + 1
    return b.get() + x
