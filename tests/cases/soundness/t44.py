MINIMUM = -1


class Box:
    #@ invariant self.value >= MINIMUM

    def __init__(self, value: int):
        self.value = value


def read(box: Box) -> int:
    #@ ensures result >= 0
    return box.value
