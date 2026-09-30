def f(x: int) -> int:
    #@ lifecycle monotonic self.n
    return x


class Part:
    def __init__(self) -> None:
        self.n = 0


class Bad:
    #@ lifecycle status: A
    #@ lifecycle monotonic self.part.n
    def __init__(self, part: Part) -> None:
        self.n = 0
        self.part = part
