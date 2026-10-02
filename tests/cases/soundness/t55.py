class A:
    def __init__(self) -> None:
        self.x: int = 0


class B:
    def __init__(self) -> None:
        self.x: int = 0


class C(A, B):
    pass


def mutate_alias(a: A, b: B) -> int:
    #@ ensures result == old(b.x)
    a.x += 1
    return b.x


def same_object() -> int:
    value = C()
    return mutate_alias(value, value)
