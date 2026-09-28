def f(x: int) -> int:
    #@ raises x < 0
    if x < 0:
        raise ValueError("neg")
    return x
