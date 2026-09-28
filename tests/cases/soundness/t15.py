def helper(x: int) -> int:
    #@ ensures result == 0
    y = {1: 2}
    return x


def user(x: int) -> int:
    #@ ensures result == 0
    return helper(x)
