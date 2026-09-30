# Recursion that never ends raises RecursionError: neither spin nor what rests on it is safe.

#@ aim FORTY: The system shall return 42.


def spin(n: int) -> int:
    xs = [0]
    xs.append(n)
    return spin(n + 1)


def claim(n: int) -> int:
    #@ aim FORTY
    #@ ensures result == 42
    spin(n)
    return 42


def ping(n: int) -> None:
    pong(n)


def pong(n: int) -> None:
    ping(n)


def claim2(n: int) -> int:
    #@ ensures result == 42
    ping(n)
    return 42
