def signed(s: str) -> int:
    # text with a minus sign parses to a negative number
    #@ requires s.startswith("-") and s[1:].isdigit()
    #@ ensures result >= 0
    try:
        return int(s)
    except ValueError:
        return 0


def unicode_digit(s: str) -> int:
    # int() reads Unicode digits too: int("٣") == 3
    #@ requires s == "٣"
    #@ ensures result != 3
    try:
        return int(s)
    except ValueError:
        return 0


def spaced(s: str) -> float:
    # float() skips surrounding spaces
    #@ requires s == " 2 "
    #@ ensures result != 2.0
    try:
        return float(s)
    except ValueError:
        return 0.0
