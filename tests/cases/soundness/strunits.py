# A Python string is code points: "é" is one, however many bytes it takes.
def accent_length() -> int:
    #@ ensures result == 2
    return len("é")
