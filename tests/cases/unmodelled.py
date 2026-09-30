from typing import Optional


class Log:
    #@ invariant self.count >= 0

    def __init__(self):
        self.count = 0
        self.lines: list[Optional[str]] = []  # telic cannot model this field

    def bump(self) -> int:
        #@ ensures result == old(self.count) + 1
        self.count = self.count + 1
        return self.count

    def reset(self) -> None:
        #@ ensures self.count == 0
        self.count = 0


def fresh_count() -> int:
    #@ ensures result == 1
    log = Log()
    return log.bump()
