# Coverage: steps no function takes, and lifecycles nothing exercises.
#@ aim DOOR-SHUT: WHILE a vault is sealed, the system shall never open it.
#@   by: Vault


class Vault:
    #@ lifecycle mode: 0 -> 1 -> 2, 1 -> 0
    #@ [DOOR-SHUT] lifecycle once self.sealed
    #@ lifecycle never mode: 2 -> 0
    def __init__(self) -> None:
        self.mode = 0
        self.sealed = False

    def arm(self) -> None:
        if self.mode == 0:
            self.mode = 1

    def fire(self) -> None:
        if self.mode == 1:
            self.mode = 2
