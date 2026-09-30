class Order:
    #@ lifecycle monotonic self.paid

    def __init__(self, paid: int):
        self.paid = paid

    def pay(self, amount: int) -> None:
        #@ requires amount >= 0
        self.paid = self.paid + amount
