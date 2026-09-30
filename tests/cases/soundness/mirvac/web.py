def web_price(x: int) -> int:
    #@ requires x < 0
    #@ aim SAME
    #@ mirrors ./server.py::price
    return x + 1000
