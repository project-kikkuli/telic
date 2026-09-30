// Double is an IEEE double.

//@ ensures result
func classic() -> Bool {
    return 0.1 + 0.2 == 0.3
}

//@ ensures result == x
func reflexive(_ x: Double) -> Double {
    return x
}

//@ ensures result > x
func grows(_ x: Double) -> Double {
    return x + 1.0
}

//@ ensures result == 1.0
func zeroSign(_ x: Double) -> Double {
    return 1.0 / (x * 0.0 + 1.0)
}

//@ ensures result == x
func roundTrip(_ x: Int) -> Int {
    return Int(Double(x))
}

//@ requires x.isFinite
//@ ensures result >= x
func fine(_ x: Double) -> Double {
    return x < 0 ? x : x + 0.0
}
