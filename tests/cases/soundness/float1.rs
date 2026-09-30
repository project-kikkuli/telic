// f64 is an IEEE double.

//@ ensures result
pub fn classic() -> bool {
    0.1 + 0.2 == 0.3
}

//@ ensures result == x
pub fn reflexive(x: f64) -> f64 {
    x
}

//@ ensures result > x
pub fn grows(x: f64) -> f64 {
    x + 1.0
}

//@ ensures result >= 0
pub fn to_int(x: f64) -> i64 {
    if x >= 0.0 { x as i64 } else { 0 }
}

//@ ensures result != 0 || x < 1.0
pub fn nan_cast(x: f64) -> i64 {
    x as i64
}

//@ ensures result == x
pub fn round_trip(x: i64) -> i64 {
    (x as f64) as i64
}

//@ requires x.is_finite() && y.is_finite()
//@ ensures result == x + (y + 1.0)
pub fn order(x: f64, y: f64) -> f64 {
    (x + y) + 1.0
}

//@ requires x == 0.0
//@ ensures !result
pub fn neg_zero(x: f64) -> bool {
    x.is_sign_negative()
}

//@ ensures result >= 0.0 || result.is_nan()
pub fn fine(x: f64) -> f64 {
    x.abs()
}
