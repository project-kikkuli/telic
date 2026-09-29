// Vacuity: preconditions that can never hold make every claim trivially true.

pub fn contradictory(x: i32) -> i32 {
    //@ requires x > 0 && x < 0
    //@ ensures result == 42
    x
}

pub fn fine(x: i32) -> i32 {
    //@ requires x > 0
    //@ ensures result > 0
    x
}
