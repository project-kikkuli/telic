// expect: proved
pub fn clamp(x: u32, hi: u32) -> u32 {
    //@ ensures result <= hi
    if x > hi { hi } else { x }
}

// expect: refuted
fn twice(x: u8) -> u8 {
    x * 2
}
