// A crate split across files (`mod x;`): verdicts pinned with `// expect:`
// in every file (tests/test_rust.py).

pub mod geo;
mod util;

use geo::shapes::{Shape, area};
use crate::util::clamp;

// expect: proved
pub fn big(s: Shape) -> bool {
    //@ ensures implies(matches!(s, Shape::Dot), !result)
    area(s) > 100
}

// expect: proved
pub fn clamped(x: u32) -> u32 {
    //@ ensures result <= 10
    clamp(x, 10)
}

// expect: proved
pub fn both(x: u32) -> u32 {
    //@ ensures result <= 10
    util::clamp(util::clamp(x, 50), 10)
}
