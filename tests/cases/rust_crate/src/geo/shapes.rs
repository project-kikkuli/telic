use super::super::util::clamp;

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Shape {
    Sq(u16),
    Dot,
}

// expect: proved
pub fn area(s: Shape) -> u32 {
    //@ ensures implies(s == Shape::Dot, result == 0)
    match s {
        Shape::Sq(n) => (n as u32) * (n as u32),
        Shape::Dot => 0,
    }
}

// expect: proved
pub fn small(s: Shape) -> u32 {
    //@ ensures result <= 5
    clamp(area(s), 5)
}

impl Shape {
    // expect: refuted
    fn perim(&self) -> u16 {
        match self {
            Shape::Sq(n) => 4 * n,
            Shape::Dot => 0,
        }
    }
}
