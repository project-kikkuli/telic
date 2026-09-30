// Rust exploits for enums, patterns, Result, traits, generics and modules:
// every contract below is false for the real program.

#[derive(Clone, Copy, Debug)]
pub struct Loose {
    pub x: u32,
}

impl PartialEq for Loose {
    fn eq(&self, _other: &Loose) -> bool {
        true
    }
}

pub fn manual_eq(a: Loose, b: Loose) -> bool {
    //@ ensures result == (a.x == b.x)
    a == b
}

#[derive(Clone, Debug, PartialEq)]
pub struct Boxed {
    pub v: Vec<u32>,
}

pub fn distinct_objects_are_equal() -> bool {
    //@ ensures !result
    let a = Boxed { v: Vec::new() };
    let b = Boxed { v: Vec::new() };
    a == b
}

pub fn generic_reflexive<T: PartialEq>(a: T) -> bool {
    //@ ensures result
    a == a
}

pub trait Tr {
    fn w(&self) -> u32 {
        1
    }
}

pub struct Five;

impl Tr for Five {
    fn w(&self) -> u32 {
        5
    }
}

pub fn through_default<T: Tr>(x: &T) -> u32 {
    //@ ensures result == 1
    x.w()
}

pub fn option_payload_kind(o: Option<u8>) -> u8 {
    match o {
        Some(v) => v + 200,
        None => 0,
    }
}

pub enum Small {
    A(u8),
    B,
}

pub fn enum_payload_kind(e: Small) -> u8 {
    match e {
        Small::A(v) => v + 200,
        Small::B => 0,
    }
}

pub fn unsigned_abs_range(x: i8) -> u8 {
    //@ ensures result <= 127
    x.unsigned_abs()
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Ctr {
    N(u32),
    Off,
}

impl Ctr {
    pub fn inc(&mut self) {
        if let Ctr::N(n) = self {
            *n += 1;
        }
    }

    pub fn reset(&mut self) {
        *self = Ctr::N(7);
    }
}

pub fn after_reset() -> u32 {
    //@ ensures result == 0
    let mut c = Ctr::N(0);
    c.reset();
    match c {
        Ctr::N(n) => n,
        Ctr::Off => 0,
    }
}

#[derive(Clone, Debug)]
pub struct In {
    pub v: u32,
}

#[derive(Clone, Debug)]
pub struct Out {
    pub i: In,
}

pub fn clone_is_deep(o: Out) -> u32 {
    //@ ensures result == 5
    let mut p = o.clone();
    p.i.v = 5;
    o.i.v
}

pub fn spec_unwrap_of_err() -> Result<u32, u8> {
    //@ ensures result.unwrap() == 0
    Err(1)
}

pub struct Pair(pub u32, pub u32);

pub fn tuple_fields_in_order(p: Pair) -> u32 {
    //@ ensures result == p.0
    p.1
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Sh {
    C(u32),
    E,
}

pub fn rebuilt_is_equal(a: Sh) -> bool {
    //@ ensures !result
    let b = match a {
        Sh::C(r) => Sh::C(r),
        Sh::E => Sh::E,
    };
    a == b
}

mod one {
    pub fn f() -> u32 {
        //@ ensures result == 1
        1
    }
}

mod two {
    pub fn f() -> u32 {
        //@ ensures result == 2
        2
    }
}

pub fn module_paths() -> u32 {
    //@ ensures result == 2
    one::f()
}

pub fn result_payload_kind(r: Result<u8, u8>) -> Result<u8, u8> {
    let v = r?;
    Ok(v + 200)
}

pub fn err_payload_kind(r: Result<u8, u8>) -> u8 {
    match r {
        Ok(_) => 0,
        Err(e) => e + 200,
    }
}

#[derive(Debug)]
pub enum E2 {
    A,
    B,
}

impl From<u8> for E2 {
    fn from(_x: u8) -> E2 {
        E2::B
    }
}

pub fn fails() -> Result<u32, u8> {
    Err(3)
}

pub fn converted() -> bool {
    //@ ensures result
    match wrap() {
        Err(E2::A) => true,
        _ => false,
    }
}

pub fn wrap() -> Result<u32, E2> {
    let v = fails()?;
    Ok(v)
}

pub fn guard_uses_binding(e: Small) -> u8 {
    //@ ensures result == 0
    match e {
        Small::A(v) if v > 3 => 0,
        Small::A(v) => v,
        Small::B => 0,
    }
}
