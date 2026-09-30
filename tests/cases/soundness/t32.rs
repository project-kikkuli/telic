// Rust exploits from a soundness review of enums, Result, traits and std
// calls: every contract below is false for the real program.

#[derive(Clone, Copy, PartialEq, Debug)]
pub enum S {
    C(u32),
    E,
}

#[derive(Clone, Copy)]
pub struct P {
    pub x: u32,
}

pub fn pow12(x: u64) -> u64 {
    //@ requires x == 2
    //@ ensures result == 2
    x.pow(12)
}

pub fn mrep() -> u32 {
    //@ ensures result == 1
    let mut e = S::C(1);
    let _old = std::mem::replace(&mut e, S::C(9));
    match e {
        S::C(r) => r,
        S::E => 0,
    }
}
pub fn mswap() -> u32 {
    //@ ensures result == 1
    let mut a = S::C(1);
    let mut b = S::C(9);
    std::mem::swap(&mut a, &mut b);
    match a {
        S::C(r) => r,
        S::E => 0,
    }
}
pub fn opt_enum_take() -> bool {
    //@ ensures result
    let mut o = Some(S::C(1));
    let _t = o.take();
    o.is_some()
}

pub fn scalar_rep() -> u32 {
    //@ ensures result == 0
    let mut n = 0u32;
    let _ = std::mem::replace(&mut n, 5);
    n
}
pub fn set(e: &mut S) {
    *e = S::C(9);
}
pub fn user_mut() -> u32 {
    //@ ensures result == 1
    let mut e = S::C(1);
    set(&mut e);
    match e {
        S::C(r) => r,
        S::E => 0,
    }
}
pub fn opt_take() -> bool {
    //@ ensures result
    let mut o = Some(1u32);
    let _ = std::mem::take(&mut o);
    o.is_some()
}
pub fn field_rep() -> u32 {
    //@ ensures result == 1
    let mut p = P { x: 1 };
    let _ = std::mem::replace(&mut p.x, 7);
    p.x
}
pub fn res_rep() -> bool {
    //@ ensures result
    let mut r: Result<u32, u8> = Ok(1);
    let _ = std::mem::replace(&mut r, Err(2));
    r.is_ok()
}

pub fn goi() -> bool {
    //@ ensures result
    let mut o: Option<u32> = None;
    o.get_or_insert(5);
    o.is_none()
}
pub fn ins() -> bool {
    //@ ensures result
    let mut o: Option<u32> = None;
    o.insert(5);
    o.is_none()
}
pub fn vrem(v: &mut Vec<u32>, i: usize) -> u32 {
    v.remove(i)
}
pub fn vins(v: &mut Vec<u32>, i: usize) {
    v.insert(i, 1)
}
pub fn vswap(v: &mut Vec<u32>, i: usize) -> u32 {
    v.swap_remove(i)
}

pub fn gq() -> u32 {
    //@ ensures result == 1
    let v = vec![1u32];
    let o = Some(10u32);
    match o {
        Some(x) if v.iter().all(|x| *x > 5) => 1,
        _ => 0,
    }
}
pub fn gq2() -> u32 {
    //@ ensures result == 1
    let v = vec![1u32];
    let o = Some(10u32);
    match o {
        Some(x) if v.iter().any(|x| *x > 5) => 1,
        _ => 0,
    }
}

pub fn re(x: i32, y: i32) -> i32 {
    //@ ensures true
    x.rem_euclid(y)
}
pub fn pw(n: u32) -> u32 {
    //@ ensures result >= 1
    2u32.pow(n)
}

pub fn powhex(x: u32) -> u32 {
    //@ requires x == 2
    //@ ensures result == 1
    x.pow(0x10)
}

pub fn fill() -> u32 {
    //@ ensures result == 1
    let mut v = vec![1u32];
    v.fill(5);
    v[0]
}
pub fn swrem() -> usize {
    //@ ensures result == 2
    let mut v = vec![1u32, 2];
    v.swap_remove(0);
    v.len()
}
pub fn rot() -> u32 {
    //@ ensures result == 1
    let mut v = vec![1u32, 2];
    v.rotate_left(1);
    v[0]
}
pub fn app() -> usize {
    //@ ensures result == 1
    let mut v = vec![1u32];
    let mut w = vec![2u32];
    v.append(&mut w);
    v.len()
}
pub fn app2() -> usize {
    //@ ensures result == 1
    let mut v = vec![1u32];
    let mut w = vec![2u32];
    v.append(&mut w);
    w.len()
}
pub fn splitoff() -> usize {
    //@ ensures result == 2
    let mut v = vec![1u32, 2];
    let _t = v.split_off(1);
    v.len()
}
pub fn getmut() -> u32 {
    //@ ensures result == 1
    let mut v = vec![1u32];
    if let Some(x) = v.get_mut(0) {
        *x = 9;
    }
    v[0]
}
pub fn itermut() -> u32 {
    //@ ensures result == 1
    let mut v = vec![1u32];
    for x in v.iter_mut() {
        *x = 9;
    }
    v[0]
}
pub fn cap(v: Vec<()>) -> usize {
    //@ ensures result <= 9223372036854775807
    v.capacity()
}
pub fn zlen(v: Vec<()>) -> usize {
    //@ ensures result <= 9223372036854775807
    v.len()
}

use std::cell::Cell;
pub struct W {
    pub c: Cell<u32>,
}
impl AsRef<[u8]> for W {
    fn as_ref(&self) -> &[u8] {
        let n = self.c.get();
        self.c.set(n + 1);
        if n % 2 == 0 {
            b"a"
        } else {
            b"ab"
        }
    }
}
pub fn twice<T: AsRef<[u8]>>(x: &T) -> bool {
    //@ ensures result
    x.as_ref().len() == x.as_ref().len()
}

pub fn rem_min(x: i32, y: i32) -> i32 {
    //@ requires y != 0
    x % y
}

pub fn rem_min_i8(x: i8) -> i8 {
    x % -1
}

pub fn div_min_i64(x: i64, y: i64) -> i64 {
    //@ requires y != 0
    x / y
}
