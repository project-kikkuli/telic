// Rust exploits: every contract below is false for the real program.

pub fn block_shadow() -> i32 {
    //@ ensures result == 2
    let x = 1;
    {
        let x = 2;
        let _ = x;
    }
    x
}

pub fn same_scope_shadow(s: u32) -> u32 {
    //@ ensures result == s
    let s = s / 2;
    s
}

#[derive(Clone, Copy)]
pub struct Counter {
    pub n: u32,
}

impl Counter {
    pub fn bump(&mut self) {
        //@ requires self.n < 100
        self.n += 1;
    }
}

pub fn copies_not_aliases(c: Counter) -> u32 {
    //@ requires c.n < 100
    //@ ensures result == c.n + 1
    let mut d = c;
    d.bump();
    c.n
}

pub fn set_through(x: &mut u32) {
    *x = 7;
}

pub fn scalar_mut_arg() -> u32 {
    //@ ensures result == 0
    let mut n = 0;
    set_through(&mut n);
    n
}

pub fn closure_mutation(v: &Vec<u32>) -> u32 {
    //@ ensures result == 0
    let mut count = 0;
    v.iter().for_each(|_| count += 1);
    count
}

pub fn default_i32(big: bool) -> i64 {
    //@ requires big
    //@ ensures result == 4000000000
    let x = if big { 2000000000 } else { 0 };
    let y = x + x;
    y as i64
}

pub fn truncating_div(a: i32) -> i32 {
    //@ requires a == -7
    //@ ensures result == -4
    a / 2
}

pub fn remainder_sign(a: i32) -> i32 {
    //@ requires a == -7
    //@ ensures result == 2
    a % 3
}

pub fn wrapping_cast(x: i32) -> u8 {
    //@ requires x == 300
    //@ ensures result as i32 == 300
    x as u8
}

pub fn early_return(v: Option<u32>) -> Option<u32> {
    //@ ensures result.is_some()
    let x = v?;
    Some(x)
}

pub fn alias_mut(v: &mut Vec<u32>) -> usize {
    //@ ensures result == old(v.len())
    let r = &mut *v;
    r.push(1);
    v.len()
}

pub fn index_from_end(v: &[u32], i: usize) -> u32 {
    //@ requires i < v.len()
    v[v.len() - i]
}
