// Verdict corpus for the Rust frontend: `// expect: <verdict>` above each
// function pins what telic must report. The file is valid Rust (checked by
// tests/test_rust.py with rustc when it is installed).

use std::collections::HashMap;

// expect: proved
pub fn negative_float_remainder() -> f64 {
    //@ ensures result == -1.5
    -5.5_f64 % 2.0_f64
}

// expect: proved
pub fn nonnegative_f32_cast(x: i32) -> f32 {
    //@ requires x >= 0
    //@ ensures result >= 0.0
    x as f32
}

// expect: proved
pub fn add_small(a: u32, b: u32) -> u32 {
    //@ requires a <= 1000 && b <= 1000
    //@ ensures result == a + b
    a + b
}

// expect: refuted
pub fn add_any(a: u8, b: u8) -> u8 {
    a + b
}

// expect: refuted
pub fn last_index(xs: &[i32]) -> usize {
    xs.len() - 1
}

// expect: proved
pub fn last_index_checked(xs: &[i32]) -> usize {
    //@ requires !xs.is_empty()
    xs.len() - 1
}

// expect: proved
pub fn saturating(a: u32, b: u32) -> u32 {
    //@ ensures result <= a
    a.saturating_sub(b)
}

// expect: proved
pub fn checked(a: u32, b: u32) -> Option<u32> {
    //@ ensures result.is_none() || result.unwrap() == a + b
    a.checked_add(b)
}

// expect: refuted
pub fn mean(xs: &[u64]) -> u64 {
    let mut total: u64 = 0;
    for x in xs.iter() {
        total = total.saturating_add(*x);
    }
    total / xs.len() as u64
}

// expect: proved
pub fn sum_to(n: u32) -> u64 {
    //@ requires n <= 1000
    //@ ensures result == (n as u64) * (n as u64 + 1) / 2
    let mut s: u64 = 0;
    let mut i: u32 = 0;
    //@ invariant i <= n
    //@ invariant s == (i as u64) * (i as u64 + 1) / 2
    while i < n {
        i += 1;
        s += i as u64;
    }
    s
}

// expect: proved
pub fn max_of(xs: &Vec<i32>) -> i32 {
    //@ requires xs.len() > 0
    //@ ensures xs.iter().all(|x| x <= result)
    //@ ensures xs.iter().any(|x| x == result)
    let mut m = xs[0];
    //@ invariant (0..i).all(|k| xs[k] <= m)
    //@ invariant (0..i).any(|k| xs[k] == m)
    for i in 1..xs.len() {
        if xs[i] > m {
            m = xs[i];
        }
    }
    m
}

// expect: refuted
pub fn first(xs: &[String]) -> String {
    xs[0].clone()
}

// expect: proved
pub fn find(xs: &[i32], target: i32) -> Option<usize> {
    //@ ensures result.is_none() || xs[result.unwrap()] == target
    for (i, x) in xs.iter().enumerate() {
        if *x == target {
            return Some(i);
        }
    }
    None
}

// expect: refuted
pub fn unwrap_first(xs: &[i32]) -> i32 {
    *xs.first().unwrap()
}

// expect: proved
pub fn unwrap_or_default(xs: &[i32]) -> i32 {
    match xs.first() {
        Some(v) => *v,
        None => 0,
    }
}

// expect: proved
pub fn count_positive(xs: &[i64]) -> usize {
    //@ ensures result <= xs.len()
    xs.iter().filter(|x| **x > 0).count()
}

// expect: proved
pub fn doubled(xs: &[i32]) -> Vec<i64> {
    //@ ensures result.len() == xs.len()
    xs.iter().map(|x| (*x as i64) * 2).collect()
}

// expect: proved
pub fn push_n(n: usize) -> Vec<u8> {
    //@ requires n <= 100
    //@ ensures result.len() == n
    let mut v = Vec::new();
    //@ invariant v.len() == i
    for i in 0..n {
        v.push(0u8);
    }
    v
}

// expect: proved
pub fn filled(n: usize) -> usize {
    //@ requires n <= 100
    //@ ensures result == n
    let v = vec![7u32; n];
    v.len()
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Tier {
    Free,
    Pro,
    Team,
}

// expect: proved
pub fn seats(t: Tier) -> u32 {
    //@ ensures result >= 1
    match t {
        Tier::Free => 1,
        Tier::Pro => 1,
        Tier::Team => 10,
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Point {
    pub x: i32,
    pub y: i32,
}

// expect: refuted
pub fn manhattan(p: Point, q: Point) -> i32 {
    (p.x - q.x).abs() + (p.y - q.y).abs()
}

// expect: proved
pub fn shift(p: Point) -> Point {
    //@ requires p.x < 1000
    //@ ensures result.x == p.x + 1 && result.y == p.y
    Point { x: p.x + 1, ..p }
}

pub struct Account {
    pub balance: u64,
    pub history: Vec<i64>,
}

impl Account {
    // expect: proved
    pub fn new() -> Account {
        //@ ensures result.balance == 0
        Account { balance: 0, history: Vec::new() }
    }

    // expect: proved
    pub fn deposit(&mut self, amount: u64) {
        //@ requires amount <= 1_000_000 && self.balance <= 1_000_000_000
        //@ ensures self.balance == old(self.balance) + amount
        self.balance += amount;
        self.history.push(amount as i64);
    }

    // expect: refuted
    pub fn withdraw(&mut self, amount: u64) {
        self.balance -= amount;
    }

    // expect: proved
    pub fn try_withdraw(&mut self, amount: u64) -> bool {
        //@ ensures result == (old(self.balance) >= amount)
        if self.balance >= amount {
            self.balance -= amount;
            true
        } else {
            false
        }
    }
}

// expect: proved
pub fn tally(words: &[String]) -> HashMap<String, u32> {
    let mut m: HashMap<String, u32> = HashMap::new();
    for w in words.iter() {
        let c = *m.get(w).unwrap_or(&0);
        if c < 1000 {
            m.insert(w.clone(), c + 1);
        }
    }
    m
}

// expect: refuted
pub fn lookup(m: &HashMap<String, u32>, k: String) -> u32 {
    m[&k]
}

// expect: proved
pub fn parse_pair(s: &str) -> Option<u32> {
    let n: u32 = s.len() as u32;
    let half = n.checked_div(2)?;
    Some(half)
}

// expect: refuted
pub fn narrow(x: i64) -> u8 {
    //@ ensures result as i64 == x
    x as u8
}

// expect: proved
pub fn widen(x: u8) -> u64 {
    //@ ensures result == x as u64
    x as u64
}

// expect: refuted
pub fn slice_mid(xs: &[i32], a: usize, b: usize) -> usize {
    xs[a..b].len()
}

// expect: proved
pub fn countdown(n: u32) -> u32 {
    //@ ensures result == 0
    let mut k = n;
    while k > 0 {
        k -= 1;
    }
    k
}

// expect: refuted
pub fn must_be_even(x: u32) -> u32 {
    assert!(x % 2 == 0);
    x / 2
}

// expect: proved
pub fn guarded_even(x: u32) -> u32 {
    //@ requires x % 2 == 0
    assert!(x % 2 == 0);
    x / 2
}

// expect: refuted
pub fn unreachable_arm(x: u32) -> u32 {
    if x > 10 {
        unreachable!("too big");
    }
    x
}

#[derive(Clone, Copy, PartialEq, Debug)]
pub enum Phase {
    Open,
    Won,
    Lost,
}

// A game, once won, stays won: whatever sequence of moves follows.
//@ lifecycle phase: Phase::Open -> Phase::Won, Phase::Open -> Phase::Lost
//@ lifecycle once self.phase == Phase::Won
#[derive(Debug)]
pub struct Game {
    //@ lifecycle monotonic self.moves
    pub phase: Phase,
    pub moves: u32,
    pub mines: u32,
}

impl Game {
    // expect: proved
    pub fn reveal(&mut self, mine: bool) {
        if self.phase == Phase::Open && self.moves < 1000 {
            self.moves += 1;
            if mine {
                self.phase = Phase::Lost;
            }
        }
    }

    // expect: proved
    pub fn check_win(&mut self) {
        if self.phase == Phase::Open && self.moves >= self.mines {
            self.phase = Phase::Won;
        }
    }

    // expect: refuted
    pub fn check_win_unguarded(&mut self) {
        // stipulate's demo bug: marks a lost game won
        if self.moves >= self.mines {
            self.phase = Phase::Won;
        }
    }
}

// expect: refuted
pub fn restart_game(g: &mut Game) {
    // overwrites the caller's game, won or not
    *g = Game { phase: Phase::Open, moves: 0, mines: g.mines };
}

// -- enums with data, and match on them ------------------------------------

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Shape {
    Circle(u32),
    Rect { w: u32, h: u32 },
    Empty,
}

// expect: proved
pub fn shape_area(s: Shape) -> u64 {
    //@ ensures implies(matches!(s, Shape::Empty), result == 0)
    match s {
        Shape::Circle(r) => (r as u64) * (r as u64),
        Shape::Rect { w, h } => (w as u64) * (h as u64),
        Shape::Empty => 0,
    }
}

// expect: refuted
pub fn perimeter(s: Shape) -> u32 {
    match s {
        Shape::Circle(r) => 6 * r,
        Shape::Rect { w, h } => 2 * (w + h),
        Shape::Empty => 0,
    }
}

// expect: proved
pub fn square(side: u32) -> Shape {
    //@ ensures result == Shape::Rect { w: side, h: side }
    Shape::Rect { w: side, h: side }
}

// expect: proved
pub fn is_round(s: Shape) -> bool {
    //@ ensures result == matches!(s, Shape::Circle(_))
    if let Shape::Circle(_) = s {
        true
    } else {
        false
    }
}

// expect: proved
pub fn small_radius(s: Shape) -> u32 {
    //@ ensures result <= 100
    match s {
        Shape::Circle(r) if r <= 100 => r,
        _ => 0,
    }
}

// expect: refuted
pub fn grow(s: Shape) -> Shape {
    match s {
        Shape::Circle(r) => Shape::Circle(r + 1),
        other => other,
    }
}

impl Shape {
    // expect: proved
    pub fn is_empty(&self) -> bool {
        //@ ensures result == (*self == Shape::Empty)
        matches!(self, Shape::Empty)
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Cmd {
    Move { dx: i8, dy: i8 },
    Wait(u8),
    Stop,
}

impl Cmd {
    // expect: proved
    pub fn cost(&self) -> u32 {
        //@ ensures result <= 255
        match *self {
            Cmd::Move { dx, dy } => (dx.unsigned_abs() as u32).max(dy.unsigned_abs() as u32),
            Cmd::Wait(n) => n as u32,
            Self::Stop => 0,
        }
    }
}

// expect: refuted
pub fn step(c: Cmd, x: i8) -> i8 {
    match c {
        Cmd::Move { dx, .. } => x + dx,
        _ => x,
    }
}

// -- tuple structs ---------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Meters(pub u32);

// expect: proved
pub fn add_meters(a: Meters, b: Meters) -> Meters {
    //@ requires a.0 <= 1000 && b.0 <= 1000
    //@ ensures result.0 == a.0 + b.0
    Meters(a.0 + b.0)
}

// expect: refuted
pub fn double_meters(a: Meters) -> Meters {
    let Meters(x) = a;
    Meters(x * 2)
}

// expect: proved
pub fn meters_eq(a: Meters) -> bool {
    //@ ensures result
    a == Meters(a.0)
}

// -- Result and '?' ----------------------------------------------------------

#[derive(Debug, PartialEq)]
pub enum DigitError {
    Empty,
    TooBig(u32),
}

// expect: proved
pub fn parse_digit(s: &str, v: u32) -> Result<u32, DigitError> {
    //@ ensures implies(result.is_ok(), result.unwrap() < 10)
    if s.is_empty() {
        return Err(DigitError::Empty);
    }
    if v >= 10 {
        return Err(DigitError::TooBig(v));
    }
    Ok(v)
}

// expect: proved
pub fn sum_digits(a: &str, x: u32, b: &str, y: u32) -> Result<u32, DigitError> {
    //@ ensures implies(result.is_ok(), result.unwrap() < 20)
    let p = parse_digit(a, x)?;
    let q = parse_digit(b, y)?;
    Ok(p + q)
}

// expect: refuted
pub fn must_parse(s: &str, v: u32) -> u32 {
    parse_digit(s, v).unwrap()
}

// expect: proved
pub fn digit_or_zero(s: &str, v: u32) -> u32 {
    //@ ensures result < 10
    match parse_digit(s, v) {
        Ok(d) => d,
        Err(DigitError::TooBig(_)) => 0,
        Err(DigitError::Empty) => 0,
    }
}

// expect: proved
pub fn required(o: Option<u32>) -> Result<u32, u8> {
    //@ ensures implies(o.is_none(), result.is_err())
    let v = o.ok_or(7u8)?;
    Ok(v)
}

// expect: refuted
pub fn plus_one(r: Result<u8, String>) -> Result<u8, String> {
    let v = r?;
    Ok(v + 1)
}

#[derive(Debug)]
pub enum AppError {
    Code(u8),
    Io,
}

impl From<u8> for AppError {
    // expect: proved
    fn from(e: u8) -> AppError {
        AppError::Code(e)
    }
}

pub type AppResult<T> = Result<T, AppError>;

// expect: proved
pub fn below_100(x: u32) -> Result<u32, u8> {
    //@ ensures implies(result.is_ok(), result.unwrap() < 100)
    if x < 100 {
        Ok(x)
    } else {
        Err(1)
    }
}

// expect: proved
pub fn doubled_below_100(x: u32) -> AppResult<u32> {
    //@ ensures implies(result.is_ok(), result.unwrap() < 200)
    let a = below_100(x)?;
    Ok(a * 2)
}

// -- traits and generics -----------------------------------------------------

pub trait Scored {
    //@ ensures result <= 10
    fn score(&self) -> u32;

    //@ ensures result >= 1
    fn weight(&self) -> u32 {
        1
    }
}

pub struct Player {
    pub points: u32,
}

impl Scored for Player {
    // expect: proved
    fn score(&self) -> u32 {
        if self.points > 10 {
            10
        } else {
            self.points
        }
    }
}

pub struct Cheater {
    pub points: u32,
}

impl Scored for Cheater {
    // expect: refuted
    fn score(&self) -> u32 {
        self.points
    }

    // expect: proved
    fn weight(&self) -> u32 {
        2
    }
}

// expect: proved
pub fn rank<T: Scored>(x: &T) -> u32 {
    //@ ensures result >= 1 && result <= 20
    x.score() + x.weight().min(10)
}

// expect: proved
pub fn rank_dyn(x: &dyn Scored) -> u32 {
    //@ ensures result <= 10
    x.score()
}

// expect: proved
pub fn player_weight(p: &Player) -> u32 {
    //@ ensures result == 1
    p.weight()
}

// expect: proved
pub fn pick<T: Copy>(c: bool, a: T, b: T) -> T {
    //@ ensures implies(c, result == a)
    if c {
        a
    } else {
        b
    }
}

// expect: proved
pub fn pick_first(x: u32) -> u32 {
    //@ ensures result == x
    pick(true, x, 7)
}

// -- modules -----------------------------------------------------------------

pub mod units {
    // expect: proved
    pub fn clamp(x: u32, hi: u32) -> u32 {
        //@ ensures result <= hi
        if x > hi {
            hi
        } else {
            x
        }
    }
}

// expect: proved
pub fn clamped(x: u32) -> u32 {
    //@ ensures result <= 10
    units::clamp(x, 10)
}
