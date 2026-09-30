// Closures handed on as values run where telic cannot see the call: given to
// std methods that call them on each element, stored, or given to a thread.
// Each closure panics for some element or captured value.

fn pos(x: i64) -> i64 {
    //@ requires x > 0
    10 / x
}

fn sort_by_key_div(mut xs: Vec<i64>) -> i64 {
    //@ ensures result == 0
    xs.sort_by_key(|x| 10 / x);
    0
}

fn for_each_div(xs: Vec<i64>) -> i64 {
    //@ ensures result == 0
    let mut t = 0;
    xs.iter().for_each(|x| {
        t += 10 / x;
    });
    0
}

fn stored(n: i64) -> i64 {
    //@ ensures result == 0
    let g = move || pos(n);
    let _ = g;
    0
}

fn spawned(n: i64) -> i64 {
    //@ ensures result == 0
    let _ = std::thread::spawn(move || pos(n));
    0
}
