// A mutable reference to an unchecked value: changing it forgets what a
// trusted predicate said about it.
use serde_json::Value;

//@ trusted
//@ ensures result >= 0
fn size(v: &Value) -> i64 {
    v.as_object().map_or(0, |o| o.len() as i64)
}

//@ requires size(v) > 0
//@ ensures size(v) > 0
fn through_callee(v: &mut Value) {
    clear(v);
}

fn clear(v: &mut Value) {
    v.as_object_mut().unwrap().clear();
}

//@ requires size(v) > 0
//@ ensures size(v) > 0
fn take(v: &mut Value) {
    v.take();
}
