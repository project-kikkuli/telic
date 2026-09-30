// Assigning a whole struct through '&mut' overwrites the caller's object.

//@ lifecycle monotonic self.count
#[derive(Clone, Debug)]
pub struct Tally {
    pub count: u32,
}

impl Tally {
    pub fn bump(&mut self) {
        if self.count < 1000 {
            self.count += 1;
        }
    }
}

pub fn overwrite(t: &mut Tally, other: &Tally) {
    *t = other.clone();
}

pub fn zero(t: &mut Tally) {
    *t = Tally { count: 0 };
}
