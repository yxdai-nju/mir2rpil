use rand::{thread_rng, Rng};

pub fn my_random() -> u32 {
    let mut rng = thread_rng();
    rng.gen()
}
