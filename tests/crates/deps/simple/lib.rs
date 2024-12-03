use std::ops::Deref;

pub fn return_boxed_ref<R: Deref>(r: R) -> Box<R> {
    Box::new(r)
}
