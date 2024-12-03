use std::ops::Deref;

pub fn box_then_unbox<R: Deref>(r: R) -> R {
    *simple::return_boxed_ref(r)
}
