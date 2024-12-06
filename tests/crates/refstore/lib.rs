use std::pin::Pin;

pub struct RefStore<'a, T> {
    ref0: Option<&'a mut T>,
    ref1: Option<&'a mut T>,
}

pub fn store_p0<'a, T>(x: &'a mut T) -> RefStore<'a, T> {
    RefStore {
        ref0: Some(x),
        ref1: None,
    }
}

pub fn store_p1<'a, T>(x: &'a mut T) -> RefStore<'a, T> {
    RefStore {
        ref0: None,
        ref1: Some(x),
    }
}

pub fn pin_p0<'a, T>(refstore: &mut RefStore<'a, T>) -> Pin<&'a mut T> {
    let x = refstore.ref0.take().unwrap();
    unsafe { Pin::new_unchecked(x) }
}
