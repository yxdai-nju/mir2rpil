use std::pin::Pin;

pub struct RefStore<'a, T, U> {
    ref0: Option<&'a mut T>,
    ref1: Option<&'a mut U>,
}

pub union RefStoreUnion<'a, T, U> {
    ref0: &'a mut T,
    ref1: &'a mut U,
}

pub fn store_p0<'a, T>(x: &'a mut T) -> RefStore<'a, T, ()> {
    RefStore {
        ref0: Some(x),
        ref1: None,
    }
}

pub fn store_p1<'a, U>(x: &'a mut U) -> RefStore<'a, (), U> {
    RefStore {
        ref0: None,
        ref1: Some(x),
    }
}

pub fn store_union_p0<'a, T>(x: &'a mut T) -> RefStoreUnion<'a, T, ()> {
    RefStoreUnion { ref0: x }
}

pub fn store_union_p1<'a, U>(x: &'a mut U) -> RefStoreUnion<'a, (), U> {
    RefStoreUnion { ref1: x }
}

pub fn pin_p0<'a, T>(refstore: &mut RefStore<'a, T, ()>) -> Pin<&'a mut T> {
    let x = refstore.ref0.take().unwrap();
    unsafe { Pin::new_unchecked(x) }
}

pub fn pin_union_p0<'a, T>(refstore_union: &mut RefStoreUnion<'a, T, T>) -> Pin<&'a mut T> {
    unsafe {
        let x = &mut *(refstore_union.ref1 as *mut T);
        Pin::new_unchecked(x)
    }
}
