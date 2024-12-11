pub fn deref_swap<'a, T>(ref1: &'a mut T, ref2: &'a mut T) {
    core::mem::swap(ref1, ref2);
}

pub fn value_swap<T>(mut arg1: T, mut arg2: T) {
    core::mem::swap(&mut arg1, &mut arg2);
}

pub struct RefStore<'a, T> {
    ref0: Option<&'a mut T>,
    ref1: Option<&'a mut T>,
}

pub fn refstore_swap<T>(refstore: &mut RefStore<'_, T>) {
    let ref0 = refstore.ref0.as_mut().unwrap();
    let ref1 = refstore.ref1.as_mut().unwrap();
    core::mem::swap(ref0, ref1);
}
