use core::pin::Pin;

pub fn swap_box_content<T>(arg1: &mut Box<T>, arg2: &mut Box<T>) {
    let ref1 = arg1.as_mut();
    let ref2 = arg2.as_mut();
    core::mem::swap(ref1, ref2);
}

pub fn pin_box_content<T>(arg1: &mut Box<T>) -> Pin<&mut T> {
    unsafe { Pin::new_unchecked(arg1.as_mut()) }
}

pub fn box_forget<T>(arg1: Box<T>) -> *mut T {
    Box::leak(arg1)
}
