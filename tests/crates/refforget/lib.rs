use core::marker::PhantomPinned;
use core::mem::ManuallyDrop;
use core::pin::Pin;

pub struct Unmovable {
    _marker: PhantomPinned,
}

impl Unmovable {
    pub fn new() -> Self {
        Self {
            _marker: PhantomPinned,
        }
    }
}

impl Drop for Unmovable {
    fn drop(&mut self) {
        println!("Unmovable got dropped");
    }
}

pub struct PinCell<T> {
    value: T,
}

impl<T> PinCell<T> {
    pub fn new(value: T) -> Self {
        Self { value }
    }

    pub fn pin(&mut self) -> Pin<&mut T> {
        unsafe { Pin::new_unchecked(&mut self.value) }
    }
}

pub fn forget_on_creation() -> ManuallyDrop<Unmovable> {
    ManuallyDrop::new(Unmovable::new())
}
