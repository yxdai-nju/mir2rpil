pub trait MyTrait {
    fn trait_method_returning_self(self) -> Self;
}

pub struct MyStruct {}

impl MyTrait for MyStruct {
    fn trait_method_returning_self(self) -> Self {
        self
    }
}

pub fn process_impl_mytrait<T: MyTrait>(arg1: T) -> T {
    arg1.trait_method_returning_self()
}
