pub fn assign_same<'a, T>(r1: &mut &'a T, r2: &mut &'a T, r3: &mut &'a T) {
    *r2 = *r1;
    *r3 = *r2;
}

pub fn assign_different<'a, T>(r1: &mut &'a T, r2: &mut &'a T, r3: &mut &'a T) {
    *r3 = *r2;
    *r2 = *r1;
}

/* Unsupported, will trigger an intentional assertion error */

// pub fn swap_two<'a, T>(r1: &mut &'a T, r2: &mut &'a T) {
//     let tmp = *r2;
//     *r2 = *r1;
//     *r1 = tmp;
// }

/* Unsupported, will trigger an intentional assertion error */

// struct SelfRef {
//     r: *mut SelfRef,
// }

// impl SelfRef {
//     pub fn init(&mut self) {
//         self.r = self as *mut SelfRef;
//     }
// }
