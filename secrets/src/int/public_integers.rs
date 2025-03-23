use crate::traits::*;
pub type I8 = i8;
pub type U8 = u8;
pub type I16 = i16;
pub type U16 = u16;
pub type I32 = i32;
pub type U32 = u32;
pub type I64 = i64;
pub type U64 = u64;
pub type I128 = i128;
pub type U128 = u128;

// Construct a secret integer
pub const fn secret<T>(x: T) -> T {
    x
}

impl<T> Classify for T {
    type Classified = T;
    fn classify(self) -> Self {
        self
    }
}

impl<T> Declassify for T {
    type Declassified = T;
    fn declassify(self) -> T {
        self
    }
}

impl<'a, T> ClassifyRef for &'a T {
    type ClassifiedRef = &'a T;
    fn classify_ref(self) -> &'a T {
        self
    }
}

impl<'a, T> DeclassifyRef for &'a T {
    type DeclassifiedRef = &'a T;
    fn declassify_ref(self) -> &'a T {
        self
    }
}

pub fn classify_mut_slice<T>(x: T) -> T{
    x
}