/// This crate defines classification and declassification over public integers
/// All functions and types here are transparent (identities) and have no performance impact
use crate::traits::*;
/// Public 8-bit signed integer type
pub type I8 = i8;
/// Public 8-bit unsigned integer type
pub type U8 = u8;
/// Public 16-bit signed integer type
pub type I16 = i16;
/// Public 16-bit unsigned integer type
pub type U16 = u16;
/// Public 32-bit signed integer type
pub type I32 = i32;
/// Public 32-bit unsigned integer type
pub type U32 = u32;
/// Public 64-bit signed integer type
pub type I64 = i64;
/// Public 64-bit unsigned integer type
pub type U64 = u64;
#[cfg(not(eurydice))]
/// Public 128-bit signed integer type
pub type I128 = i128;
#[cfg(not(eurydice))]
/// Public 128-bit unsigned integer type
pub type U128 = u128;

/// Construct a public integer (identity)
#[inline(always)]
pub const fn secret<T>(x: T) -> T {
    x
}

// Classify any type (identity)
impl<T> Classify for T {
    type Classified = T;
    #[inline(always)]
    fn classify(self) -> Self {
        self
    }
}

// Delassify any type (identity)
impl<T> Declassify for T {
    type Declassified = T;
    #[inline(always)]
    fn declassify(self) -> T {
        self
    }
}

// Classify any reference (identity)
impl<'a, T> ClassifyRef for &'a T {
    type ClassifiedRef = &'a T;
    #[inline(always)]
    fn classify_ref(self) -> &'a T {
        self
    }
}

// Delassify any reference (identity)
impl<'a, T> DeclassifyRef for &'a T {
    type DeclassifiedRef = &'a T;
    #[inline(always)]
    fn declassify_ref(self) -> &'a T {
        self
    }
}

/// Classify a mutable slice (identity)
/// We define a separate function for this because hax has limited support for &mut-returning functions
#[inline(always)]
pub fn classify_mut_slice<T>(x: T) -> T {
    x
}
/// Classify a mutable slice (identity)
/// We define a separate function for this because hax has limited support for &mut-returning functions
#[inline(always)]
pub fn declassify_mut_slice<T>(x: T) -> T {
    x
}
