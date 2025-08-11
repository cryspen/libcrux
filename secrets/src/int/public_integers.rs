/// This crate defines classification and declassification over public integers
/// All functions and types here are transparent (identities) and have no performance impact
use crate::traits::*;
pub type I8 = i8;
pub type U8 = u8;
pub type I16 = i16;
pub type U16 = u16;
pub type I32 = i32;
pub type U32 = u32;
pub type I64 = i64;
pub type U64 = u64;
#[cfg(not(eurydice))]
pub type I128 = i128;
#[cfg(not(eurydice))]
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

// Immutable references can be classified (identity)
impl<'a, T: Scalar> ClassifyRef for &'a T {
    type ClassifiedRef = &'a T;
    #[inline(always)]
    fn classify_ref(self) -> &'a T {
        self
    }
}

// Immutable references can be declassified (identity)
impl<'a, T: Scalar> DeclassifyRef for &'a T {
    type DeclassifiedRef = &'a T;
    #[inline(always)]
    fn declassify_ref(self) -> &'a T {
        self
    }
}

// Mutable references to scalars can be classified (identity)
impl<'a, T: Scalar> ClassifyRefMut for &'a mut T {
    type ClassifiedRefMut = &'a mut T;
    #[inline(always)]
    fn classify_ref_mut(self) -> &'a mut T {
        self
    }
}

// Mutable references to scalars can be declassified (identity)
impl<'a, T: Scalar> DeclassifyRefMut for &'a mut T {
    type DeclassifiedRefMut = &'a mut T;
    #[inline(always)]
    fn declassify_ref_mut(self) -> &'a mut T {
        self
    }
}

// Immutable references to slices can be classified (identity)
impl<'a, T: Scalar> ClassifyRef for &'a [T] {
    type ClassifiedRef = &'a [T];
    #[inline(always)]
    fn classify_ref(self) -> &'a [T] {
        self
    }
}

// Immutable references to slices can be declassified (identity)
impl<'a, T: Scalar> DeclassifyRef for &'a [T] {
    type DeclassifiedRef = &'a [T];
    #[inline(always)]
    fn declassify_ref(self) -> &'a [T] {
        self
    }
}

// Mutable references to scalars can be classified (identity)
impl<'a, T: Scalar> ClassifyRefMut for &'a mut [T] {
    type ClassifiedRefMut = &'a mut [T];
    #[inline(always)]
    fn classify_ref_mut(self) -> &'a mut [T] {
        self
    }
}

// Mutable references to scalars can be declassified (identity)
impl<'a, T: Scalar> DeclassifyRefMut for &'a mut [T] {
    type DeclassifiedRefMut = &'a mut [T];
    #[inline(always)]
    fn declassify_ref_mut(self) -> &'a mut [T] {
        self
    }
}

// Immutable references to arrays can be classified (identity)
impl<'a, T: Scalar, const N: usize> ClassifyRef for &'a [T; N] {
    type ClassifiedRef = &'a [T; N];
    #[inline(always)]
    fn classify_ref(self) -> &'a [T; N] {
        self
    }
}

// Immutable references to arrays can be classified (identity)
impl<'a, T: Scalar, const N: usize> DeclassifyRef for &'a [T; N] {
    type DeclassifiedRef = &'a [T; N];
    #[inline(always)]
    fn declassify_ref(self) -> &'a [T; N] {
        self
    }
}

// Mutable references to arrays can be classified (identity)
impl<'a, T: Scalar, const N: usize> ClassifyRefMut for &'a mut [T; N] {
    type ClassifiedRefMut = &'a mut [T; N];
    #[inline(always)]
    fn classify_ref_mut(self) -> &'a mut [T; N] {
        self
    }
}

// Mutable references to arrays can be declassified (identity)
impl<'a, T: Scalar, const N: usize> DeclassifyRefMut for &'a mut [T; N] {
    type DeclassifiedRefMut = &'a mut [T; N];
    #[inline(always)]
    fn declassify_ref_mut(self) -> &'a mut [T; N] {
        self
    }
}

/// Classify a mutable slice (identity)
/// We define a separate function for this because hax has limited support for &mut-returning functions
#[inline(always)]
pub fn classify_mut_slice<T>(x: T) -> T {
    x
}
