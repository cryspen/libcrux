/// This file defines functions for classifying and declassifying various types.
/// We give definitions for all conversions so that they can be tested
/// However, this file is only meant to be used when using feature "check-secret-independence"
/// That is, it should not be used when running the Rust code in production.
/// Otherwise, the crate defaults to public integers.
use crate::traits::*;

// A type for secret values
#[repr(transparent)]
pub struct Secret<T>(pub(crate) T);

// Secrets are clonable if the underlying type is
impl<T: Clone> Clone for Secret<T> {
    fn clone(&self) -> Self {
        Secret(self.0.clone())
    }
}

// Any type can be classified
impl<T> From<T> for Secret<T> {
    fn from(x: T) -> Secret<T> {
        Secret(x)
    }
}

// Secrets are copyable if the underlying type is
impl<T: Clone + Copy> Copy for Secret<T> {}

// Arrays of scalars can be classified
impl<T: Scalar, const N: usize> Classify for [T; N] {
    type Classified = [Secret<T>; N];
    fn classify(self) -> [Secret<T>; N] {
        self.map(|x| x.into())
    }
}

// Arrays of scalars can be declassified
impl<T: Scalar, const N: usize> Declassify for [Secret<T>; N] {
    type Declassified = [T; N];
    fn declassify(self) -> [T; N] {
        self.map(|x| x.0)
    }
}

// Matrices of scalars can be classified
impl<T: Scalar, const M: usize, const N: usize> Classify for [[T; N]; M] {
    type Classified = [[Secret<T>; N]; M];
    fn classify(self) -> [[Secret<T>; N]; M] {
        self.map(|x| x.map(|y| y.into()))
    }
}

// Matrices of scalars can be declassified
impl<T: Scalar, const N: usize, const M: usize> Declassify for [[Secret<T>; N]; M] {
    type Declassified = [[T; N]; M];
    fn declassify(self) -> [[T; N]; M] {
        self.map(|x| x.map(|y| y.0))
    }
}

// Mutable references to scalars can be classified
// Note: this is safe since the `Secret` type is `repr(transparent)`, so
//       the memory represnetation of the public and secret slices is the same
impl<'a, T: Scalar> ClassifyRefMut for &'a mut T {
    type ClassifiedRefMut = &'a mut Secret<T>;
    fn classify_ref_mut(self) -> &'a mut Secret<T> {
        unsafe { core::mem::transmute(self) }
    }
}

// Mutable references to scalars can be declassified
// Note: this is safe since the `Secret` type is `repr(transparent)`, so
//       the memory represnetation of the public and secret slices is the same
impl<'a, T: Scalar> DeclassifyRefMut for &'a mut Secret<T> {
    type DeclassifiedRefMut = &'a mut T;
    fn declassify_ref_mut(self) -> &'a mut T {
        unsafe { core::mem::transmute(self) }
    }
}

// Immutable references to slices can be classified
// Note: this is safe since the `Secret` type is `repr(transparent)`, so
//       the memory represnetation of the public and secret slices is the same
impl<'a, T: Scalar> ClassifyRef for &'a [T] {
    type ClassifiedRef = &'a [Secret<T>];
    fn classify_ref(self) -> &'a [Secret<T>] {
        unsafe { core::mem::transmute(self) }
    }
}

// Immutable references to slices can be declassified
// Note: this is safe since the `Secret` type is `repr(transparent)`, so
//       the memory represnetation of the public and secret slices is the same
impl<'a, T: Scalar> DeclassifyRef for &'a [Secret<T>] {
    type DeclassifiedRef = &'a [T];
    fn declassify_ref(self) -> &'a [T] {
        unsafe { core::mem::transmute(self) }
    }
}

// Mutable references to scalars can be classified
// Note: this is safe since the `Secret` type is `repr(transparent)`, so
//       the memory represnetation of the public and secret slices is the same
impl<'a, T: Scalar> ClassifyRefMut for &'a mut [T] {
    type ClassifiedRefMut = &'a mut [Secret<T>];
    fn classify_ref_mut(self) -> &'a mut [Secret<T>] {
        unsafe { core::mem::transmute(self) }
    }
}

// Mutable references to scalars can be declassified
// Note: this is safe since the `Secret` type is `repr(transparent)`, so
//       the memory represnetation of the public and secret slices is the same
impl<'a, T: Scalar> DeclassifyRefMut for &'a mut [Secret<T>] {
    type DeclassifiedRefMut = &'a mut [T];
    fn declassify_ref_mut(self) -> &'a mut [T] {
        unsafe { core::mem::transmute(self) }
    }
}

// Immutable references to arrays can be classified
// Note: this is safe since the `Secret` type is `repr(transparent)`, so
//       the memory represnetation of the public and secret slices is the same
impl<'a, T: Scalar, const N: usize> ClassifyRef for &'a [T; N] {
    type ClassifiedRef = &'a [Secret<T>; N];
    fn classify_ref(self) -> &'a [Secret<T>; N] {
        unsafe { core::mem::transmute(self) }
    }
}

// Immutable references to arrays can be classified
// Note: this is safe since the `Secret` type is `repr(transparent)`, so
//       the memory represnetation of the public and secret slices is the same
impl<'a, T: Scalar, const N: usize> DeclassifyRef for &'a [Secret<T>; N] {
    type DeclassifiedRef = &'a [T; N];
    fn declassify_ref(self) -> &'a [T; N] {
        unsafe { core::mem::transmute(self) }
    }
}

// Mutable references to arrays can be classified
// Note: this is safe since the `Secret` type is `repr(transparent)`, so
//       the memory represnetation of the public and secret slices is the same
impl<'a, T: Scalar, const N: usize> ClassifyRefMut for &'a mut [T; N] {
    type ClassifiedRefMut = &'a mut [Secret<T>; N];
    fn classify_ref_mut(self) -> &'a mut [Secret<T>; N] {
        unsafe { core::mem::transmute(self) }
    }
}

// Mutable references to arrays can be declassified
// Note: this is safe since the `Secret` type is `repr(transparent)`, so
//       the memory represnetation of the public and secret slices is the same
impl<'a, T: Scalar, const N: usize> DeclassifyRefMut for &'a mut [Secret<T>; N] {
    type DeclassifiedRefMut = &'a mut [T; N];
    fn declassify_ref_mut(self) -> &'a mut [T; N] {
        unsafe { core::mem::transmute(self) }
    }
}
