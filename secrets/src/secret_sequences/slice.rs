use crate::{Declassify, Scalar, Secret};

/// Converts a slice of native scalars into a slice of classified scalars.
/// Note that this will not provide the added protection of an owned [`SecretArray`].
///
/// [`SecretArray`]: super::array::SecretArray
pub trait AsSecret {
    type Item: Declassify;

    fn as_secret(&self) -> &[Self::Item];
}

impl<T: Scalar> AsSecret for &[T] {
    type Item = Secret<T>;

    fn as_secret(&self) -> &[Self::Item] {
        unsafe { core::mem::transmute(*self) }
    }
}

impl<'a, T: Scalar> Declassify for &'a [Secret<T>] {
    type Declassified = &'a [T];

    fn declassify(self) -> Self::Declassified {
        unsafe { core::mem::transmute(self) }
    }
}

impl<'a, T: Scalar, const N: usize> Declassify for &'a [Secret<T>; N] {
    type Declassified = &'a [T; N];

    fn declassify(self) -> Self::Declassified {
        unsafe { core::mem::transmute(self) }
    }
}
