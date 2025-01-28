use crate::{Declassify, Scalar, Secret, U8};

/// Converts a slice of native scalars into a slice of classified scalars.
/// Note that this will not provide the added protection of an owned [`SecretArray`].
///
/// [`SecretArray`]: super::array::SecretArray
pub trait AsSecret {
    type Item: Declassify;

    fn as_secret(&self) -> &[Self::Item];
}

pub trait AsSecretRef<const N: usize> {
    type Item: Declassify;

    fn as_secret(&self) -> &[Self::Item; N];
}

#[inline(always)]
pub fn special_bytes_as_secret<'a>(val: &'a [&'a mut [u8]]) -> &'a [&'a mut [U8]] {
    val
}

#[inline(always)]
pub fn special_bytes_as_secret4(val: [&mut [u8]; 4]) -> [&mut [U8]; 4] {
    unsafe { core::mem::transmute(val) }
}

// #[inline(always)]h

#[inline(always)]
pub fn special_bytes_as_secret1(val: [&mut [u8]; 1]) -> [&mut [U8]; 1] {
    unsafe { core::mem::transmute(val) }
}

impl<T: Scalar> AsSecret for &[T] {
    type Item = Secret<T>;

    #[inline(always)]
    fn as_secret(&self) -> &[Self::Item] {
        unsafe { core::mem::transmute(*self) }
    }
}

impl<T: Scalar> AsSecret for Vec<T> {
    type Item = Secret<T>;

    #[inline(always)]
    fn as_secret(&self) -> &[Self::Item] {
        unsafe { core::mem::transmute(self.as_slice()) }
    }
}

impl<T: Scalar, const N: usize> AsSecretRef<N> for &[T; N] {
    type Item = Secret<T>;

    #[inline(always)]
    fn as_secret(&self) -> &[Self::Item; N] {
        unsafe { core::mem::transmute(*self) }
    }
}

impl<'a, T: Scalar> Declassify for &'a [Secret<T>] {
    type Declassified = &'a [T];

    #[inline(always)]
    fn declassify(self) -> Self::Declassified {
        unsafe { core::mem::transmute(self) }
    }

    #[inline(always)]
    fn declassify_slice(&self) -> &Self::Declassified {
        unsafe { core::mem::transmute(self) }
    }
}

impl<'a, T: Scalar, const N: usize> Declassify for &'a [Secret<T>; N] {
    type Declassified = &'a [T; N];

    #[inline(always)]
    fn declassify(self) -> Self::Declassified {
        unsafe { core::mem::transmute(self) }
    }

    #[inline(always)]
    fn declassify_slice(&self) -> &Self::Declassified {
        unsafe { core::mem::transmute(self) }
    }
}
