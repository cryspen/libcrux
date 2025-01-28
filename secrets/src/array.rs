use crate::{
    traits::{Declassify, Zeroize},
    Scalar,
};

/// Trait bound for elements in [`SecretArray`].
pub trait ArrayElement: Default + Clone + Copy {}

/// A secret array that is zeroized on drop.
/// Getting a reference or slice of this, returns a Rust slice or array reference
/// to the underlying array of [`Secret`] elements.
#[derive(Clone)]
#[repr(transparent)]
pub struct SecretArray<T: ArrayElement, const N: usize>(pub(super) [T; N]);

impl<T: ArrayElement + Scalar, const N: usize> SecretArray<T, N> {
    /// Create a new [`SecretArray`] from a regular array `[T; N]`.
    ///
    /// Use `default` to allocate a new, empty [`SecretArray`].
    #[inline(always)]
    pub const fn new(array: [T; N]) -> Self {
        Self(array)
    }
}

impl<T: ArrayElement, const N: usize> Declassify for SecretArray<T, N> {
    type Declassified = [T; N];

    #[inline(always)]
    fn declassify(self) -> Self::Declassified {
        self.0
    }

    #[inline(always)]
    fn declassify_slice(&self) -> &Self::Declassified {
        &self.0
    }
}

impl<T: ArrayElement, const N: usize> From<[T; N]> for SecretArray<T, N> {
    #[inline(always)]
    fn from(value: [T; N]) -> Self {
        SecretArray(value)
    }
}

impl<T: ArrayElement, const N: usize> Drop for SecretArray<T, N> {
    #[inline(always)]
    fn drop(&mut self) {
        self.zeroize()
    }
}

impl<T: ArrayElement, const N: usize> Zeroize for SecretArray<T, N> {
    #[inline(always)]
    fn zeroize(&mut self) {
        crate::zeroize::zeroize(&mut self.0);
    }
}

// Implement `ArrayElement` for all integer types

impl ArrayElement for u8 {}
impl ArrayElement for u16 {}
impl ArrayElement for u32 {}
impl ArrayElement for u64 {}
impl ArrayElement for u128 {}

impl ArrayElement for i8 {}
impl ArrayElement for i16 {}
impl ArrayElement for i32 {}
impl ArrayElement for i64 {}
impl ArrayElement for i128 {}
