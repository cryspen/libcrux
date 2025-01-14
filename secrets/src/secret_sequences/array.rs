use std::ops::Index;

use crate::{
    traits::{Classify, Declassify, Zeroize},
    ClassifyRef, Scalar, Secret,
};

pub trait SecretArrayElement: Default + Clone + Scalar + Copy + Classify + ClassifyRef {}

impl<T: Default + Clone + Scalar + Copy + Classify + ClassifyRef> SecretArrayElement for T {}

#[derive(Debug, Clone)]
pub struct SecretArray<T: SecretArrayElement, const N: usize>(pub(super) [T; N]);

impl<T: Default + Clone + Classify + Copy + Scalar, const N: usize> SecretArray<T, N> {
    pub const fn secret(array: [T; N]) -> Self {
        Self(array)
    }

    pub fn as_slice(&self) -> &[T::Classified] {
        unsafe { core::mem::transmute(self.0.as_slice()) }
    }

    pub fn as_mut_slice(&mut self) -> &mut [T::Classified] {
        unsafe { core::mem::transmute(self.0.as_mut_slice()) }
    }
}

impl<T: Default + Clone + Classify + Copy + Scalar, const N: usize> AsRef<[T::Classified; N]>
    for SecretArray<T, N>
{
    fn as_ref(&self) -> &[T::Classified; N] {
        unsafe { core::mem::transmute(&self.0) }
    }
}

impl<T: Default + Clone + Classify + Copy + Scalar, const N: usize> Classify for [T; N] {
    type Classified = SecretArray<T, N>;

    fn classify(self) -> Self::Classified {
        SecretArray(self)
    }
}

impl<T: Default + Clone + Classify + Copy + Scalar, const N: usize> Declassify
    for SecretArray<T, N>
{
    type Declassified = [T; N];

    fn declassify(self) -> Self::Declassified {
        self.0
    }
}

impl<T: Default + Clone + Classify + Copy + Scalar, const N: usize> From<[T; N]>
    for SecretArray<T, N>
{
    fn from(value: [T; N]) -> Self {
        SecretArray(value)
    }
}

impl<T: Default + Clone + Classify + Copy + Scalar, const N: usize> Drop for SecretArray<T, N> {
    fn drop(&mut self) {
        self.zeroize()
    }
}
impl<T: Default + Clone + Classify + Copy + Scalar, const N: usize> TryFrom<&[Secret<T>]>
    for SecretArray<T, N>
{
    type Error = core::array::TryFromSliceError;

    fn try_from(value: &[Secret<T>]) -> Result<Self, Self::Error> {
        let x: [Secret<T>; N] = value.try_into()?;
        let x: [T; N] = x.map(|x| x.declassify());

        Ok(Self(x))
    }
}

/// Try to prevent re-ordering of instructions
#[inline(always)]
fn atomic_fence() {
    core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
}

impl<T: Default + Clone + Classify + Copy + Scalar, const N: usize> Zeroize for SecretArray<T, N> {
    fn zeroize(&mut self) {
        let len = self.0.len();

        // Ensure len is not too big
        assert!(len <= isize::MAX as usize);

        // Get the default value to fill self with
        let default = T::default();

        // Take the raw pointer to this array
        let ptr = self.0.as_mut_ptr();

        // Fill self with the default value
        //
        // This only works when
        // - self is a continuos arrays of elements of type `T`
        // - alignment of self must allow the volatile write
        for i in 0..len {
            // eprintln!("{i}: {:p}", unsafe { ptr.add(i) });
            unsafe { core::ptr::write_volatile(ptr.add(i), default) };
        }
        atomic_fence();
    }
}

impl<T: SecretArrayElement, const N: usize> Index<usize> for SecretArray<T, N> {
    type Output = <T as ClassifyRef>::Classified;

    fn index(&self, index: usize) -> &Self::Output {
        self.0[index].classify_ref()
    }
}
