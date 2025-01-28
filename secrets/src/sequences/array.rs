use std::ops::{Index, Range};

use crate::{array::*, traits::Classify, ClassifyRef, Scalar};

/// Trait bound for secret array elements.
pub trait SecretArrayElement: ArrayElement + Scalar + Classify + ClassifyRef {}

impl<T: ArrayElement + Scalar + Classify + ClassifyRef> SecretArrayElement for T {}

impl<T: ArrayElement + Classify + Scalar, const N: usize> SecretArray<T, N> {
    #[inline(always)]
    pub fn as_slice(&self) -> &[T::Classified] {
        unsafe { core::mem::transmute(self.0.as_slice()) }
    }

    #[inline(always)]
    pub fn as_mut_slice(&mut self) -> &mut [T::Classified] {
        unsafe { core::mem::transmute(self.0.as_mut_slice()) }
    }
}

impl<T: ArrayElement + Classify + Scalar, const N: usize> AsRef<[T::Classified; N]>
    for SecretArray<T, N>
{
    #[inline(always)]
    fn as_ref(&self) -> &[T::Classified; N] {
        unsafe { core::mem::transmute(&self.0) }
    }
}

impl<T: ArrayElement + Classify + Scalar, const N: usize> Classify for [T; N] {
    type Classified = SecretArray<T, N>;

    #[inline(always)]
    fn classify(self) -> Self::Classified {
        SecretArray(self)
    }
}

impl<T: SecretArrayElement, const N: usize> Index<usize> for SecretArray<T, N> {
    type Output = <T as ClassifyRef>::Classified;

    #[inline(always)]
    fn index(&self, index: usize) -> &Self::Output {
        self.0[index].classify_ref()
    }
}

impl<T: SecretArrayElement, const N: usize> Index<Range<usize>> for SecretArray<T, N> {
    type Output = [<T as Classify>::Classified];

    #[inline(always)]
    fn index(&self, index: Range<usize>) -> &Self::Output {
        &self.as_slice()[index]
    }
}
