pub use array::*;
pub use slice::*;

/// Used to classify arrays, usually of scalars.
///
/// It might make sense to require that the type inside the array is a Scalar. If we do that we can
/// also ask that Scalar implements Clone + Default, which would make the type bounds a bit simpler
pub mod array {
    use std::ops::Index;

    use super::arrayref::SecretArrayRef;
    use crate::{
        traits::{Classify, Declassify, Zeroize},
        ClassifyRef, Scalar, Secret,
    };

    #[derive(Debug, Clone)]
    pub struct SecretArray<T: Default + Clone, const N: usize>(pub(super) [T; N]);

    impl<T: Default + Clone + Classify, const N: usize> SecretArray<T, N> {
        pub const fn secret(array: [T; N]) -> Self {
            Self(array)
        }

        pub fn as_slice(&self) -> &[T::Classified] {
            unsafe { core::mem::transmute(self.0.as_slice()) }
        }

        pub fn as_mut_slice(&mut self) -> &mut [T::Classified] {
            unsafe { core::mem::transmute(self.0.as_mut_slice()) }
        }

        pub fn as_ref(&self) -> SecretArrayRef<'_, T, N> {
            SecretArrayRef(&self.0)
        }
    }

    impl<T: Default + Clone, const N: usize> Classify for [T; N] {
        type Classified = SecretArray<T, N>;

        fn classify(self) -> Self::Classified {
            SecretArray(self)
        }
    }

    impl<T: Default + Clone, const N: usize> Declassify for SecretArray<T, N> {
        type Declassified = [T; N];

        fn declassify(self) -> Self::Declassified {
            self.0.clone()
        }
    }

    impl<T: Default + Clone, const N: usize> From<[T; N]> for SecretArray<T, N> {
        fn from(value: [T; N]) -> Self {
            SecretArray(value)
        }
    }

    impl<T: Default + Clone, const N: usize> Drop for SecretArray<T, N> {
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

    impl<T: Default + Clone, const N: usize> Zeroize for SecretArray<T, N> {
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
                unsafe { core::ptr::write_volatile(ptr.add(i), default.clone()) };
            }
            atomic_fence();
        }
    }

    impl<T: Default + Clone + ClassifyRef, const N: usize> Index<usize> for SecretArray<T, N> {
        type Output = T::Classified;

        fn index(&self, index: usize) -> &Self::Output {
            self.0[index].classify_ref()
        }
    }
}

/// Contains classified array references, i.e. &[T; N]
pub mod arrayref {
    use super::array::SecretArray;
    use crate::{traits::Declassify, Classify};

    #[derive(Debug, Clone, Copy)]
    pub struct SecretArrayRef<'a, T, const N: usize>(pub(super) &'a [T; N]);

    impl<'a, T: Classify, const N: usize> SecretArrayRef<'a, T, N> {
        pub(super) fn unwrap_ref(&self) -> &'a [T; N] {
            self.0
        }

        pub fn as_slice(&self) -> &[T::Classified] {
            unsafe { core::mem::transmute(&self.0[..]) }
        }
    }

    impl<'a, T: Default + Clone + Classify, const N: usize> From<&'a SecretArray<T, N>>
        for SecretArrayRef<'a, T, N>
    {
        fn from(value: &'a SecretArray<T, N>) -> Self {
            value.as_ref()
        }
    }

    impl<'a, T: Classify, const N: usize> Declassify for SecretArrayRef<'a, T, N> {
        type Declassified = &'a [T; N];

        fn declassify(self) -> Self::Declassified {
            self.unwrap_ref()
        }
    }
}

/// Contains classified slices, i.e. &[T]
pub mod slice {
    use crate::{Declassify, Scalar, Secret};

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
    /*
    use std::ops::{Index, IndexMut, Range};

    use super::{array::SecretArray, arrayref::SecretArrayRef, iter::SecretIter};
    use crate::{traits::Declassify, ClassifyRef, ClassifyRefMut, Scalar};

    #[derive(Debug, Clone, Copy)]
    pub struct SecretSlice<'a, T>(pub(super) &'a [T]);

    impl<'a, T: Default + Clone + Scalar> SecretSlice<'a, T> {
        pub fn iter(self) -> SecretIter<'a, T> {
            SecretIter(self)
        }
    }

    impl<'a, T: Default + Clone, const N: usize> From<&'a SecretArray<T, N>> for SecretSlice<'a, T> {
        fn from(value: &'a SecretArray<T, N>) -> Self {
            value.as_slice()
        }
    }

    impl<'a, T, const N: usize> From<SecretArrayRef<'a, T, N>> for SecretSlice<'a, T> {
        fn from(value: SecretArrayRef<'a, T, N>) -> Self {
            SecretSlice(value.unwrap_ref())
        }
    }

    impl<'a, T> Declassify for SecretSlice<'a, T> {
        type Declassified = &'a [T];

        fn declassify(self) -> Self::Declassified {
            self.0
        }
    }

    impl<'a, T: Default + Clone + ClassifyRef> Index<usize> for SecretSlice<'a, T> {
        type Output = T::Classified;

        fn index(&self, index: usize) -> &Self::Output {
            self.0[index].classify_ref()
        }
    }

    impl<'a, T: Default + Clone + ClassifyRefMut> IndexMut<usize> for SecretArray<'a, T> {
        fn index_mut(&mut self, index: usize) -> &mut Self::Output {
            self.0[index].classify_mut()
        }
    }

    impl<'a, T: Default + Clone + ClassifyRef> Index<Range<usize>> for SecretSlice<'a, T> {
        type Output = Self;

        fn index(&self, index: Range<usize>) -> &Self::Output {
            let the_slice_we_want = &self.0[index];
            let the_ref: Self = unsafe { core::mem::transmute(the_slice_we_want) };

            &the_ref
        }
    }

    impl<'a, T: Default + Clone + ClassifyRefMut> IndexMut<usize> for SecretArray<'a, T> {
        fn index_mut(&mut self, index: usize) -> &mut Self::Output {
            self.0[index].classify_mut()
        }
    }
    */
}

/*
pub mod iter {
    use crate::Classify;

    use super::slice::SecretSlice;

    pub struct SecretIter<'a, T: Classify>(pub(super) SecretSlice<'a, T>);

    impl<'a, T: Classify + Clone> Iterator for SecretIter<'a, T> {
        type Item = T::Classified;

        fn next(&mut self) -> Option<Self::Item> {
            match self.0 .0.first() {
                Some(item) => {
                    self.0 .0 = &self.0 .0[1..];
                    Some(item.clone().classify())
                }
                None => None,
            }
        }
    }
}
*/

// TODO: #[cfg(feature = "simd256")]
mod avx2 {
    use crate::Scalar;

    impl Scalar for core::arch::x86_64::__m256i {}
    impl Scalar for core::arch::x86_64::__m128i {}
}
