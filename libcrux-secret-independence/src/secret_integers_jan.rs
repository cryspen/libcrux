pub type U8 = scalar::SecretScalar<u8>;
pub type U16 = scalar::SecretScalar<u16>;
pub type U32 = scalar::SecretScalar<u32>;
pub type U64 = scalar::SecretScalar<u64>;
pub type U128 = scalar::SecretScalar<u128>;

pub type I8 = scalar::SecretScalar<i8>;
pub type I16 = scalar::SecretScalar<i16>;
pub type I32 = scalar::SecretScalar<i32>;
pub type I64 = scalar::SecretScalar<i64>;
pub type I128 = scalar::SecretScalar<i128>;

// we have to redefine the traits, because otherwise we implement them multiple times for the same
// types
pub mod traits {
    pub trait Classify {
        type Classified;
        fn classify(self) -> Self::Classified;
    }

    pub trait Declassify {
        type Declassified;
        fn declassify(self) -> Self::Declassified;
    }

    pub trait Zeroize {
        fn zeroize(&mut self);
    }

    /// Marker trait to constrain the types for which we use SecretScalar
    pub(crate) trait Scalar {}

    impl Scalar for u8 {}
    impl Scalar for u16 {}
    impl Scalar for u32 {}
    impl Scalar for u64 {}
    impl Scalar for u128 {}

    impl Scalar for i8 {}
    impl Scalar for i16 {}
    impl Scalar for i32 {}
    impl Scalar for i64 {}
    impl Scalar for i128 {}
}

/// Used to classify scalar values, such as individual integers.
pub mod scalar {
    use std::ops::{Add, AddAssign};

    use super::traits::*;

    #[derive(Debug, Clone, Copy)]
    pub struct SecretScalar<T>(pub(super) T);

    impl<T: Scalar> Classify for T {
        type Classified = SecretScalar<T>;

        fn classify(self) -> Self::Classified {
            SecretScalar(self)
        }
    }

    impl<T: Scalar> Classify for SecretScalar<T> {
        type Classified = Self;

        fn classify(self) -> Self::Classified {
            self
        }
    }

    impl<T: Scalar> From<T> for SecretScalar<T> {
        fn from(value: T) -> Self {
            value.classify()
        }
    }

    impl<T: Scalar> Declassify for SecretScalar<T> {
        type Declassified = T;

        fn declassify(self) -> Self::Declassified {
            self.0
        }
    }

    impl<Rhs, T, TRhs> Add<Rhs> for SecretScalar<T>
    where
        T: Scalar + Add<TRhs, Output = T>,
        Rhs: Classify<Classified = SecretScalar<TRhs>>,
        TRhs: Scalar,
    {
        type Output = SecretScalar<T::Output>;

        fn add(self, rhs: Rhs) -> Self::Output {
            self.declassify()
                .add(rhs.classify().declassify())
                .classify()
        }
    }

    impl<Rhs, T, TRhs> AddAssign<Rhs> for SecretScalar<T>
    where
        Rhs: Classify<Classified = SecretScalar<TRhs>>,
        TRhs: Scalar,
        T: Scalar + AddAssign<TRhs>,
    {
        fn add_assign(&mut self, rhs: Rhs) {
            self.0.add_assign(rhs.classify().declassify());
        }
    }
}

/// Used to classify arrays, usually of scalars.
///
/// It might make sense to require that the type inside the array is a Scalar. If we do that we can
/// also ask that Scalar implements Clone + Default, which would make the type bounds a bit simpler
pub mod array {
    use super::{
        arrayref::SecretArrayRef,
        slice::SecretSlice,
        traits::{Classify, Declassify, Zeroize},
    };

    #[derive(Debug, Clone)]
    pub struct SecretArray<T: Default + Clone, const N: usize>(pub(super) [T; N]);

    impl<T: Default + Clone, const N: usize> SecretArray<T, N> {
        pub fn as_slice(&self) -> SecretSlice<'_, T> {
            SecretSlice(self.0.as_slice())
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
}

/// Contains classified array references, i.e. &[T; N]
pub mod arrayref {
    use super::{array::SecretArray, slice::SecretSlice, traits::Declassify};

    #[derive(Debug, Clone, Copy)]
    pub struct SecretArrayRef<'a, T, const N: usize>(pub(super) &'a [T; N]);

    impl<'a, T, const N: usize> SecretArrayRef<'a, T, N> {
        pub(super) fn unwrap_ref(&self) -> &'a [T; N] {
            self.0
        }

        pub fn as_slice(self) -> SecretSlice<'a, T> {
            SecretSlice(self.0.as_slice())
        }
    }

    impl<'a, T: Default + Clone, const N: usize> From<&'a SecretArray<T, N>>
        for SecretArrayRef<'a, T, N>
    {
        fn from(value: &'a SecretArray<T, N>) -> Self {
            value.as_ref()
        }
    }

    impl<'a, T, const N: usize> Declassify for SecretArrayRef<'a, T, N> {
        type Declassified = &'a [T; N];

        fn declassify(self) -> Self::Declassified {
            self.unwrap_ref()
        }
    }
}

/// Contains classified slices, i.e. &[T]
pub mod slice {
    use super::{array::SecretArray, arrayref::SecretArrayRef, traits::Declassify};

    #[derive(Debug, Clone, Copy)]
    pub struct SecretSlice<'a, T>(pub(super) &'a [T]);

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
}

#[cfg(test)]
mod tests {
    use super::{
        arrayref::SecretArrayRef,
        slice::SecretSlice,
        traits::{Classify, Declassify},
    };

    #[test]
    fn scalar_example() {
        const MASK: u64 = 0x55aa55aa55aa55aa;
        let secret_answer = 42u64.classify();
        let secret_mask = MASK.classify();

        // we can add a normal value to a secret value
        let masked_secret_answer = secret_answer + MASK;
        assert_eq!(masked_secret_answer.declassify(), 42 + MASK);

        // we can add a secret value to a secret value
        let masked_secret_answer = secret_answer + secret_mask;
        assert_eq!(masked_secret_answer.declassify(), 42 + MASK);

        // AddAssign works with normal values
        let mut secret_answer_inplace = secret_answer;
        secret_answer_inplace += MASK;
        assert_eq!(secret_answer_inplace.declassify(), 42 + MASK);

        // AddAssign works with secret values
        let mut secret_answer_inplace = secret_answer;
        secret_answer_inplace += secret_mask;
        assert_eq!(secret_answer_inplace.declassify(), 42 + MASK);
    }

    #[test]
    fn array_examples() {
        let secret_array = b"squeamish".classify();

        // we can turn the array into a slice and declassify to a slice
        let secret_slice: SecretSlice<_> = secret_array.as_slice();
        let _: &[u8] = secret_slice.declassify();

        // we can declassify to a full array reference (incl. length)
        let secret_array_ref: SecretArrayRef<_, 9> = secret_array.as_ref();
        let _: &[u8; 9] = secret_array_ref.declassify();

        // we can turn the array ref into a slice and declassify to a slice
        let secret_slice: SecretSlice<_> = secret_array_ref.as_slice();
        let _: &[u8] = secret_slice.declassify();
    }
}
