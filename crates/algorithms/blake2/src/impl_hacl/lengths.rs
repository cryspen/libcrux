use super::{Blake2b, Blake2s, LengthBounds};

/// A marker trait indicating whether the hash supports keys of length LEN.
/// This trait is sealed to protect the soundness of the compile time bounds checks.
#[allow(private_bounds)]
pub trait SupportsKeyLen<const LEN: usize>: SupportsKeyLenInternal<LEN> {}

/// A marker trait indicating whether the hash supports outputs of length LEN.
/// This trait is sealed to protect the soundness of the compile time bounds checks.
#[allow(private_bounds)]
pub trait SupportsOutLen<const LEN: usize>: SupportsOutLenInternal<LEN> {}

/// A marker trait indicating whether the hash supports outputs of length LEN.
/// This is internal to seal the actual trait.
pub(super) trait SupportsOutLenInternal<const LEN: usize> {}

/// A marker trait indicating whether the hash supports keys of length LEN.
/// This is internal to seal the actual trait.
pub(super) trait SupportsKeyLenInternal<const LEN: usize> {}

// blanket impl the public part of the sealed trait
#[allow(private_bounds)]
impl<T, const LEN: usize> SupportsKeyLen<LEN> for T where T: SupportsKeyLenInternal<LEN> {}

// blanket impl the public part of the sealed trait
#[allow(private_bounds)]
impl<T, const LEN: usize> SupportsOutLen<LEN> for T where T: SupportsOutLenInternal<LEN> {}

/// this helps us implement SupportsLen for more than one number
macro_rules! support_lens {
    ($ty:ty, $trait:ident, $($supported:expr),*) => {
        $( impl $trait<$supported> for $ty {})*
    };
}

// implement the private parts of the sealed trait

#[rustfmt::skip]
support_lens!(
    Blake2b<LengthBounds>, SupportsOutLenInternal,
     1,  2,  3,  4,  5,  6,  7,  8,
     9, 10, 11, 12, 13, 14, 15, 16,
    17, 18, 19, 20, 21, 22, 23, 24,
    25, 26, 27, 28, 29, 30, 31, 32,
    33, 34, 35, 36, 37, 38, 39, 40,
    41, 42, 43, 44, 45, 46, 47, 48,
    49, 50, 51, 52, 53, 54, 55, 56,
    57, 58, 59, 60, 61, 62, 63, 64
);

#[rustfmt::skip]
support_lens!(
    Blake2s<LengthBounds>, SupportsOutLenInternal,
     1,  2,  3,  4,  5,  6,  7,  8,
     9, 10, 11, 12, 13, 14, 15, 16,
    17, 18, 19, 20, 21, 22, 23, 24,
    25, 26, 27, 28, 29, 30, 31, 32
);

#[rustfmt::skip]
support_lens!(
    Blake2b<LengthBounds>, SupportsKeyLenInternal,
     0,
     1,  2,  3,  4,  5,  6,  7,  8,
     9, 10, 11, 12, 13, 14, 15, 16,
    17, 18, 19, 20, 21, 22, 23, 24,
    25, 26, 27, 28, 29, 30, 31, 32,
    33, 34, 35, 36, 37, 38, 39, 40,
    41, 42, 43, 44, 45, 46, 47, 48,
    49, 50, 51, 52, 53, 54, 55, 56,
    57, 58, 59, 60, 61, 62, 63, 64
);

#[rustfmt::skip]
support_lens!(
    Blake2s<LengthBounds>, SupportsKeyLenInternal,
     0,
     1,  2,  3,  4,  5,  6,  7,  8,
     9, 10, 11, 12, 13, 14, 15, 16,
    17, 18, 19, 20, 21, 22, 23, 24,
    25, 26, 27, 28, 29, 30, 31, 32
);
