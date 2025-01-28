use crate::{array::SecretArray, Secret};

pub trait Classify {
    type Classified;
    fn classify(self) -> Self::Classified;
}

pub trait ClassifyRef {
    type Classified;
    fn classify_ref(&self) -> &Self::Classified;
}

pub trait ClassifyRefMut: ClassifyRef {
    fn classify_mut(&mut self) -> &mut Self::Classified;
}

pub trait Declassify {
    type Declassified;
    fn declassify(self) -> Self::Declassified;
    fn declassify_slice(&self) -> &Self::Declassified;
}

/// Zero memory before dropping it
pub trait Zeroize {
    fn zeroize(&mut self);
}

/// Marker trait to constrain the types for which we use SecretScalar
pub trait Scalar {}

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

pub trait IntOps
where
    Self: Sized,
{
    fn wrapping_add<T: Into<Self>>(self, rhs: T) -> Self;
    fn wrapping_sub<T: Into<Self>>(self, rhs: T) -> Self;
    fn wrapping_mul<T: Into<Self>>(self, rhs: T) -> Self;
    fn rotate_left(self, rhs: u32) -> Self;
    fn rotate_right(self, rhs: u32) -> Self;
}

/// Encode secret arrays into secret integers.
pub trait EncodeOps<T, const N: usize> {
    fn to_le_bytes(&self) -> SecretArray<u8, N>;
    fn to_be_bytes(&self) -> SecretArray<u8, N>;

    fn from_le_bytes(x: SecretArray<u8, N>) -> Self;
    fn from_be_bytes(x: SecretArray<u8, N>) -> Self;

    /// The try from variant panics if the input doesn't have the correct size.
    fn try_from_le_bytes(x: &[Secret<u8>]) -> Self;
    /// The try from variant panics if the input doesn't have the correct size.
    fn try_from_be_bytes(x: &[Secret<u8>]) -> Self;
}

/*
#[inline(always)]
#[hax_lib::requires(C > 0 && C <= 16 && N <= 65536 / C)]
#[hax_lib::ensures(|result| if B == N * C {result.is_ok()} else {result.is_err()} )]
pub(crate) fn try_to_le_bytes<
    U: Clone,
    const C: usize,
    T: EncodeOps<U, C>,
    const N: usize,
    const B: usize,
>(
    x: &[T; N],
) -> Result<[U; B], ()> {
    let mut v = Vec::new();
    for i in 0..N {
        v.extend(x[i].to_le_bytes().as_slice().iter())
    }
    v.try_into().map_err(|_| ())
}

#[inline(always)]
#[hax_lib::requires(C > 0 && C <= 16 && N <= 65536 / C)]
#[hax_lib::ensures(|result| if B == N * C {result.is_ok()} else {result.is_err()} )]
pub(crate) fn try_to_be_bytes<
    U: Clone,
    const C: usize,
    T: EncodeOps<U, C>,
    const N: usize,
    const B: usize,
>(
    x: &[T; N],
) -> Result<[U; B], ()> {
    let mut v = Vec::new();
    for i in 0..N {
        v.extend_from_slice(&x[i].to_be_bytes())
    }
    v.try_into().map_err(|_| ())
}

#[inline(always)]
#[hax_lib::requires(C > 0 && C <= 16 && N <= 65536 / C)]
#[hax_lib::ensures(|result| if x.len() == N * C {result.is_ok()} else {result.is_err()} )]
pub(crate) fn try_from_le_bytes<U, const C: usize, T: EncodeOps<U, C>, const N: usize>(
    x: &[U],
) -> Result<[T; N], ()> {
    let mut v = Vec::new();
    for c in x.chunks_exact(C) {
        v.push(T::from_le_bytes(c.try_into().unwrap()))
    }
    v.try_into().map_err(|_| ())
}

#[inline(always)]
#[hax_lib::requires(C > 0 && C <= 16 && N <= 65536 / C)]
#[hax_lib::ensures(|result| if x.len() == N * C {result.is_ok()} else {result.is_err()} )]
pub(crate) fn try_from_be_bytes<U, const C: usize, T: EncodeOps<U, C>, const N: usize>(
    x: &[U],
) -> Result<[T; N], ()> {
    let mut v = Vec::new();
    for c in x.chunks_exact(C) {
        v.push(T::from_be_bytes(c.try_into().unwrap()))
    }
    v.try_into().map_err(|_| ())
}

pub trait TryEncodeOps<T, const N: usize>: Sized {
    fn try_to_le_bytes(&self) -> Result<[T; N], ()>;
    fn try_to_be_bytes(&self) -> Result<[T; N], ()>;
}

pub trait TryDecodeOps<T>: Sized {
    fn try_from_le_bytes(x: &[T]) -> Result<Self, ()>;
    fn try_from_be_bytes(x: &[T]) -> Result<Self, ()>;
}
*/
