use crate::{sequences::array::SecretArray, traits::*};
use core::ops::*;

/// A secret type `T`.
#[repr(transparent)]
pub struct Secret<T>(T);

pub const fn secret<T>(x: T) -> Secret<T> {
    Secret(x)
}
fn unwrap<T>(x: Secret<T>) -> T {
    x.0
}

impl<T: Scalar> Classify for T {
    type Classified = Secret<T>;
    fn classify(self) -> Secret<Self> {
        secret(self)
    }
}

impl<T: Scalar> ClassifyRef for T {
    type Classified = Secret<T>;

    fn classify_ref(&self) -> &Self::Classified {
        unsafe { core::mem::transmute(self) }
    }
}

impl<T: Scalar> Declassify for Secret<T> {
    type Declassified = T;

    #[inline(always)]
    fn declassify(self) -> T {
        unwrap(self)
    }

    #[inline(always)]
    fn declassify_slice(&self) -> &Self::Declassified {
        &self.0
    }
}

impl<T: Scalar> From<T> for Secret<T> {
    fn from(x: T) -> Secret<T> {
        x.classify()
    }
}

impl<T: Scalar + Clone> Clone for Secret<T> {
    fn clone(&self) -> Self {
        Secret(self.0.clone())
    }
}

impl<T: Clone + Copy + Scalar> Copy for Secret<T> {}

impl<T: Add + Scalar, V: Into<Secret<T>>> Add<V> for Secret<T>
where
    T::Output: Scalar,
{
    type Output = Secret<T::Output>;
    fn add(self, rhs: V) -> Self::Output {
        self.declassify().add(rhs.into().declassify()).classify()
    }
}

impl<T: Sub + Scalar, V: Into<Secret<T>>> Sub<V> for Secret<T>
where
    T::Output: Scalar,
{
    type Output = Secret<T::Output>;
    fn sub(self, rhs: V) -> Self::Output {
        self.declassify().sub(rhs.into().declassify()).into()
    }
}

impl<T: Mul + Scalar, V: Into<Secret<T>>> Mul<V> for Secret<T>
where
    T::Output: Scalar,
{
    type Output = Secret<T::Output>;
    fn mul(self, rhs: V) -> Self::Output {
        self.declassify().mul(rhs.into().declassify()).into()
    }
}

impl<T: BitXor + Scalar, V: Into<Secret<T>>> BitXor<V> for Secret<T>
where
    T::Output: Scalar,
{
    type Output = Secret<T::Output>;
    fn bitxor(self, rhs: V) -> Self::Output {
        self.declassify().bitxor(rhs.into().declassify()).into()
    }
}

impl<T: BitXor + Copy + Scalar, V: Into<Secret<T>>> BitXorAssign<V> for Secret<T>
where
    T::Output: Scalar,
    T::Output: Into<T>,
{
    fn bitxor_assign(&mut self, rhs: V) {
        let r = self.declassify().bitxor(rhs.into().declassify()).into();
        *self = r.classify();
    }
}

impl<T: BitOr + Scalar, V: Into<Secret<T>>> BitOr<V> for Secret<T>
where
    T::Output: Scalar,
{
    type Output = Secret<T::Output>;
    fn bitor(self, rhs: V) -> Self::Output {
        self.declassify().bitor(rhs.into().declassify()).into()
    }
}

impl<T: BitOr + Copy + Scalar, V: Into<Secret<T>>> BitOrAssign<V> for Secret<T>
where
    T::Output: Into<T>,
{
    fn bitor_assign(&mut self, rhs: V) {
        let r = self.declassify().bitor(rhs.into().declassify()).into();
        *self = r.classify();
    }
}

impl<T: BitAnd + Scalar, V: Into<Secret<T>>> BitAnd<V> for Secret<T>
where
    T::Output: Scalar,
{
    type Output = Secret<T::Output>;
    fn bitand(self, rhs: V) -> Self::Output {
        self.declassify().bitand(rhs.into().declassify()).into()
    }
}

impl<T: BitAnd + Copy + Scalar, V: Into<Secret<T>>> BitAndAssign<V> for Secret<T>
where
    T::Output: Into<T>,
{
    fn bitand_assign(&mut self, rhs: V) {
        let r = self.declassify().bitand(rhs.into().declassify()).into();
        *self = r.classify();
    }
}

impl<T: Not + Scalar> Not for Secret<T>
where
    T::Output: Scalar,
{
    type Output = Secret<T::Output>;
    fn not(self) -> Self::Output {
        self.declassify().not().into()
    }
}

impl<U, T: Shl<U> + Scalar> Shl<U> for Secret<T>
where
    T::Output: Scalar,
{
    type Output = Secret<T::Output>;
    fn shl(self, rhs: U) -> Self::Output {
        (self.declassify().shl(rhs)).into()
    }
}

impl<U, T: Shr<U> + Scalar> Shr<U> for Secret<T>
where
    T::Output: Scalar,
{
    type Output = Secret<T::Output>;
    fn shr(self, rhs: U) -> Self::Output {
        (self.declassify().shr(rhs)).into()
    }
}

pub type I8 = Secret<i8>;
pub type U8 = Secret<u8>;
pub type I16 = Secret<i16>;
pub type U16 = Secret<u16>;
pub type I32 = Secret<i32>;
pub type U32 = Secret<u32>;
pub type I64 = Secret<i64>;
pub type U64 = Secret<u64>;
pub type I128 = Secret<i128>;
pub type U128 = Secret<u128>;

macro_rules! impl_new {
    ($name:ident, $t:ty, $st:ty) => {
        #[allow(non_snake_case)]
        pub const fn $name(v: $t) -> $st {
            Secret(v)
        }
    };
}
impl_new!(U8, u8, U8);
impl_new!(U16, u16, U16);
impl_new!(U32, u32, U32);
impl_new!(U64, u64, U64);

impl IntOps for Secret<u32> {
    fn wrapping_add<T: Into<Secret<u32>>>(self, rhs: T) -> Self {
        self.declassify()
            .wrapping_add(rhs.into().declassify())
            .classify()
    }
    fn wrapping_sub<T: Into<Secret<u32>>>(self, rhs: T) -> Self {
        self.declassify()
            .wrapping_sub(rhs.into().declassify())
            .classify()
    }
    fn wrapping_mul<T: Into<Secret<u32>>>(self, rhs: T) -> Self {
        self.declassify()
            .wrapping_mul(rhs.into().declassify())
            .classify()
    }
    fn rotate_left(self, rhs: u32) -> Self {
        self.declassify().rotate_left(rhs).classify()
    }
    fn rotate_right(self, rhs: u32) -> Self {
        self.declassify().rotate_right(rhs).classify()
    }
}

impl EncodeOps<U8, 4> for U32 {
    fn to_le_bytes(&self) -> SecretArray<u8, 4> {
        self.declassify().to_le_bytes().classify()
    }
    fn to_be_bytes(&self) -> SecretArray<u8, 4> {
        self.declassify().to_be_bytes().classify()
    }
    fn from_le_bytes(x: SecretArray<u8, 4>) -> Self {
        u32::from_le_bytes(x.declassify()).classify()
    }
    fn from_be_bytes(x: SecretArray<u8, 4>) -> Self {
        u32::from_be_bytes(x.declassify()).classify()
    }
}

impl IntOps for Secret<u64> {
    fn wrapping_add<T: Into<Secret<u64>>>(self, rhs: T) -> Self {
        self.declassify()
            .wrapping_add(rhs.into().declassify())
            .classify()
    }
    fn wrapping_sub<T: Into<Secret<u64>>>(self, rhs: T) -> Self {
        self.declassify()
            .wrapping_sub(rhs.into().declassify())
            .classify()
    }
    fn wrapping_mul<T: Into<Secret<u64>>>(self, rhs: T) -> Self {
        self.declassify()
            .wrapping_mul(rhs.into().declassify())
            .classify()
    }
    fn rotate_left(self, rhs: u32) -> Self {
        self.declassify().rotate_left(rhs).classify()
    }
    fn rotate_right(self, rhs: u32) -> Self {
        self.declassify().rotate_right(rhs).classify()
    }
}

impl EncodeOps<U8, 8> for U64 {
    fn to_le_bytes(&self) -> SecretArray<u8, 8> {
        self.declassify().to_le_bytes().classify()
    }

    fn to_be_bytes(&self) -> SecretArray<u8, 8> {
        self.declassify().to_be_bytes().classify()
    }

    fn from_le_bytes(x: SecretArray<u8, 8>) -> Self {
        u64::from_le_bytes(x.declassify()).classify()
    }

    fn from_be_bytes(x: SecretArray<u8, 8>) -> Self {
        u64::from_be_bytes(x.declassify()).classify()
    }
}
