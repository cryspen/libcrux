use crate::traits::*;
use super::classify::*;
use std::ops::*;

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

// Construct a secret integer
pub const fn secret<T>(x: T) -> Secret<T> {
    Secret(x)
}

impl<T: Scalar> Classify for T {
    type Classified = Secret<T>;
    fn classify(self) -> Secret<Self> {
        secret(self)
    }
}

impl<T: Scalar> Declassify for Secret<T> {
    type Declassified = T;
    fn declassify(self) -> T {
        self.0
    }
}

impl<'a, T: Scalar> ClassifyRef for &'a T {
    type Classified = &'a Secret<T>;
    fn classify_ref(self) -> &'a Secret<T> {
        unsafe { core::mem::transmute(self) }
    }
}

impl<'a, T: Scalar> DeclassifyRef for &'a Secret<T> {
    type Declassified = &'a T;
    fn declassify_ref(self) -> &'a T {
        unsafe { core::mem::transmute(self) }
    }
}

impl<T: Add, V: Into<Secret<T>>> Add<V> for Secret<T> {
    type Output = Secret<T::Output>;
    fn add(self, rhs: V) -> Self::Output {
        self.0.add(rhs.into().0).into()
    }
}

impl<T: Sub, V: Into<Secret<T>>> Sub<V> for Secret<T> {
    type Output = Secret<T::Output>;
    fn sub(self, rhs: V) -> Self::Output {
        self.0.sub(rhs.into().0).into()
    }
}

impl<T: Mul, V: Into<Secret<T>>> Mul<V> for Secret<T> {
    type Output = Secret<T::Output>;
    fn mul(self, rhs: V) -> Self::Output {
        self.0.mul(rhs.into().0).into()
    }
}

impl<T: BitXor, V: Into<Secret<T>>> BitXor<V> for Secret<T> {
    type Output = Secret<T::Output>;
    fn bitxor(self, rhs: V) -> Self::Output {
        self.0.bitxor(rhs.into().0).into()
    }
}

impl<T: BitOr, V: Into<Secret<T>>> BitOr<V> for Secret<T> {
    type Output = Secret<T::Output>;
    fn bitor(self, rhs: V) -> Self::Output {
        self.0.bitor(rhs.into().0).into()
    }
}

impl<T: BitAnd, V: Into<Secret<T>>> BitAnd<V> for Secret<T> {
    type Output = Secret<T::Output>;
    fn bitand(self, rhs: V) -> Self::Output {
        self.0.bitand(rhs.into().0).into()
    }
}

impl<T: Not> Not for Secret<T> {
    type Output = Secret<T::Output>;
    fn not(self) -> Self::Output {
        self.0.not().into()
    }
}

impl<U, T: Shl<U>> Shl<U> for Secret<T>
    where T::Output: Into<T> {
    type Output = Secret<T>;
    fn shl(self, rhs: U) -> Self::Output {
        (self.0.shl(rhs).into()).into()
    }
}

impl<U, T: Shr<U>> Shr<U> for Secret<T> 
    where T::Output: Into<T> {
    type Output = Secret<T>;
    fn shr(self, rhs: U) -> Self::Output {
        (self.0.shr(rhs).into()).into()
    }
}

impl<T: AddAssign, V: Into<Secret<T>>> AddAssign<V> for Secret<T> {
    fn add_assign(&mut self, rhs: V) {
        self.0 += rhs.into().0
    }
}

impl<T: SubAssign, V: Into<Secret<T>>> SubAssign<V> for Secret<T> {
    fn sub_assign(&mut self, rhs: V) {
        self.0 -= rhs.into().0
    }
}

impl<T: MulAssign, V: Into<Secret<T>>> MulAssign<V> for Secret<T> {
    fn mul_assign(&mut self, rhs: V) {
        self.0 *= rhs.into().0
    }
}

impl<T: BitXorAssign, V: Into<Secret<T>>> BitXorAssign<V> for Secret<T> {
    fn bitxor_assign(&mut self, rhs: V) {
        self.0 ^= rhs.into().0;
    }
}

impl<T: BitOrAssign, V: Into<Secret<T>>> BitOrAssign<V> for Secret<T> {
    fn bitor_assign(&mut self, rhs: V) {
        self.0 |= rhs.into().0;
    }
}

impl<T: BitAndAssign, V: Into<Secret<T>>> BitAndAssign<V> for Secret<T> {
    fn bitand_assign(&mut self, rhs: V) {
        self.0 &= rhs.into().0;
    }
}

impl<U, T: ShrAssign<U>> ShrAssign<U> for Secret<T> {
    fn shr_assign(&mut self, rhs: U) {
        self.0 >>= rhs;
    }
}

impl<U, T: ShlAssign<U>> ShlAssign<U> for Secret<T> {
    fn shl_assign(&mut self, rhs: U) {
        self.0 <<= rhs;
    }
}

macro_rules! impl_int_ops {
    ($t:ty) => {
        impl IntOps for Secret<$t> {
            fn wrapping_add<T: Into<Secret<$t>>>(self, rhs: T) -> Self {
                self.declassify()
                    .wrapping_add(rhs.into().declassify())
                    .classify()
            }
            fn wrapping_sub<T: Into<Secret<$t>>>(self, rhs: T) -> Self {
                self.declassify()
                    .wrapping_sub(rhs.into().declassify())
                    .classify()
            }
            fn wrapping_mul<T: Into<Secret<$t>>>(self, rhs: T) -> Self {
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
    };
}
impl_int_ops!(u8);
impl_int_ops!(u16);
impl_int_ops!(u32);
impl_int_ops!(u64);
impl_int_ops!(u128);
impl_int_ops!(i8);
impl_int_ops!(i16);
impl_int_ops!(i32);
impl_int_ops!(i64);
impl_int_ops!(i128);

macro_rules! impl_encode_ops {
    ($t:ty, $N:literal) => {
        impl EncodeOps<U8, $N> for Secret<$t> {
            fn to_le_bytes(&self) -> [U8; $N] {
                self.0.to_le_bytes().classify()
            }
            fn to_be_bytes(&self) -> [U8; $N] {
                self.0.to_be_bytes().classify()
            }
            fn from_le_bytes(x: [U8; $N]) -> Self {
                <$t>::from_le_bytes(x.declassify()).classify()
            }
            fn from_be_bytes(x: [U8; $N]) -> Self {
                <$t>::from_be_bytes(x.declassify()).classify()
            }
        }
    };
}
impl_encode_ops!(u8, 1);
impl_encode_ops!(u16, 2);
impl_encode_ops!(u32, 4);
impl_encode_ops!(u64, 8);
impl_encode_ops!(u128, 16);
impl_encode_ops!(i8, 1);
impl_encode_ops!(i16, 2);
impl_encode_ops!(i32, 4);
impl_encode_ops!(i64, 8);
impl_encode_ops!(i128, 16);