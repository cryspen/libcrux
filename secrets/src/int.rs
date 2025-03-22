use crate::traits::*;

#[cfg(feature = "check-secret-independence")]
mod classify;
#[cfg(feature = "check-secret-independence")]
mod secret_integers;
#[cfg(feature = "check-secret-independence")]
pub use secret_integers::*;

#[cfg(not(feature = "check-secret-independence"))]
mod public_integers;
#[cfg(not(feature = "check-secret-independence"))]
pub use public_integers::*;

macro_rules! impl_new {
    ($name:ident, $t:ty, $st:ty) => {
        #[allow(non_snake_case)]
        #[inline(always)]
        pub const fn $name(v: $t) -> $st {
            secret(v)
        }
    };
}
impl_new!(U8, u8, U8);
impl_new!(U16, u16, U16);
impl_new!(U32, u32, U32);
impl_new!(U64, u64, U64);
impl_new!(U128, u128, U128);
impl_new!(I8, i8, I8);
impl_new!(I16, i16, I16);
impl_new!(I32, i32, I32);
impl_new!(I64, i64, I64);
impl_new!(I128, i128, I128);

pub trait CastOps {
    fn as_u8(self) -> U8;
    fn as_i8(self) -> I8;
    fn as_u16(self) -> U16;
    fn as_i16(self) -> I16;
    fn as_u32(self) -> U32;
    fn as_i32(self) -> I32;
    fn as_u64(self) -> U64;
    fn as_i64(self) -> I64;
    fn as_u128(self) -> U128;
    fn as_i128(self) -> I128;
}

macro_rules! impl_cast_ops {
    ($name:ident) => {
        impl CastOps for $name {
            #[inline(always)]
            fn as_u8(self) -> U8 {
                (self.declassify() as u8).classify()
            }
            #[inline(always)]
            fn as_i8(self) -> I8 {
                (self.declassify() as i8).classify()
            }
            #[inline(always)]
            fn as_u16(self) -> U16 {
                (self.declassify() as u16).classify()
            }
            #[inline(always)]
            fn as_i16(self) -> I16 {
                (self.declassify() as i16).classify()
            }
            #[inline(always)]
            fn as_u32(self) -> U32 {
                (self.declassify() as u32).classify()
            }
            #[inline(always)]
            fn as_i32(self) -> I32 {
                (self.declassify() as i32).classify()
            }
            #[inline(always)]
            fn as_u64(self) -> U64 {
                (self.declassify() as u64).classify()
            }
            #[inline(always)]
            fn as_i64(self) -> I64 {
                (self.declassify() as i64).classify()
            }
            #[inline(always)]
            fn as_u128(self) -> U128 {
                (self.declassify() as u128).classify()
            }
            #[inline(always)]
            fn as_i128(self) -> I128 {
                (self.declassify() as i128).classify()
            }
        }
    };
}
impl_cast_ops!(U8);
impl_cast_ops!(U16);
impl_cast_ops!(U32);
impl_cast_ops!(U64);
impl_cast_ops!(U128);
impl_cast_ops!(I8);
impl_cast_ops!(I16);
impl_cast_ops!(I32);
impl_cast_ops!(I64);
impl_cast_ops!(I128);
