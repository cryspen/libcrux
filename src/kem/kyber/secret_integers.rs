// ---- U8 -----

#[cfg(feature = "secret_integers")]
#[derive(Clone, Copy, PartialEq, Debug)]
pub(crate) struct U8(u8);
#[cfg(not(feature = "secret_integers"))]
pub(crate) type U8 = u8;
#[cfg(feature = "secret_integers")]
impl U8 {
    pub fn wrapping_sub(self, rhs: u8) -> U8 {
        U8(self.0.wrapping_sub(rhs))
    }
}
#[cfg(feature = "secret_integers")]
impl core::ops::Not for U8 {
    type Output = U8;
    fn not(self) -> Self::Output {
        Self(!self.0)
    }
}
#[cfg(feature = "secret_integers")]
impl core::ops::BitAnd for U8 {
    type Output = U8;
    fn bitand(self, rhs: Self) -> Self::Output {
        Self(self.0 & rhs.0)
    }
}
#[cfg(feature = "secret_integers")]
impl core::ops::BitOr for U8 {
    type Output = U8;
    fn bitor(self, rhs: Self) -> Self::Output {
        Self(self.0 | rhs.0)
    }
}
#[cfg(feature = "secret_integers")]
impl core::ops::BitXor for U8 {
    type Output = U8;
    fn bitxor(self, rhs: Self) -> Self::Output {
        U8(self.0 ^ rhs.0)
    }
}
#[cfg(feature = "secret_integers")]
impl core::ops::BitOrAssign for U8 {
    fn bitor_assign(&mut self, rhs: Self) {
        self.0 = self.0 | rhs.0;
    }
}
#[cfg(feature = "secret_integers")]
impl From<u8> for U8 {
    fn from(x: u8) -> U8 {
        U8(x)
    }
}
#[cfg(feature = "secret_integers")]
#[allow(non_snake_case)]
pub fn declassify_U8(v: U8) -> u8 {
    v.0
}
#[cfg(not(feature = "secret_integers"))]
#[allow(non_snake_case)]
pub fn declassify_U8(v: U8) -> u8 {
    v
}

#[cfg(feature = "secret_integers")]
pub fn classify_u8_array<const ARRAY_LENGTH: usize>(
    array: [u8; ARRAY_LENGTH],
) -> [U8; ARRAY_LENGTH] {
    array.map(|v| U8::from(v))
}

#[cfg(not(feature = "secret_integers"))]
pub fn classify_u8_array<const ARRAY_LENGTH: usize>(
    array: [u8; ARRAY_LENGTH],
) -> [U8; ARRAY_LENGTH] {
    array
}

#[allow(non_snake_case)]
pub fn declassify_U8_array<const ARRAY_LENGTH: usize>(
    array: [U8; ARRAY_LENGTH],
) -> [u8; ARRAY_LENGTH] {
    array.map(|v| declassify_U8(v))
}

// ---- U16 -----

#[cfg(feature = "secret_integers")]
#[derive(Clone, Copy, PartialEq, Debug)]
pub(crate) struct U16(u16);
#[cfg(not(feature = "secret_integers"))]
pub(crate) type U16 = u16;
#[cfg(feature = "secret_integers")]
impl From<u16> for U16 {
    fn from(x: u16) -> U16 {
        U16(x)
    }
}
#[cfg(feature = "secret_integers")]
impl core::ops::Not for U16 {
    type Output = U16;
    fn not(self) -> Self::Output {
        Self(!self.0)
    }
}

#[cfg(feature = "secret_integers")]
impl core::ops::Shr<u16> for U16 {
    type Output = U16;
    fn shr(self, rhs: u16) -> Self::Output {
        Self(self.0 >> rhs)
    }
}
#[cfg(feature = "secret_integers")]
impl core::ops::BitAnd<u16> for U16 {
    type Output = U16;
    fn bitand(self, rhs: u16) -> Self::Output {
        Self(self.0 & rhs)
    }
}
#[cfg(feature = "secret_integers")]
impl core::ops::BitOr for U16 {
    type Output = U16;
    fn bitor(self, rhs: Self) -> Self::Output {
        Self(self.0 | rhs.0)
    }
}

#[cfg(feature = "secret_integers")]
impl U16 {
    pub fn wrapping_add(self, rhs: u16) -> U16 {
        U16(self.0.wrapping_add(rhs))
    }
}

// ---- U32 -----

#[cfg(feature = "secret_integers")]
#[derive(Clone, Copy, PartialEq, Debug)]
pub(crate) struct U32(u32);
#[cfg(feature = "secret_integers")]
impl From<u32> for U32 {
    fn from(x: u32) -> U32 {
        U32(x)
    }
}

#[cfg(feature = "secret_integers")]
impl core::ops::Mul<u32> for U32 {
    type Output = U32;
    fn mul(self, rhs: u32) -> Self::Output {
        Self(self.0 * rhs)
    }
}

#[cfg(feature = "secret_integers")]
impl core::ops::Shl<u32> for U32 {
    type Output = U32;
    fn shl(self, rhs: u32) -> Self::Output {
        Self(self.0 << rhs)
    }
}

#[cfg(feature = "secret_integers")]
impl core::ops::Add<u32> for U32 {
    type Output = U32;
    fn add(self, rhs: u32) -> Self::Output {
        Self(self.0 + rhs)
    }
}

#[cfg(feature = "secret_integers")]
impl core::ops::ShrAssign<u8> for U32 {
    fn shr_assign(&mut self, rhs: u8) {
        self.0 >>= rhs;
    }
}

// ---- I16 -----

#[cfg(feature = "secret_integers")]
#[derive(Clone, Copy, PartialEq, Debug)]
pub(crate) struct I16(i16);
#[cfg(not(feature = "secret_integers"))]
pub(crate) type I16 = i16;
#[cfg(feature = "secret_integers")]
impl From<i16> for I16 {
    fn from(x: i16) -> I16 {
        I16(x)
    }
}

#[cfg(feature = "secret_integers")]
impl core::ops::Sub for I16 {
    type Output = I16;
    fn sub(self, rhs: Self) -> Self::Output {
        Self(self.0 - rhs.0)
    }
}
#[cfg(feature = "secret_integers")]
impl core::ops::Sub<i16> for I16 {
    type Output = I16;
    fn sub(self, rhs: i16) -> Self::Output {
        Self(self.0 - rhs)
    }
}
#[cfg(feature = "secret_integers")]
impl core::ops::Sub<I16> for i16 {
    type Output = I16;
    fn sub(self, rhs: I16) -> Self::Output {
        I16(self - rhs.0)
    }
}

#[cfg(feature = "secret_integers")]
impl core::ops::Shr<i16> for I16 {
    type Output = I16;
    fn shr(self, rhs: i16) -> Self::Output {
        Self(self.0 >> rhs)
    }
}
#[cfg(feature = "secret_integers")]
impl core::ops::BitXor for I16 {
    type Output = I16;
    fn bitxor(self, rhs: I16) -> Self::Output {
        Self(self.0 ^ rhs.0)
    }
}
#[cfg(feature = "secret_integers")]
impl core::ops::BitAnd<i16> for I16 {
    type Output = I16;
    fn bitand(self, rhs: i16) -> Self::Output {
        Self(self.0 & rhs)
    }
}

#[cfg(feature = "secret_integers")]
#[allow(non_snake_case)]
pub fn declassify_I16(v: I16) -> i16 {
    v.0
}
#[cfg(not(feature = "secret_integers"))]
#[allow(non_snake_case)]
pub fn declassify_I16(v: I16) -> i16 {
    v
}

// ---- I32 -----

#[cfg(feature = "secret_integers")]
#[derive(Clone, Copy, PartialEq, Debug)]
pub(crate) struct I32(i32);
#[cfg(not(feature = "secret_integers"))]
pub(crate) type I32 = i32;
#[cfg(feature = "secret_integers")]
impl From<i32> for I32 {
    fn from(x: i32) -> I32 {
        I32(x)
    }
}
#[cfg(feature = "secret_integers")]
impl core::ops::Mul<i32> for I32 {
    type Output = I32;
    fn mul(self, rhs: i32) -> Self::Output {
        Self(self.0 * rhs)
    }
}

#[cfg(feature = "secret_integers")]
impl core::ops::Sub for I32 {
    type Output = I32;
    fn sub(self, rhs: I32) -> Self::Output {
        Self(self.0 - rhs.0)
    }
}

#[cfg(feature = "secret_integers")]
#[allow(non_snake_case)]
pub fn declassify_I32(v: I32) -> i32 {
    v.0
}
#[cfg(not(feature = "secret_integers"))]
#[allow(non_snake_case)]
pub fn declassify_I32(v: I32) -> i32 {
    v
}

// ---- I64 -----

#[cfg(feature = "secret_integers")]
#[derive(Clone, Copy, PartialEq, Debug)]
pub(crate) struct I64(i64);
#[cfg(not(feature = "secret_integers"))]
pub(crate) type I64 = i64;

#[cfg(feature = "secret_integers")]
impl core::ops::Mul<i64> for I64 {
    type Output = I64;
    fn mul(self, rhs: i64) -> Self::Output {
        Self(self.0 * rhs)
    }
}

#[cfg(feature = "secret_integers")]
impl core::ops::Add<i64> for I64 {
    type Output = I64;
    fn add(self, rhs: i64) -> Self::Output {
        Self(self.0 + rhs)
    }
}

#[cfg(feature = "secret_integers")]
impl core::ops::Shr<i64> for I64 {
    type Output = I64;
    fn shr(self, rhs: i64) -> Self::Output {
        Self(self.0 >> rhs)
    }
}

// ---- as functions -----

#[cfg(feature = "secret_integers")]
#[allow(non_snake_case)]
pub fn U8_as_U16(v: U8) -> U16 {
    U16(v.0 as u16)
}
#[cfg(not(feature = "secret_integers"))]
#[allow(non_snake_case)]
pub fn U8_as_U16(v: U8) -> U16 {
    v as u16
}

#[cfg(feature = "secret_integers")]
#[allow(non_snake_case)]
pub fn U16_as_U8(v: U16) -> U8 {
    U8(v.0 as u8)
}
#[cfg(not(feature = "secret_integers"))]
#[allow(non_snake_case)]
pub fn U16_as_U8(v: U16) -> U8 {
    v as u8
}

#[cfg(feature = "secret_integers")]
#[allow(non_snake_case)]
pub fn U16_as_I16(v: U16) -> I16 {
    I16(v.0 as i16)
}
#[cfg(not(feature = "secret_integers"))]
#[allow(non_snake_case)]
pub fn U16_as_I16(v: U16) -> I16 {
    v as i16
}

#[cfg(feature = "secret_integers")]
#[allow(non_snake_case)]
pub fn I64_as_I32(v: I64) -> I32 {
    I32(v.0 as i32)
}
#[cfg(not(feature = "secret_integers"))]
#[allow(non_snake_case)]
pub fn I64_as_I32(v: I64) -> I32 {
    v as i32
}

#[cfg(feature = "secret_integers")]
#[allow(non_snake_case)]
pub fn I64_from_I32(v: I32) -> I64 {
    I64(i64::from(v.0))
}
#[cfg(not(feature = "secret_integers"))]
#[allow(non_snake_case)]
pub fn I64_from_I32(v: I32) -> I64 {
    i64::from(v)
}
