#[cfg(all(not(hax), debug_assertions))]
#[derive(Clone, Copy, PartialEq, Debug)]
pub(crate) struct U8(u8);
#[cfg(not(all(not(hax), debug_assertions)))]
pub(crate) type U8 = u8;

#[cfg(all(not(hax), debug_assertions))]
#[derive(Clone, Copy, PartialEq, Debug)]
pub(crate) struct U16(u16);
#[cfg(not(all(not(hax), debug_assertions)))]
pub(crate) type U16 = u16;

#[cfg(all(not(hax), debug_assertions))]
impl core::ops::BitXor for U8 {
    type Output = U8;
    fn bitxor(self, rhs: Self) -> Self::Output {
        U8(self.0 ^ rhs.0)
    }
}

#[cfg(all(not(hax), debug_assertions))]
impl core::ops::BitOrAssign for U8 {
    fn bitor_assign(&mut self, rhs: Self) {
        self.0 = self.0 | rhs.0;
    }
}

#[cfg(all(not(hax), debug_assertions))]
impl From<u8> for U8 {
    fn from(x: u8) -> U8 {
        U8(x)
    }
}

#[cfg(all(not(hax), debug_assertions))]
#[allow(non_snake_case)]
pub fn declassify_U8(v: U8) -> u8 {
    v.0
}
#[cfg(not(all(not(hax), debug_assertions)))]
#[allow(non_snake_case)]
pub fn declassify_U8(v: U8) -> u8 {
    v
}

#[cfg(all(not(hax), debug_assertions))]
#[allow(non_snake_case)]
pub fn U8_as_U16(v: U8) -> U16 {
    U16(v.0 as u16)
}
#[cfg(not(all(not(hax), debug_assertions)))]
#[allow(non_snake_case)]
pub fn U8_as_U16(v: U8) -> U16 {
    v as u16
}

#[cfg(all(not(hax), debug_assertions))]
#[allow(non_snake_case)]
pub fn U16_as_U8(v: U16) -> U8 {
    U8(v.0 as u8)
}
#[cfg(not(all(not(hax), debug_assertions)))]
#[allow(non_snake_case)]
pub fn U16_as_U8(v: U16) -> U8 {
    v as u8
}

#[cfg(all(not(hax), debug_assertions))]
impl core::ops::Not for U16 {
    type Output = U16;
    fn not(self) -> Self::Output {
        Self(!self.0)
    }
}

#[cfg(all(not(hax), debug_assertions))]
impl core::ops::Shr<u16> for U16 {
    type Output = U16;
    fn shr(self, rhs: u16) -> Self::Output {
        Self(self.0 >> rhs)
    }
}
#[cfg(all(not(hax), debug_assertions))]
impl core::ops::BitAnd<u16> for U16 {
    type Output = U16;
    fn bitand(self, rhs: u16) -> Self::Output {
        Self(self.0 & rhs)
    }
}
#[cfg(all(not(hax), debug_assertions))]
impl core::ops::BitOr for U16 {
    type Output = U16;
    fn bitor(self, rhs: Self) -> Self::Output {
        Self(self.0 | rhs.0)
    }
}

#[cfg(all(not(hax), debug_assertions))]
impl U16 {
    pub fn wrapping_add(self, rhs: u16) -> U16 {
        U16(self.0.wrapping_add(rhs))
    }
}
