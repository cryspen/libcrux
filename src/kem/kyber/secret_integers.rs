#[cfg(all(not(hax), debug_assertions))]
#[derive(Clone, Copy, PartialEq, Debug)]
pub(crate) struct U8(u8);

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
impl U8 {
    pub fn declassify(&self) -> u8 {
        self.0
    }
}

#[cfg(not(all(not(hax), debug_assertions)))]
pub(crate) type U8 = u8;

#[cfg(not(all(not(hax), debug_assertions)))]
pub(crate) fn U8(x: u8) -> U8 {
    x
}

#[cfg(not(all(not(hax), debug_assertions)))]
impl Declassify for U8 {
    type t = u8;
    fn declassify(&self) -> u8 {
        *self
    }
}

impl From<&u8> for U8 {
    fn from(x: &u8) -> U8 {
        U8(*x)
    }
}
