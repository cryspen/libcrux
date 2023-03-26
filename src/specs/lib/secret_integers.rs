pub(crate) type U8 = u8;
pub(crate) type U16 = u16;
pub(crate) type U32 = u32;
pub(crate) type U64 = u64;
pub(crate) type U128 = u128;

pub(crate) fn U8(x: u8) -> U8 {
    x
}

pub(crate) fn U16(x: u16) -> U16 {
    x
}

pub(crate) fn U32(x: u32) -> U32 {
    x
}

pub(crate) fn U64(x: u64) -> U64 {
    x
}

pub(crate) fn U128(x: u128) -> U128 {
    x
}

pub trait SecretInt<T> {
    fn declassify(self) -> T;
}

pub trait PublicInt<T> {
    fn classify(self) -> T;
}

macro_rules! impl_traits {
    ($stype:ty, $ptype:ty) => {
        impl SecretInt<$ptype> for $stype {
            #[inline(always)]
            fn declassify(self) -> $ptype {
                self
            }
        }

        impl PublicInt<$stype> for $ptype {
            #[inline(always)]
            fn classify(self) -> $stype {
                self
            }
        }
    };
}

impl_traits!(U8, u8);
impl_traits!(U16, u16);
impl_traits!(U32, u32);
impl_traits!(U64, u64);
impl_traits!(U128, u128);
