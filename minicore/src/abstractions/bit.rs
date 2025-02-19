/// Represent a bit: `0` or `1`.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum Bit {
    Zero,
    One,
}

macro_rules! generate_from_bit_impls {
    ($($ty:ident),*) => {
        $(impl From<Bit> for $ty {
            fn from(bit: Bit) -> Self {
                bool::from(bit) as $ty
            }
        })*
    };
}
generate_from_bit_impls!(u8, u16, u32, u64, u128, i8, i16, i32, i64, i128);

impl From<Bit> for bool {
    fn from(bit: Bit) -> Self {
        match bit {
            Bit::Zero => false,
            Bit::One => true,
        }
    }
}

impl From<bool> for Bit {
    fn from(b: bool) -> Bit {
        match b {
            false => Bit::Zero,
            true => Bit::One,
        }
    }
}

/// A trait for types that represent machine integers.
pub trait MachineInteger {
    /// The size of this integer type in bits.
    const BITS: u32;

    /// The signedness of this integer type.
    const SIGNED: bool;
}

macro_rules! generate_machine_integer_impls {
    ($($ty:ident),*) => {
        $(impl MachineInteger for $ty {
            const BITS: u32 = $ty::BITS;
            #[allow(unused_comparisons)]
            const SIGNED: bool = $ty::MIN < 0;
        })*
    };
}
generate_machine_integer_impls!(u8, u16, u32, u64, u128, i8, i16, i32, i64, i128);

impl Bit {
    fn of_raw_int(x: u128, nth: u32) -> Self {
        if x / 2u128.pow(nth) % 2 == 1 {
            Self::One
        } else {
            Self::Zero
        }
    }

    pub fn of_int<T: Into<i128> + MachineInteger>(x: T, nth: u32) -> Bit {
        let x: i128 = x.into();
        if x >= 0 {
            Self::of_raw_int(x as u128, nth)
        } else {
            Self::of_raw_int((2i128.pow(T::BITS) + x) as u128, nth)
        }
    }
}
