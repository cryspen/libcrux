#[cfg(test)]
pub mod test {
    use crate::abstractions::{bit::Bit, bitvec::BitVec, funarr::FunArray};
    use rand::prelude::*;

    /// Helper trait to generate random values
    pub trait HasRandom {
        fn random() -> Self;
    }
    macro_rules! mk_has_random {
        ($($ty:ty),*) => {
            $(impl HasRandom for $ty {
                fn random() -> Self {
                    let mut rng = rand::rng();
                    rng.random()
                }
            })*
        };
    }

    mk_has_random!(bool);
    mk_has_random!(i8, i16, i32, i64, i128);
    mk_has_random!(u8, u16, u32, u64, u128);

    impl HasRandom for isize {
        fn random() -> Self {
            i128::random() as isize
        }
    }
    impl HasRandom for usize {
        fn random() -> Self {
            i128::random() as usize
        }
    }

    impl HasRandom for Bit {
        fn random() -> Self {
            crate::abstractions::bit::Bit::from(bool::random())
        }
    }
    impl<const N: u64> HasRandom for BitVec<N> {
        fn random() -> Self {
            Self::from_fn(|_| Bit::random())
        }
    }

    impl<const N: u64, T: HasRandom> HasRandom for FunArray<N, T> {
        fn random() -> Self {
            FunArray::from_fn(|_| T::random())
        }
    }

    /// Boundary / extreme scalar values for corner-case tests.
    ///
    /// Random fuzzing (`HasRandom`) samples the whole range uniformly and so
    /// almost never hits type extremes, the sign boundary, or small
    /// magnitudes — exactly where saturation / overflow / wraparound bugs
    /// live (e.g. `vqdmulhq_s16(i16::MIN, i16::MIN)`). These lists make those
    /// inputs explicit so every arithmetic model is exercised at its corners.
    pub trait HasCorners: Sized + Copy + 'static {
        fn corners() -> &'static [Self];
    }
    macro_rules! mk_has_corners_signed {
        ($($ty:ty),*) => {
            $(impl HasCorners for $ty {
                fn corners() -> &'static [Self] {
                    &[<$ty>::MIN, <$ty>::MIN + 1, -2, -1, 0, 1, 2, <$ty>::MAX - 1, <$ty>::MAX]
                }
            })*
        };
    }
    macro_rules! mk_has_corners_unsigned {
        ($($ty:ty),*) => {
            $(impl HasCorners for $ty {
                fn corners() -> &'static [Self] {
                    &[0, 1, 2, <$ty>::MAX / 2, <$ty>::MAX / 2 + 1, <$ty>::MAX - 1, <$ty>::MAX]
                }
            })*
        };
    }
    mk_has_corners_signed!(i8, i16, i32, i64, i128);
    mk_has_corners_unsigned!(u8, u16, u32, u64, u128);
}

#[cfg(test)]
pub use test::*;
