use crate::traits::*;

#[cfg(feature = "check-secret-independence")]
mod classify;
// If the feature "check-secret-independence" is set, we use secret integers
#[cfg(feature = "check-secret-independence")]
mod secret_integers;
#[cfg(feature = "check-secret-independence")]
pub use secret_integers::*;

// If the feature "check-secret-independence" is not set, we use public integers
#[cfg(not(feature = "check-secret-independence"))]
mod public_integers;
#[cfg(not(feature = "check-secret-independence"))]
pub use public_integers::*;

// A macro defining const constructors for secret/public integers
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

#[cfg(not(eurydice))]
impl_new!(U128, u128, U128);

impl_new!(I8, i8, I8);
impl_new!(I16, i16, I16);
impl_new!(I32, i32, I32);
impl_new!(I64, i64, I64);

#[cfg(not(eurydice))]
impl_new!(I128, i128, I128);

/// A trait defining cast operations for secret/public integers
pub trait CastOps {
    fn as_u8(self) -> U8;
    fn as_i8(self) -> I8;
    fn as_u16(self) -> U16;
    fn as_i16(self) -> I16;
    fn as_u32(self) -> U32;
    fn as_i32(self) -> I32;
    fn as_u64(self) -> U64;
    fn as_i64(self) -> I64;

    #[cfg(not(eurydice))]
    fn as_u128(self) -> U128;
    #[cfg(not(eurydice))]
    fn as_i128(self) -> I128;
}

// Implementations of cast operations for all integers
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

            #[cfg(not(eurydice))]
            #[inline(always)]
            fn as_u128(self) -> U128 {
                (self.declassify() as u128).classify()
            }
            #[cfg(not(eurydice))]
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

#[cfg(not(eurydice))]
impl_cast_ops!(U128);

impl_cast_ops!(I8);
impl_cast_ops!(I16);
impl_cast_ops!(I32);
impl_cast_ops!(I64);

#[cfg(not(eurydice))]
impl_cast_ops!(I128);

#[cfg(not(any(target_arch = "aarch64")))]
mod portable {
    use super::*;
    use super::{Select, Swap};

    // Don't inline this to avoid that the compiler optimizes this out.
    #[inline(never)]
    fn is_non_zero(selector: u8) -> u64 {
        core::hint::black_box(((!(selector as u64)).wrapping_add(1) >> 63) & 1)
    }

    impl Select for [u8] {
        fn select(&mut self, other: &Self, selector: u8) {
            let mask = (is_non_zero(selector) as u8).wrapping_sub(1);
            for i in 0..self.len() {
                self[i] = (self[i] & mask) | (other[i] & !mask);
            }
        }
    }

    #[cfg(feature = "check-secret-independence")]
    impl Select for [U8] {
        fn select(&mut self, other: &Self, selector: u8) {
            let lhs = self.declassify_ref_mut();
            let rhs = other.declassify_ref();
            lhs.select(rhs, selector);
        }
    }

    impl Select for [u16] {
        fn select(&mut self, other: &Self, selector: u8) {
            let mask = (is_non_zero(selector) as u16).wrapping_sub(1);
            for i in 0..self.len() {
                self[i] = (self[i] & mask) | (other[i] & !mask);
            }
        }
    }

    #[cfg(feature = "check-secret-independence")]
    impl Select for [U16] {
        fn select(&mut self, other: &Self, selector: u8) {
            let lhs = self.declassify_ref_mut();
            let rhs = other.declassify_ref();
            lhs.select(rhs, selector);
        }
    }

    impl Select for [u32] {
        fn select(&mut self, other: &Self, selector: u8) {
            let mask = (is_non_zero(selector) as u32).wrapping_sub(1);
            for i in 0..self.len() {
                self[i] = (self[i] & mask) | (other[i] & !mask);
            }
        }
    }

    #[cfg(feature = "check-secret-independence")]
    impl Select for [U32] {
        fn select(&mut self, other: &Self, selector: u8) {
            let lhs = self.declassify_ref_mut();
            let rhs = other.declassify_ref();
            lhs.select(rhs, selector);
        }
    }

    impl Select for [u64] {
        fn select(&mut self, other: &Self, selector: u8) {
            let mask = (is_non_zero(selector) as u64).wrapping_sub(1);
            for i in 0..self.len() {
                self[i] = (self[i] & mask) | (other[i] & !mask);
            }
        }
    }

    #[cfg(feature = "check-secret-independence")]
    impl Select for [U64] {
        fn select(&mut self, other: &Self, selector: u8) {
            let lhs = self.declassify_ref_mut();
            let rhs = other.declassify_ref();
            lhs.select(rhs, selector);
        }
    }

    macro_rules! swap {
        ($t:ty, $lhs:expr, $rhs:expr, $selector:expr) => {
            let mask = core::hint::black_box(
                ((((!($selector as u64)).wrapping_add(1) >> 63) & 1) as $t).wrapping_sub(1),
            );
            for (lhs, rhs) in $lhs.iter_mut().zip($rhs.iter_mut()) {
                let dummy = !mask & (*lhs ^ *rhs);
                *lhs ^= dummy;
                *rhs ^= dummy;
            }
        };
    }

    impl Swap for [u8] {
        #[inline]
        fn cswap(&mut self, other: &mut Self, selector: u8) {
            swap!(u8, self, other, selector);
        }
    }

    #[cfg(feature = "check-secret-independence")]
    impl Swap for [U8] {
        #[inline]
        fn cswap(&mut self, other: &mut Self, selector: u8) {
            let lhs = self.declassify_ref_mut();
            let rhs = other.declassify_ref_mut();
            swap!(u8, lhs, rhs, selector);
        }
    }

    impl Swap for [u16] {
        #[inline]
        fn cswap(&mut self, other: &mut Self, selector: u8) {
            swap!(u16, self, other, selector);
        }
    }

    #[cfg(feature = "check-secret-independence")]
    impl Swap for [U16] {
        #[inline]
        fn cswap(&mut self, other: &mut Self, selector: u8) {
            let lhs = self.declassify_ref_mut();
            let rhs = other.declassify_ref_mut();
            swap!(u16, lhs, rhs, selector);
        }
    }

    impl Swap for [u32] {
        #[inline]
        fn cswap(&mut self, other: &mut Self, selector: u8) {
            swap!(u32, self, other, selector);
        }
    }
    #[cfg(feature = "check-secret-independence")]
    impl Swap for [U32] {
        #[inline]
        fn cswap(&mut self, other: &mut Self, selector: u8) {
            let lhs = self.declassify_ref_mut();
            let rhs = other.declassify_ref_mut();
            swap!(u32, lhs, rhs, selector);
        }
    }

    impl Swap for [u64] {
        #[inline]
        fn cswap(&mut self, other: &mut Self, selector: u8) {
            swap!(u64, self, other, selector);
        }
    }

    #[cfg(feature = "check-secret-independence")]
    impl Swap for [U64] {
        #[inline]
        fn cswap(&mut self, other: &mut Self, selector: u8) {
            let lhs = self.declassify_ref_mut();
            let rhs = other.declassify_ref_mut();
            swap!(u64, lhs, rhs, selector);
        }
    }
}

#[cfg(target_arch = "aarch64")]
mod aarch64 {
    use core::arch::asm;

    use super::*;

    macro_rules! select64 {
        ($lhs:expr, $rhs:expr, $selector:expr) => {
            // Using https://developer.arm.com/documentation/ddi0602/2021-12/Base-Instructions/CSEL--Conditional-Select-
            #[allow(unsafe_code)]
            unsafe {
                asm! {
                    "cmp {cond:w}, 0",
                    "csel {lhs:x}, {rhs:x}, {lhs:x}, NE",
                    cond = in(reg) $selector,
                    lhs = inlateout(reg) *$lhs,
                    rhs = in(reg) *$rhs,
                    options(pure, nomem, nostack),
                };
            }
        };
    }

    macro_rules! select32 {
        ($lhs:expr, $rhs:expr, $selector:expr) => {
            // Using https://developer.arm.com/documentation/ddi0602/2021-12/Base-Instructions/CSEL--Conditional-Select-
            #[allow(unsafe_code)]
            unsafe {
                asm! {
                    "cmp {cond:w}, 0",
                    "csel {lhs:w}, {rhs:w}, {lhs:w}, NE",
                    cond = in(reg) $selector,
                    lhs = inlateout(reg) *$lhs,
                    rhs = in(reg) *$rhs,
                    options(pure, nomem, nostack),
                };
            }
        };
    }

    impl Select for u8 {
        #[inline]
        fn select(&mut self, other: &Self, selector: u8) {
            select32!(self, other, selector);
        }
    }

    #[cfg(feature = "check-secret-independence")]
    impl Select for U8 {
        #[inline]
        fn select(&mut self, other: &Self, selector: u8) {
            let lhs = self.declassify_ref_mut();
            let rhs = other.declassify_ref();
            lhs.select(rhs, selector);
        }
    }

    impl Select for u16 {
        #[inline]
        fn select(&mut self, other: &Self, selector: u8) {
            select32!(self, other, selector);
        }
    }

    #[cfg(feature = "check-secret-independence")]
    impl Select for U16 {
        #[inline]
        fn select(&mut self, other: &Self, selector: u8) {
            let lhs = self.declassify_ref_mut();
            let rhs = other.declassify_ref();
            lhs.select(rhs, selector);
        }
    }

    impl Select for u32 {
        #[inline]
        fn select(&mut self, other: &Self, selector: u8) {
            select32!(self, other, selector);
        }
    }

    #[cfg(feature = "check-secret-independence")]
    impl Select for U32 {
        #[inline]
        fn select(&mut self, other: &Self, selector: u8) {
            let lhs = self.declassify_ref_mut();
            let rhs = other.declassify_ref();
            lhs.select(rhs, selector);
        }
    }

    impl Select for u64 {
        #[inline]
        fn select(&mut self, other: &Self, selector: u8) {
            select64!(self, other, selector);
        }
    }

    #[cfg(feature = "check-secret-independence")]
    impl Select for U64 {
        #[inline]
        fn select(&mut self, other: &Self, selector: u8) {
            let lhs = self.declassify_ref_mut();
            let rhs = other.declassify_ref();
            lhs.select(rhs, selector);
        }
    }

    impl<T: Select> Select for [T] {
        #[inline]
        fn select(&mut self, other: &Self, selector: u8) {
            for (lhs, rhs) in self.iter_mut().zip(other.iter()) {
                lhs.select(rhs, selector);
            }
        }
    }

    macro_rules! swap64 {
        ($lhs:expr, $rhs:expr, $selector:expr) => {
            // Using https://developer.arm.com/documentation/ddi0602/2021-12/Base-Instructions/CSEL--Conditional-Select-
            #[allow(unsafe_code)]
            unsafe {
                asm! {
                    "cmp {cond:w}, 0",
                    "csel {tmp}, {b:x}, {a:x}, NE",
                    "csel {b:x}, {a:x}, {b:x}, NE",
                    "mov {a:x}, {tmp}",
                    cond = in(reg) $selector,
                    a = inout(reg) *$lhs,
                    b = inout(reg) *$rhs,
                    tmp = out(reg) _,
                    options(pure, nomem, nostack),
                };
            }
        };
    }

    macro_rules! swap32 {
        ($lhs:expr, $rhs:expr, $selector:expr) => {
            // Using https://developer.arm.com/documentation/ddi0602/2021-12/Base-Instructions/CSEL--Conditional-Select-
            #[allow(unsafe_code)]
            unsafe {
                asm! {
                    "cmp {cond:w}, 0",
                    "csel {tmp:w}, {b:w}, {a:w}, NE",
                    "csel {b:w}, {a:w}, {b:w}, NE",
                    "mov {a:w}, {tmp:w}",
                    cond = in(reg) $selector,
                    a = inout(reg) *$lhs,
                    b = inout(reg) *$rhs,
                    tmp = out(reg) _,
                    options(pure, nomem, nostack),
                };
            }
        };
    }

    impl Swap for u8 {
        #[inline]
        fn cswap(&mut self, other: &mut Self, selector: u8) {
            swap32!(self, other, selector);
        }
    }

    #[cfg(feature = "check-secret-independence")]
    impl Swap for U8 {
        #[inline]
        fn cswap(&mut self, other: &mut Self, selector: u8) {
            let lhs = self.declassify_ref_mut();
            let rhs = other.declassify_ref_mut();
            lhs.cswap(rhs, selector);
        }
    }

    impl Swap for u16 {
        #[inline]
        fn cswap(&mut self, other: &mut Self, selector: u8) {
            swap32!(self, other, selector);
        }
    }

    #[cfg(feature = "check-secret-independence")]
    impl Swap for U16 {
        #[inline]
        fn cswap(&mut self, other: &mut Self, selector: u8) {
            let lhs = self.declassify_ref_mut();
            let rhs = other.declassify_ref_mut();
            lhs.cswap(rhs, selector);
        }
    }

    impl Swap for u32 {
        #[inline]
        fn cswap(&mut self, other: &mut Self, selector: u8) {
            swap32!(self, other, selector);
        }
    }

    #[cfg(feature = "check-secret-independence")]
    impl Swap for U32 {
        #[inline]
        fn cswap(&mut self, other: &mut Self, selector: u8) {
            let lhs = self.declassify_ref_mut();
            let rhs = other.declassify_ref_mut();
            lhs.cswap(rhs, selector);
        }
    }

    impl Swap for u64 {
        #[inline]
        fn cswap(&mut self, other: &mut Self, selector: u8) {
            swap64!(self, other, selector);
        }
    }

    #[cfg(feature = "check-secret-independence")]
    impl Swap for U64 {
        #[inline]
        fn cswap(&mut self, other: &mut Self, selector: u8) {
            let lhs = self.declassify_ref_mut();
            let rhs = other.declassify_ref_mut();
            lhs.cswap(rhs, selector);
        }
    }

    impl<T: Swap> Swap for [T] {
        #[inline]
        fn cswap(&mut self, other: &mut Self, selector: u8) {
            for (lhs, rhs) in self.iter_mut().zip(other.iter_mut()) {
                lhs.cswap(rhs, selector);
            }
        }
    }
}

#[cfg(test)]
mod select {
    extern crate std;
    use core::fmt::Debug;

    use super::*;
    use rand::{rng, Fill, Rng, RngCore};

    fn test<T: Classify + Default + Copy + PartialEq + Eq + Debug>(rng: &mut impl RngCore)
    where
        [T]: Fill + Select,
    {
        let selector: bool = rng.random();
        let selector = if selector { 0 } else { rng.next_u32() as u8 };
        let mut lhs = [T::default(); 256];
        rng.fill(&mut lhs);
        let mut rhs = [T::default(); 256];
        rng.fill(&mut rhs);

        let expected = if selector == 0 {
            lhs.clone()
        } else {
            rhs.clone()
        };

        lhs.select(&rhs, selector);

        assert_eq!(
            lhs, expected,
            "\nother: {:?}\nselector: {}\n",
            rhs, selector
        );
    }

    #[test]
    fn correctness() {
        let mut rng = rng();
        const ITERATIONS: usize = 1_000;

        for _ in 0..ITERATIONS {
            test::<u8>(&mut rng);
            test::<u16>(&mut rng);
            test::<u32>(&mut rng);
            test::<u64>(&mut rng);
        }
    }

    #[test]
    #[cfg(feature = "check-secret-independence")]
    fn correctness_secret() {
        macro_rules! secret_test {
            ($ty:ty, $rng:expr) => {{
                let selector: bool = $rng.random();
                let selector = if selector { 0 } else { $rng.next_u32() as u8 };
                let mut lhs = [<$ty>::default(); 256];
                $rng.fill(&mut lhs);
                let mut rhs = [<$ty>::default(); 256];
                $rng.fill(&mut rhs);

                let expected = if selector == 0 {
                    lhs.clone()
                } else {
                    rhs.clone()
                };

                let mut lhs = lhs.classify();
                let rhs = rhs.classify();

                lhs.select(&rhs, selector);

                assert_eq!(
                    lhs.declassify(),
                    expected,
                    "\nother: {:?}\nselector: {}\n",
                    rhs.declassify(),
                    selector
                );
            }};
        }
        let mut rng = rng();
        const ITERATIONS: usize = 1_000;

        for _ in 0..ITERATIONS {
            secret_test!(u8, rng);
            secret_test!(u16, rng);
            secret_test!(u32, rng);
            secret_test!(u64, rng);
        }
    }
}

#[cfg(test)]
mod swap {
    extern crate std;
    use core::fmt::Debug;

    use super::*;
    use rand::{rng, Fill, Rng, RngCore};

    /// Test swap on public integers.
    fn test<T: Default + Copy + PartialEq + Eq + Debug>(rng: &mut impl RngCore)
    where
        [T]: Fill + Swap,
    {
        let selector: bool = rng.random();
        let selector = if selector { 0 } else { rng.next_u32() as u8 };
        let mut lhs = [T::default(); 256];
        rng.fill(&mut lhs);
        let mut rhs = [T::default(); 256];
        rng.fill(&mut rhs);

        let (expected_lhs, expected_rhs) = if selector == 0 {
            (lhs.clone(), rhs.clone())
        } else {
            (rhs.clone(), lhs.clone())
        };

        lhs.cswap(&mut rhs, selector);

        assert_eq!(lhs, expected_lhs, "\nlhs / selector: {}\n", selector);
        assert_eq!(rhs, expected_rhs, "\nrhs / selector: {}\n", selector);
    }

    #[test]
    fn correctness() {
        let mut rng = rng();
        const ITERATIONS: usize = 1_000;

        for _ in 0..ITERATIONS {
            test::<u8>(&mut rng);
            test::<u16>(&mut rng);
            test::<u32>(&mut rng);
            test::<u64>(&mut rng);
        }
    }

    /// Test swap on secret integers.
    #[test]
    #[cfg(feature = "check-secret-independence")]
    fn correctness_secret() {
        macro_rules! secret_test {
            ($ty:ty, $rng:expr) => {{
                let selector: bool = $rng.random();
                let selector = if selector { 0 } else { $rng.next_u32() as u8 };
                let mut lhs = [<$ty>::default(); 256];
                $rng.fill(&mut lhs);
                let mut rhs = [<$ty>::default(); 256];
                $rng.fill(&mut rhs);

                let (expected_lhs, expected_rhs) = if selector == 0 {
                    (lhs.clone(), rhs.clone())
                } else {
                    (rhs.clone(), lhs.clone())
                };

                let mut lhs = lhs.classify();
                let mut rhs = rhs.classify();
                lhs.cswap(&mut rhs, selector);

                assert_eq!(
                    lhs.declassify(),
                    expected_lhs,
                    "\nlhs / selector: {}\n",
                    selector
                );
                assert_eq!(
                    rhs.declassify(),
                    expected_rhs,
                    "\nrhs / selector: {}\n",
                    selector
                );
            }};
        }
        let mut rng = rng();
        const ITERATIONS: usize = 1_000;

        for _ in 0..ITERATIONS {
            secret_test!(u8, rng);
            secret_test!(u16, rng);
            secret_test!(u32, rng);
            secret_test!(u64, rng);
        }
    }
}
