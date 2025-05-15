//! Maybe constant time selecting of values.

pub trait Select {
    /// Select `self` or `other`, depending on `selector`.
    /// The selected value will be in `self`.
    ///
    /// If `selector != 0`, select `other`, otherwise
    /// `self` is unchanged.
    fn select(&mut self, other: &Self, selector: u8);
}

#[cfg(not(any(target_arch = "aarch64")))]
mod portable {
    use super::*;

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

    impl Select for [u16] {
        fn select(&mut self, other: &Self, selector: u8) {
            let mask = (is_non_zero(selector) as u16).wrapping_sub(1);
            for i in 0..self.len() {
                self[i] = (self[i] & mask) | (other[i] & !mask);
            }
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

    impl Select for [u64] {
        fn select(&mut self, other: &Self, selector: u8) {
            let mask = (is_non_zero(selector) as u64).wrapping_sub(1);
            for i in 0..self.len() {
                self[i] = (self[i] & mask) | (other[i] & !mask);
            }
        }
    }
}

#[cfg(target_arch = "aarch64")]
mod aarch64 {
    use core::arch::asm;

    use super::*;

    macro_rules! select {
        ($lhs:expr, $rhs:expr, $selector:expr) => {
            // Using https://developer.arm.com/documentation/ddi0602/2021-12/Base-Instructions/CSEL--Conditional-Select-
            #[allow(unsafe_code)]
            unsafe {
                asm! {
                    "cmp {cond:w}, 0",
                    // XXX: we could use w (32-bit) registers here up to u32
                    "csel {lhs:x}, {rhs:x}, {lhs:x}, NE",
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
            select!(self, other, selector);
        }
    }

    impl Select for u16 {
        #[inline]
        fn select(&mut self, other: &Self, selector: u8) {
            select!(self, other, selector);
        }
    }

    impl Select for u32 {
        #[inline]
        fn select(&mut self, other: &Self, selector: u8) {
            select!(self, other, selector);
        }
    }

    impl Select for u64 {
        #[inline]
        fn select(&mut self, other: &Self, selector: u8) {
            select!(self, other, selector);
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
}

#[cfg(test)]
mod tests {
    extern crate std;
    use core::fmt::Debug;

    use super::*;
    use rand::{rng, Fill, Rng, RngCore};

    fn test<T: Default + Copy + PartialEq + Eq + Debug>(rng: &mut impl RngCore)
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
}
