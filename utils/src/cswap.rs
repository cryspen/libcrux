//! Maybe constant time swapping of values.

pub trait Swap {
    /// Depending on `selector`, keep everything as is, or swap `self` and `other`.
    ///
    /// If `selector == 0`, the values are unchanged, otherwise swap.
    fn cswap(&mut self, other: &mut Self, selector: u8);
}

#[cfg(not(any(target_arch = "aarch64")))]
mod portable {
    use super::Swap;

    macro_rules! swap {
        ($t:ty, $lhs:expr, $rhs:expr, $selector:expr) => {
            let mask = core::hint::black_box(
                ((((!($selector as u64)).wrapping_add(1) >> 63) & 1) as $t).wrapping_sub(1),
            );
            for (lhs, rhs) in $lhs.iter_mut().zip($rhs.iter_mut()) {
                let dummy = !mask & (*lhs ^ *rhs);
                *lhs ^= dummy;
                *rhs ^= dummy
            }
        };
    }

    impl Swap for [u8] {
        #[inline]
        fn cswap(&mut self, other: &mut Self, selector: u8) {
            swap!(u8, self, other, selector);
        }
    }

    impl Swap for [u16] {
        #[inline]
        fn cswap(&mut self, other: &mut Self, selector: u8) {
            swap!(u16, self, other, selector);
        }
    }

    impl Swap for [u32] {
        #[inline]
        fn cswap(&mut self, other: &mut Self, selector: u8) {
            swap!(u32, self, other, selector);
        }
    }

    impl Swap for [u64] {
        #[inline]
        fn cswap(&mut self, other: &mut Self, selector: u8) {
            swap!(u64, self, other, selector);
        }
    }
}

#[cfg(target_arch = "aarch64")]
mod aarch64 {
    use core::arch::asm;

    use super::*;

    macro_rules! swap {
        ($lhs:expr, $rhs:expr, $selector:expr) => {
            // Using https://developer.arm.com/documentation/ddi0602/2021-12/Base-Instructions/CSEL--Conditional-Select-
            #[allow(unsafe_code)]
            unsafe {
                asm! {
                    "cmp {cond:w}, 0",
                    // XXX: we could use w (32-bit) registers here up to u32
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

    impl Swap for u8 {
        #[inline]
        fn cswap(&mut self, other: &mut Self, selector: u8) {
            swap!(self, other, selector);
        }
    }

    impl Swap for u16 {
        #[inline]
        fn cswap(&mut self, other: &mut Self, selector: u8) {
            swap!(self, other, selector);
        }
    }

    impl Swap for u32 {
        #[inline]
        fn cswap(&mut self, other: &mut Self, selector: u8) {
            swap!(self, other, selector);
        }
    }

    impl Swap for u64 {
        #[inline]
        fn cswap(&mut self, other: &mut Self, selector: u8) {
            swap!(self, other, selector);
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
mod tests {
    extern crate std;
    use core::fmt::Debug;

    use super::*;
    use rand::{rng, Fill, Rng, RngCore};

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
}
