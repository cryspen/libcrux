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

    impl Select for [u8] {
        fn select(&mut self, other: &Self, selector: u8) {
            // Don't inline this to avoid that the compiler optimizes this out.
            #[inline(never)]
            fn is_non_zero(value: u8) -> u8 {
                fn inz(value: u8) -> u8 {
                    let value = value as u16;
                    let result = ((!value).wrapping_add(1) >> 8) as u8;
                    result & 1
                }
                core::hint::black_box(inz(value))
            }

            let mask = is_non_zero(selector).wrapping_sub(1);
            for i in 0..self.len() {
                self[i] = (self[i] & mask) | (other[i] & !mask);
            }
        }
    }

    // XXX: Make generic
    impl Select for [u16] {
        fn select(&mut self, other: &Self, selector: u8) {
            // Don't inline this to avoid that the compiler optimizes this out.
            #[inline(never)]
            fn is_non_zero(value: u16) -> u16 {
                fn inz(value: u16) -> u16 {
                    let value = value as u32;
                    let result = ((!value).wrapping_add(1) >> 8) as u16;
                    result & 1
                }
                core::hint::black_box(inz(value))
            }

            let mask = is_non_zero(selector as u16).wrapping_sub(1);
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
                    "cmp {0:w}, 0",
                    // XXX: we could use w (32-bit) registers here up to u32
                    "csel {1:x}, {2:x}, {3:x}, NE",
                    in(reg) $selector,
                    inlateout(reg) *$lhs,
                    in(reg) *$rhs,
                    in(reg) *$lhs,
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

    use super::*;
    use rand::{rng, Rng, RngCore};

    #[test]
    fn correctness_u8() {
        let mut rng = rng();
        const ITERATIONS: usize = 10_000;

        for _ in 0..ITERATIONS {
            let selector: bool = rng.random();
            let selector = if selector { 0 } else { rng.next_u32() as u8 };
            let mut lhs = [0u8; 256];
            rng.fill_bytes(&mut lhs);
            let mut rhs = [0u8; 256];
            rng.fill_bytes(&mut rhs);

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
    }

    // XXX: make generic
    #[test]
    fn correctness_u16() {
        let mut rng = rng();
        const ITERATIONS: usize = 10_000;

        for _ in 0..ITERATIONS {
            let selector: bool = rng.random();
            let selector = if selector { 0 } else { rng.next_u32() as u8 };
            let mut lhs = [0u16; 256];
            rng.fill(&mut lhs);
            let mut rhs = [0u16; 256];
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
    }

    // XXX: make generic
    #[test]
    fn correctness_u32() {
        let mut rng = rng();
        const ITERATIONS: usize = 10_000;

        for _i in 0..ITERATIONS {
            std::eprint!("{_i} ");
            let selector: bool = rng.random();
            let selector = if selector { 0 } else { rng.next_u32() as u8 };
            let mut lhs = [0u32; 256];
            rng.fill(&mut lhs);
            let mut rhs = [0u32; 256];
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
        std::eprintln!("");
    }

    // XXX: make generic
    #[test]
    fn correctness_u64() {
        let mut rng = rng();
        const ITERATIONS: usize = 10_000;

        for _i in 0..ITERATIONS {
            std::eprint!("{_i} ");
            let selector: bool = rng.random();
            let selector = if selector { 0 } else { rng.next_u32() as u8 };
            let mut lhs = [0u64; 256];
            rng.fill(&mut lhs);
            let mut rhs = [0u64; 256];
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
        std::eprintln!("");
    }
}
