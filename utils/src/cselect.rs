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

    /// Return 1 if `value` is not zero and 0 otherwise.
    #[inline(never)] // Don't inline this to avoid that the compiler optimizes this out.
                     // #[hax_lib::ensures(|result| if value == 0 {result == 0} else {result == 1})]
    fn inz(value: u8) -> u8 {
        // #[cfg(hax)]
        // let _orig_value = value; // copy original value for proofs

        let value = value as u16;
        let result = ((!value).wrapping_add(1) >> 8) as u8;
        let res = result & 1;

        // hax_lib::fstar!(
        //     r#"lognot_lemma $value;
        //    logand_lemma (mk_u8 1) $result"#
        // );
        res
    }

    #[inline(never)] // Don't inline this to avoid that the compiler optimizes this out.
                     // #[hax_lib::ensures(|result| if value == 0 {result == 0} else {result == 1})]
    fn is_non_zero(value: u8) -> u8 {
        core::hint::black_box(inz(value))
    }

    impl Select for [u8] {
        fn select(&mut self, other: &Self, selector: u8) {
            let mask = is_non_zero(selector).wrapping_sub(1);
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

    /// Using https://developer.arm.com/documentation/ddi0602/2021-12/Base-Instructions/CSEL--Conditional-Select-
    #[allow(unsafe_code)]
    fn native(lhs: &mut u8, rhs: &u8, selector: u8) {
        unsafe {
            asm! {
                "cmp {0:w}, 0",
                "csel {1:w}, {2:w}, {3:w}, NE",
                in(reg) selector,
                inlateout(reg) *lhs,
                in(reg) *rhs,
                in(reg) *lhs,
                options(pure, nomem, nostack),
            };
        }
    }

    impl Select for [u8] {
        fn select(&mut self, other: &Self, selector: u8) {
            for (lhs, rhs) in self.iter_mut().zip(other.iter()) {
                native(lhs, rhs, selector);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    #[cfg(target_arch = "aarch64")]
    #[test]
    fn correctness() {
        use rand::{rng, Rng, RngCore};

        use crate::cselect::Select;

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
}
