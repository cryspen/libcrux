//! Constant time compare for byte-slices
//!
//! Adapted from <https://github.com/celabshq/libcrux/blob/20d3da2a0b06def4e29a7746c00d65f132c63550/libcrux-ml-kem/src/constant_time_ops.rs>-
use core::hint::black_box;

// Returns 1 if value is != 0 and 0 otherwise.
fn is_not_zero(value: u8) -> u8 {
    let value = black_box(value as u16);
    let result = ((!value).wrapping_add(1) >> 8) as u8;
    let res = result & 1;
    // Steer the compiler away from using the information that res is 0 or 1.
    // Using black_box can't guarantee this and is only on a best effort basis.
    black_box(res)
}

// Use inline(never) to additionally steer the compiler from using the
// information that the result can only be 0 or 1.
#[inline(never)]
fn ct_compare_inner(a: &[u8], b: &[u8]) -> u8 {
    // Short-circuiting on the lengths is okay, this is not considered secret
    if a.len() != b.len() {
        return 1;
    }

    let mut difference = 0;
    for i in 0..a.len() {
        difference |= a[i] ^ b[i];
    }
    is_not_zero(difference)
}

/// Compare two byte slices in constant time.
///
/// This function compares the contents of the slices in constant time.
/// The result is a `bool`, so this function is only suitable if it is okay to branch on
/// the result of the comparison and leak the result.
///
/// # Note
/// This short-circuits on the length of the slices. The implementation leaks information about the slices lengths.
pub(crate) fn ct_compare(a: &[u8], b: &[u8]) -> bool {
    // compare_inner returns 0 if the slices are equal
    ct_compare_inner(a, b) == 0
}

#[cfg(test)]
mod tests {
    use crate::ct_ops::{ct_compare, is_not_zero};

    #[test]
    fn test_is_not_zero() {
        assert_eq!(0, is_not_zero(0));

        for i in 1..u8::MAX {
            assert_eq!(1, is_not_zero(i))
        }
    }

    #[test]
    fn test_ct_compare_length_differs() {
        assert!(!ct_compare(&[1, 2], &[1, 2, 3]));
    }

    #[test]
    fn test_ct_compare_equal() {
        assert!(ct_compare(&[1, 2], &[1, 2,]));
    }

    #[test]
    fn test_ct_compare_not_equal() {
        assert!(!ct_compare(&[1, 2], &[2, 2,]));
    }
}
