use core::arch::x86_64::*;

// XXX: A lot of the code below is shared with NEON. Refactor!

/// An avx2 gf128 field element.
#[derive(Clone, Copy)]
pub(crate) struct FieldElement(pub(super) u128);

#[inline]
fn zero() -> FieldElement {
    FieldElement(0)
}

#[inline]
fn load_element(b: &[u8]) -> FieldElement {
    debug_assert!(b.len() == 16);

    FieldElement(u128::from_be_bytes(b.try_into().unwrap()))
}

#[inline]
fn store_element(elem: &FieldElement, b: &mut [u8]) {
    debug_assert!(b.len() == 16);

    b.copy_from_slice(&elem.0.to_be_bytes());
}

#[inline]
fn add(elem: &FieldElement, other: &FieldElement) -> FieldElement {
    FieldElement((*elem).0 ^ (*other).0)
}

// #[inline]
// fn mul_wide(elem: &FieldElement, other: &FieldElement) -> (FieldElement, FieldElement) {
//     let lhs: __m128i = unsafe { core::mem::transmute((*elem).0) };
//     let rhs: __m128i = unsafe { core::mem::transmute((*other).0) };

//     let low = unsafe { _mm_clmulepi64_si128(lhs, rhs, 0x11) };
//     let mid0 = unsafe { _mm_clmulepi64_si128(lhs, rhs, 0x10) };
//     let mid1 = unsafe { _mm_clmulepi64_si128(lhs, rhs, 0x01) };
//     let high = unsafe { _mm_clmulepi64_si128(lhs, rhs, 0x00) };
//     let mid = unsafe { _mm_xor_si128(mid0, mid1) };
//     let m0 = unsafe { _mm_srli_si128(mid, 8) };
//     let m1 = unsafe { _mm_slli_si128(mid, 8) };
//     let low = unsafe { _mm_xor_si128(low, m0) };
//     let high = unsafe { _mm_xor_si128(high, m1) };

//     let low128: u128 = unsafe { core::mem::transmute(low) };
//     let high128: u128 = unsafe { core::mem::transmute(high) };

//     (FieldElement(low128), FieldElement(high128))
// }

/// Performs a 128x128 to 256-bit carry-less multiplication.
///
/// This implementation uses the Karatsuba algorithm to reduce the number of expensive
/// PCLMULQDQ instructions from 4 to 3. On most modern x64 CPUs (Intel Sandy
/// Bridge and newer, AMD Zen and newer), this results in higher performance due to
/// better utilization of execution ports and potentially lower overall latency.
///
/// @param elem The first 128-bit field element.
/// @param other The second 128-bit field element.
/// @returns A tuple `(high, low)` containing the 256-bit result.
#[inline]
fn mul_wide(elem: &FieldElement, other: &FieldElement) -> (FieldElement, FieldElement) {
    // Let the inputs be a = (a_hi << 64) | a_lo and b = (b_hi << 64) | b_lo.
    // The product is (a_hi*b_hi << 128) + ((a_lo*b_hi ^ a_hi*b_lo) << 64) + a_lo*b_lo.
    // The Karatsuba trick computes the middle term using the other two products:
    // (a_lo*b_hi ^ a_hi*b_lo) = (a_lo^a_hi)*(b_lo^b_hi) ^ a_lo*b_lo ^ a_hi*b_hi

    let a: __m128i = unsafe { core::mem::transmute(elem.0) };
    let b: __m128i = unsafe { core::mem::transmute(other.0) };

    // 1. Calculate the low and high 128-bit parts of the product in parallel.
    //    p_lo = a_lo * b_lo
    let p_lo = unsafe { _mm_clmulepi64_si128(a, b, 0x00) };
    //    p_hi = a_hi * b_hi
    let p_hi = unsafe { _mm_clmulepi64_si128(a, b, 0x11) };

    // 2. Calculate the middle term using the third multiplication.
    //    First, prepare the operands (a_lo^a_hi) and (b_lo^b_hi).
    //    Using unpack instructions is an alternative to shuffling.
    let a_xor = unsafe { _mm_xor_si128(_mm_unpackhi_epi64(a, a), _mm_unpacklo_epi64(a, a)) };
    let b_xor = unsafe { _mm_xor_si128(_mm_unpackhi_epi64(b, b), _mm_unpacklo_epi64(b, b)) };

    // Multiply the low 64-bit parts of the XORed results.
    // p_mid_prod = (a_lo^a_hi) * (b_lo^b_hi)
    let p_mid_prod = unsafe { _mm_clmulepi64_si128(a_xor, b_xor, 0x00) };

    // Finish computing the middle term by XORing with p_lo and p_hi.
    let p_mid = unsafe { _mm_xor_si128(_mm_xor_si128(p_mid_prod, p_lo), p_hi) };

    // 3. Combine the parts to get the final 256-bit result.
    //    The middle part is XORed at a 64-bit offset.
    //    res_low  = p_lo ^ (p_mid << 64)
    //    res_high = p_hi ^ (p_mid >> 64)
    let res_low = unsafe { _mm_xor_si128(p_lo, _mm_slli_si128(p_mid, 8)) };
    let res_high = unsafe { _mm_xor_si128(p_hi, _mm_srli_si128(p_mid, 8)) };

    // The original function returned (high_part, low_part). We maintain that order.
    let high_part: u128 = unsafe { core::mem::transmute(res_high) };
    let low_part: u128 = unsafe { core::mem::transmute(res_low) };
    (FieldElement(high_part), FieldElement(low_part))
}

#[inline]
fn reduce(high: &FieldElement, low: &FieldElement) -> FieldElement {
    let high = ((*high).0 << 1) ^ ((*low).0 >> 127);
    let low = (*low).0 << 1;
    let x0_0 = low << 64;
    let x1_x0 = low ^ (x0_0 << 63) ^ (x0_0 << 62) ^ (x0_0 << 57);
    let x1_x0 = x1_x0 ^ (x1_x0 >> 1) ^ (x1_x0 >> 2) ^ (x1_x0 >> 7);
    FieldElement(x1_x0 ^ high)
}

#[inline]
fn mul(x: &FieldElement, y: &FieldElement) -> FieldElement {
    let (high, low) = mul_wide(x, y);
    reduce(&high, &low)
}

impl crate::platform::GF128FieldElement for FieldElement {
    #[inline]
    fn zero() -> Self {
        zero()
    }

    #[inline]
    fn load_element(b: &[u8]) -> Self {
        load_element(b)
    }

    #[inline]
    fn store_element(&self, b: &mut [u8]) {
        store_element(self, b);
    }

    #[inline]
    fn add(&mut self, other: &Self) {
        *self = add(self, other);
    }

    #[inline]
    fn mul(&mut self, other: &Self) {
        *self = mul(self, other)
    }
}

#[cfg(feature = "std")]
#[test]
fn test_transmute() {
    let x = 1u128 << 64 ^ 2u128;
    let xv: __m128i = unsafe { core::mem::transmute(x) };
    let xv: __m128i = unsafe { _mm_slli_si128(xv, 8) };
    let x: u128 = unsafe { core::mem::transmute(xv) };
    std::eprintln!("trans {:x}", x);
    let mut u64s = [0u64; 2];
    unsafe { _mm_storeu_si128(u64s.as_mut_ptr() as *mut __m128i, xv) };
    std::eprintln!("store {:?}", u64s)
}
