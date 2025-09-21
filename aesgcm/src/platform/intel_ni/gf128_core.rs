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

#[inline]
fn mul_wide(elem: &FieldElement, other: &FieldElement) -> (FieldElement, FieldElement) {
    let lhs: __m128i = unsafe { core::mem::transmute((*elem).0) };
    let rhs: __m128i = unsafe { core::mem::transmute((*other).0) };
    let low = unsafe { _mm_clmulepi64_si128(lhs, rhs, 0x11) };
    let mid0 = unsafe { _mm_clmulepi64_si128(lhs, rhs, 0x10) };
    let mid1 = unsafe { _mm_clmulepi64_si128(lhs, rhs, 0x01) };
    let high = unsafe { _mm_clmulepi64_si128(lhs, rhs, 0x00) };
    let mid = unsafe { _mm_xor_si128(mid0, mid1) };
    let m0 = unsafe { _mm_srli_si128(mid, 8) };
    let m1 = unsafe { _mm_slli_si128(mid, 8) };
    let low = unsafe { _mm_xor_si128(low, m0) };
    let high = unsafe { _mm_xor_si128(high, m1) };

    let low128: u128 = unsafe { core::mem::transmute(low) };
    let high128: u128 = unsafe { core::mem::transmute(high) };
    (FieldElement(low128), FieldElement(high128))
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
