use core::arch::x86_64::*;

#[derive(Clone,Copy)]
pub struct FieldElement(pub u128);

fn zero() -> FieldElement {
    FieldElement(0)
}

fn load_elem(b: &[u8]) -> FieldElement {
    debug_assert!(b.len() == 16);
    FieldElement(u128::from_be_bytes(b.try_into().unwrap()))
}

fn store_elem(elem: &FieldElement, b: &mut [u8]) {
    debug_assert!(b.len() == 16);
    b.copy_from_slice(&elem.0.to_be_bytes());
}

fn add(elem: &FieldElement, other: &FieldElement) -> FieldElement {
    FieldElement((*elem).0 ^ (*other).0)
}

fn mul_wide(elem: &FieldElement, other: &FieldElement) -> (FieldElement, FieldElement) {
    let lhs : __m128i = unsafe { std::mem::transmute((*elem).0) };
    let rhs : __m128i = unsafe { std::mem::transmute((*other).0) };
    let low = unsafe { _mm_clmulepi64_si128(lhs, rhs, 0x11) };
    let mid0 = unsafe { _mm_clmulepi64_si128(lhs, rhs, 0x10) };
    let mid1 = unsafe { _mm_clmulepi64_si128(lhs, rhs, 0x01) };
    let high = unsafe { _mm_clmulepi64_si128(lhs, rhs, 0x00) };
    let mid = unsafe { _mm_xor_si128(mid0, mid1) };
    let m0 = unsafe { _mm_srli_si128(mid, 8) };
    let m1 = unsafe { _mm_slli_si128(mid, 8) };
    let low = unsafe { _mm_xor_si128(low, m0) };
    let high = unsafe { _mm_xor_si128(high, m1) };

    let low128 : u128 = unsafe { std::mem::transmute(low) };
    let high128 : u128 = unsafe { std::mem::transmute(high) };   
   (FieldElement(low128), FieldElement(high128))
}

fn reduce(high: &FieldElement, low: &FieldElement) -> FieldElement {
    let high = ((*high).0 << 1) ^ ((*low).0 >> 127);
    let low = (*low).0 << 1;
    let x0_0 = low << 64;
    let x1_x0 = low ^ (x0_0 << 63) ^ (x0_0 << 62) ^ (x0_0 << 57);
    let x1_x0 = x1_x0 ^ (x1_x0 >> 1) ^ (x1_x0 >> 2) ^ (x1_x0 >> 7);
    FieldElement(x1_x0 ^ high)
}

fn mul(x: &FieldElement, y: &FieldElement) -> FieldElement {
    let (high,low) = mul_wide(x,y);
    reduce(&high,&low)
}

impl crate::platform::GF128FieldElement for FieldElement {
    fn zero() -> Self {
        zero()
    }

    fn load_elem(b: &[u8]) -> Self {
        load_elem(b)
    }

    fn store_elem(&self, b: &mut [u8]) {
        store_elem(self, b);
    }

    fn add(&mut self, other: &Self) {
        *self = add(self, other);
    }

    fn mul(&mut self, other: &Self) {
        *self = mul(self, other)
    }
}

#[test]
fn test_transmute() {
    let x = 1u128 << 64 ^ 2u128;
    let xv : __m128i = unsafe { std::mem::transmute(x)};
    let xv : __m128i = unsafe { _mm_slli_si128(xv,8)};
    let x : u128 = unsafe { std::mem::transmute(xv)};
    println!("trans {:x}", x);
    let mut u64s = [0u64; 2];
    unsafe { _mm_storeu_si128(u64s.as_mut_ptr() as *mut __m128i, xv)};
    println!("store {:?}", u64s)
}