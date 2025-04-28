use core::arch::aarch64::*;

#[derive(Clone, Copy)]
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
    let l0 = (*elem).0 as u64;
    let h0 = ((*elem).0 >> 64) as u64;
    let l1 = (*other).0 as u64;
    let h1 = ((*other).0 >> 64) as u64;
    let low: u128 = unsafe { vmull_p64(l0, l1) };
    let m1: u128 = unsafe { vmull_p64(l0, h1) };
    let m2: u128 = unsafe { vmull_p64(l1, h0) };
    let high: u128 = unsafe { vmull_p64(h0, h1) };
    let mid = m1 ^ m2;
    let m0 = mid << 64;
    let m1 = mid >> 64;
    let low = low ^ m0;
    let high = high ^ m1;
    (FieldElement(high), FieldElement(low))
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
    let (high, low) = mul_wide(x, y);
    reduce(&high, &low)
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
