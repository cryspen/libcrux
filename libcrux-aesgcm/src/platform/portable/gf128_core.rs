pub(crate) type FieldElement = u128;

fn zero() -> FieldElement { 0 }
fn load_elem(b:& [u8]) -> FieldElement {
    debug_assert!(b.len() == 16);
    u128::from_be_bytes(b.try_into().unwrap())
}

fn store_elem(elem:&FieldElement, b:&mut [u8]) {
    debug_assert!(b.len() == 16);
    b.copy_from_slice(&u128::to_be_bytes(*elem));
}
   
fn add(elem: &FieldElement, other:&FieldElement) -> FieldElement {
    elem ^ other
}

fn ith_bit_mask(elem: &FieldElement, i:usize) -> FieldElement {
    debug_assert!(i < 128);
    let bit:u16 = ((elem >> (127 - i)) as u16) & 0x1;
    let bit_mask16 = (!bit).wrapping_add(1);
    let bit_mask32 = (bit_mask16 as u32) ^ ((bit_mask16 as u32) << 16);
    let bit_mask64 = (bit_mask32 as u64) ^ ((bit_mask32 as u64) << 32);
    let bit_mask128 = (bit_mask64 as u128) ^ ((bit_mask64 as u128) << 64);
    bit_mask128
}

const IRRED: FieldElement = 0xE100_0000_0000_0000_0000_0000_0000_0000;

fn mul_x(elem: &mut FieldElement) {
    let mask = ith_bit_mask(elem, 127);
    *elem = (*elem >> 1) ^ (IRRED & mask)
}

fn mul_step(x: &FieldElement, y: &mut FieldElement, i:usize, result: &mut FieldElement) {
    debug_assert!(i < 128);
    let mask = ith_bit_mask(x, i);
    *result ^= (*y & mask);
    mul_x(y);
}

fn mul(x: &FieldElement, y:&FieldElement) -> FieldElement {
    let mut result = 0;
    let mut multiplicand = *y;
    for i in 0..128{
        mul_step(x, &mut multiplicand, i, &mut result)
    }
    result
}

impl crate::platform::GF128FieldElement for FieldElement {
    fn zero() -> Self {
        zero()
    }

    fn load_elem(b:&[u8]) -> Self {
        load_elem(b)
    }

    fn store_elem(&self, b:&mut [u8]) {
        store_elem(self, b);
    }

    fn add(&mut self, other:&Self) {
        *self = add(self, other);
    }

    fn mul(&mut self, other:&Self) {
        *self = mul(self, other)
    }
}
