#[inline(always)]
pub fn rotate_left128_u32(a: u32, n: u32) -> u32 {
    a.rotate_left(n)
}

#[inline(always)]
pub fn add32(a: u32, b: u32) -> u32 {
    a.wrapping_add(b)
}

#[inline(always)]
pub fn xor32(a: u32, b: u32) -> u32 {
    a ^ b
}

#[inline(always)]
pub fn load32(x: u32) -> u32 {
    x
}

#[inline(always)]
/// No-op
pub fn load32_le(values: [u32; 1]) -> u32 {
    values[0]
}

/// Load a `u8` slice into a `u32`.
///
/// The slice must be `value.len() <= 4`.
/// When the slice is shorter, it is padded with `0`s.
#[inline(always)]
pub fn u32_from_le_bytes(value: &[u8]) -> u32 {
    let mut padded = [0u8; 4];
    padded[0..value.len()].copy_from_slice(value);
    load8_32_le(&padded)
}

/// u32 from u8s le
#[inline(always)]
pub fn load8_32_le(value: &[u8]) -> u32 {
    u32::from_le_bytes(value.try_into().unwrap())
}

/// Store a `u32` into little endian bytes.
///
/// When the output has less than 4 bytes left to write in, only the available
/// number of bytes are written.
#[inline(always)]
pub fn u32_to_le_bytes(out: &mut [u8], value: u32) {
    let mut padded = [0u8; 4];
    store8_32_le_ip(&mut padded, value);
    out.copy_from_slice(&padded[0..out.len()]);
}

#[inline(always)]
pub fn store8_32_le_ip(out: &mut [u8], value: u32) {
    let tmp = value.to_le_bytes();
    for j in 0..4 {
        out[j] = tmp[j];
    }
}
