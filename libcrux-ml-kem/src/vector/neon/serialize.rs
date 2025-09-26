use super::*;
use crate::vector::portable::PortableVector;
use libcrux_intrinsics::arm64::*;

#[inline(always)]
pub(crate) fn serialize_1(v: &SIMD128Vector, out: &mut [u8]) {
    debug_assert!(out.len() == 2);

    let shifter: [i16; 8] = [0, 1, 2, 3, 4, 5, 6, 7];
    let shift = _vld1q_s16(&shifter);
    let low = _vshlq_s16(v.low, shift);
    let high = _vshlq_s16(v.high, shift);
    out[0] = _vaddvq_s16(low) as u8;
    out[1] = _vaddvq_s16(high) as u8;
}

#[inline(always)]
pub(crate) fn deserialize_1(a: &[u8], out: &mut SIMD128Vector) {
    let one = _vdupq_n_s16(1);
    let low = _vdupq_n_s16(a[0] as i16);
    let high = _vdupq_n_s16(a[1] as i16);
    let shifter: [i16; 8] = [0, 0xff, -2, -3, -4, -5, -6, -7];
    let shift = _vld1q_s16(&shifter);
    let low = _vshlq_s16(low, shift);
    let high = _vshlq_s16(high, shift);

    out.low = _vandq_s16(low, one);
    out.high = _vandq_s16(high, one);
}

#[inline(always)]
pub(crate) fn serialize_4(v: &SIMD128Vector, out: &mut [u8]) {
    debug_assert!(out.len() == 8);

    let shifter: [i16; 8] = [0, 4, 8, 12, 0, 4, 8, 12];
    let shift = _vld1q_s16(&shifter);
    let lowt = _vshlq_u16(_vreinterpretq_u16_s16(v.low), shift);
    let hight = _vshlq_u16(_vreinterpretq_u16_s16(v.high), shift);
    let sum0 = _vaddv_u16(_vget_low_u16(lowt)) as u64;
    let sum1 = _vaddv_u16(_vget_high_u16(lowt)) as u64;
    let sum2 = _vaddv_u16(_vget_low_u16(hight)) as u64;
    let sum3 = _vaddv_u16(_vget_high_u16(hight)) as u64;
    let sum = sum0 | (sum1 << 16) | (sum2 << 32) | (sum3 << 48);

    out.copy_from_slice(&sum.to_le_bytes());
}

#[inline(always)]
pub(crate) fn deserialize_4(v: &[u8], out: &mut SIMD128Vector) {
    let mut tmp = PortableVector::ZERO();
    PortableVector::deserialize_4(v, &mut tmp);

    let mut input_i16s = [0i16; 16];
    PortableVector::to_i16_array(&tmp, &mut input_i16s);

    out.low = _vld1q_s16(&input_i16s[0..8]);
    out.high = _vld1q_s16(&input_i16s[8..16]);
}

#[inline(always)]
pub(crate) fn serialize_5(v: &SIMD128Vector, out: &mut [u8]) {
    debug_assert!(out.len() == 10);

    let mut out_i16s = [0i16; 16];
    to_i16_array(&v, &mut out_i16s);

    let mut tmp = PortableVector::ZERO();
    PortableVector::from_i16_array(&out_i16s, &mut tmp);

    PortableVector::serialize_5(&tmp, out);
}

#[inline(always)]
pub(crate) fn deserialize_5(v: &[u8], out: &mut SIMD128Vector) {
    let mut tmp = PortableVector::ZERO();
    PortableVector::deserialize_5(v, &mut tmp);

    let mut input_i16s = [0i16; 16];
    PortableVector::to_i16_array(&tmp, &mut input_i16s);

    out.low = _vld1q_s16(&input_i16s[0..8]);
    out.high = _vld1q_s16(&input_i16s[8..16]);
}

#[inline(always)]
pub(crate) fn serialize_10(v: &SIMD128Vector, out: &mut [u8]) {
    debug_assert!(out.len() == 20);

    let low0 = _vreinterpretq_s32_s16(_vtrn1q_s16(v.low, v.low)); // a0, a0, a2, a2, a4, a4, a6, a6
    let low1 = _vreinterpretq_s32_s16(_vtrn2q_s16(v.low, v.low)); // a1, a1, a3, a3, a5, a5, a7, a7
    let mixt = _vsliq_n_s32::<10>(low0, low1); // a1a0, a3a2, a5a4, a7a6

    let low0 = _vreinterpretq_s64_s32(_vtrn1q_s32(mixt, mixt)); // a1a0, a1a0, a5a4, a5a4
    let low1 = _vreinterpretq_s64_s32(_vtrn2q_s32(mixt, mixt)); // a3a2, a3a2, a7a6, a7a6
    let low_mix = _vsliq_n_s64::<20>(low0, low1); // a3a2a1a0, a7a6a5a4

    let high0 = _vreinterpretq_s32_s16(_vtrn1q_s16(v.high, v.high)); // a0, a0, a2, a2, a4, a4, a6, a6
    let high1 = _vreinterpretq_s32_s16(_vtrn2q_s16(v.high, v.high)); // a1, a1, a3, a3, a5, a5, a7, a7
    let mixt = _vsliq_n_s32::<10>(high0, high1); // a1a0, a3a2, a5a4, a7a6

    let high0 = _vreinterpretq_s64_s32(_vtrn1q_s32(mixt, mixt)); // a1a0, a1a0, a5a4, a5a4
    let high1 = _vreinterpretq_s64_s32(_vtrn2q_s32(mixt, mixt)); // a3a2, a3a2, a7a6, a7a6
    let high_mix = _vsliq_n_s64::<20>(high0, high1); // a3a2a1a0, a7a6a5a4

    let mut result32 = [0u8; 32];
    _vst1q_u8(&mut result32[0..16], _vreinterpretq_u8_s64(low_mix));
    _vst1q_u8(&mut result32[16..32], _vreinterpretq_u8_s64(high_mix));

    out[0..5].copy_from_slice(&result32[0..5]);
    out[5..10].copy_from_slice(&result32[8..13]);
    out[10..15].copy_from_slice(&result32[16..21]);
    out[15..20].copy_from_slice(&result32[24..29]);
}

#[inline(always)]
pub(crate) fn deserialize_10(v: &[u8], out: &mut SIMD128Vector) {
    let mut tmp = PortableVector::ZERO();
    PortableVector::deserialize_10(v, &mut tmp);

    let mut input_i16s = [0i16; 16];
    PortableVector::to_i16_array(&tmp, &mut input_i16s);

    out.low = _vld1q_s16(&input_i16s[0..8]);
    out.high = _vld1q_s16(&input_i16s[8..16]);
}

#[inline(always)]
pub(crate) fn serialize_11(v: &SIMD128Vector, out: &mut [u8]) {
    debug_assert!(out.len() == 22);

    let mut out_i16s = [0i16; 16];
    to_i16_array(&v, &mut out_i16s);

    let mut tmp = PortableVector::ZERO();
    PortableVector::from_i16_array(&out_i16s, &mut tmp);

    PortableVector::serialize_11(&tmp, out);
}

#[inline(always)]
pub(crate) fn deserialize_11(v: &[u8], out: &mut SIMD128Vector) {
    let mut tmp = PortableVector::ZERO();
    PortableVector::deserialize_11(v, &mut tmp);

    let mut input_i16s = [0i16; 16];
    PortableVector::to_i16_array(&tmp, &mut input_i16s);

    out.low = _vld1q_s16(&input_i16s[0..8]);
    out.high = _vld1q_s16(&input_i16s[8..16]);
}

#[inline(always)]
pub(crate) fn serialize_12(v: &SIMD128Vector, out: &mut [u8]) {
    debug_assert!(out.len() == 24);

    let low0 = _vreinterpretq_s32_s16(_vtrn1q_s16(v.low, v.low)); // a0, a0, a2, a2, a4, a4, a6, a6
    let low1 = _vreinterpretq_s32_s16(_vtrn2q_s16(v.low, v.low)); // a1, a1, a3, a3, a5, a5, a7, a7
    let mixt = _vsliq_n_s32::<12>(low0, low1); // a1a0, a3a2, a5a4, a7a6

    let low0 = _vreinterpretq_s64_s32(_vtrn1q_s32(mixt, mixt)); // a1a0, a1a0, a5a4, a5a4
    let low1 = _vreinterpretq_s64_s32(_vtrn2q_s32(mixt, mixt)); // a3a2, a3a2, a7a6, a7a6
    let low_mix = _vsliq_n_s64::<24>(low0, low1); // a3a2a1a0, a7a6a5a4

    let high0 = _vreinterpretq_s32_s16(_vtrn1q_s16(v.high, v.high)); // a0, a0, a2, a2, a4, a4, a6, a6
    let high1 = _vreinterpretq_s32_s16(_vtrn2q_s16(v.high, v.high)); // a1, a1, a3, a3, a5, a5, a7, a7
    let mixt = _vsliq_n_s32::<12>(high0, high1); // a1a0, a3a2, a5a4, a7a6

    let high0 = _vreinterpretq_s64_s32(_vtrn1q_s32(mixt, mixt)); // a1a0, a1a0, a5a4, a5a4
    let high1 = _vreinterpretq_s64_s32(_vtrn2q_s32(mixt, mixt)); // a3a2, a3a2, a7a6, a7a6
    let high_mix = _vsliq_n_s64::<24>(high0, high1); // a3a2a1a0, a7a6a5a4

    let mut result32 = [0u8; 32];
    _vst1q_u8(&mut result32[0..16], _vreinterpretq_u8_s64(low_mix));
    _vst1q_u8(&mut result32[16..32], _vreinterpretq_u8_s64(high_mix));

    out[0..6].copy_from_slice(&result32[0..6]);
    out[6..12].copy_from_slice(&result32[8..14]);
    out[12..18].copy_from_slice(&result32[16..22]);
    out[18..24].copy_from_slice(&result32[24..30]);
}

#[inline(always)]
pub(crate) fn deserialize_12(v: &[u8], out: &mut SIMD128Vector) {
    let indexes: [u8; 16] = [0, 1, 1, 2, 3, 4, 4, 5, 6, 7, 7, 8, 9, 10, 10, 11];
    let index_vec = _vld1q_u8(&indexes);
    let shifts: [i16; 8] = [0, -4, 0, -4, 0, -4, 0, -4];
    let shift_vec = _vld1q_s16(&shifts);
    let mask12 = _vdupq_n_u16(0xfff);

    let mut input0 = [0u8; 16];
    input0[0..12].copy_from_slice(&v[0..12]);
    let input_vec0 = _vld1q_u8(&input0);

    let mut input1 = [0u8; 16];
    input1[0..12].copy_from_slice(&v[12..24]);
    let input_vec1 = _vld1q_u8(&input1);

    let moved0 = _vreinterpretq_u16_u8(_vqtbl1q_u8(input_vec0, index_vec));
    let shifted0 = _vshlq_u16(moved0, shift_vec);
    out.low = _vreinterpretq_s16_u16(_vandq_u16(shifted0, mask12));

    let moved1 = _vreinterpretq_u16_u8(_vqtbl1q_u8(input_vec1, index_vec));
    let shifted1 = _vshlq_u16(moved1, shift_vec);
    out.high = _vreinterpretq_s16_u16(_vandq_u16(shifted1, mask12));
}
