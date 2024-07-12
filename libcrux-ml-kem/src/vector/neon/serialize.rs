// SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
//
// SPDX-License-Identifier: Apache-2.0

use super::vector_type::*;
use libcrux_intrinsics::arm64::*;

#[inline(always)]
pub(crate) fn serialize_1(v: SIMD128Vector) -> [u8; 2] {
    let shifter: [i16; 8] = [0, 1, 2, 3, 4, 5, 6, 7];
    let shift = _vld1q_s16(&shifter);
    let low = _vshlq_s16(v.low, shift);
    let high = _vshlq_s16(v.high, shift);
    let low = _vaddvq_s16(low);
    let high = _vaddvq_s16(high);
    [low as u8, high as u8]
}

#[inline(always)]
pub(crate) fn deserialize_1(a: &[u8]) -> SIMD128Vector {
    let one = _vdupq_n_s16(1);
    let low = _vdupq_n_s16(a[0] as i16);
    let high = _vdupq_n_s16(a[1] as i16);
    let shifter: [i16; 8] = [0, 0xff, -2, -3, -4, -5, -6, -7];
    let shift = _vld1q_s16(&shifter);
    let low = _vshlq_s16(low, shift);
    let high = _vshlq_s16(high, shift);
    SIMD128Vector {
        low: _vandq_s16(low, one),
        high: _vandq_s16(high, one),
    }
}

#[inline(always)]
pub(crate) fn serialize_4(v: SIMD128Vector) -> [u8; 8] {
    let shifter: [i16; 8] = [0, 4, 8, 12, 0, 4, 8, 12];
    let shift = _vld1q_s16(&shifter);
    let lowt = _vshlq_u16(_vreinterpretq_u16_s16(v.low), shift);
    let hight = _vshlq_u16(_vreinterpretq_u16_s16(v.high), shift);
    let sum0 = _vaddv_u16(_vget_low_u16(lowt)) as u64;
    let sum1 = _vaddv_u16(_vget_high_u16(lowt)) as u64;
    let sum2 = _vaddv_u16(_vget_low_u16(hight)) as u64;
    let sum3 = _vaddv_u16(_vget_high_u16(hight)) as u64;
    let sum = sum0 | (sum1 << 16) | (sum2 << 32) | (sum3 << 48);
    sum.to_le_bytes()
}

#[inline(always)]
pub(crate) fn deserialize_4(v: &[u8]) -> SIMD128Vector {
    let input = u64::from_le_bytes(v.try_into().unwrap());
    let mut low = [0i16; 8];
    let mut high = [0i16; 8];
    low[0] = (input & 0x0f) as i16;
    low[1] = ((input >> 4) & 0x0f) as i16;
    low[2] = ((input >> 8) & 0x0f) as i16;
    low[3] = ((input >> 12) & 0x0f) as i16;
    low[4] = ((input >> 16) & 0x0f) as i16;
    low[5] = ((input >> 20) & 0x0f) as i16;
    low[6] = ((input >> 24) & 0x0f) as i16;
    low[7] = ((input >> 28) & 0x0f) as i16;
    high[0] = ((input >> 32) & 0x0f) as i16;
    high[1] = ((input >> 36) & 0x0f) as i16;
    high[2] = ((input >> 40) & 0x0f) as i16;
    high[3] = ((input >> 44) & 0x0f) as i16;
    high[4] = ((input >> 48) & 0x0f) as i16;
    high[5] = ((input >> 52) & 0x0f) as i16;
    high[6] = ((input >> 56) & 0x0f) as i16;
    high[7] = ((input >> 60) & 0x0f) as i16;
    SIMD128Vector {
        low: _vld1q_s16(&low),
        high: _vld1q_s16(&high),
    }
}

#[inline(always)]
pub(crate) fn serialize_5(v: SIMD128Vector) -> [u8; 10] {
    let mut res = [0u8; 10];
    let out = to_i16_array(v);
    res[0] = (out[0] | out[1] << 5) as u8;
    res[1] = (out[1] >> 3 | out[2] << 2 | out[3] << 7) as u8;
    res[2] = (out[3] >> 1 | out[4] << 4) as u8;
    res[3] = (out[4] >> 4 | out[5] << 1 | out[6] << 6) as u8;
    res[4] = (out[6] >> 2 | out[7] << 3) as u8;
    res[5] = (out[8 + 0] | out[8 + 1] << 5) as u8;
    res[6] = (out[8 + 1] >> 3 | out[8 + 2] << 2 | out[8 + 3] << 7) as u8;
    res[7] = (out[8 + 3] >> 1 | out[8 + 4] << 4) as u8;
    res[8] = (out[8 + 4] >> 4 | out[8 + 5] << 1 | out[8 + 6] << 6) as u8;
    res[9] = (out[8 + 6] >> 2 | out[8 + 7] << 3) as u8;
    res
}

#[inline(always)]
pub(crate) fn deserialize_5(v: &[u8]) -> SIMD128Vector {
    let mut input0 = [0u8; 8];
    input0[0..5].copy_from_slice(&v[0..5]);
    let low64 = u64::from_le_bytes(input0);
    let mut input1 = [0u8; 8];
    input1[0..5].copy_from_slice(&v[5..10]);
    let high64 = u64::from_le_bytes(input1);

    let mut low = [0i16; 8];
    let mut high = [0i16; 8];

    low[0] = (low64 & 0x1F) as i16;
    low[1] = ((low64 >> 5) & 0x1F) as i16;
    low[2] = ((low64 >> 10) & 0x1F) as i16;
    low[3] = ((low64 >> 15) & 0x1F) as i16;
    low[4] = ((low64 >> 20) & 0x1F) as i16;
    low[5] = ((low64 >> 25) & 0x1F) as i16;
    low[6] = ((low64 >> 30) & 0x1F) as i16;
    low[7] = ((low64 >> 35) & 0x1F) as i16;

    high[0] = (high64 & 0x1F) as i16;
    high[1] = ((high64 >> 5) & 0x1F) as i16;
    high[2] = ((high64 >> 10) & 0x1F) as i16;
    high[3] = ((high64 >> 15) & 0x1F) as i16;
    high[4] = ((high64 >> 20) & 0x1F) as i16;
    high[5] = ((high64 >> 25) & 0x1F) as i16;
    high[6] = ((high64 >> 30) & 0x1F) as i16;
    high[7] = ((high64 >> 35) & 0x1F) as i16;

    SIMD128Vector {
        low: _vld1q_s16(&low),
        high: _vld1q_s16(&high),
    }
}

#[inline(always)]
pub(crate) fn serialize_10(v: SIMD128Vector) -> [u8; 20] {
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
    let mut result = [0u8; 20];
    result[0..5].copy_from_slice(&result32[0..5]);
    result[5..10].copy_from_slice(&result32[8..13]);
    result[10..15].copy_from_slice(&result32[16..21]);
    result[15..20].copy_from_slice(&result32[24..29]);
    result
}

#[inline(always)]
pub(crate) fn deserialize_10(v: &[u8]) -> SIMD128Vector {
    let mut input0 = [0u8; 8];
    let mut input1 = [0u8; 8];
    let mut input2 = [0u8; 4];
    input0.copy_from_slice(&v[0..8]);
    input1.copy_from_slice(&v[8..16]);
    input2.copy_from_slice(&v[16..20]);
    let input0 = u64::from_le_bytes(input0);
    let input1 = u64::from_le_bytes(input1);
    let input2 = u32::from_le_bytes(input2);
    let mut low = [0i16; 8];
    let mut high = [0i16; 8];
    low[0] = (input0 & 0x3ff) as i16;
    low[1] = ((input0 >> 10) & 0x3ff) as i16;
    low[2] = ((input0 >> 20) & 0x3ff) as i16;
    low[3] = ((input0 >> 30) & 0x3ff) as i16;
    low[4] = ((input0 >> 40) & 0x3ff) as i16;
    low[5] = ((input0 >> 50) & 0x3ff) as i16;
    low[6] = (((input0 >> 60) | (input1 << 4)) & 0x3ff) as i16;
    low[7] = ((input1 >> 6) & 0x3ff) as i16;
    high[0] = ((input1 >> 16) & 0x3ff) as i16;
    high[1] = ((input1 >> 26) & 0x3ff) as i16;
    high[2] = ((input1 >> 36) & 0x3ff) as i16;
    high[3] = ((input1 >> 46) & 0x3ff) as i16;
    high[4] = ((((input1 >> 56) as u32) | (input2 << 8)) & 0x3ff) as i16;
    high[5] = ((input2 >> 2) & 0x3ff) as i16;
    high[6] = ((input2 >> 12) & 0x3ff) as i16;
    high[7] = ((input2 >> 22) & 0x3ff) as i16;

    SIMD128Vector {
        low: _vld1q_s16(&low),
        high: _vld1q_s16(&high),
    }
}

#[inline(always)]
pub(crate) fn serialize_11(v: SIMD128Vector) -> [u8; 22] {
    let input = to_i16_array(v);
    let mut result = [0u8; 22];
    result[0] = input[0] as u8; // 3 left in 0
    result[1] = ((input[0] >> 8) | (input[1] << 3)) as u8; // 6 left in 1
    result[2] = ((input[1] >> 5) | (input[2] << 6)) as u8; // 9 left in 2
    result[3] = (input[2] >> 2) as u8; // 1 left in 2
    result[4] = ((input[2] >> 10) | (input[3] << 1)) as u8; // 4 left in 3
    result[5] = ((input[3] >> 7) | (input[4] << 4)) as u8; // 7 left in 4
    result[6] = ((input[4] >> 4) | (input[5] << 7)) as u8; // 10 left in 5
    result[7] = (input[5] >> 1) as u8; // 2 left in 5
    result[8] = ((input[5] >> 9) | (input[6] << 2)) as u8; // 5 left in 6
    result[9] = ((input[6] >> 6) | (input[7] << 5)) as u8; // 8 left in 7
    result[10] = (input[7] >> 3) as u8;

    result[11 + 0] = input[8 + 0] as u8; // 3 left in 0
    result[11 + 1] = ((input[8 + 0] >> 8) | (input[8 + 1] << 3)) as u8; // 6 left in 1
    result[11 + 2] = ((input[8 + 1] >> 5) | (input[8 + 2] << 6)) as u8; // 9 left in 2
    result[11 + 3] = (input[8 + 2] >> 2) as u8; // 1 left in 2
    result[11 + 4] = ((input[8 + 2] >> 10) | (input[8 + 3] << 1)) as u8; // 4 left in 3
    result[11 + 5] = ((input[8 + 3] >> 7) | (input[8 + 4] << 4)) as u8; // 7 left in 4
    result[11 + 6] = ((input[8 + 4] >> 4) | (input[8 + 5] << 7)) as u8; // 10 left in 5
    result[11 + 7] = (input[8 + 5] >> 1) as u8; // 2 left in 5
    result[11 + 8] = ((input[8 + 5] >> 9) | (input[8 + 6] << 2)) as u8; // 5 left in 6
    result[11 + 9] = ((input[8 + 6] >> 6) | (input[8 + 7] << 5)) as u8; // 8 left in 7
    result[11 + 10] = (input[8 + 7] >> 3) as u8;
    result
}

#[inline(always)]
pub(crate) fn deserialize_11(v: &[u8]) -> SIMD128Vector {
    let mut input0 = [0u8; 8];
    let mut input1 = [0u8; 8];
    let mut input2 = [0u8; 8];
    input0.copy_from_slice(&v[0..8]);
    input1.copy_from_slice(&v[8..16]);
    input2[0..6].copy_from_slice(&v[16..22]);
    let input0 = u64::from_le_bytes(input0);
    let input1 = u64::from_le_bytes(input1);
    let input2 = u64::from_le_bytes(input2);

    let mut low = [0i16; 8];
    let mut high = [0i16; 8];

    low[0] = (input0 & 0x7FF) as i16;
    low[1] = ((input0 >> 11) & 0x7FF) as i16;
    low[2] = ((input0 >> 22) & 0x7FF) as i16;
    low[3] = ((input0 >> 33) & 0x7FF) as i16;
    low[4] = ((input0 >> 44) & 0x7FF) as i16;
    low[5] = (((input0 >> 55) | (input1 << 9)) & 0x7FF) as i16;
    low[6] = ((input1 >> 2) & 0x7FF) as i16;
    low[7] = ((input1 >> 13) & 0x7FF) as i16;

    high[0] = ((input1 >> 24) & 0x7FF) as i16;
    high[1] = ((input1 >> 35) & 0x7FF) as i16;
    high[2] = ((input1 >> 46) & 0x7FF) as i16;
    high[3] = (((input1 >> 57) | (input2 << 7)) & 0x7FF) as i16;
    high[4] = ((input2 >> 4) & 0x7FF) as i16;
    high[5] = ((input2 >> 15) & 0x7FF) as i16;
    high[6] = ((input2 >> 26) & 0x7FF) as i16;
    high[7] = ((input2 >> 37) & 0x7FF) as i16;

    SIMD128Vector {
        low: _vld1q_s16(&low),
        high: _vld1q_s16(&high),
    }
}

#[inline(always)]
pub(crate) fn serialize_12(v: SIMD128Vector) -> [u8; 24] {
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
    let mut result = [0u8; 24];
    result[0..6].copy_from_slice(&result32[0..6]);
    result[6..12].copy_from_slice(&result32[8..14]);
    result[12..18].copy_from_slice(&result32[16..22]);
    result[18..24].copy_from_slice(&result32[24..30]);
    result
}

#[inline(always)]
pub(crate) fn deserialize_12(v: &[u8]) -> SIMD128Vector {
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
    let low = _vreinterpretq_s16_u16(_vandq_u16(shifted0, mask12));

    let moved1 = _vreinterpretq_u16_u8(_vqtbl1q_u8(input_vec1, index_vec));
    let shifted1 = _vshlq_u16(moved1, shift_vec);
    let high = _vreinterpretq_s16_u16(_vandq_u16(shifted1, mask12));

    SIMD128Vector { low, high }
}
