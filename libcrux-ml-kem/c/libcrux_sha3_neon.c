/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 53530427db2941ce784201e64086766504bc5642
 * Eurydice: d6e4d1bb9c27c4eebbebcb29ba8bea1d58741421
 * Karamel: 2bd16e63cfbfa2b81d3c45d597b811ca2a12d430
 * F*: e5cef6f266ece8a8b55ef4cd9b61cdf103520d38
 * Libcrux: a7de672380a622d67efb35e3707a528e375cbf76
 */

#include "libcrux_sha3_neon.h"

#include "internal/libcrux_core.h"

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for libcrux_intrinsics::arm64_extract::_uint64x2_t)}
*/
static KRML_MUSTINLINE _uint64x2_t zero_f5(void) { return _vdupq_n_u64(0ULL); }

static KRML_MUSTINLINE _uint64x2_t _veor5q_u64(_uint64x2_t a, _uint64x2_t b,
                                               _uint64x2_t c, _uint64x2_t d,
                                               _uint64x2_t e) {
  _uint64x2_t ab = _veorq_u64(a, b);
  _uint64x2_t cd = _veorq_u64(c, d);
  _uint64x2_t abcd = _veorq_u64(ab, cd);
  return _veorq_u64(abcd, e);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for libcrux_intrinsics::arm64_extract::_uint64x2_t)}
*/
static KRML_MUSTINLINE _uint64x2_t xor5_f5(_uint64x2_t a, _uint64x2_t b,
                                           _uint64x2_t c, _uint64x2_t d,
                                           _uint64x2_t e) {
  return _veor5q_u64(a, b, c, d, e);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left
with const generics
- LEFT= 1
- RIGHT= 63
*/
static KRML_MUSTINLINE _uint64x2_t rotate_left_58(_uint64x2_t x) {
  return _veorq_u64(_vshlq_n_u64((int32_t)1, x, _uint64x2_t),
                    _vshrq_n_u64((int32_t)63, x, _uint64x2_t));
}

static KRML_MUSTINLINE _uint64x2_t _vrax1q_u64(_uint64x2_t a, _uint64x2_t b) {
  _uint64x2_t uu____0 = a;
  return _veorq_u64(uu____0, rotate_left_58(b));
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for libcrux_intrinsics::arm64_extract::_uint64x2_t)}
*/
static KRML_MUSTINLINE _uint64x2_t rotate_left1_and_xor_f5(_uint64x2_t a,
                                                           _uint64x2_t b) {
  return _vrax1q_u64(a, b);
}

static KRML_MUSTINLINE _uint64x2_t _vbcaxq_u64(_uint64x2_t a, _uint64x2_t b,
                                               _uint64x2_t c) {
  return _veorq_u64(a, _vbicq_u64(b, c));
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for libcrux_intrinsics::arm64_extract::_uint64x2_t)}
*/
static KRML_MUSTINLINE _uint64x2_t and_not_xor_f5(_uint64x2_t a, _uint64x2_t b,
                                                  _uint64x2_t c) {
  return _vbcaxq_u64(a, b, c);
}

static KRML_MUSTINLINE _uint64x2_t _veorq_n_u64(_uint64x2_t a, uint64_t c) {
  _uint64x2_t c0 = _vdupq_n_u64(c);
  return _veorq_u64(a, c0);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for libcrux_intrinsics::arm64_extract::_uint64x2_t)}
*/
static KRML_MUSTINLINE _uint64x2_t xor_constant_f5(_uint64x2_t a, uint64_t c) {
  return _veorq_n_u64(a, c);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for libcrux_intrinsics::arm64_extract::_uint64x2_t)}
*/
static KRML_MUSTINLINE _uint64x2_t xor_f5(_uint64x2_t a, _uint64x2_t b) {
  return _veorq_u64(a, b);
}

static KRML_MUSTINLINE void slice_2(Eurydice_slice a[2U], size_t start,
                                    size_t len, Eurydice_slice ret[2U]) {
  ret[0U] = Eurydice_slice_subslice2(a[0U], start, start + len, uint8_t,
                                     Eurydice_slice);
  ret[1U] = Eurydice_slice_subslice2(a[1U], start, start + len, uint8_t,
                                     Eurydice_slice);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for libcrux_intrinsics::arm64_extract::_uint64x2_t)}
*/
static KRML_MUSTINLINE void slice_n_f5(Eurydice_slice a[2U], size_t start,
                                       size_t len, Eurydice_slice ret[2U]) {
  Eurydice_slice uu____0[2U];
  memcpy(uu____0, a, (size_t)2U * sizeof(Eurydice_slice));
  Eurydice_slice ret0[2U];
  slice_2(uu____0, start, len, ret0);
  memcpy(ret, ret0, (size_t)2U * sizeof(Eurydice_slice));
}

static KRML_MUSTINLINE Eurydice_slice_uint8_t_2size_t__x2
split_at_mut_2(Eurydice_slice out[2U], size_t mid) {
  Eurydice_slice out0 = out[0U];
  Eurydice_slice out1 = out[1U];
  Eurydice_slice_uint8_t_x2 uu____0 = core_slice___Slice_T___split_at_mut(
      out0, mid, uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice out00 = uu____0.fst;
  Eurydice_slice out01 = uu____0.snd;
  Eurydice_slice_uint8_t_x2 uu____1 = core_slice___Slice_T___split_at_mut(
      out1, mid, uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice out10 = uu____1.fst;
  Eurydice_slice out11 = uu____1.snd;
  Eurydice_slice_uint8_t_2size_t__x2 lit;
  lit.fst[0U] = out00;
  lit.fst[1U] = out10;
  lit.snd[0U] = out01;
  lit.snd[1U] = out11;
  return lit;
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for libcrux_intrinsics::arm64_extract::_uint64x2_t)}
*/
static KRML_MUSTINLINE Eurydice_slice_uint8_t_2size_t__x2
split_at_mut_n_f5(Eurydice_slice a[2U], size_t mid) {
  return split_at_mut_2(a, mid);
}

/**
 Create a new Shake128 x4 state.
*/
/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0]#1}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.new_1e
with types libcrux_intrinsics_arm64_extract__uint64x2_t
with const generics
- N= 2
*/
static KRML_MUSTINLINE libcrux_sha3_generic_keccak_KeccakState_cc
new_1e_ff(void) {
  libcrux_sha3_generic_keccak_KeccakState_cc lit;
  lit.st[0U][0U] = zero_f5();
  lit.st[0U][1U] = zero_f5();
  lit.st[0U][2U] = zero_f5();
  lit.st[0U][3U] = zero_f5();
  lit.st[0U][4U] = zero_f5();
  lit.st[1U][0U] = zero_f5();
  lit.st[1U][1U] = zero_f5();
  lit.st[1U][2U] = zero_f5();
  lit.st[1U][3U] = zero_f5();
  lit.st[1U][4U] = zero_f5();
  lit.st[2U][0U] = zero_f5();
  lit.st[2U][1U] = zero_f5();
  lit.st[2U][2U] = zero_f5();
  lit.st[2U][3U] = zero_f5();
  lit.st[2U][4U] = zero_f5();
  lit.st[3U][0U] = zero_f5();
  lit.st[3U][1U] = zero_f5();
  lit.st[3U][2U] = zero_f5();
  lit.st[3U][3U] = zero_f5();
  lit.st[3U][4U] = zero_f5();
  lit.st[4U][0U] = zero_f5();
  lit.st[4U][1U] = zero_f5();
  lit.st[4U][2U] = zero_f5();
  lit.st[4U][3U] = zero_f5();
  lit.st[4U][4U] = zero_f5();
  return lit;
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block
with const generics
- RATE= 72
*/
static KRML_MUSTINLINE void load_block_3c(_uint64x2_t (*s)[5U],
                                          Eurydice_slice blocks[2U]) {
  for (size_t i = (size_t)0U; i < (size_t)72U / (size_t)16U; i++) {
    size_t i0 = i;
    _uint64x2_t v0 = _vld1q_bytes_u64(Eurydice_slice_subslice2(
        blocks[0U], (size_t)16U * i0, (size_t)16U * (i0 + (size_t)1U), uint8_t,
        Eurydice_slice));
    _uint64x2_t v1 = _vld1q_bytes_u64(Eurydice_slice_subslice2(
        blocks[1U], (size_t)16U * i0, (size_t)16U * (i0 + (size_t)1U), uint8_t,
        Eurydice_slice));
    s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U] = _veorq_u64(
        s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U],
        _vtrn1q_u64(v0, v1));
    s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
     [((size_t)2U * i0 + (size_t)1U) % (size_t)5U] =
         _veorq_u64(s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
                     [((size_t)2U * i0 + (size_t)1U) % (size_t)5U],
                    _vtrn2q_u64(v0, v1));
  }
  if ((size_t)72U % (size_t)16U != (size_t)0U) {
    size_t i = ((size_t)72U / (size_t)8U - (size_t)1U) / (size_t)5U;
    size_t j = ((size_t)72U / (size_t)8U - (size_t)1U) % (size_t)5U;
    uint64_t u[2U] = {0U};
    uint8_t uu____0[8U];
    core_result_Result_56 dst0;
    Eurydice_slice_to_array2(
        &dst0,
        Eurydice_slice_subslice2(blocks[0U], (size_t)72U - (size_t)8U,
                                 (size_t)72U, uint8_t, Eurydice_slice),
        Eurydice_slice, uint8_t[8U], void *);
    core_result_unwrap_41_ac(dst0, uu____0);
    u[0U] = core_num__u64_9__from_le_bytes(uu____0);
    uint8_t uu____1[8U];
    core_result_Result_56 dst;
    Eurydice_slice_to_array2(
        &dst,
        Eurydice_slice_subslice2(blocks[1U], (size_t)72U - (size_t)8U,
                                 (size_t)72U, uint8_t, Eurydice_slice),
        Eurydice_slice, uint8_t[8U], void *);
    core_result_unwrap_41_ac(dst, uu____1);
    u[1U] = core_num__u64_9__from_le_bytes(uu____1);
    _uint64x2_t uvec = _vld1q_u64(
        Eurydice_array_to_slice((size_t)2U, u, uint64_t, Eurydice_slice));
    s[i][j] = _veorq_u64(s[i][j], uvec);
  }
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for libcrux_intrinsics::arm64_extract::_uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block_f5
with const generics
- BLOCKSIZE= 72
*/
static KRML_MUSTINLINE void load_block_f5_0f(_uint64x2_t (*a)[5U],
                                             Eurydice_slice b[2U]) {
  _uint64x2_t(*uu____0)[5U] = a;
  Eurydice_slice uu____1[2U];
  memcpy(uu____1, b, (size_t)2U * sizeof(Eurydice_slice));
  load_block_3c(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left
with const generics
- LEFT= 36
- RIGHT= 28
*/
static KRML_MUSTINLINE _uint64x2_t rotate_left_580(_uint64x2_t x) {
  return _veorq_u64(_vshlq_n_u64((int32_t)36, x, _uint64x2_t),
                    _vshrq_n_u64((int32_t)28, x, _uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 36
- RIGHT= 28
*/
static KRML_MUSTINLINE _uint64x2_t _vxarq_u64_c1(_uint64x2_t a, _uint64x2_t b) {
  _uint64x2_t ab = _veorq_u64(a, b);
  return rotate_left_580(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for libcrux_intrinsics::arm64_extract::_uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_f5
with const generics
- LEFT= 36
- RIGHT= 28
*/
static KRML_MUSTINLINE _uint64x2_t xor_and_rotate_f5_1f(_uint64x2_t a,
                                                        _uint64x2_t b) {
  return _vxarq_u64_c1(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left
with const generics
- LEFT= 3
- RIGHT= 61
*/
static KRML_MUSTINLINE _uint64x2_t rotate_left_581(_uint64x2_t x) {
  return _veorq_u64(_vshlq_n_u64((int32_t)3, x, _uint64x2_t),
                    _vshrq_n_u64((int32_t)61, x, _uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 3
- RIGHT= 61
*/
static KRML_MUSTINLINE _uint64x2_t _vxarq_u64_c10(_uint64x2_t a,
                                                  _uint64x2_t b) {
  _uint64x2_t ab = _veorq_u64(a, b);
  return rotate_left_581(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for libcrux_intrinsics::arm64_extract::_uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_f5
with const generics
- LEFT= 3
- RIGHT= 61
*/
static KRML_MUSTINLINE _uint64x2_t xor_and_rotate_f5_1f0(_uint64x2_t a,
                                                         _uint64x2_t b) {
  return _vxarq_u64_c10(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left
with const generics
- LEFT= 41
- RIGHT= 23
*/
static KRML_MUSTINLINE _uint64x2_t rotate_left_582(_uint64x2_t x) {
  return _veorq_u64(_vshlq_n_u64((int32_t)41, x, _uint64x2_t),
                    _vshrq_n_u64((int32_t)23, x, _uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 41
- RIGHT= 23
*/
static KRML_MUSTINLINE _uint64x2_t _vxarq_u64_c11(_uint64x2_t a,
                                                  _uint64x2_t b) {
  _uint64x2_t ab = _veorq_u64(a, b);
  return rotate_left_582(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for libcrux_intrinsics::arm64_extract::_uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_f5
with const generics
- LEFT= 41
- RIGHT= 23
*/
static KRML_MUSTINLINE _uint64x2_t xor_and_rotate_f5_1f1(_uint64x2_t a,
                                                         _uint64x2_t b) {
  return _vxarq_u64_c11(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left
with const generics
- LEFT= 18
- RIGHT= 46
*/
static KRML_MUSTINLINE _uint64x2_t rotate_left_583(_uint64x2_t x) {
  return _veorq_u64(_vshlq_n_u64((int32_t)18, x, _uint64x2_t),
                    _vshrq_n_u64((int32_t)46, x, _uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 18
- RIGHT= 46
*/
static KRML_MUSTINLINE _uint64x2_t _vxarq_u64_c12(_uint64x2_t a,
                                                  _uint64x2_t b) {
  _uint64x2_t ab = _veorq_u64(a, b);
  return rotate_left_583(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for libcrux_intrinsics::arm64_extract::_uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_f5
with const generics
- LEFT= 18
- RIGHT= 46
*/
static KRML_MUSTINLINE _uint64x2_t xor_and_rotate_f5_1f2(_uint64x2_t a,
                                                         _uint64x2_t b) {
  return _vxarq_u64_c12(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 1
- RIGHT= 63
*/
static KRML_MUSTINLINE _uint64x2_t _vxarq_u64_c13(_uint64x2_t a,
                                                  _uint64x2_t b) {
  _uint64x2_t ab = _veorq_u64(a, b);
  return rotate_left_58(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for libcrux_intrinsics::arm64_extract::_uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_f5
with const generics
- LEFT= 1
- RIGHT= 63
*/
static KRML_MUSTINLINE _uint64x2_t xor_and_rotate_f5_1f3(_uint64x2_t a,
                                                         _uint64x2_t b) {
  return _vxarq_u64_c13(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left
with const generics
- LEFT= 44
- RIGHT= 20
*/
static KRML_MUSTINLINE _uint64x2_t rotate_left_584(_uint64x2_t x) {
  return _veorq_u64(_vshlq_n_u64((int32_t)44, x, _uint64x2_t),
                    _vshrq_n_u64((int32_t)20, x, _uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 44
- RIGHT= 20
*/
static KRML_MUSTINLINE _uint64x2_t _vxarq_u64_c14(_uint64x2_t a,
                                                  _uint64x2_t b) {
  _uint64x2_t ab = _veorq_u64(a, b);
  return rotate_left_584(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for libcrux_intrinsics::arm64_extract::_uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_f5
with const generics
- LEFT= 44
- RIGHT= 20
*/
static KRML_MUSTINLINE _uint64x2_t xor_and_rotate_f5_1f4(_uint64x2_t a,
                                                         _uint64x2_t b) {
  return _vxarq_u64_c14(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left
with const generics
- LEFT= 10
- RIGHT= 54
*/
static KRML_MUSTINLINE _uint64x2_t rotate_left_585(_uint64x2_t x) {
  return _veorq_u64(_vshlq_n_u64((int32_t)10, x, _uint64x2_t),
                    _vshrq_n_u64((int32_t)54, x, _uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 10
- RIGHT= 54
*/
static KRML_MUSTINLINE _uint64x2_t _vxarq_u64_c15(_uint64x2_t a,
                                                  _uint64x2_t b) {
  _uint64x2_t ab = _veorq_u64(a, b);
  return rotate_left_585(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for libcrux_intrinsics::arm64_extract::_uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_f5
with const generics
- LEFT= 10
- RIGHT= 54
*/
static KRML_MUSTINLINE _uint64x2_t xor_and_rotate_f5_1f5(_uint64x2_t a,
                                                         _uint64x2_t b) {
  return _vxarq_u64_c15(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left
with const generics
- LEFT= 45
- RIGHT= 19
*/
static KRML_MUSTINLINE _uint64x2_t rotate_left_586(_uint64x2_t x) {
  return _veorq_u64(_vshlq_n_u64((int32_t)45, x, _uint64x2_t),
                    _vshrq_n_u64((int32_t)19, x, _uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 45
- RIGHT= 19
*/
static KRML_MUSTINLINE _uint64x2_t _vxarq_u64_c16(_uint64x2_t a,
                                                  _uint64x2_t b) {
  _uint64x2_t ab = _veorq_u64(a, b);
  return rotate_left_586(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for libcrux_intrinsics::arm64_extract::_uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_f5
with const generics
- LEFT= 45
- RIGHT= 19
*/
static KRML_MUSTINLINE _uint64x2_t xor_and_rotate_f5_1f6(_uint64x2_t a,
                                                         _uint64x2_t b) {
  return _vxarq_u64_c16(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left
with const generics
- LEFT= 2
- RIGHT= 62
*/
static KRML_MUSTINLINE _uint64x2_t rotate_left_587(_uint64x2_t x) {
  return _veorq_u64(_vshlq_n_u64((int32_t)2, x, _uint64x2_t),
                    _vshrq_n_u64((int32_t)62, x, _uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 2
- RIGHT= 62
*/
static KRML_MUSTINLINE _uint64x2_t _vxarq_u64_c17(_uint64x2_t a,
                                                  _uint64x2_t b) {
  _uint64x2_t ab = _veorq_u64(a, b);
  return rotate_left_587(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for libcrux_intrinsics::arm64_extract::_uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_f5
with const generics
- LEFT= 2
- RIGHT= 62
*/
static KRML_MUSTINLINE _uint64x2_t xor_and_rotate_f5_1f7(_uint64x2_t a,
                                                         _uint64x2_t b) {
  return _vxarq_u64_c17(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left
with const generics
- LEFT= 62
- RIGHT= 2
*/
static KRML_MUSTINLINE _uint64x2_t rotate_left_588(_uint64x2_t x) {
  return _veorq_u64(_vshlq_n_u64((int32_t)62, x, _uint64x2_t),
                    _vshrq_n_u64((int32_t)2, x, _uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 62
- RIGHT= 2
*/
static KRML_MUSTINLINE _uint64x2_t _vxarq_u64_c18(_uint64x2_t a,
                                                  _uint64x2_t b) {
  _uint64x2_t ab = _veorq_u64(a, b);
  return rotate_left_588(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for libcrux_intrinsics::arm64_extract::_uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_f5
with const generics
- LEFT= 62
- RIGHT= 2
*/
static KRML_MUSTINLINE _uint64x2_t xor_and_rotate_f5_1f8(_uint64x2_t a,
                                                         _uint64x2_t b) {
  return _vxarq_u64_c18(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left
with const generics
- LEFT= 6
- RIGHT= 58
*/
static KRML_MUSTINLINE _uint64x2_t rotate_left_589(_uint64x2_t x) {
  return _veorq_u64(_vshlq_n_u64((int32_t)6, x, _uint64x2_t),
                    _vshrq_n_u64((int32_t)58, x, _uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 6
- RIGHT= 58
*/
static KRML_MUSTINLINE _uint64x2_t _vxarq_u64_c19(_uint64x2_t a,
                                                  _uint64x2_t b) {
  _uint64x2_t ab = _veorq_u64(a, b);
  return rotate_left_589(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for libcrux_intrinsics::arm64_extract::_uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_f5
with const generics
- LEFT= 6
- RIGHT= 58
*/
static KRML_MUSTINLINE _uint64x2_t xor_and_rotate_f5_1f9(_uint64x2_t a,
                                                         _uint64x2_t b) {
  return _vxarq_u64_c19(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left
with const generics
- LEFT= 43
- RIGHT= 21
*/
static KRML_MUSTINLINE _uint64x2_t rotate_left_5810(_uint64x2_t x) {
  return _veorq_u64(_vshlq_n_u64((int32_t)43, x, _uint64x2_t),
                    _vshrq_n_u64((int32_t)21, x, _uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 43
- RIGHT= 21
*/
static KRML_MUSTINLINE _uint64x2_t _vxarq_u64_c110(_uint64x2_t a,
                                                   _uint64x2_t b) {
  _uint64x2_t ab = _veorq_u64(a, b);
  return rotate_left_5810(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for libcrux_intrinsics::arm64_extract::_uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_f5
with const generics
- LEFT= 43
- RIGHT= 21
*/
static KRML_MUSTINLINE _uint64x2_t xor_and_rotate_f5_1f10(_uint64x2_t a,
                                                          _uint64x2_t b) {
  return _vxarq_u64_c110(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left
with const generics
- LEFT= 15
- RIGHT= 49
*/
static KRML_MUSTINLINE _uint64x2_t rotate_left_5811(_uint64x2_t x) {
  return _veorq_u64(_vshlq_n_u64((int32_t)15, x, _uint64x2_t),
                    _vshrq_n_u64((int32_t)49, x, _uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 15
- RIGHT= 49
*/
static KRML_MUSTINLINE _uint64x2_t _vxarq_u64_c111(_uint64x2_t a,
                                                   _uint64x2_t b) {
  _uint64x2_t ab = _veorq_u64(a, b);
  return rotate_left_5811(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for libcrux_intrinsics::arm64_extract::_uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_f5
with const generics
- LEFT= 15
- RIGHT= 49
*/
static KRML_MUSTINLINE _uint64x2_t xor_and_rotate_f5_1f11(_uint64x2_t a,
                                                          _uint64x2_t b) {
  return _vxarq_u64_c111(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left
with const generics
- LEFT= 61
- RIGHT= 3
*/
static KRML_MUSTINLINE _uint64x2_t rotate_left_5812(_uint64x2_t x) {
  return _veorq_u64(_vshlq_n_u64((int32_t)61, x, _uint64x2_t),
                    _vshrq_n_u64((int32_t)3, x, _uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 61
- RIGHT= 3
*/
static KRML_MUSTINLINE _uint64x2_t _vxarq_u64_c112(_uint64x2_t a,
                                                   _uint64x2_t b) {
  _uint64x2_t ab = _veorq_u64(a, b);
  return rotate_left_5812(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for libcrux_intrinsics::arm64_extract::_uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_f5
with const generics
- LEFT= 61
- RIGHT= 3
*/
static KRML_MUSTINLINE _uint64x2_t xor_and_rotate_f5_1f12(_uint64x2_t a,
                                                          _uint64x2_t b) {
  return _vxarq_u64_c112(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left
with const generics
- LEFT= 28
- RIGHT= 36
*/
static KRML_MUSTINLINE _uint64x2_t rotate_left_5813(_uint64x2_t x) {
  return _veorq_u64(_vshlq_n_u64((int32_t)28, x, _uint64x2_t),
                    _vshrq_n_u64((int32_t)36, x, _uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 28
- RIGHT= 36
*/
static KRML_MUSTINLINE _uint64x2_t _vxarq_u64_c113(_uint64x2_t a,
                                                   _uint64x2_t b) {
  _uint64x2_t ab = _veorq_u64(a, b);
  return rotate_left_5813(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for libcrux_intrinsics::arm64_extract::_uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_f5
with const generics
- LEFT= 28
- RIGHT= 36
*/
static KRML_MUSTINLINE _uint64x2_t xor_and_rotate_f5_1f13(_uint64x2_t a,
                                                          _uint64x2_t b) {
  return _vxarq_u64_c113(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left
with const generics
- LEFT= 55
- RIGHT= 9
*/
static KRML_MUSTINLINE _uint64x2_t rotate_left_5814(_uint64x2_t x) {
  return _veorq_u64(_vshlq_n_u64((int32_t)55, x, _uint64x2_t),
                    _vshrq_n_u64((int32_t)9, x, _uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 55
- RIGHT= 9
*/
static KRML_MUSTINLINE _uint64x2_t _vxarq_u64_c114(_uint64x2_t a,
                                                   _uint64x2_t b) {
  _uint64x2_t ab = _veorq_u64(a, b);
  return rotate_left_5814(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for libcrux_intrinsics::arm64_extract::_uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_f5
with const generics
- LEFT= 55
- RIGHT= 9
*/
static KRML_MUSTINLINE _uint64x2_t xor_and_rotate_f5_1f14(_uint64x2_t a,
                                                          _uint64x2_t b) {
  return _vxarq_u64_c114(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left
with const generics
- LEFT= 25
- RIGHT= 39
*/
static KRML_MUSTINLINE _uint64x2_t rotate_left_5815(_uint64x2_t x) {
  return _veorq_u64(_vshlq_n_u64((int32_t)25, x, _uint64x2_t),
                    _vshrq_n_u64((int32_t)39, x, _uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 25
- RIGHT= 39
*/
static KRML_MUSTINLINE _uint64x2_t _vxarq_u64_c115(_uint64x2_t a,
                                                   _uint64x2_t b) {
  _uint64x2_t ab = _veorq_u64(a, b);
  return rotate_left_5815(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for libcrux_intrinsics::arm64_extract::_uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_f5
with const generics
- LEFT= 25
- RIGHT= 39
*/
static KRML_MUSTINLINE _uint64x2_t xor_and_rotate_f5_1f15(_uint64x2_t a,
                                                          _uint64x2_t b) {
  return _vxarq_u64_c115(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left
with const generics
- LEFT= 21
- RIGHT= 43
*/
static KRML_MUSTINLINE _uint64x2_t rotate_left_5816(_uint64x2_t x) {
  return _veorq_u64(_vshlq_n_u64((int32_t)21, x, _uint64x2_t),
                    _vshrq_n_u64((int32_t)43, x, _uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 21
- RIGHT= 43
*/
static KRML_MUSTINLINE _uint64x2_t _vxarq_u64_c116(_uint64x2_t a,
                                                   _uint64x2_t b) {
  _uint64x2_t ab = _veorq_u64(a, b);
  return rotate_left_5816(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for libcrux_intrinsics::arm64_extract::_uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_f5
with const generics
- LEFT= 21
- RIGHT= 43
*/
static KRML_MUSTINLINE _uint64x2_t xor_and_rotate_f5_1f16(_uint64x2_t a,
                                                          _uint64x2_t b) {
  return _vxarq_u64_c116(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left
with const generics
- LEFT= 56
- RIGHT= 8
*/
static KRML_MUSTINLINE _uint64x2_t rotate_left_5817(_uint64x2_t x) {
  return _veorq_u64(_vshlq_n_u64((int32_t)56, x, _uint64x2_t),
                    _vshrq_n_u64((int32_t)8, x, _uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 56
- RIGHT= 8
*/
static KRML_MUSTINLINE _uint64x2_t _vxarq_u64_c117(_uint64x2_t a,
                                                   _uint64x2_t b) {
  _uint64x2_t ab = _veorq_u64(a, b);
  return rotate_left_5817(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for libcrux_intrinsics::arm64_extract::_uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_f5
with const generics
- LEFT= 56
- RIGHT= 8
*/
static KRML_MUSTINLINE _uint64x2_t xor_and_rotate_f5_1f17(_uint64x2_t a,
                                                          _uint64x2_t b) {
  return _vxarq_u64_c117(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left
with const generics
- LEFT= 27
- RIGHT= 37
*/
static KRML_MUSTINLINE _uint64x2_t rotate_left_5818(_uint64x2_t x) {
  return _veorq_u64(_vshlq_n_u64((int32_t)27, x, _uint64x2_t),
                    _vshrq_n_u64((int32_t)37, x, _uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 27
- RIGHT= 37
*/
static KRML_MUSTINLINE _uint64x2_t _vxarq_u64_c118(_uint64x2_t a,
                                                   _uint64x2_t b) {
  _uint64x2_t ab = _veorq_u64(a, b);
  return rotate_left_5818(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for libcrux_intrinsics::arm64_extract::_uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_f5
with const generics
- LEFT= 27
- RIGHT= 37
*/
static KRML_MUSTINLINE _uint64x2_t xor_and_rotate_f5_1f18(_uint64x2_t a,
                                                          _uint64x2_t b) {
  return _vxarq_u64_c118(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left
with const generics
- LEFT= 20
- RIGHT= 44
*/
static KRML_MUSTINLINE _uint64x2_t rotate_left_5819(_uint64x2_t x) {
  return _veorq_u64(_vshlq_n_u64((int32_t)20, x, _uint64x2_t),
                    _vshrq_n_u64((int32_t)44, x, _uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 20
- RIGHT= 44
*/
static KRML_MUSTINLINE _uint64x2_t _vxarq_u64_c119(_uint64x2_t a,
                                                   _uint64x2_t b) {
  _uint64x2_t ab = _veorq_u64(a, b);
  return rotate_left_5819(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for libcrux_intrinsics::arm64_extract::_uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_f5
with const generics
- LEFT= 20
- RIGHT= 44
*/
static KRML_MUSTINLINE _uint64x2_t xor_and_rotate_f5_1f19(_uint64x2_t a,
                                                          _uint64x2_t b) {
  return _vxarq_u64_c119(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left
with const generics
- LEFT= 39
- RIGHT= 25
*/
static KRML_MUSTINLINE _uint64x2_t rotate_left_5820(_uint64x2_t x) {
  return _veorq_u64(_vshlq_n_u64((int32_t)39, x, _uint64x2_t),
                    _vshrq_n_u64((int32_t)25, x, _uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 39
- RIGHT= 25
*/
static KRML_MUSTINLINE _uint64x2_t _vxarq_u64_c120(_uint64x2_t a,
                                                   _uint64x2_t b) {
  _uint64x2_t ab = _veorq_u64(a, b);
  return rotate_left_5820(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for libcrux_intrinsics::arm64_extract::_uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_f5
with const generics
- LEFT= 39
- RIGHT= 25
*/
static KRML_MUSTINLINE _uint64x2_t xor_and_rotate_f5_1f20(_uint64x2_t a,
                                                          _uint64x2_t b) {
  return _vxarq_u64_c120(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left
with const generics
- LEFT= 8
- RIGHT= 56
*/
static KRML_MUSTINLINE _uint64x2_t rotate_left_5821(_uint64x2_t x) {
  return _veorq_u64(_vshlq_n_u64((int32_t)8, x, _uint64x2_t),
                    _vshrq_n_u64((int32_t)56, x, _uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 8
- RIGHT= 56
*/
static KRML_MUSTINLINE _uint64x2_t _vxarq_u64_c121(_uint64x2_t a,
                                                   _uint64x2_t b) {
  _uint64x2_t ab = _veorq_u64(a, b);
  return rotate_left_5821(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for libcrux_intrinsics::arm64_extract::_uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_f5
with const generics
- LEFT= 8
- RIGHT= 56
*/
static KRML_MUSTINLINE _uint64x2_t xor_and_rotate_f5_1f21(_uint64x2_t a,
                                                          _uint64x2_t b) {
  return _vxarq_u64_c121(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left
with const generics
- LEFT= 14
- RIGHT= 50
*/
static KRML_MUSTINLINE _uint64x2_t rotate_left_5822(_uint64x2_t x) {
  return _veorq_u64(_vshlq_n_u64((int32_t)14, x, _uint64x2_t),
                    _vshrq_n_u64((int32_t)50, x, _uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 14
- RIGHT= 50
*/
static KRML_MUSTINLINE _uint64x2_t _vxarq_u64_c122(_uint64x2_t a,
                                                   _uint64x2_t b) {
  _uint64x2_t ab = _veorq_u64(a, b);
  return rotate_left_5822(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for libcrux_intrinsics::arm64_extract::_uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_f5
with const generics
- LEFT= 14
- RIGHT= 50
*/
static KRML_MUSTINLINE _uint64x2_t xor_and_rotate_f5_1f22(_uint64x2_t a,
                                                          _uint64x2_t b) {
  return _vxarq_u64_c122(a, b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.theta_rho
with types libcrux_intrinsics_arm64_extract__uint64x2_t
with const generics
- N= 2
*/
static KRML_MUSTINLINE void theta_rho_f5(
    libcrux_sha3_generic_keccak_KeccakState_cc *s) {
  _uint64x2_t c[5U] = {xor5_f5(s->st[0U][0U], s->st[1U][0U], s->st[2U][0U],
                               s->st[3U][0U], s->st[4U][0U]),
                       xor5_f5(s->st[0U][1U], s->st[1U][1U], s->st[2U][1U],
                               s->st[3U][1U], s->st[4U][1U]),
                       xor5_f5(s->st[0U][2U], s->st[1U][2U], s->st[2U][2U],
                               s->st[3U][2U], s->st[4U][2U]),
                       xor5_f5(s->st[0U][3U], s->st[1U][3U], s->st[2U][3U],
                               s->st[3U][3U], s->st[4U][3U]),
                       xor5_f5(s->st[0U][4U], s->st[1U][4U], s->st[2U][4U],
                               s->st[3U][4U], s->st[4U][4U])};
  _uint64x2_t uu____0 =
      rotate_left1_and_xor_f5(c[((size_t)0U + (size_t)4U) % (size_t)5U],
                              c[((size_t)0U + (size_t)1U) % (size_t)5U]);
  _uint64x2_t uu____1 =
      rotate_left1_and_xor_f5(c[((size_t)1U + (size_t)4U) % (size_t)5U],
                              c[((size_t)1U + (size_t)1U) % (size_t)5U]);
  _uint64x2_t uu____2 =
      rotate_left1_and_xor_f5(c[((size_t)2U + (size_t)4U) % (size_t)5U],
                              c[((size_t)2U + (size_t)1U) % (size_t)5U]);
  _uint64x2_t uu____3 =
      rotate_left1_and_xor_f5(c[((size_t)3U + (size_t)4U) % (size_t)5U],
                              c[((size_t)3U + (size_t)1U) % (size_t)5U]);
  _uint64x2_t t[5U] = {
      uu____0, uu____1, uu____2, uu____3,
      rotate_left1_and_xor_f5(c[((size_t)4U + (size_t)4U) % (size_t)5U],
                              c[((size_t)4U + (size_t)1U) % (size_t)5U])};
  s->st[0U][0U] = xor_f5(s->st[0U][0U], t[0U]);
  s->st[1U][0U] = xor_and_rotate_f5_1f(s->st[1U][0U], t[0U]);
  s->st[2U][0U] = xor_and_rotate_f5_1f0(s->st[2U][0U], t[0U]);
  s->st[3U][0U] = xor_and_rotate_f5_1f1(s->st[3U][0U], t[0U]);
  s->st[4U][0U] = xor_and_rotate_f5_1f2(s->st[4U][0U], t[0U]);
  s->st[0U][1U] = xor_and_rotate_f5_1f3(s->st[0U][1U], t[1U]);
  s->st[1U][1U] = xor_and_rotate_f5_1f4(s->st[1U][1U], t[1U]);
  s->st[2U][1U] = xor_and_rotate_f5_1f5(s->st[2U][1U], t[1U]);
  s->st[3U][1U] = xor_and_rotate_f5_1f6(s->st[3U][1U], t[1U]);
  s->st[4U][1U] = xor_and_rotate_f5_1f7(s->st[4U][1U], t[1U]);
  s->st[0U][2U] = xor_and_rotate_f5_1f8(s->st[0U][2U], t[2U]);
  s->st[1U][2U] = xor_and_rotate_f5_1f9(s->st[1U][2U], t[2U]);
  s->st[2U][2U] = xor_and_rotate_f5_1f10(s->st[2U][2U], t[2U]);
  s->st[3U][2U] = xor_and_rotate_f5_1f11(s->st[3U][2U], t[2U]);
  s->st[4U][2U] = xor_and_rotate_f5_1f12(s->st[4U][2U], t[2U]);
  s->st[0U][3U] = xor_and_rotate_f5_1f13(s->st[0U][3U], t[3U]);
  s->st[1U][3U] = xor_and_rotate_f5_1f14(s->st[1U][3U], t[3U]);
  s->st[2U][3U] = xor_and_rotate_f5_1f15(s->st[2U][3U], t[3U]);
  s->st[3U][3U] = xor_and_rotate_f5_1f16(s->st[3U][3U], t[3U]);
  s->st[4U][3U] = xor_and_rotate_f5_1f17(s->st[4U][3U], t[3U]);
  s->st[0U][4U] = xor_and_rotate_f5_1f18(s->st[0U][4U], t[4U]);
  s->st[1U][4U] = xor_and_rotate_f5_1f19(s->st[1U][4U], t[4U]);
  s->st[2U][4U] = xor_and_rotate_f5_1f20(s->st[2U][4U], t[4U]);
  s->st[3U][4U] = xor_and_rotate_f5_1f21(s->st[3U][4U], t[4U]);
  _uint64x2_t uu____27 = xor_and_rotate_f5_1f22(s->st[4U][4U], t[4U]);
  s->st[4U][4U] = uu____27;
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.pi
with types libcrux_intrinsics_arm64_extract__uint64x2_t
with const generics
- N= 2
*/
static KRML_MUSTINLINE void pi_3f(
    libcrux_sha3_generic_keccak_KeccakState_cc *s) {
  _uint64x2_t old[5U][5U];
  memcpy(old, s->st, (size_t)5U * sizeof(_uint64x2_t[5U]));
  s->st[0U][1U] = old[1U][1U];
  s->st[0U][2U] = old[2U][2U];
  s->st[0U][3U] = old[3U][3U];
  s->st[0U][4U] = old[4U][4U];
  s->st[1U][0U] = old[0U][3U];
  s->st[1U][1U] = old[1U][4U];
  s->st[1U][2U] = old[2U][0U];
  s->st[1U][3U] = old[3U][1U];
  s->st[1U][4U] = old[4U][2U];
  s->st[2U][0U] = old[0U][1U];
  s->st[2U][1U] = old[1U][2U];
  s->st[2U][2U] = old[2U][3U];
  s->st[2U][3U] = old[3U][4U];
  s->st[2U][4U] = old[4U][0U];
  s->st[3U][0U] = old[0U][4U];
  s->st[3U][1U] = old[1U][0U];
  s->st[3U][2U] = old[2U][1U];
  s->st[3U][3U] = old[3U][2U];
  s->st[3U][4U] = old[4U][3U];
  s->st[4U][0U] = old[0U][2U];
  s->st[4U][1U] = old[1U][3U];
  s->st[4U][2U] = old[2U][4U];
  s->st[4U][3U] = old[3U][0U];
  s->st[4U][4U] = old[4U][1U];
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.chi
with types libcrux_intrinsics_arm64_extract__uint64x2_t
with const generics
- N= 2
*/
static KRML_MUSTINLINE void chi_91(
    libcrux_sha3_generic_keccak_KeccakState_cc *s) {
  _uint64x2_t old[5U][5U];
  memcpy(old, s->st, (size_t)5U * sizeof(_uint64x2_t[5U]));
  KRML_MAYBE_FOR5(
      i0, (size_t)0U, (size_t)5U, (size_t)1U, size_t i1 = i0;
      KRML_MAYBE_FOR5(i, (size_t)0U, (size_t)5U, (size_t)1U, size_t j = i;
                      s->st[i1][j] = and_not_xor_f5(
                          s->st[i1][j], old[i1][(j + (size_t)2U) % (size_t)5U],
                          old[i1][(j + (size_t)1U) % (size_t)5U]);););
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.iota
with types libcrux_intrinsics_arm64_extract__uint64x2_t
with const generics
- N= 2
*/
static KRML_MUSTINLINE void iota_df(
    libcrux_sha3_generic_keccak_KeccakState_cc *s, size_t i) {
  s->st[0U][0U] = xor_constant_f5(
      s->st[0U][0U], libcrux_sha3_generic_keccak_ROUNDCONSTANTS[i]);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.keccakf1600
with types libcrux_intrinsics_arm64_extract__uint64x2_t
with const generics
- N= 2
*/
static KRML_MUSTINLINE void keccakf1600_31(
    libcrux_sha3_generic_keccak_KeccakState_cc *s) {
  for (size_t i = (size_t)0U; i < (size_t)24U; i++) {
    size_t i0 = i;
    theta_rho_f5(s);
    pi_3f(s);
    chi_91(s);
    iota_df(s, i0);
  }
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block
with types libcrux_intrinsics_arm64_extract__uint64x2_t
with const generics
- N= 2
- RATE= 72
*/
static KRML_MUSTINLINE void absorb_block_12(
    libcrux_sha3_generic_keccak_KeccakState_cc *s, Eurydice_slice blocks[2U]) {
  _uint64x2_t(*uu____0)[5U] = s->st;
  Eurydice_slice uu____1[2U];
  memcpy(uu____1, blocks, (size_t)2U * sizeof(Eurydice_slice));
  load_block_f5_0f(uu____0, uu____1);
  keccakf1600_31(s);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block_full
with const generics
- RATE= 72
*/
static KRML_MUSTINLINE void load_block_full_3e(_uint64x2_t (*s)[5U],
                                               uint8_t blocks[2U][200U]) {
  Eurydice_slice buf[2U] = {Eurydice_array_to_slice((size_t)200U, blocks[0U],
                                                    uint8_t, Eurydice_slice),
                            Eurydice_array_to_slice((size_t)200U, blocks[1U],
                                                    uint8_t, Eurydice_slice)};
  load_block_3c(s, buf);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for libcrux_intrinsics::arm64_extract::_uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block_full_f5
with const generics
- BLOCKSIZE= 72
*/
static KRML_MUSTINLINE void load_block_full_f5_07(_uint64x2_t (*a)[5U],
                                                  uint8_t b[2U][200U]) {
  _uint64x2_t(*uu____0)[5U] = a;
  uint8_t uu____1[2U][200U];
  memcpy(uu____1, b, (size_t)2U * sizeof(uint8_t[200U]));
  load_block_full_3e(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final
with types libcrux_intrinsics_arm64_extract__uint64x2_t
with const generics
- N= 2
- RATE= 72
- DELIM= 6
*/
static KRML_MUSTINLINE void absorb_final_ee(
    libcrux_sha3_generic_keccak_KeccakState_cc *s, Eurydice_slice last[2U]) {
  size_t last_len = core_slice___Slice_T___len(last[0U], uint8_t, size_t);
  uint8_t blocks[2U][200U] = {{0U}};
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      if (last_len > (size_t)0U) {
        Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
            blocks[i0], (size_t)0U, last_len, uint8_t, Eurydice_slice);
        core_slice___Slice_T___copy_from_slice(uu____0, last[i0], uint8_t,
                                               void *);
      } blocks[i0][last_len] = 6U;
      size_t uu____1 = i0; size_t uu____2 = (size_t)72U - (size_t)1U;
      blocks[uu____1][uu____2] = (uint32_t)blocks[uu____1][uu____2] | 128U;);
  _uint64x2_t(*uu____3)[5U] = s->st;
  uint8_t uu____4[2U][200U];
  memcpy(uu____4, blocks, (size_t)2U * sizeof(uint8_t[200U]));
  load_block_full_f5_07(uu____3, uu____4);
  keccakf1600_31(s);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.store_block
with const generics
- RATE= 72
*/
static KRML_MUSTINLINE void store_block_2f(_uint64x2_t (*s)[5U],
                                           Eurydice_slice out[2U]) {
  for (size_t i = (size_t)0U; i < (size_t)72U / (size_t)16U; i++) {
    size_t i0 = i;
    _uint64x2_t v0 = _vtrn1q_u64(
        s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U],
        s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
         [((size_t)2U * i0 + (size_t)1U) % (size_t)5U]);
    _uint64x2_t v1 = _vtrn2q_u64(
        s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U],
        s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
         [((size_t)2U * i0 + (size_t)1U) % (size_t)5U]);
    _vst1q_bytes_u64(Eurydice_slice_subslice2(out[0U], (size_t)16U * i0,
                                              (size_t)16U * (i0 + (size_t)1U),
                                              uint8_t, Eurydice_slice),
                     v0);
    _vst1q_bytes_u64(Eurydice_slice_subslice2(out[1U], (size_t)16U * i0,
                                              (size_t)16U * (i0 + (size_t)1U),
                                              uint8_t, Eurydice_slice),
                     v1);
  }
  if ((size_t)72U % (size_t)16U != (size_t)0U) {
    size_t i = ((size_t)72U / (size_t)8U - (size_t)1U) / (size_t)5U;
    size_t j = ((size_t)72U / (size_t)8U - (size_t)1U) % (size_t)5U;
    uint8_t u[16U] = {0U};
    _vst1q_bytes_u64(
        Eurydice_array_to_slice((size_t)16U, u, uint8_t, Eurydice_slice),
        s[i][j]);
    Eurydice_slice uu____0 =
        Eurydice_slice_subslice2(out[0U], (size_t)72U - (size_t)8U, (size_t)72U,
                                 uint8_t, Eurydice_slice);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_subslice2(u, (size_t)0U, (size_t)8U, uint8_t,
                                    Eurydice_slice),
        uint8_t, void *);
    Eurydice_slice uu____1 =
        Eurydice_slice_subslice2(out[1U], (size_t)72U - (size_t)8U, (size_t)72U,
                                 uint8_t, Eurydice_slice);
    core_slice___Slice_T___copy_from_slice(
        uu____1,
        Eurydice_array_to_subslice2(u, (size_t)8U, (size_t)16U, uint8_t,
                                    Eurydice_slice),
        uint8_t, void *);
  }
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.store_block_full
with const generics
- RATE= 72
*/
static KRML_MUSTINLINE void store_block_full_9a(_uint64x2_t (*s)[5U],
                                                uint8_t ret[2U][200U]) {
  uint8_t out0[200U] = {0U};
  uint8_t out1[200U] = {0U};
  Eurydice_slice buf[2U] = {
      Eurydice_array_to_slice((size_t)200U, out0, uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)200U, out1, uint8_t, Eurydice_slice)};
  store_block_2f(s, buf);
  uint8_t uu____0[200U];
  memcpy(uu____0, out0, (size_t)200U * sizeof(uint8_t));
  uint8_t uu____1[200U];
  memcpy(uu____1, out1, (size_t)200U * sizeof(uint8_t));
  memcpy(ret[0U], uu____0, (size_t)200U * sizeof(uint8_t));
  memcpy(ret[1U], uu____1, (size_t)200U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for libcrux_intrinsics::arm64_extract::_uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.store_block_full_f5
with const generics
- BLOCKSIZE= 72
*/
static KRML_MUSTINLINE void store_block_full_f5_a5(_uint64x2_t (*a)[5U],
                                                   uint8_t ret[2U][200U]) {
  store_block_full_9a(a, ret);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_and_last
with types libcrux_intrinsics_arm64_extract__uint64x2_t
with const generics
- N= 2
- RATE= 72
*/
static KRML_MUSTINLINE void squeeze_first_and_last_6c(
    libcrux_sha3_generic_keccak_KeccakState_cc *s, Eurydice_slice out[2U]) {
  uint8_t b[2U][200U];
  store_block_full_f5_a5(s->st, b);
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      Eurydice_slice uu____0 = out[i0]; uint8_t *uu____1 = b[i0];
      core_ops_range_Range_b3 lit; lit.start = (size_t)0U;
      lit.end = core_slice___Slice_T___len(out[i0], uint8_t, size_t);
      core_slice___Slice_T___copy_from_slice(
          uu____0,
          Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                     core_ops_range_Range_b3, Eurydice_slice),
          uint8_t, void *););
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for libcrux_intrinsics::arm64_extract::_uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.store_block_f5
with const generics
- BLOCKSIZE= 72
*/
static KRML_MUSTINLINE void store_block_f5_90(_uint64x2_t (*a)[5U],
                                              Eurydice_slice b[2U]) {
  store_block_2f(a, b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_block
with types libcrux_intrinsics_arm64_extract__uint64x2_t
with const generics
- N= 2
- RATE= 72
*/
static KRML_MUSTINLINE void squeeze_first_block_bf(
    libcrux_sha3_generic_keccak_KeccakState_cc *s, Eurydice_slice out[2U]) {
  store_block_f5_90(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_next_block
with types libcrux_intrinsics_arm64_extract__uint64x2_t
with const generics
- N= 2
- RATE= 72
*/
static KRML_MUSTINLINE void squeeze_next_block_f1(
    libcrux_sha3_generic_keccak_KeccakState_cc *s, Eurydice_slice out[2U]) {
  keccakf1600_31(s);
  store_block_f5_90(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_last
with types libcrux_intrinsics_arm64_extract__uint64x2_t
with const generics
- N= 2
- RATE= 72
*/
static KRML_MUSTINLINE void squeeze_last_6c(
    libcrux_sha3_generic_keccak_KeccakState_cc s, Eurydice_slice out[2U]) {
  keccakf1600_31(&s);
  uint8_t b[2U][200U];
  store_block_full_f5_a5(s.st, b);
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      Eurydice_slice uu____0 = out[i0]; uint8_t *uu____1 = b[i0];
      core_ops_range_Range_b3 lit; lit.start = (size_t)0U;
      lit.end = core_slice___Slice_T___len(out[i0], uint8_t, size_t);
      core_slice___Slice_T___copy_from_slice(
          uu____0,
          Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                     core_ops_range_Range_b3, Eurydice_slice),
          uint8_t, void *););
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.keccak
with types libcrux_intrinsics_arm64_extract__uint64x2_t
with const generics
- N= 2
- RATE= 72
- DELIM= 6
*/
static KRML_MUSTINLINE void keccak_6e(Eurydice_slice data[2U],
                                      Eurydice_slice out[2U]) {
  libcrux_sha3_generic_keccak_KeccakState_cc s = new_1e_ff();
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(data[0U], uint8_t, size_t) / (size_t)72U;
       i++) {
    size_t i0 = i;
    libcrux_sha3_generic_keccak_KeccakState_cc *uu____0 = &s;
    Eurydice_slice uu____1[2U];
    memcpy(uu____1, data, (size_t)2U * sizeof(Eurydice_slice));
    Eurydice_slice ret[2U];
    slice_n_f5(uu____1, i0 * (size_t)72U, (size_t)72U, ret);
    absorb_block_12(uu____0, ret);
  }
  size_t rem =
      core_slice___Slice_T___len(data[0U], uint8_t, size_t) % (size_t)72U;
  libcrux_sha3_generic_keccak_KeccakState_cc *uu____2 = &s;
  Eurydice_slice uu____3[2U];
  memcpy(uu____3, data, (size_t)2U * sizeof(Eurydice_slice));
  Eurydice_slice ret[2U];
  slice_n_f5(uu____3,
             core_slice___Slice_T___len(data[0U], uint8_t, size_t) - rem, rem,
             ret);
  absorb_final_ee(uu____2, ret);
  size_t outlen = core_slice___Slice_T___len(out[0U], uint8_t, size_t);
  size_t blocks = outlen / (size_t)72U;
  size_t last = outlen - outlen % (size_t)72U;
  if (blocks == (size_t)0U) {
    squeeze_first_and_last_6c(&s, out);
  } else {
    Eurydice_slice_uint8_t_2size_t__x2 uu____4 =
        split_at_mut_n_f5(out, (size_t)72U);
    Eurydice_slice o0[2U];
    memcpy(o0, uu____4.fst, (size_t)2U * sizeof(Eurydice_slice));
    Eurydice_slice o1[2U];
    memcpy(o1, uu____4.snd, (size_t)2U * sizeof(Eurydice_slice));
    squeeze_first_block_bf(&s, o0);
    core_ops_range_Range_b3 iter =
        core_iter_traits_collect___core__iter__traits__collect__IntoIterator_for_I__1__into_iter(
            (CLITERAL(core_ops_range_Range_b3){.start = (size_t)1U,
                                               .end = blocks}),
            core_ops_range_Range_b3, core_ops_range_Range_b3);
    while (true) {
      if (core_iter_range___core__iter__traits__iterator__Iterator_for_core__ops__range__Range_A___6__next(
              &iter, size_t, core_option_Option_b3)
              .tag == core_option_None) {
        break;
      } else {
        Eurydice_slice_uint8_t_2size_t__x2 uu____5 =
            split_at_mut_n_f5(o1, (size_t)72U);
        Eurydice_slice o[2U];
        memcpy(o, uu____5.fst, (size_t)2U * sizeof(Eurydice_slice));
        Eurydice_slice orest[2U];
        memcpy(orest, uu____5.snd, (size_t)2U * sizeof(Eurydice_slice));
        squeeze_next_block_f1(&s, o);
        memcpy(o1, orest, (size_t)2U * sizeof(Eurydice_slice));
      }
    }
    if (last < outlen) {
      squeeze_last_6c(s, o1);
    }
  }
}

/**
A monomorphic instance of libcrux_sha3.neon.keccakx2
with const generics
- RATE= 72
- DELIM= 6
*/
static KRML_MUSTINLINE void keccakx2_6e(Eurydice_slice data[2U],
                                        Eurydice_slice out[2U]) {
  Eurydice_slice uu____0[2U];
  memcpy(uu____0, data, (size_t)2U * sizeof(Eurydice_slice));
  keccak_6e(uu____0, out);
}

/**
 A portable SHA3 512 implementation.
*/
void libcrux_sha3_neon_sha512(Eurydice_slice digest, Eurydice_slice data) {
  uint8_t dummy[64U] = {0U};
  Eurydice_slice uu____0[2U] = {data, data};
  Eurydice_slice buf[2U] = {
      digest,
      Eurydice_array_to_slice((size_t)64U, dummy, uint8_t, Eurydice_slice)};
  keccakx2_6e(uu____0, buf);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block
with const generics
- RATE= 136
*/
static KRML_MUSTINLINE void load_block_3c0(_uint64x2_t (*s)[5U],
                                           Eurydice_slice blocks[2U]) {
  for (size_t i = (size_t)0U; i < (size_t)136U / (size_t)16U; i++) {
    size_t i0 = i;
    _uint64x2_t v0 = _vld1q_bytes_u64(Eurydice_slice_subslice2(
        blocks[0U], (size_t)16U * i0, (size_t)16U * (i0 + (size_t)1U), uint8_t,
        Eurydice_slice));
    _uint64x2_t v1 = _vld1q_bytes_u64(Eurydice_slice_subslice2(
        blocks[1U], (size_t)16U * i0, (size_t)16U * (i0 + (size_t)1U), uint8_t,
        Eurydice_slice));
    s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U] = _veorq_u64(
        s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U],
        _vtrn1q_u64(v0, v1));
    s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
     [((size_t)2U * i0 + (size_t)1U) % (size_t)5U] =
         _veorq_u64(s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
                     [((size_t)2U * i0 + (size_t)1U) % (size_t)5U],
                    _vtrn2q_u64(v0, v1));
  }
  if ((size_t)136U % (size_t)16U != (size_t)0U) {
    size_t i = ((size_t)136U / (size_t)8U - (size_t)1U) / (size_t)5U;
    size_t j = ((size_t)136U / (size_t)8U - (size_t)1U) % (size_t)5U;
    uint64_t u[2U] = {0U};
    uint8_t uu____0[8U];
    core_result_Result_56 dst0;
    Eurydice_slice_to_array2(
        &dst0,
        Eurydice_slice_subslice2(blocks[0U], (size_t)136U - (size_t)8U,
                                 (size_t)136U, uint8_t, Eurydice_slice),
        Eurydice_slice, uint8_t[8U], void *);
    core_result_unwrap_41_ac(dst0, uu____0);
    u[0U] = core_num__u64_9__from_le_bytes(uu____0);
    uint8_t uu____1[8U];
    core_result_Result_56 dst;
    Eurydice_slice_to_array2(
        &dst,
        Eurydice_slice_subslice2(blocks[1U], (size_t)136U - (size_t)8U,
                                 (size_t)136U, uint8_t, Eurydice_slice),
        Eurydice_slice, uint8_t[8U], void *);
    core_result_unwrap_41_ac(dst, uu____1);
    u[1U] = core_num__u64_9__from_le_bytes(uu____1);
    _uint64x2_t uvec = _vld1q_u64(
        Eurydice_array_to_slice((size_t)2U, u, uint64_t, Eurydice_slice));
    s[i][j] = _veorq_u64(s[i][j], uvec);
  }
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for libcrux_intrinsics::arm64_extract::_uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block_f5
with const generics
- BLOCKSIZE= 136
*/
static KRML_MUSTINLINE void load_block_f5_0f0(_uint64x2_t (*a)[5U],
                                              Eurydice_slice b[2U]) {
  _uint64x2_t(*uu____0)[5U] = a;
  Eurydice_slice uu____1[2U];
  memcpy(uu____1, b, (size_t)2U * sizeof(Eurydice_slice));
  load_block_3c0(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block
with types libcrux_intrinsics_arm64_extract__uint64x2_t
with const generics
- N= 2
- RATE= 136
*/
static KRML_MUSTINLINE void absorb_block_120(
    libcrux_sha3_generic_keccak_KeccakState_cc *s, Eurydice_slice blocks[2U]) {
  _uint64x2_t(*uu____0)[5U] = s->st;
  Eurydice_slice uu____1[2U];
  memcpy(uu____1, blocks, (size_t)2U * sizeof(Eurydice_slice));
  load_block_f5_0f0(uu____0, uu____1);
  keccakf1600_31(s);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block_full
with const generics
- RATE= 136
*/
static KRML_MUSTINLINE void load_block_full_3e0(_uint64x2_t (*s)[5U],
                                                uint8_t blocks[2U][200U]) {
  Eurydice_slice buf[2U] = {Eurydice_array_to_slice((size_t)200U, blocks[0U],
                                                    uint8_t, Eurydice_slice),
                            Eurydice_array_to_slice((size_t)200U, blocks[1U],
                                                    uint8_t, Eurydice_slice)};
  load_block_3c0(s, buf);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for libcrux_intrinsics::arm64_extract::_uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block_full_f5
with const generics
- BLOCKSIZE= 136
*/
static KRML_MUSTINLINE void load_block_full_f5_070(_uint64x2_t (*a)[5U],
                                                   uint8_t b[2U][200U]) {
  _uint64x2_t(*uu____0)[5U] = a;
  uint8_t uu____1[2U][200U];
  memcpy(uu____1, b, (size_t)2U * sizeof(uint8_t[200U]));
  load_block_full_3e0(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final
with types libcrux_intrinsics_arm64_extract__uint64x2_t
with const generics
- N= 2
- RATE= 136
- DELIM= 6
*/
static KRML_MUSTINLINE void absorb_final_ee0(
    libcrux_sha3_generic_keccak_KeccakState_cc *s, Eurydice_slice last[2U]) {
  size_t last_len = core_slice___Slice_T___len(last[0U], uint8_t, size_t);
  uint8_t blocks[2U][200U] = {{0U}};
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      if (last_len > (size_t)0U) {
        Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
            blocks[i0], (size_t)0U, last_len, uint8_t, Eurydice_slice);
        core_slice___Slice_T___copy_from_slice(uu____0, last[i0], uint8_t,
                                               void *);
      } blocks[i0][last_len] = 6U;
      size_t uu____1 = i0; size_t uu____2 = (size_t)136U - (size_t)1U;
      blocks[uu____1][uu____2] = (uint32_t)blocks[uu____1][uu____2] | 128U;);
  _uint64x2_t(*uu____3)[5U] = s->st;
  uint8_t uu____4[2U][200U];
  memcpy(uu____4, blocks, (size_t)2U * sizeof(uint8_t[200U]));
  load_block_full_f5_070(uu____3, uu____4);
  keccakf1600_31(s);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.store_block
with const generics
- RATE= 136
*/
static KRML_MUSTINLINE void store_block_2f0(_uint64x2_t (*s)[5U],
                                            Eurydice_slice out[2U]) {
  for (size_t i = (size_t)0U; i < (size_t)136U / (size_t)16U; i++) {
    size_t i0 = i;
    _uint64x2_t v0 = _vtrn1q_u64(
        s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U],
        s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
         [((size_t)2U * i0 + (size_t)1U) % (size_t)5U]);
    _uint64x2_t v1 = _vtrn2q_u64(
        s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U],
        s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
         [((size_t)2U * i0 + (size_t)1U) % (size_t)5U]);
    _vst1q_bytes_u64(Eurydice_slice_subslice2(out[0U], (size_t)16U * i0,
                                              (size_t)16U * (i0 + (size_t)1U),
                                              uint8_t, Eurydice_slice),
                     v0);
    _vst1q_bytes_u64(Eurydice_slice_subslice2(out[1U], (size_t)16U * i0,
                                              (size_t)16U * (i0 + (size_t)1U),
                                              uint8_t, Eurydice_slice),
                     v1);
  }
  if ((size_t)136U % (size_t)16U != (size_t)0U) {
    size_t i = ((size_t)136U / (size_t)8U - (size_t)1U) / (size_t)5U;
    size_t j = ((size_t)136U / (size_t)8U - (size_t)1U) % (size_t)5U;
    uint8_t u[16U] = {0U};
    _vst1q_bytes_u64(
        Eurydice_array_to_slice((size_t)16U, u, uint8_t, Eurydice_slice),
        s[i][j]);
    Eurydice_slice uu____0 =
        Eurydice_slice_subslice2(out[0U], (size_t)136U - (size_t)8U,
                                 (size_t)136U, uint8_t, Eurydice_slice);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_subslice2(u, (size_t)0U, (size_t)8U, uint8_t,
                                    Eurydice_slice),
        uint8_t, void *);
    Eurydice_slice uu____1 =
        Eurydice_slice_subslice2(out[1U], (size_t)136U - (size_t)8U,
                                 (size_t)136U, uint8_t, Eurydice_slice);
    core_slice___Slice_T___copy_from_slice(
        uu____1,
        Eurydice_array_to_subslice2(u, (size_t)8U, (size_t)16U, uint8_t,
                                    Eurydice_slice),
        uint8_t, void *);
  }
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.store_block_full
with const generics
- RATE= 136
*/
static KRML_MUSTINLINE void store_block_full_9a0(_uint64x2_t (*s)[5U],
                                                 uint8_t ret[2U][200U]) {
  uint8_t out0[200U] = {0U};
  uint8_t out1[200U] = {0U};
  Eurydice_slice buf[2U] = {
      Eurydice_array_to_slice((size_t)200U, out0, uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)200U, out1, uint8_t, Eurydice_slice)};
  store_block_2f0(s, buf);
  uint8_t uu____0[200U];
  memcpy(uu____0, out0, (size_t)200U * sizeof(uint8_t));
  uint8_t uu____1[200U];
  memcpy(uu____1, out1, (size_t)200U * sizeof(uint8_t));
  memcpy(ret[0U], uu____0, (size_t)200U * sizeof(uint8_t));
  memcpy(ret[1U], uu____1, (size_t)200U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for libcrux_intrinsics::arm64_extract::_uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.store_block_full_f5
with const generics
- BLOCKSIZE= 136
*/
static KRML_MUSTINLINE void store_block_full_f5_a50(_uint64x2_t (*a)[5U],
                                                    uint8_t ret[2U][200U]) {
  store_block_full_9a0(a, ret);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_and_last
with types libcrux_intrinsics_arm64_extract__uint64x2_t
with const generics
- N= 2
- RATE= 136
*/
static KRML_MUSTINLINE void squeeze_first_and_last_6c0(
    libcrux_sha3_generic_keccak_KeccakState_cc *s, Eurydice_slice out[2U]) {
  uint8_t b[2U][200U];
  store_block_full_f5_a50(s->st, b);
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      Eurydice_slice uu____0 = out[i0]; uint8_t *uu____1 = b[i0];
      core_ops_range_Range_b3 lit; lit.start = (size_t)0U;
      lit.end = core_slice___Slice_T___len(out[i0], uint8_t, size_t);
      core_slice___Slice_T___copy_from_slice(
          uu____0,
          Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                     core_ops_range_Range_b3, Eurydice_slice),
          uint8_t, void *););
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for libcrux_intrinsics::arm64_extract::_uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.store_block_f5
with const generics
- BLOCKSIZE= 136
*/
static KRML_MUSTINLINE void store_block_f5_900(_uint64x2_t (*a)[5U],
                                               Eurydice_slice b[2U]) {
  store_block_2f0(a, b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_block
with types libcrux_intrinsics_arm64_extract__uint64x2_t
with const generics
- N= 2
- RATE= 136
*/
static KRML_MUSTINLINE void squeeze_first_block_bf0(
    libcrux_sha3_generic_keccak_KeccakState_cc *s, Eurydice_slice out[2U]) {
  store_block_f5_900(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_next_block
with types libcrux_intrinsics_arm64_extract__uint64x2_t
with const generics
- N= 2
- RATE= 136
*/
static KRML_MUSTINLINE void squeeze_next_block_f10(
    libcrux_sha3_generic_keccak_KeccakState_cc *s, Eurydice_slice out[2U]) {
  keccakf1600_31(s);
  store_block_f5_900(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_last
with types libcrux_intrinsics_arm64_extract__uint64x2_t
with const generics
- N= 2
- RATE= 136
*/
static KRML_MUSTINLINE void squeeze_last_6c0(
    libcrux_sha3_generic_keccak_KeccakState_cc s, Eurydice_slice out[2U]) {
  keccakf1600_31(&s);
  uint8_t b[2U][200U];
  store_block_full_f5_a50(s.st, b);
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      Eurydice_slice uu____0 = out[i0]; uint8_t *uu____1 = b[i0];
      core_ops_range_Range_b3 lit; lit.start = (size_t)0U;
      lit.end = core_slice___Slice_T___len(out[i0], uint8_t, size_t);
      core_slice___Slice_T___copy_from_slice(
          uu____0,
          Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                     core_ops_range_Range_b3, Eurydice_slice),
          uint8_t, void *););
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.keccak
with types libcrux_intrinsics_arm64_extract__uint64x2_t
with const generics
- N= 2
- RATE= 136
- DELIM= 6
*/
static KRML_MUSTINLINE void keccak_6e0(Eurydice_slice data[2U],
                                       Eurydice_slice out[2U]) {
  libcrux_sha3_generic_keccak_KeccakState_cc s = new_1e_ff();
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(data[0U], uint8_t, size_t) / (size_t)136U;
       i++) {
    size_t i0 = i;
    libcrux_sha3_generic_keccak_KeccakState_cc *uu____0 = &s;
    Eurydice_slice uu____1[2U];
    memcpy(uu____1, data, (size_t)2U * sizeof(Eurydice_slice));
    Eurydice_slice ret[2U];
    slice_n_f5(uu____1, i0 * (size_t)136U, (size_t)136U, ret);
    absorb_block_120(uu____0, ret);
  }
  size_t rem =
      core_slice___Slice_T___len(data[0U], uint8_t, size_t) % (size_t)136U;
  libcrux_sha3_generic_keccak_KeccakState_cc *uu____2 = &s;
  Eurydice_slice uu____3[2U];
  memcpy(uu____3, data, (size_t)2U * sizeof(Eurydice_slice));
  Eurydice_slice ret[2U];
  slice_n_f5(uu____3,
             core_slice___Slice_T___len(data[0U], uint8_t, size_t) - rem, rem,
             ret);
  absorb_final_ee0(uu____2, ret);
  size_t outlen = core_slice___Slice_T___len(out[0U], uint8_t, size_t);
  size_t blocks = outlen / (size_t)136U;
  size_t last = outlen - outlen % (size_t)136U;
  if (blocks == (size_t)0U) {
    squeeze_first_and_last_6c0(&s, out);
  } else {
    Eurydice_slice_uint8_t_2size_t__x2 uu____4 =
        split_at_mut_n_f5(out, (size_t)136U);
    Eurydice_slice o0[2U];
    memcpy(o0, uu____4.fst, (size_t)2U * sizeof(Eurydice_slice));
    Eurydice_slice o1[2U];
    memcpy(o1, uu____4.snd, (size_t)2U * sizeof(Eurydice_slice));
    squeeze_first_block_bf0(&s, o0);
    core_ops_range_Range_b3 iter =
        core_iter_traits_collect___core__iter__traits__collect__IntoIterator_for_I__1__into_iter(
            (CLITERAL(core_ops_range_Range_b3){.start = (size_t)1U,
                                               .end = blocks}),
            core_ops_range_Range_b3, core_ops_range_Range_b3);
    while (true) {
      if (core_iter_range___core__iter__traits__iterator__Iterator_for_core__ops__range__Range_A___6__next(
              &iter, size_t, core_option_Option_b3)
              .tag == core_option_None) {
        break;
      } else {
        Eurydice_slice_uint8_t_2size_t__x2 uu____5 =
            split_at_mut_n_f5(o1, (size_t)136U);
        Eurydice_slice o[2U];
        memcpy(o, uu____5.fst, (size_t)2U * sizeof(Eurydice_slice));
        Eurydice_slice orest[2U];
        memcpy(orest, uu____5.snd, (size_t)2U * sizeof(Eurydice_slice));
        squeeze_next_block_f10(&s, o);
        memcpy(o1, orest, (size_t)2U * sizeof(Eurydice_slice));
      }
    }
    if (last < outlen) {
      squeeze_last_6c0(s, o1);
    }
  }
}

/**
A monomorphic instance of libcrux_sha3.neon.keccakx2
with const generics
- RATE= 136
- DELIM= 6
*/
static KRML_MUSTINLINE void keccakx2_6e0(Eurydice_slice data[2U],
                                         Eurydice_slice out[2U]) {
  Eurydice_slice uu____0[2U];
  memcpy(uu____0, data, (size_t)2U * sizeof(Eurydice_slice));
  keccak_6e0(uu____0, out);
}

/**
 A portable SHA3 256 implementation.
*/
void libcrux_sha3_neon_sha256(Eurydice_slice digest, Eurydice_slice data) {
  uint8_t dummy[32U] = {0U};
  Eurydice_slice uu____0[2U] = {data, data};
  Eurydice_slice buf[2U] = {
      digest,
      Eurydice_array_to_slice((size_t)32U, dummy, uint8_t, Eurydice_slice)};
  keccakx2_6e0(uu____0, buf);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final
with types libcrux_intrinsics_arm64_extract__uint64x2_t
with const generics
- N= 2
- RATE= 136
- DELIM= 31
*/
static KRML_MUSTINLINE void absorb_final_ee1(
    libcrux_sha3_generic_keccak_KeccakState_cc *s, Eurydice_slice last[2U]) {
  size_t last_len = core_slice___Slice_T___len(last[0U], uint8_t, size_t);
  uint8_t blocks[2U][200U] = {{0U}};
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      if (last_len > (size_t)0U) {
        Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
            blocks[i0], (size_t)0U, last_len, uint8_t, Eurydice_slice);
        core_slice___Slice_T___copy_from_slice(uu____0, last[i0], uint8_t,
                                               void *);
      } blocks[i0][last_len] = 31U;
      size_t uu____1 = i0; size_t uu____2 = (size_t)136U - (size_t)1U;
      blocks[uu____1][uu____2] = (uint32_t)blocks[uu____1][uu____2] | 128U;);
  _uint64x2_t(*uu____3)[5U] = s->st;
  uint8_t uu____4[2U][200U];
  memcpy(uu____4, blocks, (size_t)2U * sizeof(uint8_t[200U]));
  load_block_full_f5_070(uu____3, uu____4);
  keccakf1600_31(s);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.keccak
with types libcrux_intrinsics_arm64_extract__uint64x2_t
with const generics
- N= 2
- RATE= 136
- DELIM= 31
*/
static KRML_MUSTINLINE void keccak_6e1(Eurydice_slice data[2U],
                                       Eurydice_slice out[2U]) {
  libcrux_sha3_generic_keccak_KeccakState_cc s = new_1e_ff();
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(data[0U], uint8_t, size_t) / (size_t)136U;
       i++) {
    size_t i0 = i;
    libcrux_sha3_generic_keccak_KeccakState_cc *uu____0 = &s;
    Eurydice_slice uu____1[2U];
    memcpy(uu____1, data, (size_t)2U * sizeof(Eurydice_slice));
    Eurydice_slice ret[2U];
    slice_n_f5(uu____1, i0 * (size_t)136U, (size_t)136U, ret);
    absorb_block_120(uu____0, ret);
  }
  size_t rem =
      core_slice___Slice_T___len(data[0U], uint8_t, size_t) % (size_t)136U;
  libcrux_sha3_generic_keccak_KeccakState_cc *uu____2 = &s;
  Eurydice_slice uu____3[2U];
  memcpy(uu____3, data, (size_t)2U * sizeof(Eurydice_slice));
  Eurydice_slice ret[2U];
  slice_n_f5(uu____3,
             core_slice___Slice_T___len(data[0U], uint8_t, size_t) - rem, rem,
             ret);
  absorb_final_ee1(uu____2, ret);
  size_t outlen = core_slice___Slice_T___len(out[0U], uint8_t, size_t);
  size_t blocks = outlen / (size_t)136U;
  size_t last = outlen - outlen % (size_t)136U;
  if (blocks == (size_t)0U) {
    squeeze_first_and_last_6c0(&s, out);
  } else {
    Eurydice_slice_uint8_t_2size_t__x2 uu____4 =
        split_at_mut_n_f5(out, (size_t)136U);
    Eurydice_slice o0[2U];
    memcpy(o0, uu____4.fst, (size_t)2U * sizeof(Eurydice_slice));
    Eurydice_slice o1[2U];
    memcpy(o1, uu____4.snd, (size_t)2U * sizeof(Eurydice_slice));
    squeeze_first_block_bf0(&s, o0);
    core_ops_range_Range_b3 iter =
        core_iter_traits_collect___core__iter__traits__collect__IntoIterator_for_I__1__into_iter(
            (CLITERAL(core_ops_range_Range_b3){.start = (size_t)1U,
                                               .end = blocks}),
            core_ops_range_Range_b3, core_ops_range_Range_b3);
    while (true) {
      if (core_iter_range___core__iter__traits__iterator__Iterator_for_core__ops__range__Range_A___6__next(
              &iter, size_t, core_option_Option_b3)
              .tag == core_option_None) {
        break;
      } else {
        Eurydice_slice_uint8_t_2size_t__x2 uu____5 =
            split_at_mut_n_f5(o1, (size_t)136U);
        Eurydice_slice o[2U];
        memcpy(o, uu____5.fst, (size_t)2U * sizeof(Eurydice_slice));
        Eurydice_slice orest[2U];
        memcpy(orest, uu____5.snd, (size_t)2U * sizeof(Eurydice_slice));
        squeeze_next_block_f10(&s, o);
        memcpy(o1, orest, (size_t)2U * sizeof(Eurydice_slice));
      }
    }
    if (last < outlen) {
      squeeze_last_6c0(s, o1);
    }
  }
}

/**
A monomorphic instance of libcrux_sha3.neon.keccakx2
with const generics
- RATE= 136
- DELIM= 31
*/
static KRML_MUSTINLINE void keccakx2_6e1(Eurydice_slice data[2U],
                                         Eurydice_slice out[2U]) {
  Eurydice_slice uu____0[2U];
  memcpy(uu____0, data, (size_t)2U * sizeof(Eurydice_slice));
  keccak_6e1(uu____0, out);
}

/**
 Run SHAKE256 on both inputs in parallel.

 Writes the two results into `out0` and `out1`
*/
void libcrux_sha3_neon_x2_shake256(Eurydice_slice input0, Eurydice_slice input1,
                                   Eurydice_slice out0, Eurydice_slice out1) {
  Eurydice_slice buf0[2U] = {input0, input1};
  Eurydice_slice buf[2U] = {out0, out1};
  keccakx2_6e1(buf0, buf);
}

/**
 Initialise the `KeccakState2`.
*/
libcrux_sha3_generic_keccak_KeccakState_cc
libcrux_sha3_neon_x2_incremental_shake128_init(void) {
  return new_1e_ff();
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block
with const generics
- RATE= 168
*/
static KRML_MUSTINLINE void load_block_3c1(_uint64x2_t (*s)[5U],
                                           Eurydice_slice blocks[2U]) {
  for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)16U; i++) {
    size_t i0 = i;
    _uint64x2_t v0 = _vld1q_bytes_u64(Eurydice_slice_subslice2(
        blocks[0U], (size_t)16U * i0, (size_t)16U * (i0 + (size_t)1U), uint8_t,
        Eurydice_slice));
    _uint64x2_t v1 = _vld1q_bytes_u64(Eurydice_slice_subslice2(
        blocks[1U], (size_t)16U * i0, (size_t)16U * (i0 + (size_t)1U), uint8_t,
        Eurydice_slice));
    s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U] = _veorq_u64(
        s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U],
        _vtrn1q_u64(v0, v1));
    s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
     [((size_t)2U * i0 + (size_t)1U) % (size_t)5U] =
         _veorq_u64(s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
                     [((size_t)2U * i0 + (size_t)1U) % (size_t)5U],
                    _vtrn2q_u64(v0, v1));
  }
  if ((size_t)168U % (size_t)16U != (size_t)0U) {
    size_t i = ((size_t)168U / (size_t)8U - (size_t)1U) / (size_t)5U;
    size_t j = ((size_t)168U / (size_t)8U - (size_t)1U) % (size_t)5U;
    uint64_t u[2U] = {0U};
    uint8_t uu____0[8U];
    core_result_Result_56 dst0;
    Eurydice_slice_to_array2(
        &dst0,
        Eurydice_slice_subslice2(blocks[0U], (size_t)168U - (size_t)8U,
                                 (size_t)168U, uint8_t, Eurydice_slice),
        Eurydice_slice, uint8_t[8U], void *);
    core_result_unwrap_41_ac(dst0, uu____0);
    u[0U] = core_num__u64_9__from_le_bytes(uu____0);
    uint8_t uu____1[8U];
    core_result_Result_56 dst;
    Eurydice_slice_to_array2(
        &dst,
        Eurydice_slice_subslice2(blocks[1U], (size_t)168U - (size_t)8U,
                                 (size_t)168U, uint8_t, Eurydice_slice),
        Eurydice_slice, uint8_t[8U], void *);
    core_result_unwrap_41_ac(dst, uu____1);
    u[1U] = core_num__u64_9__from_le_bytes(uu____1);
    _uint64x2_t uvec = _vld1q_u64(
        Eurydice_array_to_slice((size_t)2U, u, uint64_t, Eurydice_slice));
    s[i][j] = _veorq_u64(s[i][j], uvec);
  }
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block_full
with const generics
- RATE= 168
*/
static KRML_MUSTINLINE void load_block_full_3e1(_uint64x2_t (*s)[5U],
                                                uint8_t blocks[2U][200U]) {
  Eurydice_slice buf[2U] = {Eurydice_array_to_slice((size_t)200U, blocks[0U],
                                                    uint8_t, Eurydice_slice),
                            Eurydice_array_to_slice((size_t)200U, blocks[1U],
                                                    uint8_t, Eurydice_slice)};
  load_block_3c1(s, buf);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for libcrux_intrinsics::arm64_extract::_uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block_full_f5
with const generics
- BLOCKSIZE= 168
*/
static KRML_MUSTINLINE void load_block_full_f5_071(_uint64x2_t (*a)[5U],
                                                   uint8_t b[2U][200U]) {
  _uint64x2_t(*uu____0)[5U] = a;
  uint8_t uu____1[2U][200U];
  memcpy(uu____1, b, (size_t)2U * sizeof(uint8_t[200U]));
  load_block_full_3e1(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final
with types libcrux_intrinsics_arm64_extract__uint64x2_t
with const generics
- N= 2
- RATE= 168
- DELIM= 31
*/
static KRML_MUSTINLINE void absorb_final_ee2(
    libcrux_sha3_generic_keccak_KeccakState_cc *s, Eurydice_slice last[2U]) {
  size_t last_len = core_slice___Slice_T___len(last[0U], uint8_t, size_t);
  uint8_t blocks[2U][200U] = {{0U}};
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      if (last_len > (size_t)0U) {
        Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
            blocks[i0], (size_t)0U, last_len, uint8_t, Eurydice_slice);
        core_slice___Slice_T___copy_from_slice(uu____0, last[i0], uint8_t,
                                               void *);
      } blocks[i0][last_len] = 31U;
      size_t uu____1 = i0; size_t uu____2 = (size_t)168U - (size_t)1U;
      blocks[uu____1][uu____2] = (uint32_t)blocks[uu____1][uu____2] | 128U;);
  _uint64x2_t(*uu____3)[5U] = s->st;
  uint8_t uu____4[2U][200U];
  memcpy(uu____4, blocks, (size_t)2U * sizeof(uint8_t[200U]));
  load_block_full_f5_071(uu____3, uu____4);
  keccakf1600_31(s);
}

/**
 Shake128 absorb `data0` and `data1` in the [`KeccakState`] `s`.
*/
void libcrux_sha3_neon_x2_incremental_shake128_absorb_final(
    libcrux_sha3_generic_keccak_KeccakState_cc *s, Eurydice_slice data0,
    Eurydice_slice data1) {
  Eurydice_slice buf[2U] = {data0, data1};
  absorb_final_ee2(s, buf);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.store_block
with const generics
- RATE= 168
*/
static KRML_MUSTINLINE void store_block_2f1(_uint64x2_t (*s)[5U],
                                            Eurydice_slice out[2U]) {
  for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)16U; i++) {
    size_t i0 = i;
    _uint64x2_t v0 = _vtrn1q_u64(
        s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U],
        s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
         [((size_t)2U * i0 + (size_t)1U) % (size_t)5U]);
    _uint64x2_t v1 = _vtrn2q_u64(
        s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U],
        s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
         [((size_t)2U * i0 + (size_t)1U) % (size_t)5U]);
    _vst1q_bytes_u64(Eurydice_slice_subslice2(out[0U], (size_t)16U * i0,
                                              (size_t)16U * (i0 + (size_t)1U),
                                              uint8_t, Eurydice_slice),
                     v0);
    _vst1q_bytes_u64(Eurydice_slice_subslice2(out[1U], (size_t)16U * i0,
                                              (size_t)16U * (i0 + (size_t)1U),
                                              uint8_t, Eurydice_slice),
                     v1);
  }
  if ((size_t)168U % (size_t)16U != (size_t)0U) {
    size_t i = ((size_t)168U / (size_t)8U - (size_t)1U) / (size_t)5U;
    size_t j = ((size_t)168U / (size_t)8U - (size_t)1U) % (size_t)5U;
    uint8_t u[16U] = {0U};
    _vst1q_bytes_u64(
        Eurydice_array_to_slice((size_t)16U, u, uint8_t, Eurydice_slice),
        s[i][j]);
    Eurydice_slice uu____0 =
        Eurydice_slice_subslice2(out[0U], (size_t)168U - (size_t)8U,
                                 (size_t)168U, uint8_t, Eurydice_slice);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_subslice2(u, (size_t)0U, (size_t)8U, uint8_t,
                                    Eurydice_slice),
        uint8_t, void *);
    Eurydice_slice uu____1 =
        Eurydice_slice_subslice2(out[1U], (size_t)168U - (size_t)8U,
                                 (size_t)168U, uint8_t, Eurydice_slice);
    core_slice___Slice_T___copy_from_slice(
        uu____1,
        Eurydice_array_to_subslice2(u, (size_t)8U, (size_t)16U, uint8_t,
                                    Eurydice_slice),
        uint8_t, void *);
  }
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for libcrux_intrinsics::arm64_extract::_uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.store_block_f5
with const generics
- BLOCKSIZE= 168
*/
static KRML_MUSTINLINE void store_block_f5_901(_uint64x2_t (*a)[5U],
                                               Eurydice_slice b[2U]) {
  store_block_2f1(a, b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_next_block
with types libcrux_intrinsics_arm64_extract__uint64x2_t
with const generics
- N= 2
- RATE= 168
*/
static KRML_MUSTINLINE void squeeze_next_block_f11(
    libcrux_sha3_generic_keccak_KeccakState_cc *s, Eurydice_slice out[2U]) {
  keccakf1600_31(s);
  store_block_f5_901(s->st, out);
}

/**
 Squeeze 2 times the next block in parallel in the
 [`KeccakState`] and return the output in `out0` and `out1`.
*/
void libcrux_sha3_neon_x2_incremental_shake128_squeeze_next_block(
    libcrux_sha3_generic_keccak_KeccakState_cc *s, Eurydice_slice out0,
    Eurydice_slice out1) {
  Eurydice_slice buf[2U] = {out0, out1};
  squeeze_next_block_f11(s, buf);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_block
with types libcrux_intrinsics_arm64_extract__uint64x2_t
with const generics
- N= 2
- RATE= 168
*/
static KRML_MUSTINLINE void squeeze_first_block_bf1(
    libcrux_sha3_generic_keccak_KeccakState_cc *s, Eurydice_slice out[2U]) {
  store_block_f5_901(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_three_blocks
with types libcrux_intrinsics_arm64_extract__uint64x2_t
with const generics
- N= 2
- RATE= 168
*/
static KRML_MUSTINLINE void squeeze_first_three_blocks_77(
    libcrux_sha3_generic_keccak_KeccakState_cc *s, Eurydice_slice out[2U]) {
  Eurydice_slice_uint8_t_2size_t__x2 uu____0 =
      split_at_mut_n_f5(out, (size_t)168U);
  Eurydice_slice o0[2U];
  memcpy(o0, uu____0.fst, (size_t)2U * sizeof(Eurydice_slice));
  Eurydice_slice o10[2U];
  memcpy(o10, uu____0.snd, (size_t)2U * sizeof(Eurydice_slice));
  squeeze_first_block_bf1(s, o0);
  Eurydice_slice_uint8_t_2size_t__x2 uu____1 =
      split_at_mut_n_f5(o10, (size_t)168U);
  Eurydice_slice o1[2U];
  memcpy(o1, uu____1.fst, (size_t)2U * sizeof(Eurydice_slice));
  Eurydice_slice o2[2U];
  memcpy(o2, uu____1.snd, (size_t)2U * sizeof(Eurydice_slice));
  squeeze_next_block_f11(s, o1);
  squeeze_next_block_f11(s, o2);
}

/**
 Squeeze 2 times the first three blocks in parallel in the
 [`KeccakState`] and return the output in `out0` and `out1`.
*/
void libcrux_sha3_neon_x2_incremental_shake128_squeeze_first_three_blocks(
    libcrux_sha3_generic_keccak_KeccakState_cc *s, Eurydice_slice out0,
    Eurydice_slice out1) {
  Eurydice_slice buf[2U] = {out0, out1};
  squeeze_first_three_blocks_77(s, buf);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block
with const generics
- RATE= 144
*/
static KRML_MUSTINLINE void load_block_3c2(_uint64x2_t (*s)[5U],
                                           Eurydice_slice blocks[2U]) {
  for (size_t i = (size_t)0U; i < (size_t)144U / (size_t)16U; i++) {
    size_t i0 = i;
    _uint64x2_t v0 = _vld1q_bytes_u64(Eurydice_slice_subslice2(
        blocks[0U], (size_t)16U * i0, (size_t)16U * (i0 + (size_t)1U), uint8_t,
        Eurydice_slice));
    _uint64x2_t v1 = _vld1q_bytes_u64(Eurydice_slice_subslice2(
        blocks[1U], (size_t)16U * i0, (size_t)16U * (i0 + (size_t)1U), uint8_t,
        Eurydice_slice));
    s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U] = _veorq_u64(
        s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U],
        _vtrn1q_u64(v0, v1));
    s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
     [((size_t)2U * i0 + (size_t)1U) % (size_t)5U] =
         _veorq_u64(s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
                     [((size_t)2U * i0 + (size_t)1U) % (size_t)5U],
                    _vtrn2q_u64(v0, v1));
  }
  if ((size_t)144U % (size_t)16U != (size_t)0U) {
    size_t i = ((size_t)144U / (size_t)8U - (size_t)1U) / (size_t)5U;
    size_t j = ((size_t)144U / (size_t)8U - (size_t)1U) % (size_t)5U;
    uint64_t u[2U] = {0U};
    uint8_t uu____0[8U];
    core_result_Result_56 dst0;
    Eurydice_slice_to_array2(
        &dst0,
        Eurydice_slice_subslice2(blocks[0U], (size_t)144U - (size_t)8U,
                                 (size_t)144U, uint8_t, Eurydice_slice),
        Eurydice_slice, uint8_t[8U], void *);
    core_result_unwrap_41_ac(dst0, uu____0);
    u[0U] = core_num__u64_9__from_le_bytes(uu____0);
    uint8_t uu____1[8U];
    core_result_Result_56 dst;
    Eurydice_slice_to_array2(
        &dst,
        Eurydice_slice_subslice2(blocks[1U], (size_t)144U - (size_t)8U,
                                 (size_t)144U, uint8_t, Eurydice_slice),
        Eurydice_slice, uint8_t[8U], void *);
    core_result_unwrap_41_ac(dst, uu____1);
    u[1U] = core_num__u64_9__from_le_bytes(uu____1);
    _uint64x2_t uvec = _vld1q_u64(
        Eurydice_array_to_slice((size_t)2U, u, uint64_t, Eurydice_slice));
    s[i][j] = _veorq_u64(s[i][j], uvec);
  }
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for libcrux_intrinsics::arm64_extract::_uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block_f5
with const generics
- BLOCKSIZE= 144
*/
static KRML_MUSTINLINE void load_block_f5_0f1(_uint64x2_t (*a)[5U],
                                              Eurydice_slice b[2U]) {
  _uint64x2_t(*uu____0)[5U] = a;
  Eurydice_slice uu____1[2U];
  memcpy(uu____1, b, (size_t)2U * sizeof(Eurydice_slice));
  load_block_3c2(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block
with types libcrux_intrinsics_arm64_extract__uint64x2_t
with const generics
- N= 2
- RATE= 144
*/
static KRML_MUSTINLINE void absorb_block_121(
    libcrux_sha3_generic_keccak_KeccakState_cc *s, Eurydice_slice blocks[2U]) {
  _uint64x2_t(*uu____0)[5U] = s->st;
  Eurydice_slice uu____1[2U];
  memcpy(uu____1, blocks, (size_t)2U * sizeof(Eurydice_slice));
  load_block_f5_0f1(uu____0, uu____1);
  keccakf1600_31(s);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block_full
with const generics
- RATE= 144
*/
static KRML_MUSTINLINE void load_block_full_3e2(_uint64x2_t (*s)[5U],
                                                uint8_t blocks[2U][200U]) {
  Eurydice_slice buf[2U] = {Eurydice_array_to_slice((size_t)200U, blocks[0U],
                                                    uint8_t, Eurydice_slice),
                            Eurydice_array_to_slice((size_t)200U, blocks[1U],
                                                    uint8_t, Eurydice_slice)};
  load_block_3c2(s, buf);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for libcrux_intrinsics::arm64_extract::_uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block_full_f5
with const generics
- BLOCKSIZE= 144
*/
static KRML_MUSTINLINE void load_block_full_f5_072(_uint64x2_t (*a)[5U],
                                                   uint8_t b[2U][200U]) {
  _uint64x2_t(*uu____0)[5U] = a;
  uint8_t uu____1[2U][200U];
  memcpy(uu____1, b, (size_t)2U * sizeof(uint8_t[200U]));
  load_block_full_3e2(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final
with types libcrux_intrinsics_arm64_extract__uint64x2_t
with const generics
- N= 2
- RATE= 144
- DELIM= 6
*/
static KRML_MUSTINLINE void absorb_final_ee3(
    libcrux_sha3_generic_keccak_KeccakState_cc *s, Eurydice_slice last[2U]) {
  size_t last_len = core_slice___Slice_T___len(last[0U], uint8_t, size_t);
  uint8_t blocks[2U][200U] = {{0U}};
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      if (last_len > (size_t)0U) {
        Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
            blocks[i0], (size_t)0U, last_len, uint8_t, Eurydice_slice);
        core_slice___Slice_T___copy_from_slice(uu____0, last[i0], uint8_t,
                                               void *);
      } blocks[i0][last_len] = 6U;
      size_t uu____1 = i0; size_t uu____2 = (size_t)144U - (size_t)1U;
      blocks[uu____1][uu____2] = (uint32_t)blocks[uu____1][uu____2] | 128U;);
  _uint64x2_t(*uu____3)[5U] = s->st;
  uint8_t uu____4[2U][200U];
  memcpy(uu____4, blocks, (size_t)2U * sizeof(uint8_t[200U]));
  load_block_full_f5_072(uu____3, uu____4);
  keccakf1600_31(s);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.store_block
with const generics
- RATE= 144
*/
static KRML_MUSTINLINE void store_block_2f2(_uint64x2_t (*s)[5U],
                                            Eurydice_slice out[2U]) {
  for (size_t i = (size_t)0U; i < (size_t)144U / (size_t)16U; i++) {
    size_t i0 = i;
    _uint64x2_t v0 = _vtrn1q_u64(
        s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U],
        s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
         [((size_t)2U * i0 + (size_t)1U) % (size_t)5U]);
    _uint64x2_t v1 = _vtrn2q_u64(
        s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U],
        s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
         [((size_t)2U * i0 + (size_t)1U) % (size_t)5U]);
    _vst1q_bytes_u64(Eurydice_slice_subslice2(out[0U], (size_t)16U * i0,
                                              (size_t)16U * (i0 + (size_t)1U),
                                              uint8_t, Eurydice_slice),
                     v0);
    _vst1q_bytes_u64(Eurydice_slice_subslice2(out[1U], (size_t)16U * i0,
                                              (size_t)16U * (i0 + (size_t)1U),
                                              uint8_t, Eurydice_slice),
                     v1);
  }
  if ((size_t)144U % (size_t)16U != (size_t)0U) {
    size_t i = ((size_t)144U / (size_t)8U - (size_t)1U) / (size_t)5U;
    size_t j = ((size_t)144U / (size_t)8U - (size_t)1U) % (size_t)5U;
    uint8_t u[16U] = {0U};
    _vst1q_bytes_u64(
        Eurydice_array_to_slice((size_t)16U, u, uint8_t, Eurydice_slice),
        s[i][j]);
    Eurydice_slice uu____0 =
        Eurydice_slice_subslice2(out[0U], (size_t)144U - (size_t)8U,
                                 (size_t)144U, uint8_t, Eurydice_slice);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_subslice2(u, (size_t)0U, (size_t)8U, uint8_t,
                                    Eurydice_slice),
        uint8_t, void *);
    Eurydice_slice uu____1 =
        Eurydice_slice_subslice2(out[1U], (size_t)144U - (size_t)8U,
                                 (size_t)144U, uint8_t, Eurydice_slice);
    core_slice___Slice_T___copy_from_slice(
        uu____1,
        Eurydice_array_to_subslice2(u, (size_t)8U, (size_t)16U, uint8_t,
                                    Eurydice_slice),
        uint8_t, void *);
  }
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.store_block_full
with const generics
- RATE= 144
*/
static KRML_MUSTINLINE void store_block_full_9a1(_uint64x2_t (*s)[5U],
                                                 uint8_t ret[2U][200U]) {
  uint8_t out0[200U] = {0U};
  uint8_t out1[200U] = {0U};
  Eurydice_slice buf[2U] = {
      Eurydice_array_to_slice((size_t)200U, out0, uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)200U, out1, uint8_t, Eurydice_slice)};
  store_block_2f2(s, buf);
  uint8_t uu____0[200U];
  memcpy(uu____0, out0, (size_t)200U * sizeof(uint8_t));
  uint8_t uu____1[200U];
  memcpy(uu____1, out1, (size_t)200U * sizeof(uint8_t));
  memcpy(ret[0U], uu____0, (size_t)200U * sizeof(uint8_t));
  memcpy(ret[1U], uu____1, (size_t)200U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for libcrux_intrinsics::arm64_extract::_uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.store_block_full_f5
with const generics
- BLOCKSIZE= 144
*/
static KRML_MUSTINLINE void store_block_full_f5_a51(_uint64x2_t (*a)[5U],
                                                    uint8_t ret[2U][200U]) {
  store_block_full_9a1(a, ret);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_and_last
with types libcrux_intrinsics_arm64_extract__uint64x2_t
with const generics
- N= 2
- RATE= 144
*/
static KRML_MUSTINLINE void squeeze_first_and_last_6c1(
    libcrux_sha3_generic_keccak_KeccakState_cc *s, Eurydice_slice out[2U]) {
  uint8_t b[2U][200U];
  store_block_full_f5_a51(s->st, b);
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      Eurydice_slice uu____0 = out[i0]; uint8_t *uu____1 = b[i0];
      core_ops_range_Range_b3 lit; lit.start = (size_t)0U;
      lit.end = core_slice___Slice_T___len(out[i0], uint8_t, size_t);
      core_slice___Slice_T___copy_from_slice(
          uu____0,
          Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                     core_ops_range_Range_b3, Eurydice_slice),
          uint8_t, void *););
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for libcrux_intrinsics::arm64_extract::_uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.store_block_f5
with const generics
- BLOCKSIZE= 144
*/
static KRML_MUSTINLINE void store_block_f5_902(_uint64x2_t (*a)[5U],
                                               Eurydice_slice b[2U]) {
  store_block_2f2(a, b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_block
with types libcrux_intrinsics_arm64_extract__uint64x2_t
with const generics
- N= 2
- RATE= 144
*/
static KRML_MUSTINLINE void squeeze_first_block_bf2(
    libcrux_sha3_generic_keccak_KeccakState_cc *s, Eurydice_slice out[2U]) {
  store_block_f5_902(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_next_block
with types libcrux_intrinsics_arm64_extract__uint64x2_t
with const generics
- N= 2
- RATE= 144
*/
static KRML_MUSTINLINE void squeeze_next_block_f12(
    libcrux_sha3_generic_keccak_KeccakState_cc *s, Eurydice_slice out[2U]) {
  keccakf1600_31(s);
  store_block_f5_902(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_last
with types libcrux_intrinsics_arm64_extract__uint64x2_t
with const generics
- N= 2
- RATE= 144
*/
static KRML_MUSTINLINE void squeeze_last_6c1(
    libcrux_sha3_generic_keccak_KeccakState_cc s, Eurydice_slice out[2U]) {
  keccakf1600_31(&s);
  uint8_t b[2U][200U];
  store_block_full_f5_a51(s.st, b);
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      Eurydice_slice uu____0 = out[i0]; uint8_t *uu____1 = b[i0];
      core_ops_range_Range_b3 lit; lit.start = (size_t)0U;
      lit.end = core_slice___Slice_T___len(out[i0], uint8_t, size_t);
      core_slice___Slice_T___copy_from_slice(
          uu____0,
          Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                     core_ops_range_Range_b3, Eurydice_slice),
          uint8_t, void *););
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.keccak
with types libcrux_intrinsics_arm64_extract__uint64x2_t
with const generics
- N= 2
- RATE= 144
- DELIM= 6
*/
static KRML_MUSTINLINE void keccak_6e2(Eurydice_slice data[2U],
                                       Eurydice_slice out[2U]) {
  libcrux_sha3_generic_keccak_KeccakState_cc s = new_1e_ff();
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(data[0U], uint8_t, size_t) / (size_t)144U;
       i++) {
    size_t i0 = i;
    libcrux_sha3_generic_keccak_KeccakState_cc *uu____0 = &s;
    Eurydice_slice uu____1[2U];
    memcpy(uu____1, data, (size_t)2U * sizeof(Eurydice_slice));
    Eurydice_slice ret[2U];
    slice_n_f5(uu____1, i0 * (size_t)144U, (size_t)144U, ret);
    absorb_block_121(uu____0, ret);
  }
  size_t rem =
      core_slice___Slice_T___len(data[0U], uint8_t, size_t) % (size_t)144U;
  libcrux_sha3_generic_keccak_KeccakState_cc *uu____2 = &s;
  Eurydice_slice uu____3[2U];
  memcpy(uu____3, data, (size_t)2U * sizeof(Eurydice_slice));
  Eurydice_slice ret[2U];
  slice_n_f5(uu____3,
             core_slice___Slice_T___len(data[0U], uint8_t, size_t) - rem, rem,
             ret);
  absorb_final_ee3(uu____2, ret);
  size_t outlen = core_slice___Slice_T___len(out[0U], uint8_t, size_t);
  size_t blocks = outlen / (size_t)144U;
  size_t last = outlen - outlen % (size_t)144U;
  if (blocks == (size_t)0U) {
    squeeze_first_and_last_6c1(&s, out);
  } else {
    Eurydice_slice_uint8_t_2size_t__x2 uu____4 =
        split_at_mut_n_f5(out, (size_t)144U);
    Eurydice_slice o0[2U];
    memcpy(o0, uu____4.fst, (size_t)2U * sizeof(Eurydice_slice));
    Eurydice_slice o1[2U];
    memcpy(o1, uu____4.snd, (size_t)2U * sizeof(Eurydice_slice));
    squeeze_first_block_bf2(&s, o0);
    core_ops_range_Range_b3 iter =
        core_iter_traits_collect___core__iter__traits__collect__IntoIterator_for_I__1__into_iter(
            (CLITERAL(core_ops_range_Range_b3){.start = (size_t)1U,
                                               .end = blocks}),
            core_ops_range_Range_b3, core_ops_range_Range_b3);
    while (true) {
      if (core_iter_range___core__iter__traits__iterator__Iterator_for_core__ops__range__Range_A___6__next(
              &iter, size_t, core_option_Option_b3)
              .tag == core_option_None) {
        break;
      } else {
        Eurydice_slice_uint8_t_2size_t__x2 uu____5 =
            split_at_mut_n_f5(o1, (size_t)144U);
        Eurydice_slice o[2U];
        memcpy(o, uu____5.fst, (size_t)2U * sizeof(Eurydice_slice));
        Eurydice_slice orest[2U];
        memcpy(orest, uu____5.snd, (size_t)2U * sizeof(Eurydice_slice));
        squeeze_next_block_f12(&s, o);
        memcpy(o1, orest, (size_t)2U * sizeof(Eurydice_slice));
      }
    }
    if (last < outlen) {
      squeeze_last_6c1(s, o1);
    }
  }
}

/**
A monomorphic instance of libcrux_sha3.neon.keccakx2
with const generics
- RATE= 144
- DELIM= 6
*/
static KRML_MUSTINLINE void keccakx2_6e2(Eurydice_slice data[2U],
                                         Eurydice_slice out[2U]) {
  Eurydice_slice uu____0[2U];
  memcpy(uu____0, data, (size_t)2U * sizeof(Eurydice_slice));
  keccak_6e2(uu____0, out);
}

/**
 A portable SHA3 224 implementation.
*/
KRML_MUSTINLINE void libcrux_sha3_neon_sha224(Eurydice_slice digest,
                                              Eurydice_slice data) {
  uint8_t dummy[28U] = {0U};
  Eurydice_slice uu____0[2U] = {data, data};
  Eurydice_slice buf[2U] = {
      digest,
      Eurydice_array_to_slice((size_t)28U, dummy, uint8_t, Eurydice_slice)};
  keccakx2_6e2(uu____0, buf);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block
with const generics
- RATE= 104
*/
static KRML_MUSTINLINE void load_block_3c3(_uint64x2_t (*s)[5U],
                                           Eurydice_slice blocks[2U]) {
  for (size_t i = (size_t)0U; i < (size_t)104U / (size_t)16U; i++) {
    size_t i0 = i;
    _uint64x2_t v0 = _vld1q_bytes_u64(Eurydice_slice_subslice2(
        blocks[0U], (size_t)16U * i0, (size_t)16U * (i0 + (size_t)1U), uint8_t,
        Eurydice_slice));
    _uint64x2_t v1 = _vld1q_bytes_u64(Eurydice_slice_subslice2(
        blocks[1U], (size_t)16U * i0, (size_t)16U * (i0 + (size_t)1U), uint8_t,
        Eurydice_slice));
    s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U] = _veorq_u64(
        s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U],
        _vtrn1q_u64(v0, v1));
    s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
     [((size_t)2U * i0 + (size_t)1U) % (size_t)5U] =
         _veorq_u64(s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
                     [((size_t)2U * i0 + (size_t)1U) % (size_t)5U],
                    _vtrn2q_u64(v0, v1));
  }
  if ((size_t)104U % (size_t)16U != (size_t)0U) {
    size_t i = ((size_t)104U / (size_t)8U - (size_t)1U) / (size_t)5U;
    size_t j = ((size_t)104U / (size_t)8U - (size_t)1U) % (size_t)5U;
    uint64_t u[2U] = {0U};
    uint8_t uu____0[8U];
    core_result_Result_56 dst0;
    Eurydice_slice_to_array2(
        &dst0,
        Eurydice_slice_subslice2(blocks[0U], (size_t)104U - (size_t)8U,
                                 (size_t)104U, uint8_t, Eurydice_slice),
        Eurydice_slice, uint8_t[8U], void *);
    core_result_unwrap_41_ac(dst0, uu____0);
    u[0U] = core_num__u64_9__from_le_bytes(uu____0);
    uint8_t uu____1[8U];
    core_result_Result_56 dst;
    Eurydice_slice_to_array2(
        &dst,
        Eurydice_slice_subslice2(blocks[1U], (size_t)104U - (size_t)8U,
                                 (size_t)104U, uint8_t, Eurydice_slice),
        Eurydice_slice, uint8_t[8U], void *);
    core_result_unwrap_41_ac(dst, uu____1);
    u[1U] = core_num__u64_9__from_le_bytes(uu____1);
    _uint64x2_t uvec = _vld1q_u64(
        Eurydice_array_to_slice((size_t)2U, u, uint64_t, Eurydice_slice));
    s[i][j] = _veorq_u64(s[i][j], uvec);
  }
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for libcrux_intrinsics::arm64_extract::_uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block_f5
with const generics
- BLOCKSIZE= 104
*/
static KRML_MUSTINLINE void load_block_f5_0f2(_uint64x2_t (*a)[5U],
                                              Eurydice_slice b[2U]) {
  _uint64x2_t(*uu____0)[5U] = a;
  Eurydice_slice uu____1[2U];
  memcpy(uu____1, b, (size_t)2U * sizeof(Eurydice_slice));
  load_block_3c3(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block
with types libcrux_intrinsics_arm64_extract__uint64x2_t
with const generics
- N= 2
- RATE= 104
*/
static KRML_MUSTINLINE void absorb_block_122(
    libcrux_sha3_generic_keccak_KeccakState_cc *s, Eurydice_slice blocks[2U]) {
  _uint64x2_t(*uu____0)[5U] = s->st;
  Eurydice_slice uu____1[2U];
  memcpy(uu____1, blocks, (size_t)2U * sizeof(Eurydice_slice));
  load_block_f5_0f2(uu____0, uu____1);
  keccakf1600_31(s);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block_full
with const generics
- RATE= 104
*/
static KRML_MUSTINLINE void load_block_full_3e3(_uint64x2_t (*s)[5U],
                                                uint8_t blocks[2U][200U]) {
  Eurydice_slice buf[2U] = {Eurydice_array_to_slice((size_t)200U, blocks[0U],
                                                    uint8_t, Eurydice_slice),
                            Eurydice_array_to_slice((size_t)200U, blocks[1U],
                                                    uint8_t, Eurydice_slice)};
  load_block_3c3(s, buf);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for libcrux_intrinsics::arm64_extract::_uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block_full_f5
with const generics
- BLOCKSIZE= 104
*/
static KRML_MUSTINLINE void load_block_full_f5_073(_uint64x2_t (*a)[5U],
                                                   uint8_t b[2U][200U]) {
  _uint64x2_t(*uu____0)[5U] = a;
  uint8_t uu____1[2U][200U];
  memcpy(uu____1, b, (size_t)2U * sizeof(uint8_t[200U]));
  load_block_full_3e3(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final
with types libcrux_intrinsics_arm64_extract__uint64x2_t
with const generics
- N= 2
- RATE= 104
- DELIM= 6
*/
static KRML_MUSTINLINE void absorb_final_ee4(
    libcrux_sha3_generic_keccak_KeccakState_cc *s, Eurydice_slice last[2U]) {
  size_t last_len = core_slice___Slice_T___len(last[0U], uint8_t, size_t);
  uint8_t blocks[2U][200U] = {{0U}};
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      if (last_len > (size_t)0U) {
        Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
            blocks[i0], (size_t)0U, last_len, uint8_t, Eurydice_slice);
        core_slice___Slice_T___copy_from_slice(uu____0, last[i0], uint8_t,
                                               void *);
      } blocks[i0][last_len] = 6U;
      size_t uu____1 = i0; size_t uu____2 = (size_t)104U - (size_t)1U;
      blocks[uu____1][uu____2] = (uint32_t)blocks[uu____1][uu____2] | 128U;);
  _uint64x2_t(*uu____3)[5U] = s->st;
  uint8_t uu____4[2U][200U];
  memcpy(uu____4, blocks, (size_t)2U * sizeof(uint8_t[200U]));
  load_block_full_f5_073(uu____3, uu____4);
  keccakf1600_31(s);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.store_block
with const generics
- RATE= 104
*/
static KRML_MUSTINLINE void store_block_2f3(_uint64x2_t (*s)[5U],
                                            Eurydice_slice out[2U]) {
  for (size_t i = (size_t)0U; i < (size_t)104U / (size_t)16U; i++) {
    size_t i0 = i;
    _uint64x2_t v0 = _vtrn1q_u64(
        s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U],
        s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
         [((size_t)2U * i0 + (size_t)1U) % (size_t)5U]);
    _uint64x2_t v1 = _vtrn2q_u64(
        s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U],
        s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
         [((size_t)2U * i0 + (size_t)1U) % (size_t)5U]);
    _vst1q_bytes_u64(Eurydice_slice_subslice2(out[0U], (size_t)16U * i0,
                                              (size_t)16U * (i0 + (size_t)1U),
                                              uint8_t, Eurydice_slice),
                     v0);
    _vst1q_bytes_u64(Eurydice_slice_subslice2(out[1U], (size_t)16U * i0,
                                              (size_t)16U * (i0 + (size_t)1U),
                                              uint8_t, Eurydice_slice),
                     v1);
  }
  if ((size_t)104U % (size_t)16U != (size_t)0U) {
    size_t i = ((size_t)104U / (size_t)8U - (size_t)1U) / (size_t)5U;
    size_t j = ((size_t)104U / (size_t)8U - (size_t)1U) % (size_t)5U;
    uint8_t u[16U] = {0U};
    _vst1q_bytes_u64(
        Eurydice_array_to_slice((size_t)16U, u, uint8_t, Eurydice_slice),
        s[i][j]);
    Eurydice_slice uu____0 =
        Eurydice_slice_subslice2(out[0U], (size_t)104U - (size_t)8U,
                                 (size_t)104U, uint8_t, Eurydice_slice);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_subslice2(u, (size_t)0U, (size_t)8U, uint8_t,
                                    Eurydice_slice),
        uint8_t, void *);
    Eurydice_slice uu____1 =
        Eurydice_slice_subslice2(out[1U], (size_t)104U - (size_t)8U,
                                 (size_t)104U, uint8_t, Eurydice_slice);
    core_slice___Slice_T___copy_from_slice(
        uu____1,
        Eurydice_array_to_subslice2(u, (size_t)8U, (size_t)16U, uint8_t,
                                    Eurydice_slice),
        uint8_t, void *);
  }
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.store_block_full
with const generics
- RATE= 104
*/
static KRML_MUSTINLINE void store_block_full_9a2(_uint64x2_t (*s)[5U],
                                                 uint8_t ret[2U][200U]) {
  uint8_t out0[200U] = {0U};
  uint8_t out1[200U] = {0U};
  Eurydice_slice buf[2U] = {
      Eurydice_array_to_slice((size_t)200U, out0, uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)200U, out1, uint8_t, Eurydice_slice)};
  store_block_2f3(s, buf);
  uint8_t uu____0[200U];
  memcpy(uu____0, out0, (size_t)200U * sizeof(uint8_t));
  uint8_t uu____1[200U];
  memcpy(uu____1, out1, (size_t)200U * sizeof(uint8_t));
  memcpy(ret[0U], uu____0, (size_t)200U * sizeof(uint8_t));
  memcpy(ret[1U], uu____1, (size_t)200U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for libcrux_intrinsics::arm64_extract::_uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.store_block_full_f5
with const generics
- BLOCKSIZE= 104
*/
static KRML_MUSTINLINE void store_block_full_f5_a52(_uint64x2_t (*a)[5U],
                                                    uint8_t ret[2U][200U]) {
  store_block_full_9a2(a, ret);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_and_last
with types libcrux_intrinsics_arm64_extract__uint64x2_t
with const generics
- N= 2
- RATE= 104
*/
static KRML_MUSTINLINE void squeeze_first_and_last_6c2(
    libcrux_sha3_generic_keccak_KeccakState_cc *s, Eurydice_slice out[2U]) {
  uint8_t b[2U][200U];
  store_block_full_f5_a52(s->st, b);
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      Eurydice_slice uu____0 = out[i0]; uint8_t *uu____1 = b[i0];
      core_ops_range_Range_b3 lit; lit.start = (size_t)0U;
      lit.end = core_slice___Slice_T___len(out[i0], uint8_t, size_t);
      core_slice___Slice_T___copy_from_slice(
          uu____0,
          Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                     core_ops_range_Range_b3, Eurydice_slice),
          uint8_t, void *););
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for libcrux_intrinsics::arm64_extract::_uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.store_block_f5
with const generics
- BLOCKSIZE= 104
*/
static KRML_MUSTINLINE void store_block_f5_903(_uint64x2_t (*a)[5U],
                                               Eurydice_slice b[2U]) {
  store_block_2f3(a, b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_block
with types libcrux_intrinsics_arm64_extract__uint64x2_t
with const generics
- N= 2
- RATE= 104
*/
static KRML_MUSTINLINE void squeeze_first_block_bf3(
    libcrux_sha3_generic_keccak_KeccakState_cc *s, Eurydice_slice out[2U]) {
  store_block_f5_903(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_next_block
with types libcrux_intrinsics_arm64_extract__uint64x2_t
with const generics
- N= 2
- RATE= 104
*/
static KRML_MUSTINLINE void squeeze_next_block_f13(
    libcrux_sha3_generic_keccak_KeccakState_cc *s, Eurydice_slice out[2U]) {
  keccakf1600_31(s);
  store_block_f5_903(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_last
with types libcrux_intrinsics_arm64_extract__uint64x2_t
with const generics
- N= 2
- RATE= 104
*/
static KRML_MUSTINLINE void squeeze_last_6c2(
    libcrux_sha3_generic_keccak_KeccakState_cc s, Eurydice_slice out[2U]) {
  keccakf1600_31(&s);
  uint8_t b[2U][200U];
  store_block_full_f5_a52(s.st, b);
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      Eurydice_slice uu____0 = out[i0]; uint8_t *uu____1 = b[i0];
      core_ops_range_Range_b3 lit; lit.start = (size_t)0U;
      lit.end = core_slice___Slice_T___len(out[i0], uint8_t, size_t);
      core_slice___Slice_T___copy_from_slice(
          uu____0,
          Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                     core_ops_range_Range_b3, Eurydice_slice),
          uint8_t, void *););
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.keccak
with types libcrux_intrinsics_arm64_extract__uint64x2_t
with const generics
- N= 2
- RATE= 104
- DELIM= 6
*/
static KRML_MUSTINLINE void keccak_6e3(Eurydice_slice data[2U],
                                       Eurydice_slice out[2U]) {
  libcrux_sha3_generic_keccak_KeccakState_cc s = new_1e_ff();
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(data[0U], uint8_t, size_t) / (size_t)104U;
       i++) {
    size_t i0 = i;
    libcrux_sha3_generic_keccak_KeccakState_cc *uu____0 = &s;
    Eurydice_slice uu____1[2U];
    memcpy(uu____1, data, (size_t)2U * sizeof(Eurydice_slice));
    Eurydice_slice ret[2U];
    slice_n_f5(uu____1, i0 * (size_t)104U, (size_t)104U, ret);
    absorb_block_122(uu____0, ret);
  }
  size_t rem =
      core_slice___Slice_T___len(data[0U], uint8_t, size_t) % (size_t)104U;
  libcrux_sha3_generic_keccak_KeccakState_cc *uu____2 = &s;
  Eurydice_slice uu____3[2U];
  memcpy(uu____3, data, (size_t)2U * sizeof(Eurydice_slice));
  Eurydice_slice ret[2U];
  slice_n_f5(uu____3,
             core_slice___Slice_T___len(data[0U], uint8_t, size_t) - rem, rem,
             ret);
  absorb_final_ee4(uu____2, ret);
  size_t outlen = core_slice___Slice_T___len(out[0U], uint8_t, size_t);
  size_t blocks = outlen / (size_t)104U;
  size_t last = outlen - outlen % (size_t)104U;
  if (blocks == (size_t)0U) {
    squeeze_first_and_last_6c2(&s, out);
  } else {
    Eurydice_slice_uint8_t_2size_t__x2 uu____4 =
        split_at_mut_n_f5(out, (size_t)104U);
    Eurydice_slice o0[2U];
    memcpy(o0, uu____4.fst, (size_t)2U * sizeof(Eurydice_slice));
    Eurydice_slice o1[2U];
    memcpy(o1, uu____4.snd, (size_t)2U * sizeof(Eurydice_slice));
    squeeze_first_block_bf3(&s, o0);
    core_ops_range_Range_b3 iter =
        core_iter_traits_collect___core__iter__traits__collect__IntoIterator_for_I__1__into_iter(
            (CLITERAL(core_ops_range_Range_b3){.start = (size_t)1U,
                                               .end = blocks}),
            core_ops_range_Range_b3, core_ops_range_Range_b3);
    while (true) {
      if (core_iter_range___core__iter__traits__iterator__Iterator_for_core__ops__range__Range_A___6__next(
              &iter, size_t, core_option_Option_b3)
              .tag == core_option_None) {
        break;
      } else {
        Eurydice_slice_uint8_t_2size_t__x2 uu____5 =
            split_at_mut_n_f5(o1, (size_t)104U);
        Eurydice_slice o[2U];
        memcpy(o, uu____5.fst, (size_t)2U * sizeof(Eurydice_slice));
        Eurydice_slice orest[2U];
        memcpy(orest, uu____5.snd, (size_t)2U * sizeof(Eurydice_slice));
        squeeze_next_block_f13(&s, o);
        memcpy(o1, orest, (size_t)2U * sizeof(Eurydice_slice));
      }
    }
    if (last < outlen) {
      squeeze_last_6c2(s, o1);
    }
  }
}

/**
A monomorphic instance of libcrux_sha3.neon.keccakx2
with const generics
- RATE= 104
- DELIM= 6
*/
static KRML_MUSTINLINE void keccakx2_6e3(Eurydice_slice data[2U],
                                         Eurydice_slice out[2U]) {
  Eurydice_slice uu____0[2U];
  memcpy(uu____0, data, (size_t)2U * sizeof(Eurydice_slice));
  keccak_6e3(uu____0, out);
}

/**
 A portable SHA3 384 implementation.
*/
KRML_MUSTINLINE void libcrux_sha3_neon_sha384(Eurydice_slice digest,
                                              Eurydice_slice data) {
  uint8_t dummy[48U] = {0U};
  Eurydice_slice uu____0[2U] = {data, data};
  Eurydice_slice buf[2U] = {
      digest,
      Eurydice_array_to_slice((size_t)48U, dummy, uint8_t, Eurydice_slice)};
  keccakx2_6e3(uu____0, buf);
}
