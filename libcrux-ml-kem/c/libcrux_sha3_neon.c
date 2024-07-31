/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 45b95e0f63cb830202c0b3ca00a341a3451a02ba
 * Eurydice: 013beb9e4046a151131c6a56dfe25e606b49c4a1
 * Karamel: 4626e5fcb3787a47c806d160539342ade4b0809c
 * F*: b2931dfbe46e839cd757220c63d48c71335bb1ae
 * Libcrux: a0db75c27aa09b79eae1c2315196383465857308
 */

#include "libcrux_sha3_neon.h"

#include "internal/libcrux_core.h"

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t zero_fa(void) {
  return libcrux_intrinsics_arm64__vdupq_n_u64(0ULL);
}

static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
_veor5q_u64(core_core_arch_arm_shared_neon_uint64x2_t a,
            core_core_arch_arm_shared_neon_uint64x2_t b,
            core_core_arch_arm_shared_neon_uint64x2_t c,
            core_core_arch_arm_shared_neon_uint64x2_t d,
            core_core_arch_arm_shared_neon_uint64x2_t e) {
  core_core_arch_arm_shared_neon_uint64x2_t ab =
      libcrux_intrinsics_arm64__veorq_u64(a, b);
  core_core_arch_arm_shared_neon_uint64x2_t cd =
      libcrux_intrinsics_arm64__veorq_u64(c, d);
  core_core_arch_arm_shared_neon_uint64x2_t abcd =
      libcrux_intrinsics_arm64__veorq_u64(ab, cd);
  return libcrux_intrinsics_arm64__veorq_u64(abcd, e);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
xor5_fa(core_core_arch_arm_shared_neon_uint64x2_t a,
        core_core_arch_arm_shared_neon_uint64x2_t b,
        core_core_arch_arm_shared_neon_uint64x2_t c,
        core_core_arch_arm_shared_neon_uint64x2_t d,
        core_core_arch_arm_shared_neon_uint64x2_t e) {
  return _veor5q_u64(a, b, c, d, e);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left with const
generics:
- LEFT = 1
- RIGHT = 63
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
rotate_left_70(core_core_arch_arm_shared_neon_uint64x2_t x) {
  return libcrux_intrinsics_arm64__veorq_u64(
      libcrux_intrinsics_arm64__vshlq_n_u64(
          (int32_t)1, x, core_core_arch_arm_shared_neon_uint64x2_t),
      libcrux_intrinsics_arm64__vshrq_n_u64(
          (int32_t)63, x, core_core_arch_arm_shared_neon_uint64x2_t));
}

static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
_vrax1q_u64(core_core_arch_arm_shared_neon_uint64x2_t a,
            core_core_arch_arm_shared_neon_uint64x2_t b) {
  core_core_arch_arm_shared_neon_uint64x2_t uu____0 = a;
  return libcrux_intrinsics_arm64__veorq_u64(uu____0, rotate_left_70(b));
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
rotate_left1_and_xor_fa(core_core_arch_arm_shared_neon_uint64x2_t a,
                        core_core_arch_arm_shared_neon_uint64x2_t b) {
  return _vrax1q_u64(a, b);
}

static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
_vbcaxq_u64(core_core_arch_arm_shared_neon_uint64x2_t a,
            core_core_arch_arm_shared_neon_uint64x2_t b,
            core_core_arch_arm_shared_neon_uint64x2_t c) {
  return libcrux_intrinsics_arm64__veorq_u64(
      a, libcrux_intrinsics_arm64__vbicq_u64(b, c));
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
and_not_xor_fa(core_core_arch_arm_shared_neon_uint64x2_t a,
               core_core_arch_arm_shared_neon_uint64x2_t b,
               core_core_arch_arm_shared_neon_uint64x2_t c) {
  return _vbcaxq_u64(a, b, c);
}

static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
_veorq_n_u64(core_core_arch_arm_shared_neon_uint64x2_t a, uint64_t c) {
  core_core_arch_arm_shared_neon_uint64x2_t c0 =
      libcrux_intrinsics_arm64__vdupq_n_u64(c);
  return libcrux_intrinsics_arm64__veorq_u64(a, c0);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
xor_constant_fa(core_core_arch_arm_shared_neon_uint64x2_t a, uint64_t c) {
  return _veorq_n_u64(a, c);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
xor_fa(core_core_arch_arm_shared_neon_uint64x2_t a,
       core_core_arch_arm_shared_neon_uint64x2_t b) {
  return libcrux_intrinsics_arm64__veorq_u64(a, b);
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
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
static KRML_MUSTINLINE void slice_n_fa(Eurydice_slice a[2U], size_t start,
                                       size_t len, Eurydice_slice ret[2U]) {
  Eurydice_slice uu____0[2U];
  memcpy(uu____0, a, (size_t)2U * sizeof(Eurydice_slice));
  Eurydice_slice ret0[2U];
  slice_2(uu____0, start, len, ret0);
  memcpy(ret, ret0, (size_t)2U * sizeof(Eurydice_slice));
}

static KRML_MUSTINLINE
    K___Eurydice_slice_uint8_t_2size_t__Eurydice_slice_uint8_t_2size_t_
    split_at_mut_2(Eurydice_slice out[2U], size_t mid) {
  Eurydice_slice out0 = out[0U];
  Eurydice_slice out1 = out[1U];
  K___Eurydice_slice_uint8_t_Eurydice_slice_uint8_t uu____0 =
      core_slice___Slice_T___split_at_mut(
          out0, mid, uint8_t,
          K___Eurydice_slice_uint8_t_Eurydice_slice_uint8_t);
  Eurydice_slice out00 = uu____0.fst;
  Eurydice_slice out01 = uu____0.snd;
  K___Eurydice_slice_uint8_t_Eurydice_slice_uint8_t uu____1 =
      core_slice___Slice_T___split_at_mut(
          out1, mid, uint8_t,
          K___Eurydice_slice_uint8_t_Eurydice_slice_uint8_t);
  Eurydice_slice out10 = uu____1.fst;
  Eurydice_slice out11 = uu____1.snd;
  K___Eurydice_slice_uint8_t_2size_t__Eurydice_slice_uint8_t_2size_t_ lit;
  lit.fst[0U] = out00;
  lit.fst[1U] = out10;
  lit.snd[0U] = out01;
  lit.snd[1U] = out11;
  return lit;
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
static KRML_MUSTINLINE
    K___Eurydice_slice_uint8_t_2size_t__Eurydice_slice_uint8_t_2size_t_
    split_at_mut_n_fa(Eurydice_slice a[2U], size_t mid) {
  return split_at_mut_2(a, mid);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0]#1}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.new_1e with types
core_core_arch_arm_shared_neon_uint64x2_t and with const generics:
- N = 2
*/
static KRML_MUSTINLINE
    libcrux_sha3_generic_keccak_KeccakState__core_core_arch_arm_shared_neon_uint64x2_t__2size_t
    new_1e_39(void) {
  libcrux_sha3_generic_keccak_KeccakState__core_core_arch_arm_shared_neon_uint64x2_t__2size_t
      lit;
  lit.st[0U][0U] = zero_fa();
  lit.st[0U][1U] = zero_fa();
  lit.st[0U][2U] = zero_fa();
  lit.st[0U][3U] = zero_fa();
  lit.st[0U][4U] = zero_fa();
  lit.st[1U][0U] = zero_fa();
  lit.st[1U][1U] = zero_fa();
  lit.st[1U][2U] = zero_fa();
  lit.st[1U][3U] = zero_fa();
  lit.st[1U][4U] = zero_fa();
  lit.st[2U][0U] = zero_fa();
  lit.st[2U][1U] = zero_fa();
  lit.st[2U][2U] = zero_fa();
  lit.st[2U][3U] = zero_fa();
  lit.st[2U][4U] = zero_fa();
  lit.st[3U][0U] = zero_fa();
  lit.st[3U][1U] = zero_fa();
  lit.st[3U][2U] = zero_fa();
  lit.st[3U][3U] = zero_fa();
  lit.st[3U][4U] = zero_fa();
  lit.st[4U][0U] = zero_fa();
  lit.st[4U][1U] = zero_fa();
  lit.st[4U][2U] = zero_fa();
  lit.st[4U][3U] = zero_fa();
  lit.st[4U][4U] = zero_fa();
  return lit;
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block with const
generics:
- RATE = 72
*/
static KRML_MUSTINLINE void load_block_66(
    core_core_arch_arm_shared_neon_uint64x2_t (*s)[5U],
    Eurydice_slice blocks[2U]) {
  for (size_t i = (size_t)0U; i < (size_t)72U / (size_t)16U; i++) {
    size_t i0 = i;
    core_core_arch_arm_shared_neon_uint64x2_t v0 =
        libcrux_intrinsics_arm64__vld1q_bytes_u64(Eurydice_slice_subslice2(
            blocks[0U], (size_t)16U * i0, (size_t)16U * (i0 + (size_t)1U),
            uint8_t, Eurydice_slice));
    core_core_arch_arm_shared_neon_uint64x2_t v1 =
        libcrux_intrinsics_arm64__vld1q_bytes_u64(Eurydice_slice_subslice2(
            blocks[1U], (size_t)16U * i0, (size_t)16U * (i0 + (size_t)1U),
            uint8_t, Eurydice_slice));
    s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U] =
        libcrux_intrinsics_arm64__veorq_u64(
            s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U],
            libcrux_intrinsics_arm64__vtrn1q_u64(v0, v1));
    s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
     [((size_t)2U * i0 + (size_t)1U) % (size_t)5U] =
         libcrux_intrinsics_arm64__veorq_u64(
             s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
              [((size_t)2U * i0 + (size_t)1U) % (size_t)5U],
             libcrux_intrinsics_arm64__vtrn2q_u64(v0, v1));
  }
  if ((size_t)72U % (size_t)16U != (size_t)0U) {
    size_t i = ((size_t)72U / (size_t)8U - (size_t)1U) / (size_t)5U;
    size_t j = ((size_t)72U / (size_t)8U - (size_t)1U) % (size_t)5U;
    uint64_t u[2U] = {0U};
    uint8_t uu____0[8U];
    core_result_Result__uint8_t_8size_t__core_array_TryFromSliceError dst0;
    Eurydice_slice_to_array2(
        &dst0,
        Eurydice_slice_subslice2(blocks[0U], (size_t)72U - (size_t)8U,
                                 (size_t)72U, uint8_t, Eurydice_slice),
        Eurydice_slice, uint8_t[8U], void *);
    core_result_unwrap_41_15(dst0, uu____0);
    u[0U] = core_num__u64_9__from_le_bytes(uu____0);
    uint8_t uu____1[8U];
    core_result_Result__uint8_t_8size_t__core_array_TryFromSliceError dst;
    Eurydice_slice_to_array2(
        &dst,
        Eurydice_slice_subslice2(blocks[1U], (size_t)72U - (size_t)8U,
                                 (size_t)72U, uint8_t, Eurydice_slice),
        Eurydice_slice, uint8_t[8U], void *);
    core_result_unwrap_41_15(dst, uu____1);
    u[1U] = core_num__u64_9__from_le_bytes(uu____1);
    core_core_arch_arm_shared_neon_uint64x2_t uvec =
        libcrux_intrinsics_arm64__vld1q_u64(
            Eurydice_array_to_slice((size_t)2U, u, uint64_t, Eurydice_slice));
    s[i][j] = libcrux_intrinsics_arm64__veorq_u64(s[i][j], uvec);
  }
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block_fa with const
generics:
- BLOCKSIZE = 72
*/
static KRML_MUSTINLINE void load_block_fa_66(
    core_core_arch_arm_shared_neon_uint64x2_t (*a)[5U], Eurydice_slice b[2U]) {
  core_core_arch_arm_shared_neon_uint64x2_t(*uu____0)[5U] = a;
  Eurydice_slice uu____1[2U];
  memcpy(uu____1, b, (size_t)2U * sizeof(Eurydice_slice));
  load_block_66(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left with const
generics:
- LEFT = 36
- RIGHT = 28
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
rotate_left_71(core_core_arch_arm_shared_neon_uint64x2_t x) {
  return libcrux_intrinsics_arm64__veorq_u64(
      libcrux_intrinsics_arm64__vshlq_n_u64(
          (int32_t)36, x, core_core_arch_arm_shared_neon_uint64x2_t),
      libcrux_intrinsics_arm64__vshrq_n_u64(
          (int32_t)28, x, core_core_arch_arm_shared_neon_uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64 with const
generics:
- LEFT = 36
- RIGHT = 28
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
_vxarq_u64_71(core_core_arch_arm_shared_neon_uint64x2_t a,
              core_core_arch_arm_shared_neon_uint64x2_t b) {
  core_core_arch_arm_shared_neon_uint64x2_t ab =
      libcrux_intrinsics_arm64__veorq_u64(a, b);
  return rotate_left_71(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_fa with const
generics:
- LEFT = 36
- RIGHT = 28
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
xor_and_rotate_fa_71(core_core_arch_arm_shared_neon_uint64x2_t a,
                     core_core_arch_arm_shared_neon_uint64x2_t b) {
  return _vxarq_u64_71(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left with const
generics:
- LEFT = 3
- RIGHT = 61
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
rotate_left_08(core_core_arch_arm_shared_neon_uint64x2_t x) {
  return libcrux_intrinsics_arm64__veorq_u64(
      libcrux_intrinsics_arm64__vshlq_n_u64(
          (int32_t)3, x, core_core_arch_arm_shared_neon_uint64x2_t),
      libcrux_intrinsics_arm64__vshrq_n_u64(
          (int32_t)61, x, core_core_arch_arm_shared_neon_uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64 with const
generics:
- LEFT = 3
- RIGHT = 61
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
_vxarq_u64_08(core_core_arch_arm_shared_neon_uint64x2_t a,
              core_core_arch_arm_shared_neon_uint64x2_t b) {
  core_core_arch_arm_shared_neon_uint64x2_t ab =
      libcrux_intrinsics_arm64__veorq_u64(a, b);
  return rotate_left_08(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_fa with const
generics:
- LEFT = 3
- RIGHT = 61
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
xor_and_rotate_fa_08(core_core_arch_arm_shared_neon_uint64x2_t a,
                     core_core_arch_arm_shared_neon_uint64x2_t b) {
  return _vxarq_u64_08(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left with const
generics:
- LEFT = 41
- RIGHT = 23
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
rotate_left_6a(core_core_arch_arm_shared_neon_uint64x2_t x) {
  return libcrux_intrinsics_arm64__veorq_u64(
      libcrux_intrinsics_arm64__vshlq_n_u64(
          (int32_t)41, x, core_core_arch_arm_shared_neon_uint64x2_t),
      libcrux_intrinsics_arm64__vshrq_n_u64(
          (int32_t)23, x, core_core_arch_arm_shared_neon_uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64 with const
generics:
- LEFT = 41
- RIGHT = 23
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
_vxarq_u64_6a(core_core_arch_arm_shared_neon_uint64x2_t a,
              core_core_arch_arm_shared_neon_uint64x2_t b) {
  core_core_arch_arm_shared_neon_uint64x2_t ab =
      libcrux_intrinsics_arm64__veorq_u64(a, b);
  return rotate_left_6a(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_fa with const
generics:
- LEFT = 41
- RIGHT = 23
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
xor_and_rotate_fa_6a(core_core_arch_arm_shared_neon_uint64x2_t a,
                     core_core_arch_arm_shared_neon_uint64x2_t b) {
  return _vxarq_u64_6a(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left with const
generics:
- LEFT = 18
- RIGHT = 46
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
rotate_left_95(core_core_arch_arm_shared_neon_uint64x2_t x) {
  return libcrux_intrinsics_arm64__veorq_u64(
      libcrux_intrinsics_arm64__vshlq_n_u64(
          (int32_t)18, x, core_core_arch_arm_shared_neon_uint64x2_t),
      libcrux_intrinsics_arm64__vshrq_n_u64(
          (int32_t)46, x, core_core_arch_arm_shared_neon_uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64 with const
generics:
- LEFT = 18
- RIGHT = 46
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
_vxarq_u64_95(core_core_arch_arm_shared_neon_uint64x2_t a,
              core_core_arch_arm_shared_neon_uint64x2_t b) {
  core_core_arch_arm_shared_neon_uint64x2_t ab =
      libcrux_intrinsics_arm64__veorq_u64(a, b);
  return rotate_left_95(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_fa with const
generics:
- LEFT = 18
- RIGHT = 46
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
xor_and_rotate_fa_95(core_core_arch_arm_shared_neon_uint64x2_t a,
                     core_core_arch_arm_shared_neon_uint64x2_t b) {
  return _vxarq_u64_95(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64 with const
generics:
- LEFT = 1
- RIGHT = 63
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
_vxarq_u64_70(core_core_arch_arm_shared_neon_uint64x2_t a,
              core_core_arch_arm_shared_neon_uint64x2_t b) {
  core_core_arch_arm_shared_neon_uint64x2_t ab =
      libcrux_intrinsics_arm64__veorq_u64(a, b);
  return rotate_left_70(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_fa with const
generics:
- LEFT = 1
- RIGHT = 63
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
xor_and_rotate_fa_70(core_core_arch_arm_shared_neon_uint64x2_t a,
                     core_core_arch_arm_shared_neon_uint64x2_t b) {
  return _vxarq_u64_70(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left with const
generics:
- LEFT = 44
- RIGHT = 20
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
rotate_left_e1(core_core_arch_arm_shared_neon_uint64x2_t x) {
  return libcrux_intrinsics_arm64__veorq_u64(
      libcrux_intrinsics_arm64__vshlq_n_u64(
          (int32_t)44, x, core_core_arch_arm_shared_neon_uint64x2_t),
      libcrux_intrinsics_arm64__vshrq_n_u64(
          (int32_t)20, x, core_core_arch_arm_shared_neon_uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64 with const
generics:
- LEFT = 44
- RIGHT = 20
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
_vxarq_u64_e1(core_core_arch_arm_shared_neon_uint64x2_t a,
              core_core_arch_arm_shared_neon_uint64x2_t b) {
  core_core_arch_arm_shared_neon_uint64x2_t ab =
      libcrux_intrinsics_arm64__veorq_u64(a, b);
  return rotate_left_e1(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_fa with const
generics:
- LEFT = 44
- RIGHT = 20
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
xor_and_rotate_fa_e1(core_core_arch_arm_shared_neon_uint64x2_t a,
                     core_core_arch_arm_shared_neon_uint64x2_t b) {
  return _vxarq_u64_e1(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left with const
generics:
- LEFT = 10
- RIGHT = 54
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
rotate_left_ce(core_core_arch_arm_shared_neon_uint64x2_t x) {
  return libcrux_intrinsics_arm64__veorq_u64(
      libcrux_intrinsics_arm64__vshlq_n_u64(
          (int32_t)10, x, core_core_arch_arm_shared_neon_uint64x2_t),
      libcrux_intrinsics_arm64__vshrq_n_u64(
          (int32_t)54, x, core_core_arch_arm_shared_neon_uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64 with const
generics:
- LEFT = 10
- RIGHT = 54
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
_vxarq_u64_ce(core_core_arch_arm_shared_neon_uint64x2_t a,
              core_core_arch_arm_shared_neon_uint64x2_t b) {
  core_core_arch_arm_shared_neon_uint64x2_t ab =
      libcrux_intrinsics_arm64__veorq_u64(a, b);
  return rotate_left_ce(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_fa with const
generics:
- LEFT = 10
- RIGHT = 54
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
xor_and_rotate_fa_ce(core_core_arch_arm_shared_neon_uint64x2_t a,
                     core_core_arch_arm_shared_neon_uint64x2_t b) {
  return _vxarq_u64_ce(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left with const
generics:
- LEFT = 45
- RIGHT = 19
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
rotate_left_b6(core_core_arch_arm_shared_neon_uint64x2_t x) {
  return libcrux_intrinsics_arm64__veorq_u64(
      libcrux_intrinsics_arm64__vshlq_n_u64(
          (int32_t)45, x, core_core_arch_arm_shared_neon_uint64x2_t),
      libcrux_intrinsics_arm64__vshrq_n_u64(
          (int32_t)19, x, core_core_arch_arm_shared_neon_uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64 with const
generics:
- LEFT = 45
- RIGHT = 19
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
_vxarq_u64_b6(core_core_arch_arm_shared_neon_uint64x2_t a,
              core_core_arch_arm_shared_neon_uint64x2_t b) {
  core_core_arch_arm_shared_neon_uint64x2_t ab =
      libcrux_intrinsics_arm64__veorq_u64(a, b);
  return rotate_left_b6(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_fa with const
generics:
- LEFT = 45
- RIGHT = 19
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
xor_and_rotate_fa_b6(core_core_arch_arm_shared_neon_uint64x2_t a,
                     core_core_arch_arm_shared_neon_uint64x2_t b) {
  return _vxarq_u64_b6(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left with const
generics:
- LEFT = 2
- RIGHT = 62
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
rotate_left_2a(core_core_arch_arm_shared_neon_uint64x2_t x) {
  return libcrux_intrinsics_arm64__veorq_u64(
      libcrux_intrinsics_arm64__vshlq_n_u64(
          (int32_t)2, x, core_core_arch_arm_shared_neon_uint64x2_t),
      libcrux_intrinsics_arm64__vshrq_n_u64(
          (int32_t)62, x, core_core_arch_arm_shared_neon_uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64 with const
generics:
- LEFT = 2
- RIGHT = 62
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
_vxarq_u64_2a(core_core_arch_arm_shared_neon_uint64x2_t a,
              core_core_arch_arm_shared_neon_uint64x2_t b) {
  core_core_arch_arm_shared_neon_uint64x2_t ab =
      libcrux_intrinsics_arm64__veorq_u64(a, b);
  return rotate_left_2a(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_fa with const
generics:
- LEFT = 2
- RIGHT = 62
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
xor_and_rotate_fa_2a(core_core_arch_arm_shared_neon_uint64x2_t a,
                     core_core_arch_arm_shared_neon_uint64x2_t b) {
  return _vxarq_u64_2a(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left with const
generics:
- LEFT = 62
- RIGHT = 2
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
rotate_left_25(core_core_arch_arm_shared_neon_uint64x2_t x) {
  return libcrux_intrinsics_arm64__veorq_u64(
      libcrux_intrinsics_arm64__vshlq_n_u64(
          (int32_t)62, x, core_core_arch_arm_shared_neon_uint64x2_t),
      libcrux_intrinsics_arm64__vshrq_n_u64(
          (int32_t)2, x, core_core_arch_arm_shared_neon_uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64 with const
generics:
- LEFT = 62
- RIGHT = 2
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
_vxarq_u64_25(core_core_arch_arm_shared_neon_uint64x2_t a,
              core_core_arch_arm_shared_neon_uint64x2_t b) {
  core_core_arch_arm_shared_neon_uint64x2_t ab =
      libcrux_intrinsics_arm64__veorq_u64(a, b);
  return rotate_left_25(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_fa with const
generics:
- LEFT = 62
- RIGHT = 2
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
xor_and_rotate_fa_25(core_core_arch_arm_shared_neon_uint64x2_t a,
                     core_core_arch_arm_shared_neon_uint64x2_t b) {
  return _vxarq_u64_25(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left with const
generics:
- LEFT = 6
- RIGHT = 58
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
rotate_left_4b(core_core_arch_arm_shared_neon_uint64x2_t x) {
  return libcrux_intrinsics_arm64__veorq_u64(
      libcrux_intrinsics_arm64__vshlq_n_u64(
          (int32_t)6, x, core_core_arch_arm_shared_neon_uint64x2_t),
      libcrux_intrinsics_arm64__vshrq_n_u64(
          (int32_t)58, x, core_core_arch_arm_shared_neon_uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64 with const
generics:
- LEFT = 6
- RIGHT = 58
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
_vxarq_u64_4b(core_core_arch_arm_shared_neon_uint64x2_t a,
              core_core_arch_arm_shared_neon_uint64x2_t b) {
  core_core_arch_arm_shared_neon_uint64x2_t ab =
      libcrux_intrinsics_arm64__veorq_u64(a, b);
  return rotate_left_4b(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_fa with const
generics:
- LEFT = 6
- RIGHT = 58
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
xor_and_rotate_fa_4b(core_core_arch_arm_shared_neon_uint64x2_t a,
                     core_core_arch_arm_shared_neon_uint64x2_t b) {
  return _vxarq_u64_4b(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left with const
generics:
- LEFT = 43
- RIGHT = 21
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
rotate_left_c2(core_core_arch_arm_shared_neon_uint64x2_t x) {
  return libcrux_intrinsics_arm64__veorq_u64(
      libcrux_intrinsics_arm64__vshlq_n_u64(
          (int32_t)43, x, core_core_arch_arm_shared_neon_uint64x2_t),
      libcrux_intrinsics_arm64__vshrq_n_u64(
          (int32_t)21, x, core_core_arch_arm_shared_neon_uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64 with const
generics:
- LEFT = 43
- RIGHT = 21
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
_vxarq_u64_c2(core_core_arch_arm_shared_neon_uint64x2_t a,
              core_core_arch_arm_shared_neon_uint64x2_t b) {
  core_core_arch_arm_shared_neon_uint64x2_t ab =
      libcrux_intrinsics_arm64__veorq_u64(a, b);
  return rotate_left_c2(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_fa with const
generics:
- LEFT = 43
- RIGHT = 21
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
xor_and_rotate_fa_c2(core_core_arch_arm_shared_neon_uint64x2_t a,
                     core_core_arch_arm_shared_neon_uint64x2_t b) {
  return _vxarq_u64_c2(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left with const
generics:
- LEFT = 15
- RIGHT = 49
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
rotate_left_3e(core_core_arch_arm_shared_neon_uint64x2_t x) {
  return libcrux_intrinsics_arm64__veorq_u64(
      libcrux_intrinsics_arm64__vshlq_n_u64(
          (int32_t)15, x, core_core_arch_arm_shared_neon_uint64x2_t),
      libcrux_intrinsics_arm64__vshrq_n_u64(
          (int32_t)49, x, core_core_arch_arm_shared_neon_uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64 with const
generics:
- LEFT = 15
- RIGHT = 49
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
_vxarq_u64_3e(core_core_arch_arm_shared_neon_uint64x2_t a,
              core_core_arch_arm_shared_neon_uint64x2_t b) {
  core_core_arch_arm_shared_neon_uint64x2_t ab =
      libcrux_intrinsics_arm64__veorq_u64(a, b);
  return rotate_left_3e(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_fa with const
generics:
- LEFT = 15
- RIGHT = 49
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
xor_and_rotate_fa_3e(core_core_arch_arm_shared_neon_uint64x2_t a,
                     core_core_arch_arm_shared_neon_uint64x2_t b) {
  return _vxarq_u64_3e(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left with const
generics:
- LEFT = 61
- RIGHT = 3
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
rotate_left_bd(core_core_arch_arm_shared_neon_uint64x2_t x) {
  return libcrux_intrinsics_arm64__veorq_u64(
      libcrux_intrinsics_arm64__vshlq_n_u64(
          (int32_t)61, x, core_core_arch_arm_shared_neon_uint64x2_t),
      libcrux_intrinsics_arm64__vshrq_n_u64(
          (int32_t)3, x, core_core_arch_arm_shared_neon_uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64 with const
generics:
- LEFT = 61
- RIGHT = 3
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
_vxarq_u64_bd(core_core_arch_arm_shared_neon_uint64x2_t a,
              core_core_arch_arm_shared_neon_uint64x2_t b) {
  core_core_arch_arm_shared_neon_uint64x2_t ab =
      libcrux_intrinsics_arm64__veorq_u64(a, b);
  return rotate_left_bd(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_fa with const
generics:
- LEFT = 61
- RIGHT = 3
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
xor_and_rotate_fa_bd(core_core_arch_arm_shared_neon_uint64x2_t a,
                     core_core_arch_arm_shared_neon_uint64x2_t b) {
  return _vxarq_u64_bd(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left with const
generics:
- LEFT = 28
- RIGHT = 36
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
rotate_left_42(core_core_arch_arm_shared_neon_uint64x2_t x) {
  return libcrux_intrinsics_arm64__veorq_u64(
      libcrux_intrinsics_arm64__vshlq_n_u64(
          (int32_t)28, x, core_core_arch_arm_shared_neon_uint64x2_t),
      libcrux_intrinsics_arm64__vshrq_n_u64(
          (int32_t)36, x, core_core_arch_arm_shared_neon_uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64 with const
generics:
- LEFT = 28
- RIGHT = 36
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
_vxarq_u64_42(core_core_arch_arm_shared_neon_uint64x2_t a,
              core_core_arch_arm_shared_neon_uint64x2_t b) {
  core_core_arch_arm_shared_neon_uint64x2_t ab =
      libcrux_intrinsics_arm64__veorq_u64(a, b);
  return rotate_left_42(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_fa with const
generics:
- LEFT = 28
- RIGHT = 36
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
xor_and_rotate_fa_42(core_core_arch_arm_shared_neon_uint64x2_t a,
                     core_core_arch_arm_shared_neon_uint64x2_t b) {
  return _vxarq_u64_42(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left with const
generics:
- LEFT = 55
- RIGHT = 9
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
rotate_left_64(core_core_arch_arm_shared_neon_uint64x2_t x) {
  return libcrux_intrinsics_arm64__veorq_u64(
      libcrux_intrinsics_arm64__vshlq_n_u64(
          (int32_t)55, x, core_core_arch_arm_shared_neon_uint64x2_t),
      libcrux_intrinsics_arm64__vshrq_n_u64(
          (int32_t)9, x, core_core_arch_arm_shared_neon_uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64 with const
generics:
- LEFT = 55
- RIGHT = 9
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
_vxarq_u64_64(core_core_arch_arm_shared_neon_uint64x2_t a,
              core_core_arch_arm_shared_neon_uint64x2_t b) {
  core_core_arch_arm_shared_neon_uint64x2_t ab =
      libcrux_intrinsics_arm64__veorq_u64(a, b);
  return rotate_left_64(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_fa with const
generics:
- LEFT = 55
- RIGHT = 9
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
xor_and_rotate_fa_64(core_core_arch_arm_shared_neon_uint64x2_t a,
                     core_core_arch_arm_shared_neon_uint64x2_t b) {
  return _vxarq_u64_64(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left with const
generics:
- LEFT = 25
- RIGHT = 39
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
rotate_left_cc(core_core_arch_arm_shared_neon_uint64x2_t x) {
  return libcrux_intrinsics_arm64__veorq_u64(
      libcrux_intrinsics_arm64__vshlq_n_u64(
          (int32_t)25, x, core_core_arch_arm_shared_neon_uint64x2_t),
      libcrux_intrinsics_arm64__vshrq_n_u64(
          (int32_t)39, x, core_core_arch_arm_shared_neon_uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64 with const
generics:
- LEFT = 25
- RIGHT = 39
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
_vxarq_u64_cc(core_core_arch_arm_shared_neon_uint64x2_t a,
              core_core_arch_arm_shared_neon_uint64x2_t b) {
  core_core_arch_arm_shared_neon_uint64x2_t ab =
      libcrux_intrinsics_arm64__veorq_u64(a, b);
  return rotate_left_cc(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_fa with const
generics:
- LEFT = 25
- RIGHT = 39
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
xor_and_rotate_fa_cc(core_core_arch_arm_shared_neon_uint64x2_t a,
                     core_core_arch_arm_shared_neon_uint64x2_t b) {
  return _vxarq_u64_cc(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left with const
generics:
- LEFT = 21
- RIGHT = 43
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
rotate_left_d5(core_core_arch_arm_shared_neon_uint64x2_t x) {
  return libcrux_intrinsics_arm64__veorq_u64(
      libcrux_intrinsics_arm64__vshlq_n_u64(
          (int32_t)21, x, core_core_arch_arm_shared_neon_uint64x2_t),
      libcrux_intrinsics_arm64__vshrq_n_u64(
          (int32_t)43, x, core_core_arch_arm_shared_neon_uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64 with const
generics:
- LEFT = 21
- RIGHT = 43
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
_vxarq_u64_d5(core_core_arch_arm_shared_neon_uint64x2_t a,
              core_core_arch_arm_shared_neon_uint64x2_t b) {
  core_core_arch_arm_shared_neon_uint64x2_t ab =
      libcrux_intrinsics_arm64__veorq_u64(a, b);
  return rotate_left_d5(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_fa with const
generics:
- LEFT = 21
- RIGHT = 43
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
xor_and_rotate_fa_d5(core_core_arch_arm_shared_neon_uint64x2_t a,
                     core_core_arch_arm_shared_neon_uint64x2_t b) {
  return _vxarq_u64_d5(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left with const
generics:
- LEFT = 56
- RIGHT = 8
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
rotate_left_61(core_core_arch_arm_shared_neon_uint64x2_t x) {
  return libcrux_intrinsics_arm64__veorq_u64(
      libcrux_intrinsics_arm64__vshlq_n_u64(
          (int32_t)56, x, core_core_arch_arm_shared_neon_uint64x2_t),
      libcrux_intrinsics_arm64__vshrq_n_u64(
          (int32_t)8, x, core_core_arch_arm_shared_neon_uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64 with const
generics:
- LEFT = 56
- RIGHT = 8
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
_vxarq_u64_61(core_core_arch_arm_shared_neon_uint64x2_t a,
              core_core_arch_arm_shared_neon_uint64x2_t b) {
  core_core_arch_arm_shared_neon_uint64x2_t ab =
      libcrux_intrinsics_arm64__veorq_u64(a, b);
  return rotate_left_61(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_fa with const
generics:
- LEFT = 56
- RIGHT = 8
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
xor_and_rotate_fa_61(core_core_arch_arm_shared_neon_uint64x2_t a,
                     core_core_arch_arm_shared_neon_uint64x2_t b) {
  return _vxarq_u64_61(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left with const
generics:
- LEFT = 27
- RIGHT = 37
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
rotate_left_6f(core_core_arch_arm_shared_neon_uint64x2_t x) {
  return libcrux_intrinsics_arm64__veorq_u64(
      libcrux_intrinsics_arm64__vshlq_n_u64(
          (int32_t)27, x, core_core_arch_arm_shared_neon_uint64x2_t),
      libcrux_intrinsics_arm64__vshrq_n_u64(
          (int32_t)37, x, core_core_arch_arm_shared_neon_uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64 with const
generics:
- LEFT = 27
- RIGHT = 37
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
_vxarq_u64_6f(core_core_arch_arm_shared_neon_uint64x2_t a,
              core_core_arch_arm_shared_neon_uint64x2_t b) {
  core_core_arch_arm_shared_neon_uint64x2_t ab =
      libcrux_intrinsics_arm64__veorq_u64(a, b);
  return rotate_left_6f(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_fa with const
generics:
- LEFT = 27
- RIGHT = 37
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
xor_and_rotate_fa_6f(core_core_arch_arm_shared_neon_uint64x2_t a,
                     core_core_arch_arm_shared_neon_uint64x2_t b) {
  return _vxarq_u64_6f(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left with const
generics:
- LEFT = 20
- RIGHT = 44
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
rotate_left_06(core_core_arch_arm_shared_neon_uint64x2_t x) {
  return libcrux_intrinsics_arm64__veorq_u64(
      libcrux_intrinsics_arm64__vshlq_n_u64(
          (int32_t)20, x, core_core_arch_arm_shared_neon_uint64x2_t),
      libcrux_intrinsics_arm64__vshrq_n_u64(
          (int32_t)44, x, core_core_arch_arm_shared_neon_uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64 with const
generics:
- LEFT = 20
- RIGHT = 44
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
_vxarq_u64_06(core_core_arch_arm_shared_neon_uint64x2_t a,
              core_core_arch_arm_shared_neon_uint64x2_t b) {
  core_core_arch_arm_shared_neon_uint64x2_t ab =
      libcrux_intrinsics_arm64__veorq_u64(a, b);
  return rotate_left_06(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_fa with const
generics:
- LEFT = 20
- RIGHT = 44
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
xor_and_rotate_fa_06(core_core_arch_arm_shared_neon_uint64x2_t a,
                     core_core_arch_arm_shared_neon_uint64x2_t b) {
  return _vxarq_u64_06(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left with const
generics:
- LEFT = 39
- RIGHT = 25
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
rotate_left_3d(core_core_arch_arm_shared_neon_uint64x2_t x) {
  return libcrux_intrinsics_arm64__veorq_u64(
      libcrux_intrinsics_arm64__vshlq_n_u64(
          (int32_t)39, x, core_core_arch_arm_shared_neon_uint64x2_t),
      libcrux_intrinsics_arm64__vshrq_n_u64(
          (int32_t)25, x, core_core_arch_arm_shared_neon_uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64 with const
generics:
- LEFT = 39
- RIGHT = 25
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
_vxarq_u64_3d(core_core_arch_arm_shared_neon_uint64x2_t a,
              core_core_arch_arm_shared_neon_uint64x2_t b) {
  core_core_arch_arm_shared_neon_uint64x2_t ab =
      libcrux_intrinsics_arm64__veorq_u64(a, b);
  return rotate_left_3d(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_fa with const
generics:
- LEFT = 39
- RIGHT = 25
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
xor_and_rotate_fa_3d(core_core_arch_arm_shared_neon_uint64x2_t a,
                     core_core_arch_arm_shared_neon_uint64x2_t b) {
  return _vxarq_u64_3d(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left with const
generics:
- LEFT = 8
- RIGHT = 56
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
rotate_left_0c(core_core_arch_arm_shared_neon_uint64x2_t x) {
  return libcrux_intrinsics_arm64__veorq_u64(
      libcrux_intrinsics_arm64__vshlq_n_u64(
          (int32_t)8, x, core_core_arch_arm_shared_neon_uint64x2_t),
      libcrux_intrinsics_arm64__vshrq_n_u64(
          (int32_t)56, x, core_core_arch_arm_shared_neon_uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64 with const
generics:
- LEFT = 8
- RIGHT = 56
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
_vxarq_u64_0c(core_core_arch_arm_shared_neon_uint64x2_t a,
              core_core_arch_arm_shared_neon_uint64x2_t b) {
  core_core_arch_arm_shared_neon_uint64x2_t ab =
      libcrux_intrinsics_arm64__veorq_u64(a, b);
  return rotate_left_0c(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_fa with const
generics:
- LEFT = 8
- RIGHT = 56
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
xor_and_rotate_fa_0c(core_core_arch_arm_shared_neon_uint64x2_t a,
                     core_core_arch_arm_shared_neon_uint64x2_t b) {
  return _vxarq_u64_0c(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left with const
generics:
- LEFT = 14
- RIGHT = 50
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
rotate_left_98(core_core_arch_arm_shared_neon_uint64x2_t x) {
  return libcrux_intrinsics_arm64__veorq_u64(
      libcrux_intrinsics_arm64__vshlq_n_u64(
          (int32_t)14, x, core_core_arch_arm_shared_neon_uint64x2_t),
      libcrux_intrinsics_arm64__vshrq_n_u64(
          (int32_t)50, x, core_core_arch_arm_shared_neon_uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64 with const
generics:
- LEFT = 14
- RIGHT = 50
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
_vxarq_u64_98(core_core_arch_arm_shared_neon_uint64x2_t a,
              core_core_arch_arm_shared_neon_uint64x2_t b) {
  core_core_arch_arm_shared_neon_uint64x2_t ab =
      libcrux_intrinsics_arm64__veorq_u64(a, b);
  return rotate_left_98(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_fa with const
generics:
- LEFT = 14
- RIGHT = 50
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
xor_and_rotate_fa_98(core_core_arch_arm_shared_neon_uint64x2_t a,
                     core_core_arch_arm_shared_neon_uint64x2_t b) {
  return _vxarq_u64_98(a, b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.theta_rho with types
core_core_arch_arm_shared_neon_uint64x2_t and with const generics:
- N = 2
*/
static KRML_MUSTINLINE void theta_rho_39(
    libcrux_sha3_generic_keccak_KeccakState__core_core_arch_arm_shared_neon_uint64x2_t__2size_t
        *s) {
  core_core_arch_arm_shared_neon_uint64x2_t c[5U] = {
      xor5_fa(s->st[0U][0U], s->st[1U][0U], s->st[2U][0U], s->st[3U][0U],
              s->st[4U][0U]),
      xor5_fa(s->st[0U][1U], s->st[1U][1U], s->st[2U][1U], s->st[3U][1U],
              s->st[4U][1U]),
      xor5_fa(s->st[0U][2U], s->st[1U][2U], s->st[2U][2U], s->st[3U][2U],
              s->st[4U][2U]),
      xor5_fa(s->st[0U][3U], s->st[1U][3U], s->st[2U][3U], s->st[3U][3U],
              s->st[4U][3U]),
      xor5_fa(s->st[0U][4U], s->st[1U][4U], s->st[2U][4U], s->st[3U][4U],
              s->st[4U][4U])};
  core_core_arch_arm_shared_neon_uint64x2_t uu____0 =
      rotate_left1_and_xor_fa(c[((size_t)0U + (size_t)4U) % (size_t)5U],
                              c[((size_t)0U + (size_t)1U) % (size_t)5U]);
  core_core_arch_arm_shared_neon_uint64x2_t uu____1 =
      rotate_left1_and_xor_fa(c[((size_t)1U + (size_t)4U) % (size_t)5U],
                              c[((size_t)1U + (size_t)1U) % (size_t)5U]);
  core_core_arch_arm_shared_neon_uint64x2_t uu____2 =
      rotate_left1_and_xor_fa(c[((size_t)2U + (size_t)4U) % (size_t)5U],
                              c[((size_t)2U + (size_t)1U) % (size_t)5U]);
  core_core_arch_arm_shared_neon_uint64x2_t uu____3 =
      rotate_left1_and_xor_fa(c[((size_t)3U + (size_t)4U) % (size_t)5U],
                              c[((size_t)3U + (size_t)1U) % (size_t)5U]);
  core_core_arch_arm_shared_neon_uint64x2_t t[5U] = {
      uu____0, uu____1, uu____2, uu____3,
      rotate_left1_and_xor_fa(c[((size_t)4U + (size_t)4U) % (size_t)5U],
                              c[((size_t)4U + (size_t)1U) % (size_t)5U])};
  s->st[0U][0U] = xor_fa(s->st[0U][0U], t[0U]);
  core_core_arch_arm_shared_neon_uint64x2_t uu____4 =
      xor_and_rotate_fa_71(s->st[1U][0U], t[0U]);
  s->st[1U][0U] = uu____4;
  core_core_arch_arm_shared_neon_uint64x2_t uu____5 =
      xor_and_rotate_fa_08(s->st[2U][0U], t[0U]);
  s->st[2U][0U] = uu____5;
  core_core_arch_arm_shared_neon_uint64x2_t uu____6 =
      xor_and_rotate_fa_6a(s->st[3U][0U], t[0U]);
  s->st[3U][0U] = uu____6;
  core_core_arch_arm_shared_neon_uint64x2_t uu____7 =
      xor_and_rotate_fa_95(s->st[4U][0U], t[0U]);
  s->st[4U][0U] = uu____7;
  core_core_arch_arm_shared_neon_uint64x2_t uu____8 =
      xor_and_rotate_fa_70(s->st[0U][1U], t[1U]);
  s->st[0U][1U] = uu____8;
  core_core_arch_arm_shared_neon_uint64x2_t uu____9 =
      xor_and_rotate_fa_e1(s->st[1U][1U], t[1U]);
  s->st[1U][1U] = uu____9;
  core_core_arch_arm_shared_neon_uint64x2_t uu____10 =
      xor_and_rotate_fa_ce(s->st[2U][1U], t[1U]);
  s->st[2U][1U] = uu____10;
  core_core_arch_arm_shared_neon_uint64x2_t uu____11 =
      xor_and_rotate_fa_b6(s->st[3U][1U], t[1U]);
  s->st[3U][1U] = uu____11;
  core_core_arch_arm_shared_neon_uint64x2_t uu____12 =
      xor_and_rotate_fa_2a(s->st[4U][1U], t[1U]);
  s->st[4U][1U] = uu____12;
  core_core_arch_arm_shared_neon_uint64x2_t uu____13 =
      xor_and_rotate_fa_25(s->st[0U][2U], t[2U]);
  s->st[0U][2U] = uu____13;
  core_core_arch_arm_shared_neon_uint64x2_t uu____14 =
      xor_and_rotate_fa_4b(s->st[1U][2U], t[2U]);
  s->st[1U][2U] = uu____14;
  core_core_arch_arm_shared_neon_uint64x2_t uu____15 =
      xor_and_rotate_fa_c2(s->st[2U][2U], t[2U]);
  s->st[2U][2U] = uu____15;
  core_core_arch_arm_shared_neon_uint64x2_t uu____16 =
      xor_and_rotate_fa_3e(s->st[3U][2U], t[2U]);
  s->st[3U][2U] = uu____16;
  core_core_arch_arm_shared_neon_uint64x2_t uu____17 =
      xor_and_rotate_fa_bd(s->st[4U][2U], t[2U]);
  s->st[4U][2U] = uu____17;
  core_core_arch_arm_shared_neon_uint64x2_t uu____18 =
      xor_and_rotate_fa_42(s->st[0U][3U], t[3U]);
  s->st[0U][3U] = uu____18;
  core_core_arch_arm_shared_neon_uint64x2_t uu____19 =
      xor_and_rotate_fa_64(s->st[1U][3U], t[3U]);
  s->st[1U][3U] = uu____19;
  core_core_arch_arm_shared_neon_uint64x2_t uu____20 =
      xor_and_rotate_fa_cc(s->st[2U][3U], t[3U]);
  s->st[2U][3U] = uu____20;
  core_core_arch_arm_shared_neon_uint64x2_t uu____21 =
      xor_and_rotate_fa_d5(s->st[3U][3U], t[3U]);
  s->st[3U][3U] = uu____21;
  core_core_arch_arm_shared_neon_uint64x2_t uu____22 =
      xor_and_rotate_fa_61(s->st[4U][3U], t[3U]);
  s->st[4U][3U] = uu____22;
  core_core_arch_arm_shared_neon_uint64x2_t uu____23 =
      xor_and_rotate_fa_6f(s->st[0U][4U], t[4U]);
  s->st[0U][4U] = uu____23;
  core_core_arch_arm_shared_neon_uint64x2_t uu____24 =
      xor_and_rotate_fa_06(s->st[1U][4U], t[4U]);
  s->st[1U][4U] = uu____24;
  core_core_arch_arm_shared_neon_uint64x2_t uu____25 =
      xor_and_rotate_fa_3d(s->st[2U][4U], t[4U]);
  s->st[2U][4U] = uu____25;
  core_core_arch_arm_shared_neon_uint64x2_t uu____26 =
      xor_and_rotate_fa_0c(s->st[3U][4U], t[4U]);
  s->st[3U][4U] = uu____26;
  core_core_arch_arm_shared_neon_uint64x2_t uu____27 =
      xor_and_rotate_fa_98(s->st[4U][4U], t[4U]);
  s->st[4U][4U] = uu____27;
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.pi with types
core_core_arch_arm_shared_neon_uint64x2_t and with const generics:
- N = 2
*/
static KRML_MUSTINLINE void pi_39(
    libcrux_sha3_generic_keccak_KeccakState__core_core_arch_arm_shared_neon_uint64x2_t__2size_t
        *s) {
  core_core_arch_arm_shared_neon_uint64x2_t old[5U][5U];
  memcpy(old, s->st,
         (size_t)5U * sizeof(core_core_arch_arm_shared_neon_uint64x2_t[5U]));
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
A monomorphic instance of libcrux_sha3.generic_keccak.chi with types
core_core_arch_arm_shared_neon_uint64x2_t and with const generics:
- N = 2
*/
static KRML_MUSTINLINE void chi_39(
    libcrux_sha3_generic_keccak_KeccakState__core_core_arch_arm_shared_neon_uint64x2_t__2size_t
        *s) {
  core_core_arch_arm_shared_neon_uint64x2_t old[5U][5U];
  memcpy(old, s->st,
         (size_t)5U * sizeof(core_core_arch_arm_shared_neon_uint64x2_t[5U]));
  KRML_MAYBE_FOR5(
      i0, (size_t)0U, (size_t)5U, (size_t)1U, size_t i1 = i0;
      KRML_MAYBE_FOR5(i, (size_t)0U, (size_t)5U, (size_t)1U, size_t j = i;
                      s->st[i1][j] = and_not_xor_fa(
                          s->st[i1][j], old[i1][(j + (size_t)2U) % (size_t)5U],
                          old[i1][(j + (size_t)1U) % (size_t)5U]);););
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.iota with types
core_core_arch_arm_shared_neon_uint64x2_t and with const generics:
- N = 2
*/
static KRML_MUSTINLINE void iota_39(
    libcrux_sha3_generic_keccak_KeccakState__core_core_arch_arm_shared_neon_uint64x2_t__2size_t
        *s,
    size_t i) {
  s->st[0U][0U] = xor_constant_fa(
      s->st[0U][0U], libcrux_sha3_generic_keccak_ROUNDCONSTANTS[i]);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.keccakf1600 with types
core_core_arch_arm_shared_neon_uint64x2_t and with const generics:
- N = 2
*/
static KRML_MUSTINLINE void keccakf1600_39(
    libcrux_sha3_generic_keccak_KeccakState__core_core_arch_arm_shared_neon_uint64x2_t__2size_t
        *s) {
  for (size_t i = (size_t)0U; i < (size_t)24U; i++) {
    size_t i0 = i;
    theta_rho_39(s);
    pi_39(s);
    chi_39(s);
    iota_39(s, i0);
  }
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block with types
core_core_arch_arm_shared_neon_uint64x2_t and with const generics:
- N = 2
- RATE = 72
*/
static KRML_MUSTINLINE void absorb_block_33(
    libcrux_sha3_generic_keccak_KeccakState__core_core_arch_arm_shared_neon_uint64x2_t__2size_t
        *s,
    Eurydice_slice blocks[2U]) {
  core_core_arch_arm_shared_neon_uint64x2_t(*uu____0)[5U] = s->st;
  Eurydice_slice uu____1[2U];
  memcpy(uu____1, blocks, (size_t)2U * sizeof(Eurydice_slice));
  load_block_fa_66(uu____0, uu____1);
  keccakf1600_39(s);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block_full with const
generics:
- RATE = 72
*/
static KRML_MUSTINLINE void load_block_full_66(
    core_core_arch_arm_shared_neon_uint64x2_t (*s)[5U],
    uint8_t blocks[2U][200U]) {
  Eurydice_slice buf[2U] = {Eurydice_array_to_slice((size_t)200U, blocks[0U],
                                                    uint8_t, Eurydice_slice),
                            Eurydice_array_to_slice((size_t)200U, blocks[1U],
                                                    uint8_t, Eurydice_slice)};
  load_block_66(s, buf);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block_full_fa with const
generics:
- BLOCKSIZE = 72
*/
static KRML_MUSTINLINE void load_block_full_fa_66(
    core_core_arch_arm_shared_neon_uint64x2_t (*a)[5U], uint8_t b[2U][200U]) {
  core_core_arch_arm_shared_neon_uint64x2_t(*uu____0)[5U] = a;
  uint8_t uu____1[2U][200U];
  memcpy(uu____1, b, (size_t)2U * sizeof(uint8_t[200U]));
  load_block_full_66(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final with types
core_core_arch_arm_shared_neon_uint64x2_t and with const generics:
- N = 2
- RATE = 72
- DELIM = 6
*/
static KRML_MUSTINLINE void absorb_final_8b(
    libcrux_sha3_generic_keccak_KeccakState__core_core_arch_arm_shared_neon_uint64x2_t__2size_t
        *s,
    Eurydice_slice last[2U]) {
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
  core_core_arch_arm_shared_neon_uint64x2_t(*uu____3)[5U] = s->st;
  uint8_t uu____4[2U][200U];
  memcpy(uu____4, blocks, (size_t)2U * sizeof(uint8_t[200U]));
  load_block_full_fa_66(uu____3, uu____4);
  keccakf1600_39(s);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.store_block with const
generics:
- RATE = 72
*/
static KRML_MUSTINLINE void store_block_66(
    core_core_arch_arm_shared_neon_uint64x2_t (*s)[5U],
    Eurydice_slice out[2U]) {
  for (size_t i = (size_t)0U; i < (size_t)72U / (size_t)16U; i++) {
    size_t i0 = i;
    core_core_arch_arm_shared_neon_uint64x2_t v0 =
        libcrux_intrinsics_arm64__vtrn1q_u64(
            s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U],
            s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
             [((size_t)2U * i0 + (size_t)1U) % (size_t)5U]);
    core_core_arch_arm_shared_neon_uint64x2_t v1 =
        libcrux_intrinsics_arm64__vtrn2q_u64(
            s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U],
            s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
             [((size_t)2U * i0 + (size_t)1U) % (size_t)5U]);
    libcrux_intrinsics_arm64__vst1q_bytes_u64(
        Eurydice_slice_subslice2(out[0U], (size_t)16U * i0,
                                 (size_t)16U * (i0 + (size_t)1U), uint8_t,
                                 Eurydice_slice),
        v0);
    libcrux_intrinsics_arm64__vst1q_bytes_u64(
        Eurydice_slice_subslice2(out[1U], (size_t)16U * i0,
                                 (size_t)16U * (i0 + (size_t)1U), uint8_t,
                                 Eurydice_slice),
        v1);
  }
  if ((size_t)72U % (size_t)16U != (size_t)0U) {
    size_t i = ((size_t)72U / (size_t)8U - (size_t)1U) / (size_t)5U;
    size_t j = ((size_t)72U / (size_t)8U - (size_t)1U) % (size_t)5U;
    uint8_t u[16U] = {0U};
    libcrux_intrinsics_arm64__vst1q_bytes_u64(
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
A monomorphic instance of libcrux_sha3.simd.arm64.store_block_full with const
generics:
- RATE = 72
*/
static KRML_MUSTINLINE void store_block_full_66(
    core_core_arch_arm_shared_neon_uint64x2_t (*s)[5U], uint8_t ret[2U][200U]) {
  uint8_t out0[200U] = {0U};
  uint8_t out1[200U] = {0U};
  Eurydice_slice buf[2U] = {
      Eurydice_array_to_slice((size_t)200U, out0, uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)200U, out1, uint8_t, Eurydice_slice)};
  store_block_66(s, buf);
  uint8_t uu____0[200U];
  memcpy(uu____0, out0, (size_t)200U * sizeof(uint8_t));
  uint8_t uu____1[200U];
  memcpy(uu____1, out1, (size_t)200U * sizeof(uint8_t));
  memcpy(ret[0U], uu____0, (size_t)200U * sizeof(uint8_t));
  memcpy(ret[1U], uu____1, (size_t)200U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.store_block_full_fa with const
generics:
- BLOCKSIZE = 72
*/
static KRML_MUSTINLINE void store_block_full_fa_66(
    core_core_arch_arm_shared_neon_uint64x2_t (*a)[5U], uint8_t ret[2U][200U]) {
  store_block_full_66(a, ret);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_and_last
with types core_core_arch_arm_shared_neon_uint64x2_t and with const generics:
- N = 2
- RATE = 72
*/
static KRML_MUSTINLINE void squeeze_first_and_last_33(
    libcrux_sha3_generic_keccak_KeccakState__core_core_arch_arm_shared_neon_uint64x2_t__2size_t
        *s,
    Eurydice_slice out[2U]) {
  uint8_t b[2U][200U];
  store_block_full_fa_66(s->st, b);
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      Eurydice_slice uu____0 = out[i0]; uint8_t *uu____1 = b[i0];
      core_ops_range_Range__size_t lit; lit.start = (size_t)0U;
      lit.end = core_slice___Slice_T___len(out[i0], uint8_t, size_t);
      core_slice___Slice_T___copy_from_slice(
          uu____0,
          Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                     core_ops_range_Range__size_t,
                                     Eurydice_slice),
          uint8_t, void *););
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.store_block_fa with const
generics:
- BLOCKSIZE = 72
*/
static KRML_MUSTINLINE void store_block_fa_66(
    core_core_arch_arm_shared_neon_uint64x2_t (*a)[5U], Eurydice_slice b[2U]) {
  store_block_66(a, b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_block with
types core_core_arch_arm_shared_neon_uint64x2_t and with const generics:
- N = 2
- RATE = 72
*/
static KRML_MUSTINLINE void squeeze_first_block_33(
    libcrux_sha3_generic_keccak_KeccakState__core_core_arch_arm_shared_neon_uint64x2_t__2size_t
        *s,
    Eurydice_slice out[2U]) {
  store_block_fa_66(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_next_block with
types core_core_arch_arm_shared_neon_uint64x2_t and with const generics:
- N = 2
- RATE = 72
*/
static KRML_MUSTINLINE void squeeze_next_block_33(
    libcrux_sha3_generic_keccak_KeccakState__core_core_arch_arm_shared_neon_uint64x2_t__2size_t
        *s,
    Eurydice_slice out[2U]) {
  keccakf1600_39(s);
  store_block_fa_66(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_last with types
core_core_arch_arm_shared_neon_uint64x2_t and with const generics:
- N = 2
- RATE = 72
*/
static KRML_MUSTINLINE void squeeze_last_33(
    libcrux_sha3_generic_keccak_KeccakState__core_core_arch_arm_shared_neon_uint64x2_t__2size_t
        s,
    Eurydice_slice out[2U]) {
  keccakf1600_39(&s);
  uint8_t b[2U][200U];
  store_block_full_fa_66(s.st, b);
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      Eurydice_slice uu____0 = out[i0]; uint8_t *uu____1 = b[i0];
      core_ops_range_Range__size_t lit; lit.start = (size_t)0U;
      lit.end = core_slice___Slice_T___len(out[i0], uint8_t, size_t);
      core_slice___Slice_T___copy_from_slice(
          uu____0,
          Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                     core_ops_range_Range__size_t,
                                     Eurydice_slice),
          uint8_t, void *););
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.keccak with types
core_core_arch_arm_shared_neon_uint64x2_t and with const generics:
- N = 2
- RATE = 72
- DELIM = 6
*/
static KRML_MUSTINLINE void keccak_8b(Eurydice_slice data[2U],
                                      Eurydice_slice out[2U]) {
  libcrux_sha3_generic_keccak_KeccakState__core_core_arch_arm_shared_neon_uint64x2_t__2size_t
      s = new_1e_39();
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(data[0U], uint8_t, size_t) / (size_t)72U;
       i++) {
    size_t i0 = i;
    libcrux_sha3_generic_keccak_KeccakState__core_core_arch_arm_shared_neon_uint64x2_t__2size_t
        *uu____0 = &s;
    Eurydice_slice uu____1[2U];
    memcpy(uu____1, data, (size_t)2U * sizeof(Eurydice_slice));
    Eurydice_slice ret[2U];
    slice_n_fa(uu____1, i0 * (size_t)72U, (size_t)72U, ret);
    absorb_block_33(uu____0, ret);
  }
  size_t rem =
      core_slice___Slice_T___len(data[0U], uint8_t, size_t) % (size_t)72U;
  libcrux_sha3_generic_keccak_KeccakState__core_core_arch_arm_shared_neon_uint64x2_t__2size_t
      *uu____2 = &s;
  Eurydice_slice uu____3[2U];
  memcpy(uu____3, data, (size_t)2U * sizeof(Eurydice_slice));
  Eurydice_slice ret[2U];
  slice_n_fa(uu____3,
             core_slice___Slice_T___len(data[0U], uint8_t, size_t) - rem, rem,
             ret);
  absorb_final_8b(uu____2, ret);
  size_t outlen = core_slice___Slice_T___len(out[0U], uint8_t, size_t);
  size_t blocks = outlen / (size_t)72U;
  size_t last = outlen - outlen % (size_t)72U;
  if (blocks == (size_t)0U) {
    squeeze_first_and_last_33(&s, out);
  } else {
    K___Eurydice_slice_uint8_t_2size_t__Eurydice_slice_uint8_t_2size_t_
        uu____4 = split_at_mut_n_fa(out, (size_t)72U);
    Eurydice_slice o0[2U];
    memcpy(o0, uu____4.fst, (size_t)2U * sizeof(Eurydice_slice));
    Eurydice_slice o1[2U];
    memcpy(o1, uu____4.snd, (size_t)2U * sizeof(Eurydice_slice));
    squeeze_first_block_33(&s, o0);
    core_ops_range_Range__size_t iter =
        core_iter_traits_collect___core__iter__traits__collect__IntoIterator_for_I__1__into_iter(
            (CLITERAL(core_ops_range_Range__size_t){.start = (size_t)1U,
                                                    .end = blocks}),
            core_ops_range_Range__size_t, core_ops_range_Range__size_t);
    while (true) {
      if (core_iter_range___core__iter__traits__iterator__Iterator_for_core__ops__range__Range_A___6__next(
              &iter, size_t, core_option_Option__size_t)
              .tag == core_option_None) {
        break;
      } else {
        K___Eurydice_slice_uint8_t_2size_t__Eurydice_slice_uint8_t_2size_t_
            uu____5 = split_at_mut_n_fa(o1, (size_t)72U);
        Eurydice_slice o[2U];
        memcpy(o, uu____5.fst, (size_t)2U * sizeof(Eurydice_slice));
        Eurydice_slice orest[2U];
        memcpy(orest, uu____5.snd, (size_t)2U * sizeof(Eurydice_slice));
        squeeze_next_block_33(&s, o);
        memcpy(o1, orest, (size_t)2U * sizeof(Eurydice_slice));
      }
    }
    if (last < outlen) {
      squeeze_last_33(s, o1);
    }
  }
}

/**
A monomorphic instance of libcrux_sha3.neon.keccakx2 with const generics:
- RATE = 72
- DELIM = 6
*/
static KRML_MUSTINLINE void keccakx2_26(Eurydice_slice data[2U],
                                        Eurydice_slice out[2U]) {
  Eurydice_slice uu____0[2U];
  memcpy(uu____0, data, (size_t)2U * sizeof(Eurydice_slice));
  keccak_8b(uu____0, out);
}

void libcrux_sha3_neon_sha512(Eurydice_slice digest, Eurydice_slice data) {
  uint8_t dummy[64U] = {0U};
  Eurydice_slice uu____0[2U] = {data, data};
  Eurydice_slice buf[2U] = {
      digest,
      Eurydice_array_to_slice((size_t)64U, dummy, uint8_t, Eurydice_slice)};
  keccakx2_26(uu____0, buf);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block with const
generics:
- RATE = 136
*/
static KRML_MUSTINLINE void load_block_35(
    core_core_arch_arm_shared_neon_uint64x2_t (*s)[5U],
    Eurydice_slice blocks[2U]) {
  for (size_t i = (size_t)0U; i < (size_t)136U / (size_t)16U; i++) {
    size_t i0 = i;
    core_core_arch_arm_shared_neon_uint64x2_t v0 =
        libcrux_intrinsics_arm64__vld1q_bytes_u64(Eurydice_slice_subslice2(
            blocks[0U], (size_t)16U * i0, (size_t)16U * (i0 + (size_t)1U),
            uint8_t, Eurydice_slice));
    core_core_arch_arm_shared_neon_uint64x2_t v1 =
        libcrux_intrinsics_arm64__vld1q_bytes_u64(Eurydice_slice_subslice2(
            blocks[1U], (size_t)16U * i0, (size_t)16U * (i0 + (size_t)1U),
            uint8_t, Eurydice_slice));
    s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U] =
        libcrux_intrinsics_arm64__veorq_u64(
            s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U],
            libcrux_intrinsics_arm64__vtrn1q_u64(v0, v1));
    s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
     [((size_t)2U * i0 + (size_t)1U) % (size_t)5U] =
         libcrux_intrinsics_arm64__veorq_u64(
             s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
              [((size_t)2U * i0 + (size_t)1U) % (size_t)5U],
             libcrux_intrinsics_arm64__vtrn2q_u64(v0, v1));
  }
  if ((size_t)136U % (size_t)16U != (size_t)0U) {
    size_t i = ((size_t)136U / (size_t)8U - (size_t)1U) / (size_t)5U;
    size_t j = ((size_t)136U / (size_t)8U - (size_t)1U) % (size_t)5U;
    uint64_t u[2U] = {0U};
    uint8_t uu____0[8U];
    core_result_Result__uint8_t_8size_t__core_array_TryFromSliceError dst0;
    Eurydice_slice_to_array2(
        &dst0,
        Eurydice_slice_subslice2(blocks[0U], (size_t)136U - (size_t)8U,
                                 (size_t)136U, uint8_t, Eurydice_slice),
        Eurydice_slice, uint8_t[8U], void *);
    core_result_unwrap_41_15(dst0, uu____0);
    u[0U] = core_num__u64_9__from_le_bytes(uu____0);
    uint8_t uu____1[8U];
    core_result_Result__uint8_t_8size_t__core_array_TryFromSliceError dst;
    Eurydice_slice_to_array2(
        &dst,
        Eurydice_slice_subslice2(blocks[1U], (size_t)136U - (size_t)8U,
                                 (size_t)136U, uint8_t, Eurydice_slice),
        Eurydice_slice, uint8_t[8U], void *);
    core_result_unwrap_41_15(dst, uu____1);
    u[1U] = core_num__u64_9__from_le_bytes(uu____1);
    core_core_arch_arm_shared_neon_uint64x2_t uvec =
        libcrux_intrinsics_arm64__vld1q_u64(
            Eurydice_array_to_slice((size_t)2U, u, uint64_t, Eurydice_slice));
    s[i][j] = libcrux_intrinsics_arm64__veorq_u64(s[i][j], uvec);
  }
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block_fa with const
generics:
- BLOCKSIZE = 136
*/
static KRML_MUSTINLINE void load_block_fa_35(
    core_core_arch_arm_shared_neon_uint64x2_t (*a)[5U], Eurydice_slice b[2U]) {
  core_core_arch_arm_shared_neon_uint64x2_t(*uu____0)[5U] = a;
  Eurydice_slice uu____1[2U];
  memcpy(uu____1, b, (size_t)2U * sizeof(Eurydice_slice));
  load_block_35(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block with types
core_core_arch_arm_shared_neon_uint64x2_t and with const generics:
- N = 2
- RATE = 136
*/
static KRML_MUSTINLINE void absorb_block_48(
    libcrux_sha3_generic_keccak_KeccakState__core_core_arch_arm_shared_neon_uint64x2_t__2size_t
        *s,
    Eurydice_slice blocks[2U]) {
  core_core_arch_arm_shared_neon_uint64x2_t(*uu____0)[5U] = s->st;
  Eurydice_slice uu____1[2U];
  memcpy(uu____1, blocks, (size_t)2U * sizeof(Eurydice_slice));
  load_block_fa_35(uu____0, uu____1);
  keccakf1600_39(s);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block_full with const
generics:
- RATE = 136
*/
static KRML_MUSTINLINE void load_block_full_35(
    core_core_arch_arm_shared_neon_uint64x2_t (*s)[5U],
    uint8_t blocks[2U][200U]) {
  Eurydice_slice buf[2U] = {Eurydice_array_to_slice((size_t)200U, blocks[0U],
                                                    uint8_t, Eurydice_slice),
                            Eurydice_array_to_slice((size_t)200U, blocks[1U],
                                                    uint8_t, Eurydice_slice)};
  load_block_35(s, buf);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block_full_fa with const
generics:
- BLOCKSIZE = 136
*/
static KRML_MUSTINLINE void load_block_full_fa_35(
    core_core_arch_arm_shared_neon_uint64x2_t (*a)[5U], uint8_t b[2U][200U]) {
  core_core_arch_arm_shared_neon_uint64x2_t(*uu____0)[5U] = a;
  uint8_t uu____1[2U][200U];
  memcpy(uu____1, b, (size_t)2U * sizeof(uint8_t[200U]));
  load_block_full_35(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final with types
core_core_arch_arm_shared_neon_uint64x2_t and with const generics:
- N = 2
- RATE = 136
- DELIM = 6
*/
static KRML_MUSTINLINE void absorb_final_0f(
    libcrux_sha3_generic_keccak_KeccakState__core_core_arch_arm_shared_neon_uint64x2_t__2size_t
        *s,
    Eurydice_slice last[2U]) {
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
  core_core_arch_arm_shared_neon_uint64x2_t(*uu____3)[5U] = s->st;
  uint8_t uu____4[2U][200U];
  memcpy(uu____4, blocks, (size_t)2U * sizeof(uint8_t[200U]));
  load_block_full_fa_35(uu____3, uu____4);
  keccakf1600_39(s);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.store_block with const
generics:
- RATE = 136
*/
static KRML_MUSTINLINE void store_block_35(
    core_core_arch_arm_shared_neon_uint64x2_t (*s)[5U],
    Eurydice_slice out[2U]) {
  for (size_t i = (size_t)0U; i < (size_t)136U / (size_t)16U; i++) {
    size_t i0 = i;
    core_core_arch_arm_shared_neon_uint64x2_t v0 =
        libcrux_intrinsics_arm64__vtrn1q_u64(
            s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U],
            s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
             [((size_t)2U * i0 + (size_t)1U) % (size_t)5U]);
    core_core_arch_arm_shared_neon_uint64x2_t v1 =
        libcrux_intrinsics_arm64__vtrn2q_u64(
            s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U],
            s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
             [((size_t)2U * i0 + (size_t)1U) % (size_t)5U]);
    libcrux_intrinsics_arm64__vst1q_bytes_u64(
        Eurydice_slice_subslice2(out[0U], (size_t)16U * i0,
                                 (size_t)16U * (i0 + (size_t)1U), uint8_t,
                                 Eurydice_slice),
        v0);
    libcrux_intrinsics_arm64__vst1q_bytes_u64(
        Eurydice_slice_subslice2(out[1U], (size_t)16U * i0,
                                 (size_t)16U * (i0 + (size_t)1U), uint8_t,
                                 Eurydice_slice),
        v1);
  }
  if ((size_t)136U % (size_t)16U != (size_t)0U) {
    size_t i = ((size_t)136U / (size_t)8U - (size_t)1U) / (size_t)5U;
    size_t j = ((size_t)136U / (size_t)8U - (size_t)1U) % (size_t)5U;
    uint8_t u[16U] = {0U};
    libcrux_intrinsics_arm64__vst1q_bytes_u64(
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
A monomorphic instance of libcrux_sha3.simd.arm64.store_block_full with const
generics:
- RATE = 136
*/
static KRML_MUSTINLINE void store_block_full_35(
    core_core_arch_arm_shared_neon_uint64x2_t (*s)[5U], uint8_t ret[2U][200U]) {
  uint8_t out0[200U] = {0U};
  uint8_t out1[200U] = {0U};
  Eurydice_slice buf[2U] = {
      Eurydice_array_to_slice((size_t)200U, out0, uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)200U, out1, uint8_t, Eurydice_slice)};
  store_block_35(s, buf);
  uint8_t uu____0[200U];
  memcpy(uu____0, out0, (size_t)200U * sizeof(uint8_t));
  uint8_t uu____1[200U];
  memcpy(uu____1, out1, (size_t)200U * sizeof(uint8_t));
  memcpy(ret[0U], uu____0, (size_t)200U * sizeof(uint8_t));
  memcpy(ret[1U], uu____1, (size_t)200U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.store_block_full_fa with const
generics:
- BLOCKSIZE = 136
*/
static KRML_MUSTINLINE void store_block_full_fa_35(
    core_core_arch_arm_shared_neon_uint64x2_t (*a)[5U], uint8_t ret[2U][200U]) {
  store_block_full_35(a, ret);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_and_last
with types core_core_arch_arm_shared_neon_uint64x2_t and with const generics:
- N = 2
- RATE = 136
*/
static KRML_MUSTINLINE void squeeze_first_and_last_48(
    libcrux_sha3_generic_keccak_KeccakState__core_core_arch_arm_shared_neon_uint64x2_t__2size_t
        *s,
    Eurydice_slice out[2U]) {
  uint8_t b[2U][200U];
  store_block_full_fa_35(s->st, b);
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      Eurydice_slice uu____0 = out[i0]; uint8_t *uu____1 = b[i0];
      core_ops_range_Range__size_t lit; lit.start = (size_t)0U;
      lit.end = core_slice___Slice_T___len(out[i0], uint8_t, size_t);
      core_slice___Slice_T___copy_from_slice(
          uu____0,
          Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                     core_ops_range_Range__size_t,
                                     Eurydice_slice),
          uint8_t, void *););
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.store_block_fa with const
generics:
- BLOCKSIZE = 136
*/
static KRML_MUSTINLINE void store_block_fa_35(
    core_core_arch_arm_shared_neon_uint64x2_t (*a)[5U], Eurydice_slice b[2U]) {
  store_block_35(a, b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_block with
types core_core_arch_arm_shared_neon_uint64x2_t and with const generics:
- N = 2
- RATE = 136
*/
static KRML_MUSTINLINE void squeeze_first_block_48(
    libcrux_sha3_generic_keccak_KeccakState__core_core_arch_arm_shared_neon_uint64x2_t__2size_t
        *s,
    Eurydice_slice out[2U]) {
  store_block_fa_35(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_next_block with
types core_core_arch_arm_shared_neon_uint64x2_t and with const generics:
- N = 2
- RATE = 136
*/
static KRML_MUSTINLINE void squeeze_next_block_48(
    libcrux_sha3_generic_keccak_KeccakState__core_core_arch_arm_shared_neon_uint64x2_t__2size_t
        *s,
    Eurydice_slice out[2U]) {
  keccakf1600_39(s);
  store_block_fa_35(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_last with types
core_core_arch_arm_shared_neon_uint64x2_t and with const generics:
- N = 2
- RATE = 136
*/
static KRML_MUSTINLINE void squeeze_last_48(
    libcrux_sha3_generic_keccak_KeccakState__core_core_arch_arm_shared_neon_uint64x2_t__2size_t
        s,
    Eurydice_slice out[2U]) {
  keccakf1600_39(&s);
  uint8_t b[2U][200U];
  store_block_full_fa_35(s.st, b);
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      Eurydice_slice uu____0 = out[i0]; uint8_t *uu____1 = b[i0];
      core_ops_range_Range__size_t lit; lit.start = (size_t)0U;
      lit.end = core_slice___Slice_T___len(out[i0], uint8_t, size_t);
      core_slice___Slice_T___copy_from_slice(
          uu____0,
          Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                     core_ops_range_Range__size_t,
                                     Eurydice_slice),
          uint8_t, void *););
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.keccak with types
core_core_arch_arm_shared_neon_uint64x2_t and with const generics:
- N = 2
- RATE = 136
- DELIM = 6
*/
static KRML_MUSTINLINE void keccak_0f(Eurydice_slice data[2U],
                                      Eurydice_slice out[2U]) {
  libcrux_sha3_generic_keccak_KeccakState__core_core_arch_arm_shared_neon_uint64x2_t__2size_t
      s = new_1e_39();
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(data[0U], uint8_t, size_t) / (size_t)136U;
       i++) {
    size_t i0 = i;
    libcrux_sha3_generic_keccak_KeccakState__core_core_arch_arm_shared_neon_uint64x2_t__2size_t
        *uu____0 = &s;
    Eurydice_slice uu____1[2U];
    memcpy(uu____1, data, (size_t)2U * sizeof(Eurydice_slice));
    Eurydice_slice ret[2U];
    slice_n_fa(uu____1, i0 * (size_t)136U, (size_t)136U, ret);
    absorb_block_48(uu____0, ret);
  }
  size_t rem =
      core_slice___Slice_T___len(data[0U], uint8_t, size_t) % (size_t)136U;
  libcrux_sha3_generic_keccak_KeccakState__core_core_arch_arm_shared_neon_uint64x2_t__2size_t
      *uu____2 = &s;
  Eurydice_slice uu____3[2U];
  memcpy(uu____3, data, (size_t)2U * sizeof(Eurydice_slice));
  Eurydice_slice ret[2U];
  slice_n_fa(uu____3,
             core_slice___Slice_T___len(data[0U], uint8_t, size_t) - rem, rem,
             ret);
  absorb_final_0f(uu____2, ret);
  size_t outlen = core_slice___Slice_T___len(out[0U], uint8_t, size_t);
  size_t blocks = outlen / (size_t)136U;
  size_t last = outlen - outlen % (size_t)136U;
  if (blocks == (size_t)0U) {
    squeeze_first_and_last_48(&s, out);
  } else {
    K___Eurydice_slice_uint8_t_2size_t__Eurydice_slice_uint8_t_2size_t_
        uu____4 = split_at_mut_n_fa(out, (size_t)136U);
    Eurydice_slice o0[2U];
    memcpy(o0, uu____4.fst, (size_t)2U * sizeof(Eurydice_slice));
    Eurydice_slice o1[2U];
    memcpy(o1, uu____4.snd, (size_t)2U * sizeof(Eurydice_slice));
    squeeze_first_block_48(&s, o0);
    core_ops_range_Range__size_t iter =
        core_iter_traits_collect___core__iter__traits__collect__IntoIterator_for_I__1__into_iter(
            (CLITERAL(core_ops_range_Range__size_t){.start = (size_t)1U,
                                                    .end = blocks}),
            core_ops_range_Range__size_t, core_ops_range_Range__size_t);
    while (true) {
      if (core_iter_range___core__iter__traits__iterator__Iterator_for_core__ops__range__Range_A___6__next(
              &iter, size_t, core_option_Option__size_t)
              .tag == core_option_None) {
        break;
      } else {
        K___Eurydice_slice_uint8_t_2size_t__Eurydice_slice_uint8_t_2size_t_
            uu____5 = split_at_mut_n_fa(o1, (size_t)136U);
        Eurydice_slice o[2U];
        memcpy(o, uu____5.fst, (size_t)2U * sizeof(Eurydice_slice));
        Eurydice_slice orest[2U];
        memcpy(orest, uu____5.snd, (size_t)2U * sizeof(Eurydice_slice));
        squeeze_next_block_48(&s, o);
        memcpy(o1, orest, (size_t)2U * sizeof(Eurydice_slice));
      }
    }
    if (last < outlen) {
      squeeze_last_48(s, o1);
    }
  }
}

/**
A monomorphic instance of libcrux_sha3.neon.keccakx2 with const generics:
- RATE = 136
- DELIM = 6
*/
static KRML_MUSTINLINE void keccakx2_2f(Eurydice_slice data[2U],
                                        Eurydice_slice out[2U]) {
  Eurydice_slice uu____0[2U];
  memcpy(uu____0, data, (size_t)2U * sizeof(Eurydice_slice));
  keccak_0f(uu____0, out);
}

void libcrux_sha3_neon_sha256(Eurydice_slice digest, Eurydice_slice data) {
  uint8_t dummy[32U] = {0U};
  Eurydice_slice uu____0[2U] = {data, data};
  Eurydice_slice buf[2U] = {
      digest,
      Eurydice_array_to_slice((size_t)32U, dummy, uint8_t, Eurydice_slice)};
  keccakx2_2f(uu____0, buf);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final with types
core_core_arch_arm_shared_neon_uint64x2_t and with const generics:
- N = 2
- RATE = 136
- DELIM = 31
*/
static KRML_MUSTINLINE void absorb_final_0f0(
    libcrux_sha3_generic_keccak_KeccakState__core_core_arch_arm_shared_neon_uint64x2_t__2size_t
        *s,
    Eurydice_slice last[2U]) {
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
  core_core_arch_arm_shared_neon_uint64x2_t(*uu____3)[5U] = s->st;
  uint8_t uu____4[2U][200U];
  memcpy(uu____4, blocks, (size_t)2U * sizeof(uint8_t[200U]));
  load_block_full_fa_35(uu____3, uu____4);
  keccakf1600_39(s);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.keccak with types
core_core_arch_arm_shared_neon_uint64x2_t and with const generics:
- N = 2
- RATE = 136
- DELIM = 31
*/
static KRML_MUSTINLINE void keccak_0f0(Eurydice_slice data[2U],
                                       Eurydice_slice out[2U]) {
  libcrux_sha3_generic_keccak_KeccakState__core_core_arch_arm_shared_neon_uint64x2_t__2size_t
      s = new_1e_39();
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(data[0U], uint8_t, size_t) / (size_t)136U;
       i++) {
    size_t i0 = i;
    libcrux_sha3_generic_keccak_KeccakState__core_core_arch_arm_shared_neon_uint64x2_t__2size_t
        *uu____0 = &s;
    Eurydice_slice uu____1[2U];
    memcpy(uu____1, data, (size_t)2U * sizeof(Eurydice_slice));
    Eurydice_slice ret[2U];
    slice_n_fa(uu____1, i0 * (size_t)136U, (size_t)136U, ret);
    absorb_block_48(uu____0, ret);
  }
  size_t rem =
      core_slice___Slice_T___len(data[0U], uint8_t, size_t) % (size_t)136U;
  libcrux_sha3_generic_keccak_KeccakState__core_core_arch_arm_shared_neon_uint64x2_t__2size_t
      *uu____2 = &s;
  Eurydice_slice uu____3[2U];
  memcpy(uu____3, data, (size_t)2U * sizeof(Eurydice_slice));
  Eurydice_slice ret[2U];
  slice_n_fa(uu____3,
             core_slice___Slice_T___len(data[0U], uint8_t, size_t) - rem, rem,
             ret);
  absorb_final_0f0(uu____2, ret);
  size_t outlen = core_slice___Slice_T___len(out[0U], uint8_t, size_t);
  size_t blocks = outlen / (size_t)136U;
  size_t last = outlen - outlen % (size_t)136U;
  if (blocks == (size_t)0U) {
    squeeze_first_and_last_48(&s, out);
  } else {
    K___Eurydice_slice_uint8_t_2size_t__Eurydice_slice_uint8_t_2size_t_
        uu____4 = split_at_mut_n_fa(out, (size_t)136U);
    Eurydice_slice o0[2U];
    memcpy(o0, uu____4.fst, (size_t)2U * sizeof(Eurydice_slice));
    Eurydice_slice o1[2U];
    memcpy(o1, uu____4.snd, (size_t)2U * sizeof(Eurydice_slice));
    squeeze_first_block_48(&s, o0);
    core_ops_range_Range__size_t iter =
        core_iter_traits_collect___core__iter__traits__collect__IntoIterator_for_I__1__into_iter(
            (CLITERAL(core_ops_range_Range__size_t){.start = (size_t)1U,
                                                    .end = blocks}),
            core_ops_range_Range__size_t, core_ops_range_Range__size_t);
    while (true) {
      if (core_iter_range___core__iter__traits__iterator__Iterator_for_core__ops__range__Range_A___6__next(
              &iter, size_t, core_option_Option__size_t)
              .tag == core_option_None) {
        break;
      } else {
        K___Eurydice_slice_uint8_t_2size_t__Eurydice_slice_uint8_t_2size_t_
            uu____5 = split_at_mut_n_fa(o1, (size_t)136U);
        Eurydice_slice o[2U];
        memcpy(o, uu____5.fst, (size_t)2U * sizeof(Eurydice_slice));
        Eurydice_slice orest[2U];
        memcpy(orest, uu____5.snd, (size_t)2U * sizeof(Eurydice_slice));
        squeeze_next_block_48(&s, o);
        memcpy(o1, orest, (size_t)2U * sizeof(Eurydice_slice));
      }
    }
    if (last < outlen) {
      squeeze_last_48(s, o1);
    }
  }
}

/**
A monomorphic instance of libcrux_sha3.neon.keccakx2 with const generics:
- RATE = 136
- DELIM = 31
*/
static KRML_MUSTINLINE void keccakx2_d2(Eurydice_slice data[2U],
                                        Eurydice_slice out[2U]) {
  Eurydice_slice uu____0[2U];
  memcpy(uu____0, data, (size_t)2U * sizeof(Eurydice_slice));
  keccak_0f0(uu____0, out);
}

void libcrux_sha3_neon_x2_shake256(Eurydice_slice input0, Eurydice_slice input1,
                                   Eurydice_slice out0, Eurydice_slice out1) {
  Eurydice_slice buf0[2U] = {input0, input1};
  Eurydice_slice buf[2U] = {out0, out1};
  keccakx2_d2(buf0, buf);
}

libcrux_sha3_generic_keccak_KeccakState__core_core_arch_arm_shared_neon_uint64x2_t__2size_t
libcrux_sha3_neon_x2_incremental_shake128_init(void) {
  return new_1e_39();
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block with const
generics:
- RATE = 168
*/
static KRML_MUSTINLINE void load_block_660(
    core_core_arch_arm_shared_neon_uint64x2_t (*s)[5U],
    Eurydice_slice blocks[2U]) {
  for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)16U; i++) {
    size_t i0 = i;
    core_core_arch_arm_shared_neon_uint64x2_t v0 =
        libcrux_intrinsics_arm64__vld1q_bytes_u64(Eurydice_slice_subslice2(
            blocks[0U], (size_t)16U * i0, (size_t)16U * (i0 + (size_t)1U),
            uint8_t, Eurydice_slice));
    core_core_arch_arm_shared_neon_uint64x2_t v1 =
        libcrux_intrinsics_arm64__vld1q_bytes_u64(Eurydice_slice_subslice2(
            blocks[1U], (size_t)16U * i0, (size_t)16U * (i0 + (size_t)1U),
            uint8_t, Eurydice_slice));
    s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U] =
        libcrux_intrinsics_arm64__veorq_u64(
            s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U],
            libcrux_intrinsics_arm64__vtrn1q_u64(v0, v1));
    s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
     [((size_t)2U * i0 + (size_t)1U) % (size_t)5U] =
         libcrux_intrinsics_arm64__veorq_u64(
             s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
              [((size_t)2U * i0 + (size_t)1U) % (size_t)5U],
             libcrux_intrinsics_arm64__vtrn2q_u64(v0, v1));
  }
  if ((size_t)168U % (size_t)16U != (size_t)0U) {
    size_t i = ((size_t)168U / (size_t)8U - (size_t)1U) / (size_t)5U;
    size_t j = ((size_t)168U / (size_t)8U - (size_t)1U) % (size_t)5U;
    uint64_t u[2U] = {0U};
    uint8_t uu____0[8U];
    core_result_Result__uint8_t_8size_t__core_array_TryFromSliceError dst0;
    Eurydice_slice_to_array2(
        &dst0,
        Eurydice_slice_subslice2(blocks[0U], (size_t)168U - (size_t)8U,
                                 (size_t)168U, uint8_t, Eurydice_slice),
        Eurydice_slice, uint8_t[8U], void *);
    core_result_unwrap_41_15(dst0, uu____0);
    u[0U] = core_num__u64_9__from_le_bytes(uu____0);
    uint8_t uu____1[8U];
    core_result_Result__uint8_t_8size_t__core_array_TryFromSliceError dst;
    Eurydice_slice_to_array2(
        &dst,
        Eurydice_slice_subslice2(blocks[1U], (size_t)168U - (size_t)8U,
                                 (size_t)168U, uint8_t, Eurydice_slice),
        Eurydice_slice, uint8_t[8U], void *);
    core_result_unwrap_41_15(dst, uu____1);
    u[1U] = core_num__u64_9__from_le_bytes(uu____1);
    core_core_arch_arm_shared_neon_uint64x2_t uvec =
        libcrux_intrinsics_arm64__vld1q_u64(
            Eurydice_array_to_slice((size_t)2U, u, uint64_t, Eurydice_slice));
    s[i][j] = libcrux_intrinsics_arm64__veorq_u64(s[i][j], uvec);
  }
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block_full with const
generics:
- RATE = 168
*/
static KRML_MUSTINLINE void load_block_full_660(
    core_core_arch_arm_shared_neon_uint64x2_t (*s)[5U],
    uint8_t blocks[2U][200U]) {
  Eurydice_slice buf[2U] = {Eurydice_array_to_slice((size_t)200U, blocks[0U],
                                                    uint8_t, Eurydice_slice),
                            Eurydice_array_to_slice((size_t)200U, blocks[1U],
                                                    uint8_t, Eurydice_slice)};
  load_block_660(s, buf);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block_full_fa with const
generics:
- BLOCKSIZE = 168
*/
static KRML_MUSTINLINE void load_block_full_fa_660(
    core_core_arch_arm_shared_neon_uint64x2_t (*a)[5U], uint8_t b[2U][200U]) {
  core_core_arch_arm_shared_neon_uint64x2_t(*uu____0)[5U] = a;
  uint8_t uu____1[2U][200U];
  memcpy(uu____1, b, (size_t)2U * sizeof(uint8_t[200U]));
  load_block_full_660(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final with types
core_core_arch_arm_shared_neon_uint64x2_t and with const generics:
- N = 2
- RATE = 168
- DELIM = 31
*/
static KRML_MUSTINLINE void absorb_final_f2(
    libcrux_sha3_generic_keccak_KeccakState__core_core_arch_arm_shared_neon_uint64x2_t__2size_t
        *s,
    Eurydice_slice last[2U]) {
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
  core_core_arch_arm_shared_neon_uint64x2_t(*uu____3)[5U] = s->st;
  uint8_t uu____4[2U][200U];
  memcpy(uu____4, blocks, (size_t)2U * sizeof(uint8_t[200U]));
  load_block_full_fa_660(uu____3, uu____4);
  keccakf1600_39(s);
}

void libcrux_sha3_neon_x2_incremental_shake128_absorb_final(
    libcrux_sha3_generic_keccak_KeccakState__core_core_arch_arm_shared_neon_uint64x2_t__2size_t
        *s,
    Eurydice_slice data0, Eurydice_slice data1) {
  Eurydice_slice buf[2U] = {data0, data1};
  absorb_final_f2(s, buf);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.store_block with const
generics:
- RATE = 168
*/
static KRML_MUSTINLINE void store_block_660(
    core_core_arch_arm_shared_neon_uint64x2_t (*s)[5U],
    Eurydice_slice out[2U]) {
  for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)16U; i++) {
    size_t i0 = i;
    core_core_arch_arm_shared_neon_uint64x2_t v0 =
        libcrux_intrinsics_arm64__vtrn1q_u64(
            s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U],
            s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
             [((size_t)2U * i0 + (size_t)1U) % (size_t)5U]);
    core_core_arch_arm_shared_neon_uint64x2_t v1 =
        libcrux_intrinsics_arm64__vtrn2q_u64(
            s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U],
            s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
             [((size_t)2U * i0 + (size_t)1U) % (size_t)5U]);
    libcrux_intrinsics_arm64__vst1q_bytes_u64(
        Eurydice_slice_subslice2(out[0U], (size_t)16U * i0,
                                 (size_t)16U * (i0 + (size_t)1U), uint8_t,
                                 Eurydice_slice),
        v0);
    libcrux_intrinsics_arm64__vst1q_bytes_u64(
        Eurydice_slice_subslice2(out[1U], (size_t)16U * i0,
                                 (size_t)16U * (i0 + (size_t)1U), uint8_t,
                                 Eurydice_slice),
        v1);
  }
  if ((size_t)168U % (size_t)16U != (size_t)0U) {
    size_t i = ((size_t)168U / (size_t)8U - (size_t)1U) / (size_t)5U;
    size_t j = ((size_t)168U / (size_t)8U - (size_t)1U) % (size_t)5U;
    uint8_t u[16U] = {0U};
    libcrux_intrinsics_arm64__vst1q_bytes_u64(
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
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.store_block_fa with const
generics:
- BLOCKSIZE = 168
*/
static KRML_MUSTINLINE void store_block_fa_660(
    core_core_arch_arm_shared_neon_uint64x2_t (*a)[5U], Eurydice_slice b[2U]) {
  store_block_660(a, b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_next_block with
types core_core_arch_arm_shared_neon_uint64x2_t and with const generics:
- N = 2
- RATE = 168
*/
static KRML_MUSTINLINE void squeeze_next_block_c2(
    libcrux_sha3_generic_keccak_KeccakState__core_core_arch_arm_shared_neon_uint64x2_t__2size_t
        *s,
    Eurydice_slice out[2U]) {
  keccakf1600_39(s);
  store_block_fa_660(s->st, out);
}

void libcrux_sha3_neon_x2_incremental_shake128_squeeze_next_block(
    libcrux_sha3_generic_keccak_KeccakState__core_core_arch_arm_shared_neon_uint64x2_t__2size_t
        *s,
    Eurydice_slice out0, Eurydice_slice out1) {
  Eurydice_slice buf[2U] = {out0, out1};
  squeeze_next_block_c2(s, buf);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_block with
types core_core_arch_arm_shared_neon_uint64x2_t and with const generics:
- N = 2
- RATE = 168
*/
static KRML_MUSTINLINE void squeeze_first_block_c2(
    libcrux_sha3_generic_keccak_KeccakState__core_core_arch_arm_shared_neon_uint64x2_t__2size_t
        *s,
    Eurydice_slice out[2U]) {
  store_block_fa_660(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_three_blocks
with types core_core_arch_arm_shared_neon_uint64x2_t and with const generics:
- N = 2
- RATE = 168
*/
static KRML_MUSTINLINE void squeeze_first_three_blocks_c2(
    libcrux_sha3_generic_keccak_KeccakState__core_core_arch_arm_shared_neon_uint64x2_t__2size_t
        *s,
    Eurydice_slice out[2U]) {
  K___Eurydice_slice_uint8_t_2size_t__Eurydice_slice_uint8_t_2size_t_ uu____0 =
      split_at_mut_n_fa(out, (size_t)168U);
  Eurydice_slice o0[2U];
  memcpy(o0, uu____0.fst, (size_t)2U * sizeof(Eurydice_slice));
  Eurydice_slice o10[2U];
  memcpy(o10, uu____0.snd, (size_t)2U * sizeof(Eurydice_slice));
  squeeze_first_block_c2(s, o0);
  K___Eurydice_slice_uint8_t_2size_t__Eurydice_slice_uint8_t_2size_t_ uu____1 =
      split_at_mut_n_fa(o10, (size_t)168U);
  Eurydice_slice o1[2U];
  memcpy(o1, uu____1.fst, (size_t)2U * sizeof(Eurydice_slice));
  Eurydice_slice o2[2U];
  memcpy(o2, uu____1.snd, (size_t)2U * sizeof(Eurydice_slice));
  squeeze_next_block_c2(s, o1);
  squeeze_next_block_c2(s, o2);
}

void libcrux_sha3_neon_x2_incremental_shake128_squeeze_first_three_blocks(
    libcrux_sha3_generic_keccak_KeccakState__core_core_arch_arm_shared_neon_uint64x2_t__2size_t
        *s,
    Eurydice_slice out0, Eurydice_slice out1) {
  Eurydice_slice buf[2U] = {out0, out1};
  squeeze_first_three_blocks_c2(s, buf);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block with const
generics:
- RATE = 144
*/
static KRML_MUSTINLINE void load_block_f0(
    core_core_arch_arm_shared_neon_uint64x2_t (*s)[5U],
    Eurydice_slice blocks[2U]) {
  for (size_t i = (size_t)0U; i < (size_t)144U / (size_t)16U; i++) {
    size_t i0 = i;
    core_core_arch_arm_shared_neon_uint64x2_t v0 =
        libcrux_intrinsics_arm64__vld1q_bytes_u64(Eurydice_slice_subslice2(
            blocks[0U], (size_t)16U * i0, (size_t)16U * (i0 + (size_t)1U),
            uint8_t, Eurydice_slice));
    core_core_arch_arm_shared_neon_uint64x2_t v1 =
        libcrux_intrinsics_arm64__vld1q_bytes_u64(Eurydice_slice_subslice2(
            blocks[1U], (size_t)16U * i0, (size_t)16U * (i0 + (size_t)1U),
            uint8_t, Eurydice_slice));
    s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U] =
        libcrux_intrinsics_arm64__veorq_u64(
            s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U],
            libcrux_intrinsics_arm64__vtrn1q_u64(v0, v1));
    s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
     [((size_t)2U * i0 + (size_t)1U) % (size_t)5U] =
         libcrux_intrinsics_arm64__veorq_u64(
             s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
              [((size_t)2U * i0 + (size_t)1U) % (size_t)5U],
             libcrux_intrinsics_arm64__vtrn2q_u64(v0, v1));
  }
  if ((size_t)144U % (size_t)16U != (size_t)0U) {
    size_t i = ((size_t)144U / (size_t)8U - (size_t)1U) / (size_t)5U;
    size_t j = ((size_t)144U / (size_t)8U - (size_t)1U) % (size_t)5U;
    uint64_t u[2U] = {0U};
    uint8_t uu____0[8U];
    core_result_Result__uint8_t_8size_t__core_array_TryFromSliceError dst0;
    Eurydice_slice_to_array2(
        &dst0,
        Eurydice_slice_subslice2(blocks[0U], (size_t)144U - (size_t)8U,
                                 (size_t)144U, uint8_t, Eurydice_slice),
        Eurydice_slice, uint8_t[8U], void *);
    core_result_unwrap_41_15(dst0, uu____0);
    u[0U] = core_num__u64_9__from_le_bytes(uu____0);
    uint8_t uu____1[8U];
    core_result_Result__uint8_t_8size_t__core_array_TryFromSliceError dst;
    Eurydice_slice_to_array2(
        &dst,
        Eurydice_slice_subslice2(blocks[1U], (size_t)144U - (size_t)8U,
                                 (size_t)144U, uint8_t, Eurydice_slice),
        Eurydice_slice, uint8_t[8U], void *);
    core_result_unwrap_41_15(dst, uu____1);
    u[1U] = core_num__u64_9__from_le_bytes(uu____1);
    core_core_arch_arm_shared_neon_uint64x2_t uvec =
        libcrux_intrinsics_arm64__vld1q_u64(
            Eurydice_array_to_slice((size_t)2U, u, uint64_t, Eurydice_slice));
    s[i][j] = libcrux_intrinsics_arm64__veorq_u64(s[i][j], uvec);
  }
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block_fa with const
generics:
- BLOCKSIZE = 144
*/
static KRML_MUSTINLINE void load_block_fa_f0(
    core_core_arch_arm_shared_neon_uint64x2_t (*a)[5U], Eurydice_slice b[2U]) {
  core_core_arch_arm_shared_neon_uint64x2_t(*uu____0)[5U] = a;
  Eurydice_slice uu____1[2U];
  memcpy(uu____1, b, (size_t)2U * sizeof(Eurydice_slice));
  load_block_f0(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block with types
core_core_arch_arm_shared_neon_uint64x2_t and with const generics:
- N = 2
- RATE = 144
*/
static KRML_MUSTINLINE void absorb_block_41(
    libcrux_sha3_generic_keccak_KeccakState__core_core_arch_arm_shared_neon_uint64x2_t__2size_t
        *s,
    Eurydice_slice blocks[2U]) {
  core_core_arch_arm_shared_neon_uint64x2_t(*uu____0)[5U] = s->st;
  Eurydice_slice uu____1[2U];
  memcpy(uu____1, blocks, (size_t)2U * sizeof(Eurydice_slice));
  load_block_fa_f0(uu____0, uu____1);
  keccakf1600_39(s);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block_full with const
generics:
- RATE = 144
*/
static KRML_MUSTINLINE void load_block_full_f0(
    core_core_arch_arm_shared_neon_uint64x2_t (*s)[5U],
    uint8_t blocks[2U][200U]) {
  Eurydice_slice buf[2U] = {Eurydice_array_to_slice((size_t)200U, blocks[0U],
                                                    uint8_t, Eurydice_slice),
                            Eurydice_array_to_slice((size_t)200U, blocks[1U],
                                                    uint8_t, Eurydice_slice)};
  load_block_f0(s, buf);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block_full_fa with const
generics:
- BLOCKSIZE = 144
*/
static KRML_MUSTINLINE void load_block_full_fa_f0(
    core_core_arch_arm_shared_neon_uint64x2_t (*a)[5U], uint8_t b[2U][200U]) {
  core_core_arch_arm_shared_neon_uint64x2_t(*uu____0)[5U] = a;
  uint8_t uu____1[2U][200U];
  memcpy(uu____1, b, (size_t)2U * sizeof(uint8_t[200U]));
  load_block_full_f0(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final with types
core_core_arch_arm_shared_neon_uint64x2_t and with const generics:
- N = 2
- RATE = 144
- DELIM = 6
*/
static KRML_MUSTINLINE void absorb_final_24(
    libcrux_sha3_generic_keccak_KeccakState__core_core_arch_arm_shared_neon_uint64x2_t__2size_t
        *s,
    Eurydice_slice last[2U]) {
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
  core_core_arch_arm_shared_neon_uint64x2_t(*uu____3)[5U] = s->st;
  uint8_t uu____4[2U][200U];
  memcpy(uu____4, blocks, (size_t)2U * sizeof(uint8_t[200U]));
  load_block_full_fa_f0(uu____3, uu____4);
  keccakf1600_39(s);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.store_block with const
generics:
- RATE = 144
*/
static KRML_MUSTINLINE void store_block_f0(
    core_core_arch_arm_shared_neon_uint64x2_t (*s)[5U],
    Eurydice_slice out[2U]) {
  for (size_t i = (size_t)0U; i < (size_t)144U / (size_t)16U; i++) {
    size_t i0 = i;
    core_core_arch_arm_shared_neon_uint64x2_t v0 =
        libcrux_intrinsics_arm64__vtrn1q_u64(
            s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U],
            s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
             [((size_t)2U * i0 + (size_t)1U) % (size_t)5U]);
    core_core_arch_arm_shared_neon_uint64x2_t v1 =
        libcrux_intrinsics_arm64__vtrn2q_u64(
            s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U],
            s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
             [((size_t)2U * i0 + (size_t)1U) % (size_t)5U]);
    libcrux_intrinsics_arm64__vst1q_bytes_u64(
        Eurydice_slice_subslice2(out[0U], (size_t)16U * i0,
                                 (size_t)16U * (i0 + (size_t)1U), uint8_t,
                                 Eurydice_slice),
        v0);
    libcrux_intrinsics_arm64__vst1q_bytes_u64(
        Eurydice_slice_subslice2(out[1U], (size_t)16U * i0,
                                 (size_t)16U * (i0 + (size_t)1U), uint8_t,
                                 Eurydice_slice),
        v1);
  }
  if ((size_t)144U % (size_t)16U != (size_t)0U) {
    size_t i = ((size_t)144U / (size_t)8U - (size_t)1U) / (size_t)5U;
    size_t j = ((size_t)144U / (size_t)8U - (size_t)1U) % (size_t)5U;
    uint8_t u[16U] = {0U};
    libcrux_intrinsics_arm64__vst1q_bytes_u64(
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
A monomorphic instance of libcrux_sha3.simd.arm64.store_block_full with const
generics:
- RATE = 144
*/
static KRML_MUSTINLINE void store_block_full_f0(
    core_core_arch_arm_shared_neon_uint64x2_t (*s)[5U], uint8_t ret[2U][200U]) {
  uint8_t out0[200U] = {0U};
  uint8_t out1[200U] = {0U};
  Eurydice_slice buf[2U] = {
      Eurydice_array_to_slice((size_t)200U, out0, uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)200U, out1, uint8_t, Eurydice_slice)};
  store_block_f0(s, buf);
  uint8_t uu____0[200U];
  memcpy(uu____0, out0, (size_t)200U * sizeof(uint8_t));
  uint8_t uu____1[200U];
  memcpy(uu____1, out1, (size_t)200U * sizeof(uint8_t));
  memcpy(ret[0U], uu____0, (size_t)200U * sizeof(uint8_t));
  memcpy(ret[1U], uu____1, (size_t)200U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.store_block_full_fa with const
generics:
- BLOCKSIZE = 144
*/
static KRML_MUSTINLINE void store_block_full_fa_f0(
    core_core_arch_arm_shared_neon_uint64x2_t (*a)[5U], uint8_t ret[2U][200U]) {
  store_block_full_f0(a, ret);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_and_last
with types core_core_arch_arm_shared_neon_uint64x2_t and with const generics:
- N = 2
- RATE = 144
*/
static KRML_MUSTINLINE void squeeze_first_and_last_41(
    libcrux_sha3_generic_keccak_KeccakState__core_core_arch_arm_shared_neon_uint64x2_t__2size_t
        *s,
    Eurydice_slice out[2U]) {
  uint8_t b[2U][200U];
  store_block_full_fa_f0(s->st, b);
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      Eurydice_slice uu____0 = out[i0]; uint8_t *uu____1 = b[i0];
      core_ops_range_Range__size_t lit; lit.start = (size_t)0U;
      lit.end = core_slice___Slice_T___len(out[i0], uint8_t, size_t);
      core_slice___Slice_T___copy_from_slice(
          uu____0,
          Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                     core_ops_range_Range__size_t,
                                     Eurydice_slice),
          uint8_t, void *););
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.store_block_fa with const
generics:
- BLOCKSIZE = 144
*/
static KRML_MUSTINLINE void store_block_fa_f0(
    core_core_arch_arm_shared_neon_uint64x2_t (*a)[5U], Eurydice_slice b[2U]) {
  store_block_f0(a, b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_block with
types core_core_arch_arm_shared_neon_uint64x2_t and with const generics:
- N = 2
- RATE = 144
*/
static KRML_MUSTINLINE void squeeze_first_block_41(
    libcrux_sha3_generic_keccak_KeccakState__core_core_arch_arm_shared_neon_uint64x2_t__2size_t
        *s,
    Eurydice_slice out[2U]) {
  store_block_fa_f0(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_next_block with
types core_core_arch_arm_shared_neon_uint64x2_t and with const generics:
- N = 2
- RATE = 144
*/
static KRML_MUSTINLINE void squeeze_next_block_41(
    libcrux_sha3_generic_keccak_KeccakState__core_core_arch_arm_shared_neon_uint64x2_t__2size_t
        *s,
    Eurydice_slice out[2U]) {
  keccakf1600_39(s);
  store_block_fa_f0(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_last with types
core_core_arch_arm_shared_neon_uint64x2_t and with const generics:
- N = 2
- RATE = 144
*/
static KRML_MUSTINLINE void squeeze_last_41(
    libcrux_sha3_generic_keccak_KeccakState__core_core_arch_arm_shared_neon_uint64x2_t__2size_t
        s,
    Eurydice_slice out[2U]) {
  keccakf1600_39(&s);
  uint8_t b[2U][200U];
  store_block_full_fa_f0(s.st, b);
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      Eurydice_slice uu____0 = out[i0]; uint8_t *uu____1 = b[i0];
      core_ops_range_Range__size_t lit; lit.start = (size_t)0U;
      lit.end = core_slice___Slice_T___len(out[i0], uint8_t, size_t);
      core_slice___Slice_T___copy_from_slice(
          uu____0,
          Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                     core_ops_range_Range__size_t,
                                     Eurydice_slice),
          uint8_t, void *););
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.keccak with types
core_core_arch_arm_shared_neon_uint64x2_t and with const generics:
- N = 2
- RATE = 144
- DELIM = 6
*/
static KRML_MUSTINLINE void keccak_24(Eurydice_slice data[2U],
                                      Eurydice_slice out[2U]) {
  libcrux_sha3_generic_keccak_KeccakState__core_core_arch_arm_shared_neon_uint64x2_t__2size_t
      s = new_1e_39();
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(data[0U], uint8_t, size_t) / (size_t)144U;
       i++) {
    size_t i0 = i;
    libcrux_sha3_generic_keccak_KeccakState__core_core_arch_arm_shared_neon_uint64x2_t__2size_t
        *uu____0 = &s;
    Eurydice_slice uu____1[2U];
    memcpy(uu____1, data, (size_t)2U * sizeof(Eurydice_slice));
    Eurydice_slice ret[2U];
    slice_n_fa(uu____1, i0 * (size_t)144U, (size_t)144U, ret);
    absorb_block_41(uu____0, ret);
  }
  size_t rem =
      core_slice___Slice_T___len(data[0U], uint8_t, size_t) % (size_t)144U;
  libcrux_sha3_generic_keccak_KeccakState__core_core_arch_arm_shared_neon_uint64x2_t__2size_t
      *uu____2 = &s;
  Eurydice_slice uu____3[2U];
  memcpy(uu____3, data, (size_t)2U * sizeof(Eurydice_slice));
  Eurydice_slice ret[2U];
  slice_n_fa(uu____3,
             core_slice___Slice_T___len(data[0U], uint8_t, size_t) - rem, rem,
             ret);
  absorb_final_24(uu____2, ret);
  size_t outlen = core_slice___Slice_T___len(out[0U], uint8_t, size_t);
  size_t blocks = outlen / (size_t)144U;
  size_t last = outlen - outlen % (size_t)144U;
  if (blocks == (size_t)0U) {
    squeeze_first_and_last_41(&s, out);
  } else {
    K___Eurydice_slice_uint8_t_2size_t__Eurydice_slice_uint8_t_2size_t_
        uu____4 = split_at_mut_n_fa(out, (size_t)144U);
    Eurydice_slice o0[2U];
    memcpy(o0, uu____4.fst, (size_t)2U * sizeof(Eurydice_slice));
    Eurydice_slice o1[2U];
    memcpy(o1, uu____4.snd, (size_t)2U * sizeof(Eurydice_slice));
    squeeze_first_block_41(&s, o0);
    core_ops_range_Range__size_t iter =
        core_iter_traits_collect___core__iter__traits__collect__IntoIterator_for_I__1__into_iter(
            (CLITERAL(core_ops_range_Range__size_t){.start = (size_t)1U,
                                                    .end = blocks}),
            core_ops_range_Range__size_t, core_ops_range_Range__size_t);
    while (true) {
      if (core_iter_range___core__iter__traits__iterator__Iterator_for_core__ops__range__Range_A___6__next(
              &iter, size_t, core_option_Option__size_t)
              .tag == core_option_None) {
        break;
      } else {
        K___Eurydice_slice_uint8_t_2size_t__Eurydice_slice_uint8_t_2size_t_
            uu____5 = split_at_mut_n_fa(o1, (size_t)144U);
        Eurydice_slice o[2U];
        memcpy(o, uu____5.fst, (size_t)2U * sizeof(Eurydice_slice));
        Eurydice_slice orest[2U];
        memcpy(orest, uu____5.snd, (size_t)2U * sizeof(Eurydice_slice));
        squeeze_next_block_41(&s, o);
        memcpy(o1, orest, (size_t)2U * sizeof(Eurydice_slice));
      }
    }
    if (last < outlen) {
      squeeze_last_41(s, o1);
    }
  }
}

/**
A monomorphic instance of libcrux_sha3.neon.keccakx2 with const generics:
- RATE = 144
- DELIM = 6
*/
static KRML_MUSTINLINE void keccakx2_d4(Eurydice_slice data[2U],
                                        Eurydice_slice out[2U]) {
  Eurydice_slice uu____0[2U];
  memcpy(uu____0, data, (size_t)2U * sizeof(Eurydice_slice));
  keccak_24(uu____0, out);
}

KRML_MUSTINLINE void libcrux_sha3_neon_sha224(Eurydice_slice digest,
                                              Eurydice_slice data) {
  uint8_t dummy[28U] = {0U};
  Eurydice_slice uu____0[2U] = {data, data};
  Eurydice_slice buf[2U] = {
      digest,
      Eurydice_array_to_slice((size_t)28U, dummy, uint8_t, Eurydice_slice)};
  keccakx2_d4(uu____0, buf);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block with const
generics:
- RATE = 104
*/
static KRML_MUSTINLINE void load_block_d4(
    core_core_arch_arm_shared_neon_uint64x2_t (*s)[5U],
    Eurydice_slice blocks[2U]) {
  for (size_t i = (size_t)0U; i < (size_t)104U / (size_t)16U; i++) {
    size_t i0 = i;
    core_core_arch_arm_shared_neon_uint64x2_t v0 =
        libcrux_intrinsics_arm64__vld1q_bytes_u64(Eurydice_slice_subslice2(
            blocks[0U], (size_t)16U * i0, (size_t)16U * (i0 + (size_t)1U),
            uint8_t, Eurydice_slice));
    core_core_arch_arm_shared_neon_uint64x2_t v1 =
        libcrux_intrinsics_arm64__vld1q_bytes_u64(Eurydice_slice_subslice2(
            blocks[1U], (size_t)16U * i0, (size_t)16U * (i0 + (size_t)1U),
            uint8_t, Eurydice_slice));
    s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U] =
        libcrux_intrinsics_arm64__veorq_u64(
            s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U],
            libcrux_intrinsics_arm64__vtrn1q_u64(v0, v1));
    s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
     [((size_t)2U * i0 + (size_t)1U) % (size_t)5U] =
         libcrux_intrinsics_arm64__veorq_u64(
             s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
              [((size_t)2U * i0 + (size_t)1U) % (size_t)5U],
             libcrux_intrinsics_arm64__vtrn2q_u64(v0, v1));
  }
  if ((size_t)104U % (size_t)16U != (size_t)0U) {
    size_t i = ((size_t)104U / (size_t)8U - (size_t)1U) / (size_t)5U;
    size_t j = ((size_t)104U / (size_t)8U - (size_t)1U) % (size_t)5U;
    uint64_t u[2U] = {0U};
    uint8_t uu____0[8U];
    core_result_Result__uint8_t_8size_t__core_array_TryFromSliceError dst0;
    Eurydice_slice_to_array2(
        &dst0,
        Eurydice_slice_subslice2(blocks[0U], (size_t)104U - (size_t)8U,
                                 (size_t)104U, uint8_t, Eurydice_slice),
        Eurydice_slice, uint8_t[8U], void *);
    core_result_unwrap_41_15(dst0, uu____0);
    u[0U] = core_num__u64_9__from_le_bytes(uu____0);
    uint8_t uu____1[8U];
    core_result_Result__uint8_t_8size_t__core_array_TryFromSliceError dst;
    Eurydice_slice_to_array2(
        &dst,
        Eurydice_slice_subslice2(blocks[1U], (size_t)104U - (size_t)8U,
                                 (size_t)104U, uint8_t, Eurydice_slice),
        Eurydice_slice, uint8_t[8U], void *);
    core_result_unwrap_41_15(dst, uu____1);
    u[1U] = core_num__u64_9__from_le_bytes(uu____1);
    core_core_arch_arm_shared_neon_uint64x2_t uvec =
        libcrux_intrinsics_arm64__vld1q_u64(
            Eurydice_array_to_slice((size_t)2U, u, uint64_t, Eurydice_slice));
    s[i][j] = libcrux_intrinsics_arm64__veorq_u64(s[i][j], uvec);
  }
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block_fa with const
generics:
- BLOCKSIZE = 104
*/
static KRML_MUSTINLINE void load_block_fa_d4(
    core_core_arch_arm_shared_neon_uint64x2_t (*a)[5U], Eurydice_slice b[2U]) {
  core_core_arch_arm_shared_neon_uint64x2_t(*uu____0)[5U] = a;
  Eurydice_slice uu____1[2U];
  memcpy(uu____1, b, (size_t)2U * sizeof(Eurydice_slice));
  load_block_d4(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block with types
core_core_arch_arm_shared_neon_uint64x2_t and with const generics:
- N = 2
- RATE = 104
*/
static KRML_MUSTINLINE void absorb_block_95(
    libcrux_sha3_generic_keccak_KeccakState__core_core_arch_arm_shared_neon_uint64x2_t__2size_t
        *s,
    Eurydice_slice blocks[2U]) {
  core_core_arch_arm_shared_neon_uint64x2_t(*uu____0)[5U] = s->st;
  Eurydice_slice uu____1[2U];
  memcpy(uu____1, blocks, (size_t)2U * sizeof(Eurydice_slice));
  load_block_fa_d4(uu____0, uu____1);
  keccakf1600_39(s);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block_full with const
generics:
- RATE = 104
*/
static KRML_MUSTINLINE void load_block_full_d4(
    core_core_arch_arm_shared_neon_uint64x2_t (*s)[5U],
    uint8_t blocks[2U][200U]) {
  Eurydice_slice buf[2U] = {Eurydice_array_to_slice((size_t)200U, blocks[0U],
                                                    uint8_t, Eurydice_slice),
                            Eurydice_array_to_slice((size_t)200U, blocks[1U],
                                                    uint8_t, Eurydice_slice)};
  load_block_d4(s, buf);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block_full_fa with const
generics:
- BLOCKSIZE = 104
*/
static KRML_MUSTINLINE void load_block_full_fa_d4(
    core_core_arch_arm_shared_neon_uint64x2_t (*a)[5U], uint8_t b[2U][200U]) {
  core_core_arch_arm_shared_neon_uint64x2_t(*uu____0)[5U] = a;
  uint8_t uu____1[2U][200U];
  memcpy(uu____1, b, (size_t)2U * sizeof(uint8_t[200U]));
  load_block_full_d4(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final with types
core_core_arch_arm_shared_neon_uint64x2_t and with const generics:
- N = 2
- RATE = 104
- DELIM = 6
*/
static KRML_MUSTINLINE void absorb_final_72(
    libcrux_sha3_generic_keccak_KeccakState__core_core_arch_arm_shared_neon_uint64x2_t__2size_t
        *s,
    Eurydice_slice last[2U]) {
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
  core_core_arch_arm_shared_neon_uint64x2_t(*uu____3)[5U] = s->st;
  uint8_t uu____4[2U][200U];
  memcpy(uu____4, blocks, (size_t)2U * sizeof(uint8_t[200U]));
  load_block_full_fa_d4(uu____3, uu____4);
  keccakf1600_39(s);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.store_block with const
generics:
- RATE = 104
*/
static KRML_MUSTINLINE void store_block_d4(
    core_core_arch_arm_shared_neon_uint64x2_t (*s)[5U],
    Eurydice_slice out[2U]) {
  for (size_t i = (size_t)0U; i < (size_t)104U / (size_t)16U; i++) {
    size_t i0 = i;
    core_core_arch_arm_shared_neon_uint64x2_t v0 =
        libcrux_intrinsics_arm64__vtrn1q_u64(
            s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U],
            s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
             [((size_t)2U * i0 + (size_t)1U) % (size_t)5U]);
    core_core_arch_arm_shared_neon_uint64x2_t v1 =
        libcrux_intrinsics_arm64__vtrn2q_u64(
            s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U],
            s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
             [((size_t)2U * i0 + (size_t)1U) % (size_t)5U]);
    libcrux_intrinsics_arm64__vst1q_bytes_u64(
        Eurydice_slice_subslice2(out[0U], (size_t)16U * i0,
                                 (size_t)16U * (i0 + (size_t)1U), uint8_t,
                                 Eurydice_slice),
        v0);
    libcrux_intrinsics_arm64__vst1q_bytes_u64(
        Eurydice_slice_subslice2(out[1U], (size_t)16U * i0,
                                 (size_t)16U * (i0 + (size_t)1U), uint8_t,
                                 Eurydice_slice),
        v1);
  }
  if ((size_t)104U % (size_t)16U != (size_t)0U) {
    size_t i = ((size_t)104U / (size_t)8U - (size_t)1U) / (size_t)5U;
    size_t j = ((size_t)104U / (size_t)8U - (size_t)1U) % (size_t)5U;
    uint8_t u[16U] = {0U};
    libcrux_intrinsics_arm64__vst1q_bytes_u64(
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
A monomorphic instance of libcrux_sha3.simd.arm64.store_block_full with const
generics:
- RATE = 104
*/
static KRML_MUSTINLINE void store_block_full_d4(
    core_core_arch_arm_shared_neon_uint64x2_t (*s)[5U], uint8_t ret[2U][200U]) {
  uint8_t out0[200U] = {0U};
  uint8_t out1[200U] = {0U};
  Eurydice_slice buf[2U] = {
      Eurydice_array_to_slice((size_t)200U, out0, uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)200U, out1, uint8_t, Eurydice_slice)};
  store_block_d4(s, buf);
  uint8_t uu____0[200U];
  memcpy(uu____0, out0, (size_t)200U * sizeof(uint8_t));
  uint8_t uu____1[200U];
  memcpy(uu____1, out1, (size_t)200U * sizeof(uint8_t));
  memcpy(ret[0U], uu____0, (size_t)200U * sizeof(uint8_t));
  memcpy(ret[1U], uu____1, (size_t)200U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.store_block_full_fa with const
generics:
- BLOCKSIZE = 104
*/
static KRML_MUSTINLINE void store_block_full_fa_d4(
    core_core_arch_arm_shared_neon_uint64x2_t (*a)[5U], uint8_t ret[2U][200U]) {
  store_block_full_d4(a, ret);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_and_last
with types core_core_arch_arm_shared_neon_uint64x2_t and with const generics:
- N = 2
- RATE = 104
*/
static KRML_MUSTINLINE void squeeze_first_and_last_95(
    libcrux_sha3_generic_keccak_KeccakState__core_core_arch_arm_shared_neon_uint64x2_t__2size_t
        *s,
    Eurydice_slice out[2U]) {
  uint8_t b[2U][200U];
  store_block_full_fa_d4(s->st, b);
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      Eurydice_slice uu____0 = out[i0]; uint8_t *uu____1 = b[i0];
      core_ops_range_Range__size_t lit; lit.start = (size_t)0U;
      lit.end = core_slice___Slice_T___len(out[i0], uint8_t, size_t);
      core_slice___Slice_T___copy_from_slice(
          uu____0,
          Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                     core_ops_range_Range__size_t,
                                     Eurydice_slice),
          uint8_t, void *););
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.store_block_fa with const
generics:
- BLOCKSIZE = 104
*/
static KRML_MUSTINLINE void store_block_fa_d4(
    core_core_arch_arm_shared_neon_uint64x2_t (*a)[5U], Eurydice_slice b[2U]) {
  store_block_d4(a, b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_block with
types core_core_arch_arm_shared_neon_uint64x2_t and with const generics:
- N = 2
- RATE = 104
*/
static KRML_MUSTINLINE void squeeze_first_block_95(
    libcrux_sha3_generic_keccak_KeccakState__core_core_arch_arm_shared_neon_uint64x2_t__2size_t
        *s,
    Eurydice_slice out[2U]) {
  store_block_fa_d4(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_next_block with
types core_core_arch_arm_shared_neon_uint64x2_t and with const generics:
- N = 2
- RATE = 104
*/
static KRML_MUSTINLINE void squeeze_next_block_95(
    libcrux_sha3_generic_keccak_KeccakState__core_core_arch_arm_shared_neon_uint64x2_t__2size_t
        *s,
    Eurydice_slice out[2U]) {
  keccakf1600_39(s);
  store_block_fa_d4(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_last with types
core_core_arch_arm_shared_neon_uint64x2_t and with const generics:
- N = 2
- RATE = 104
*/
static KRML_MUSTINLINE void squeeze_last_95(
    libcrux_sha3_generic_keccak_KeccakState__core_core_arch_arm_shared_neon_uint64x2_t__2size_t
        s,
    Eurydice_slice out[2U]) {
  keccakf1600_39(&s);
  uint8_t b[2U][200U];
  store_block_full_fa_d4(s.st, b);
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      Eurydice_slice uu____0 = out[i0]; uint8_t *uu____1 = b[i0];
      core_ops_range_Range__size_t lit; lit.start = (size_t)0U;
      lit.end = core_slice___Slice_T___len(out[i0], uint8_t, size_t);
      core_slice___Slice_T___copy_from_slice(
          uu____0,
          Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                     core_ops_range_Range__size_t,
                                     Eurydice_slice),
          uint8_t, void *););
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.keccak with types
core_core_arch_arm_shared_neon_uint64x2_t and with const generics:
- N = 2
- RATE = 104
- DELIM = 6
*/
static KRML_MUSTINLINE void keccak_72(Eurydice_slice data[2U],
                                      Eurydice_slice out[2U]) {
  libcrux_sha3_generic_keccak_KeccakState__core_core_arch_arm_shared_neon_uint64x2_t__2size_t
      s = new_1e_39();
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(data[0U], uint8_t, size_t) / (size_t)104U;
       i++) {
    size_t i0 = i;
    libcrux_sha3_generic_keccak_KeccakState__core_core_arch_arm_shared_neon_uint64x2_t__2size_t
        *uu____0 = &s;
    Eurydice_slice uu____1[2U];
    memcpy(uu____1, data, (size_t)2U * sizeof(Eurydice_slice));
    Eurydice_slice ret[2U];
    slice_n_fa(uu____1, i0 * (size_t)104U, (size_t)104U, ret);
    absorb_block_95(uu____0, ret);
  }
  size_t rem =
      core_slice___Slice_T___len(data[0U], uint8_t, size_t) % (size_t)104U;
  libcrux_sha3_generic_keccak_KeccakState__core_core_arch_arm_shared_neon_uint64x2_t__2size_t
      *uu____2 = &s;
  Eurydice_slice uu____3[2U];
  memcpy(uu____3, data, (size_t)2U * sizeof(Eurydice_slice));
  Eurydice_slice ret[2U];
  slice_n_fa(uu____3,
             core_slice___Slice_T___len(data[0U], uint8_t, size_t) - rem, rem,
             ret);
  absorb_final_72(uu____2, ret);
  size_t outlen = core_slice___Slice_T___len(out[0U], uint8_t, size_t);
  size_t blocks = outlen / (size_t)104U;
  size_t last = outlen - outlen % (size_t)104U;
  if (blocks == (size_t)0U) {
    squeeze_first_and_last_95(&s, out);
  } else {
    K___Eurydice_slice_uint8_t_2size_t__Eurydice_slice_uint8_t_2size_t_
        uu____4 = split_at_mut_n_fa(out, (size_t)104U);
    Eurydice_slice o0[2U];
    memcpy(o0, uu____4.fst, (size_t)2U * sizeof(Eurydice_slice));
    Eurydice_slice o1[2U];
    memcpy(o1, uu____4.snd, (size_t)2U * sizeof(Eurydice_slice));
    squeeze_first_block_95(&s, o0);
    core_ops_range_Range__size_t iter =
        core_iter_traits_collect___core__iter__traits__collect__IntoIterator_for_I__1__into_iter(
            (CLITERAL(core_ops_range_Range__size_t){.start = (size_t)1U,
                                                    .end = blocks}),
            core_ops_range_Range__size_t, core_ops_range_Range__size_t);
    while (true) {
      if (core_iter_range___core__iter__traits__iterator__Iterator_for_core__ops__range__Range_A___6__next(
              &iter, size_t, core_option_Option__size_t)
              .tag == core_option_None) {
        break;
      } else {
        K___Eurydice_slice_uint8_t_2size_t__Eurydice_slice_uint8_t_2size_t_
            uu____5 = split_at_mut_n_fa(o1, (size_t)104U);
        Eurydice_slice o[2U];
        memcpy(o, uu____5.fst, (size_t)2U * sizeof(Eurydice_slice));
        Eurydice_slice orest[2U];
        memcpy(orest, uu____5.snd, (size_t)2U * sizeof(Eurydice_slice));
        squeeze_next_block_95(&s, o);
        memcpy(o1, orest, (size_t)2U * sizeof(Eurydice_slice));
      }
    }
    if (last < outlen) {
      squeeze_last_95(s, o1);
    }
  }
}

/**
A monomorphic instance of libcrux_sha3.neon.keccakx2 with const generics:
- RATE = 104
- DELIM = 6
*/
static KRML_MUSTINLINE void keccakx2_b6(Eurydice_slice data[2U],
                                        Eurydice_slice out[2U]) {
  Eurydice_slice uu____0[2U];
  memcpy(uu____0, data, (size_t)2U * sizeof(Eurydice_slice));
  keccak_72(uu____0, out);
}

KRML_MUSTINLINE void libcrux_sha3_neon_sha384(Eurydice_slice digest,
                                              Eurydice_slice data) {
  uint8_t dummy[48U] = {0U};
  Eurydice_slice uu____0[2U] = {data, data};
  Eurydice_slice buf[2U] = {
      digest,
      Eurydice_array_to_slice((size_t)48U, dummy, uint8_t, Eurydice_slice)};
  keccakx2_b6(uu____0, buf);
}
