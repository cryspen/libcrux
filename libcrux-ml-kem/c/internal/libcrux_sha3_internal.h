/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: a8f2211d1b95e0462a96382023b164a4116c7ca4
 * Eurydice: 60f543ddc60a777138070968daaf7620ec48170d
 * Karamel: 1d81d757d5d9e16dd6463ccc72324e587c707959
 * F*: b0961063393215ca65927f017720cb365a193833-dirty
 * Libcrux: e2291b6e918559a4712b2a553f49ec92fdba1e42
 */

#ifndef __internal_libcrux_sha3_internal_H
#define __internal_libcrux_sha3_internal_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "../libcrux_sha3_internal.h"
#include "eurydice_glue.h"
#include "libcrux_core.h"

typedef libcrux_sha3_generic_keccak_KeccakState_17
    libcrux_sha3_portable_KeccakState;

/**
 Create a new SHAKE-128 state object.
*/
static KRML_MUSTINLINE libcrux_sha3_generic_keccak_KeccakState_17
libcrux_sha3_portable_incremental_shake128_init(void) {
  return libcrux_sha3_generic_keccak_new_89_04();
}

/**
 Absorb
*/
static KRML_MUSTINLINE void
libcrux_sha3_portable_incremental_shake128_absorb_final(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice data0) {
  Eurydice_slice buf[1U] = {data0};
  libcrux_sha3_generic_keccak_absorb_final_9e(s, buf);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_three_blocks
with types uint64_t
with const generics
- N= 1
- RATE= 168
*/
static KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_squeeze_first_three_blocks_c6(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice out[1U]) {
  Eurydice_slice_uint8_t_1size_t__x2 uu____0 =
      libcrux_sha3_portable_keccak_split_at_mut_n_5a(out, (size_t)168U);
  Eurydice_slice o0[1U];
  memcpy(o0, uu____0.fst, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice o10[1U];
  memcpy(o10, uu____0.snd, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_squeeze_first_block_c6(s, o0);
  Eurydice_slice_uint8_t_1size_t__x2 uu____1 =
      libcrux_sha3_portable_keccak_split_at_mut_n_5a(o10, (size_t)168U);
  Eurydice_slice o1[1U];
  memcpy(o1, uu____1.fst, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice o2[1U];
  memcpy(o2, uu____1.snd, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_squeeze_next_block_c6(s, o1);
  libcrux_sha3_generic_keccak_squeeze_next_block_c6(s, o2);
}

/**
 Squeeze three blocks
*/
static KRML_MUSTINLINE void
libcrux_sha3_portable_incremental_shake128_squeeze_first_three_blocks(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice out0) {
  Eurydice_slice buf[1U] = {out0};
  libcrux_sha3_generic_keccak_squeeze_first_three_blocks_c6(s, buf);
}

/**
 Squeeze another block
*/
static KRML_MUSTINLINE void
libcrux_sha3_portable_incremental_shake128_squeeze_next_block(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice out0) {
  Eurydice_slice buf[1U] = {out0};
  libcrux_sha3_generic_keccak_squeeze_next_block_c6(s, buf);
}

#define libcrux_sha3_Algorithm_Sha224 1
#define libcrux_sha3_Algorithm_Sha256 2
#define libcrux_sha3_Algorithm_Sha384 3
#define libcrux_sha3_Algorithm_Sha512 4

typedef uint8_t libcrux_sha3_Algorithm;

/**
 Returns the output size of a digest.
*/
static inline size_t libcrux_sha3_digest_size(libcrux_sha3_Algorithm mode) {
  if (!(mode == libcrux_sha3_Algorithm_Sha224)) {
    if (mode == libcrux_sha3_Algorithm_Sha256) {
      return (size_t)32U;
    } else if (mode == libcrux_sha3_Algorithm_Sha384) {
      return (size_t)48U;
    } else {
      return (size_t)64U;
    }
  }
  return (size_t)28U;
}

static const size_t libcrux_sha3_generic_keccak__PI[24U] = {
    (size_t)6U, (size_t)12U, (size_t)18U, (size_t)24U, (size_t)3U,
    (size_t)9U, (size_t)10U, (size_t)16U, (size_t)22U, (size_t)1U,
    (size_t)7U, (size_t)13U, (size_t)19U, (size_t)20U, (size_t)4U,
    (size_t)5U, (size_t)11U, (size_t)17U, (size_t)23U, (size_t)2U,
    (size_t)8U, (size_t)14U, (size_t)15U, (size_t)21U};

static const size_t libcrux_sha3_generic_keccak__ROTC[24U] = {
    (size_t)1U,  (size_t)62U, (size_t)28U, (size_t)27U, (size_t)36U,
    (size_t)44U, (size_t)6U,  (size_t)55U, (size_t)20U, (size_t)3U,
    (size_t)10U, (size_t)43U, (size_t)25U, (size_t)39U, (size_t)41U,
    (size_t)45U, (size_t)15U, (size_t)21U, (size_t)8U,  (size_t)18U,
    (size_t)2U,  (size_t)61U, (size_t)56U, (size_t)14U};

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_five_blocks
with types uint64_t
with const generics
- N= 1
- RATE= 168
*/
static KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_squeeze_first_five_blocks_c6(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice out[1U]) {
  Eurydice_slice_uint8_t_1size_t__x2 uu____0 =
      libcrux_sha3_portable_keccak_split_at_mut_n_5a(out, (size_t)168U);
  Eurydice_slice o0[1U];
  memcpy(o0, uu____0.fst, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice o10[1U];
  memcpy(o10, uu____0.snd, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_squeeze_first_block_c6(s, o0);
  Eurydice_slice_uint8_t_1size_t__x2 uu____1 =
      libcrux_sha3_portable_keccak_split_at_mut_n_5a(o10, (size_t)168U);
  Eurydice_slice o1[1U];
  memcpy(o1, uu____1.fst, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice o20[1U];
  memcpy(o20, uu____1.snd, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_squeeze_next_block_c6(s, o1);
  Eurydice_slice_uint8_t_1size_t__x2 uu____2 =
      libcrux_sha3_portable_keccak_split_at_mut_n_5a(o20, (size_t)168U);
  Eurydice_slice o2[1U];
  memcpy(o2, uu____2.fst, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice o30[1U];
  memcpy(o30, uu____2.snd, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_squeeze_next_block_c6(s, o2);
  Eurydice_slice_uint8_t_1size_t__x2 uu____3 =
      libcrux_sha3_portable_keccak_split_at_mut_n_5a(o30, (size_t)168U);
  Eurydice_slice o3[1U];
  memcpy(o3, uu____3.fst, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice o4[1U];
  memcpy(o4, uu____3.snd, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_squeeze_next_block_c6(s, o3);
  libcrux_sha3_generic_keccak_squeeze_next_block_c6(s, o4);
}

/**
 Squeeze five blocks
*/
static KRML_MUSTINLINE void
libcrux_sha3_portable_incremental_shake128_squeeze_first_five_blocks(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice out0) {
  Eurydice_slice buf[1U] = {out0};
  libcrux_sha3_generic_keccak_squeeze_first_five_blocks_c6(s, buf);
}

/**
 Absorb some data for SHAKE-256 for the last time
*/
static KRML_MUSTINLINE void
libcrux_sha3_portable_incremental_shake256_absorb_final(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice data) {
  Eurydice_slice buf[1U] = {data};
  libcrux_sha3_generic_keccak_absorb_final_9e0(s, buf);
}

/**
 Create a new SHAKE-256 state object.
*/
static KRML_MUSTINLINE libcrux_sha3_generic_keccak_KeccakState_17
libcrux_sha3_portable_incremental_shake256_init(void) {
  return libcrux_sha3_generic_keccak_new_89_04();
}

/**
 Squeeze the first SHAKE-256 block
*/
static KRML_MUSTINLINE void
libcrux_sha3_portable_incremental_shake256_squeeze_first_block(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice out) {
  Eurydice_slice buf[1U] = {out};
  libcrux_sha3_generic_keccak_squeeze_first_block_c60(s, buf);
}

/**
 Squeeze the next SHAKE-256 block
*/
static KRML_MUSTINLINE void
libcrux_sha3_portable_incremental_shake256_squeeze_next_block(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice out) {
  Eurydice_slice buf[1U] = {out};
  libcrux_sha3_generic_keccak_squeeze_next_block_c60(s, buf);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.KeccakXofState
with types uint64_t
with const generics
- $1size_t
- $136size_t
*/
typedef struct libcrux_sha3_generic_keccak_KeccakXofState_e2_s {
  libcrux_sha3_generic_keccak_KeccakState_17 inner;
  uint8_t buf[1U][136U];
  size_t buf_len;
  bool sponge;
} libcrux_sha3_generic_keccak_KeccakXofState_e2;

typedef libcrux_sha3_generic_keccak_KeccakXofState_e2
    libcrux_sha3_portable_incremental_Shake256Xof;

/**
 Consume the internal buffer and the required amount of the input to pad to
 `RATE`.

 Returns the `consumed` bytes from `inputs` if there's enough buffered
 content to consume, and `0` otherwise.
 If `consumed > 0` is returned, `self.buf` contains a full block to be
 loaded.
*/
/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakXofState<STATE,
PARALLEL_LANES, RATE>[TraitClause@0, TraitClause@1]#2}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.fill_buffer_8b
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 136
*/
static inline size_t libcrux_sha3_generic_keccak_fill_buffer_8b_c6(
    libcrux_sha3_generic_keccak_KeccakXofState_e2 *self,
    Eurydice_slice inputs[1U]) {
  size_t input_len = Eurydice_slice_len(inputs[0U], uint8_t);
  size_t consumed = (size_t)0U;
  if (self->buf_len > (size_t)0U) {
    if (self->buf_len + input_len >= (size_t)136U) {
      consumed = (size_t)136U - self->buf_len;
      {
        size_t i = (size_t)0U;
        Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
            (size_t)136U, self->buf[i], self->buf_len, uint8_t, size_t);
        Eurydice_slice_copy(
            uu____0,
            Eurydice_slice_subslice_to(inputs[i], consumed, uint8_t, size_t),
            uint8_t);
      }
      self->buf_len = self->buf_len + consumed;
    }
  }
  return consumed;
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakXofState<STATE,
PARALLEL_LANES, RATE>[TraitClause@0, TraitClause@1]#2}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_full_8b
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 136
*/
static inline size_t libcrux_sha3_generic_keccak_absorb_full_8b_c6(
    libcrux_sha3_generic_keccak_KeccakXofState_e2 *self,
    Eurydice_slice inputs[1U]) {
  libcrux_sha3_generic_keccak_KeccakXofState_e2 *uu____0 = self;
  /* Passing arrays by value in Rust generates a copy in C */
  Eurydice_slice copy_of_inputs0[1U];
  memcpy(copy_of_inputs0, inputs, (size_t)1U * sizeof(Eurydice_slice));
  size_t input_consumed =
      libcrux_sha3_generic_keccak_fill_buffer_8b_c6(uu____0, copy_of_inputs0);
  if (input_consumed > (size_t)0U) {
    Eurydice_slice borrowed[1U];
    {
      uint8_t repeat_expression[136U] = {0U};
      borrowed[0U] = core_array___Array_T__N__23__as_slice(
          (size_t)136U, repeat_expression, uint8_t, Eurydice_slice);
    }
    {
      size_t i = (size_t)0U;
      borrowed[i] =
          Eurydice_array_to_slice((size_t)136U, self->buf[i], uint8_t);
    }
    uint64_t(*uu____2)[5U] = self->inner.st;
    Eurydice_slice uu____3[1U];
    memcpy(uu____3, borrowed, (size_t)1U * sizeof(Eurydice_slice));
    libcrux_sha3_portable_keccak_load_block_5a_5b(uu____2, uu____3);
    libcrux_sha3_generic_keccak_keccakf1600_04(&self->inner);
    self->buf_len = (size_t)0U;
  }
  size_t input_to_consume =
      Eurydice_slice_len(inputs[0U], uint8_t) - input_consumed;
  size_t num_blocks = input_to_consume / (size_t)136U;
  size_t remainder = input_to_consume % (size_t)136U;
  for (size_t i = (size_t)0U; i < num_blocks; i++) {
    size_t i0 = i;
    uint64_t(*uu____4)[5U] = self->inner.st;
    /* Passing arrays by value in Rust generates a copy in C */
    Eurydice_slice copy_of_inputs[1U];
    memcpy(copy_of_inputs, inputs, (size_t)1U * sizeof(Eurydice_slice));
    Eurydice_slice ret[1U];
    libcrux_sha3_portable_keccak_slice_n_5a(
        copy_of_inputs, input_consumed + i0 * (size_t)136U, (size_t)136U, ret);
    libcrux_sha3_portable_keccak_load_block_5a_5b(uu____4, ret);
    libcrux_sha3_generic_keccak_keccakf1600_04(&self->inner);
  }
  return remainder;
}

/**
 Absorb

 This function takes any number of bytes to absorb and buffers if it's not
 enough. The function assumes that all input slices in `blocks` have the same
 length.

 Only a multiple of `RATE` blocks are absorbed.
 For the remaining bytes [`absorb_final`] needs to be called.

 This works best with relatively small `inputs`.
*/
/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakXofState<STATE,
PARALLEL_LANES, RATE>[TraitClause@0, TraitClause@1]#2}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_8b
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_8b_c6(
    libcrux_sha3_generic_keccak_KeccakXofState_e2 *self,
    Eurydice_slice inputs[1U]) {
  libcrux_sha3_generic_keccak_KeccakXofState_e2 *uu____0 = self;
  /* Passing arrays by value in Rust generates a copy in C */
  Eurydice_slice copy_of_inputs[1U];
  memcpy(copy_of_inputs, inputs, (size_t)1U * sizeof(Eurydice_slice));
  size_t input_remainder_len =
      libcrux_sha3_generic_keccak_absorb_full_8b_c6(uu____0, copy_of_inputs);
  if (input_remainder_len > (size_t)0U) {
    size_t input_len = Eurydice_slice_len(inputs[0U], uint8_t);
    {
      size_t i = (size_t)0U;
      Eurydice_slice uu____2 = Eurydice_array_to_subslice2(
          self->buf[i], self->buf_len, self->buf_len + input_remainder_len,
          uint8_t);
      Eurydice_slice_copy(
          uu____2,
          Eurydice_slice_subslice_from(
              inputs[i], input_len - input_remainder_len, uint8_t, size_t),
          uint8_t);
    }
    self->buf_len = self->buf_len + input_remainder_len;
  }
}

/**
 Shake256 absorb
*/
/**
This function found in impl {(libcrux_sha3::portable::incremental::Xof<136:
usize> for libcrux_sha3::portable::incremental::Shake256Xof)#1}
*/
static inline void libcrux_sha3_portable_incremental_absorb_68(
    libcrux_sha3_generic_keccak_KeccakXofState_e2 *self, Eurydice_slice input) {
  Eurydice_slice buf[1U] = {input};
  libcrux_sha3_generic_keccak_absorb_8b_c6(self, buf);
}

/**
 Absorb a final block.

 The `inputs` block may be empty. Everything in the `inputs` block beyond
 `RATE` bytes is ignored.
*/
/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakXofState<STATE,
PARALLEL_LANES, RATE>[TraitClause@0, TraitClause@1]#2}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final_8b
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 136
- DELIMITER= 31
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_8b_9e(
    libcrux_sha3_generic_keccak_KeccakXofState_e2 *self,
    Eurydice_slice inputs[1U]) {
  libcrux_sha3_generic_keccak_KeccakXofState_e2 *uu____0 = self;
  /* Passing arrays by value in Rust generates a copy in C */
  Eurydice_slice copy_of_inputs[1U];
  memcpy(copy_of_inputs, inputs, (size_t)1U * sizeof(Eurydice_slice));
  size_t input_remainder_len =
      libcrux_sha3_generic_keccak_absorb_full_8b_c6(uu____0, copy_of_inputs);
  size_t input_len = Eurydice_slice_len(inputs[0U], uint8_t);
  uint8_t blocks[1U][200U] = {{0U}};
  {
    size_t i = (size_t)0U;
    if (self->buf_len > (size_t)0U) {
      Eurydice_slice uu____2 = Eurydice_array_to_subslice2(
          blocks[i], (size_t)0U, self->buf_len, uint8_t);
      Eurydice_slice_copy(uu____2,
                          Eurydice_array_to_subslice2(self->buf[i], (size_t)0U,
                                                      self->buf_len, uint8_t),
                          uint8_t);
    }
    if (input_remainder_len > (size_t)0U) {
      Eurydice_slice uu____3 = Eurydice_array_to_subslice2(
          blocks[i], self->buf_len, self->buf_len + input_remainder_len,
          uint8_t);
      Eurydice_slice_copy(
          uu____3,
          Eurydice_slice_subslice_from(
              inputs[i], input_len - input_remainder_len, uint8_t, size_t),
          uint8_t);
    }
    blocks[i][self->buf_len + input_remainder_len] = 31U;
    size_t uu____4 = i;
    size_t uu____5 = (size_t)136U - (size_t)1U;
    blocks[uu____4][uu____5] = (uint32_t)blocks[uu____4][uu____5] | 128U;
  }
  uint64_t(*uu____6)[5U] = self->inner.st;
  uint8_t uu____7[1U][200U];
  memcpy(uu____7, blocks, (size_t)1U * sizeof(uint8_t[200U]));
  libcrux_sha3_portable_keccak_load_block_full_5a_5b(uu____6, uu____7);
  libcrux_sha3_generic_keccak_keccakf1600_04(&self->inner);
}

/**
 Shake256 absorb final
*/
/**
This function found in impl {(libcrux_sha3::portable::incremental::Xof<136:
usize> for libcrux_sha3::portable::incremental::Shake256Xof)#1}
*/
static inline void libcrux_sha3_portable_incremental_absorb_final_68(
    libcrux_sha3_generic_keccak_KeccakXofState_e2 *self, Eurydice_slice input) {
  Eurydice_slice buf[1U] = {input};
  libcrux_sha3_generic_keccak_absorb_final_8b_9e(self, buf);
}

/**
 An all zero block
*/
/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakXofState<STATE,
PARALLEL_LANES, RATE>[TraitClause@0, TraitClause@1]#2}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.zero_block_8b
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 136
*/
static inline void libcrux_sha3_generic_keccak_zero_block_8b_c6(
    uint8_t ret[136U]) {
  uint8_t repeat_expression[136U] = {0U};
  memcpy(ret, repeat_expression, (size_t)136U * sizeof(uint8_t));
}

/**
 Generate a new keccak xof state.
*/
/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakXofState<STATE,
PARALLEL_LANES, RATE>[TraitClause@0, TraitClause@1]#2}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.new_8b
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 136
*/
static inline libcrux_sha3_generic_keccak_KeccakXofState_e2
libcrux_sha3_generic_keccak_new_8b_c6(void) {
  libcrux_sha3_generic_keccak_KeccakXofState_e2 lit;
  lit.inner = libcrux_sha3_generic_keccak_new_89_04();
  uint8_t repeat_expression[1U][136U];
  { libcrux_sha3_generic_keccak_zero_block_8b_c6(repeat_expression[0U]); }
  memcpy(lit.buf, repeat_expression, (size_t)1U * sizeof(uint8_t[136U]));
  lit.buf_len = (size_t)0U;
  lit.sponge = false;
  return lit;
}

/**
 Shake256 new state
*/
/**
This function found in impl {(libcrux_sha3::portable::incremental::Xof<136:
usize> for libcrux_sha3::portable::incremental::Shake256Xof)#1}
*/
static inline libcrux_sha3_generic_keccak_KeccakXofState_e2
libcrux_sha3_portable_incremental_new_68(void) {
  return libcrux_sha3_generic_keccak_new_8b_c6();
}

/**
 `out` has the exact size we want here. It must be less than or equal to `RATE`.
*/
/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_5a
with const generics
- RATE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_5a_5b(
    uint64_t (*state)[5U], Eurydice_slice out[1U]) {
  size_t num_full_blocks = Eurydice_slice_len(out[0U], uint8_t) / (size_t)8U;
  size_t last_block_len = Eurydice_slice_len(out[0U], uint8_t) % (size_t)8U;
  for (size_t i = (size_t)0U; i < num_full_blocks; i++) {
    size_t i0 = i;
    Eurydice_slice uu____0 = Eurydice_slice_subslice2(
        out[0U], i0 * (size_t)8U, i0 * (size_t)8U + (size_t)8U, uint8_t);
    uint8_t ret[8U];
    core_num__u64_9__to_le_bytes(state[i0 / (size_t)5U][i0 % (size_t)5U], ret);
    Eurydice_slice_copy(
        uu____0, Eurydice_array_to_slice((size_t)8U, ret, uint8_t), uint8_t);
  }
  if (last_block_len != (size_t)0U) {
    Eurydice_slice uu____1 = Eurydice_slice_subslice2(
        out[0U], num_full_blocks * (size_t)8U,
        num_full_blocks * (size_t)8U + last_block_len, uint8_t);
    uint8_t ret[8U];
    core_num__u64_9__to_le_bytes(
        state[num_full_blocks / (size_t)5U][num_full_blocks % (size_t)5U], ret);
    Eurydice_slice_copy(
        uu____1,
        Eurydice_array_to_subslice2(ret, (size_t)0U, last_block_len, uint8_t),
        uint8_t);
  }
}

/**
 Squeeze `N` x `LEN` bytes.
*/
/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakXofState<STATE,
PARALLEL_LANES, RATE>[TraitClause@0, TraitClause@1]#2}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_8b
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_8b_c6(
    libcrux_sha3_generic_keccak_KeccakXofState_e2 *self,
    Eurydice_slice out[1U]) {
  if (self->sponge) {
    libcrux_sha3_generic_keccak_keccakf1600_04(&self->inner);
  }
  size_t out_len = Eurydice_slice_len(out[0U], uint8_t);
  size_t blocks = out_len / (size_t)136U;
  size_t last = out_len - out_len % (size_t)136U;
  size_t mid;
  if ((size_t)136U >= out_len) {
    mid = out_len;
  } else {
    mid = (size_t)136U;
  }
  Eurydice_slice_uint8_t_1size_t__x2 uu____0 =
      libcrux_sha3_portable_keccak_split_at_mut_n_5a(out, mid);
  Eurydice_slice out00[1U];
  memcpy(out00, uu____0.fst, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice out_rest[1U];
  memcpy(out_rest, uu____0.snd, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_portable_keccak_store_5a_5b(self->inner.st, out00);
  core_ops_range_Range_08 iter =
      core_iter_traits_collect___core__iter__traits__collect__IntoIterator_for_I__1__into_iter(
          (CLITERAL(core_ops_range_Range_08){.start = (size_t)1U,
                                             .end = blocks}),
          core_ops_range_Range_08, core_ops_range_Range_08);
  while (true) {
    if (core_iter_range___core__iter__traits__iterator__Iterator_for_core__ops__range__Range_A__TraitClause_0___6__next(
            &iter, size_t, core_option_Option_08)
            .tag == core_option_None) {
      break;
    } else {
      Eurydice_slice_uint8_t_1size_t__x2 uu____1 =
          libcrux_sha3_portable_keccak_split_at_mut_n_5a(out_rest,
                                                         (size_t)136U);
      Eurydice_slice out0[1U];
      memcpy(out0, uu____1.fst, (size_t)1U * sizeof(Eurydice_slice));
      Eurydice_slice tmp[1U];
      memcpy(tmp, uu____1.snd, (size_t)1U * sizeof(Eurydice_slice));
      libcrux_sha3_generic_keccak_keccakf1600_04(&self->inner);
      libcrux_sha3_portable_keccak_store_5a_5b(self->inner.st, out0);
      memcpy(out_rest, tmp, (size_t)1U * sizeof(Eurydice_slice));
    }
  }
  if (last < out_len) {
    libcrux_sha3_generic_keccak_keccakf1600_04(&self->inner);
    libcrux_sha3_portable_keccak_store_5a_5b(self->inner.st, out_rest);
  }
  self->sponge = true;
}

/**
 Shake256 squeeze
*/
/**
This function found in impl {(libcrux_sha3::portable::incremental::Xof<136:
usize> for libcrux_sha3::portable::incremental::Shake256Xof)#1}
*/
static inline void libcrux_sha3_portable_incremental_squeeze_68(
    libcrux_sha3_generic_keccak_KeccakXofState_e2 *self, Eurydice_slice out) {
  Eurydice_slice buf[1U] = {out};
  libcrux_sha3_generic_keccak_squeeze_8b_c6(self, buf);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.KeccakXofState
with types uint64_t
with const generics
- $1size_t
- $168size_t
*/
typedef struct libcrux_sha3_generic_keccak_KeccakXofState_97_s {
  libcrux_sha3_generic_keccak_KeccakState_17 inner;
  uint8_t buf[1U][168U];
  size_t buf_len;
  bool sponge;
} libcrux_sha3_generic_keccak_KeccakXofState_97;

typedef libcrux_sha3_generic_keccak_KeccakXofState_97
    libcrux_sha3_portable_incremental_Shake128Xof;

/**
 Consume the internal buffer and the required amount of the input to pad to
 `RATE`.

 Returns the `consumed` bytes from `inputs` if there's enough buffered
 content to consume, and `0` otherwise.
 If `consumed > 0` is returned, `self.buf` contains a full block to be
 loaded.
*/
/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakXofState<STATE,
PARALLEL_LANES, RATE>[TraitClause@0, TraitClause@1]#2}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.fill_buffer_8b
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 168
*/
static inline size_t libcrux_sha3_generic_keccak_fill_buffer_8b_c60(
    libcrux_sha3_generic_keccak_KeccakXofState_97 *self,
    Eurydice_slice inputs[1U]) {
  size_t input_len = Eurydice_slice_len(inputs[0U], uint8_t);
  size_t consumed = (size_t)0U;
  if (self->buf_len > (size_t)0U) {
    if (self->buf_len + input_len >= (size_t)168U) {
      consumed = (size_t)168U - self->buf_len;
      {
        size_t i = (size_t)0U;
        Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
            (size_t)168U, self->buf[i], self->buf_len, uint8_t, size_t);
        Eurydice_slice_copy(
            uu____0,
            Eurydice_slice_subslice_to(inputs[i], consumed, uint8_t, size_t),
            uint8_t);
      }
      self->buf_len = self->buf_len + consumed;
    }
  }
  return consumed;
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakXofState<STATE,
PARALLEL_LANES, RATE>[TraitClause@0, TraitClause@1]#2}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_full_8b
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 168
*/
static inline size_t libcrux_sha3_generic_keccak_absorb_full_8b_c60(
    libcrux_sha3_generic_keccak_KeccakXofState_97 *self,
    Eurydice_slice inputs[1U]) {
  libcrux_sha3_generic_keccak_KeccakXofState_97 *uu____0 = self;
  /* Passing arrays by value in Rust generates a copy in C */
  Eurydice_slice copy_of_inputs0[1U];
  memcpy(copy_of_inputs0, inputs, (size_t)1U * sizeof(Eurydice_slice));
  size_t input_consumed =
      libcrux_sha3_generic_keccak_fill_buffer_8b_c60(uu____0, copy_of_inputs0);
  if (input_consumed > (size_t)0U) {
    Eurydice_slice borrowed[1U];
    {
      uint8_t repeat_expression[168U] = {0U};
      borrowed[0U] = core_array___Array_T__N__23__as_slice(
          (size_t)168U, repeat_expression, uint8_t, Eurydice_slice);
    }
    {
      size_t i = (size_t)0U;
      borrowed[i] =
          Eurydice_array_to_slice((size_t)168U, self->buf[i], uint8_t);
    }
    uint64_t(*uu____2)[5U] = self->inner.st;
    Eurydice_slice uu____3[1U];
    memcpy(uu____3, borrowed, (size_t)1U * sizeof(Eurydice_slice));
    libcrux_sha3_portable_keccak_load_block_5a_3a(uu____2, uu____3);
    libcrux_sha3_generic_keccak_keccakf1600_04(&self->inner);
    self->buf_len = (size_t)0U;
  }
  size_t input_to_consume =
      Eurydice_slice_len(inputs[0U], uint8_t) - input_consumed;
  size_t num_blocks = input_to_consume / (size_t)168U;
  size_t remainder = input_to_consume % (size_t)168U;
  for (size_t i = (size_t)0U; i < num_blocks; i++) {
    size_t i0 = i;
    uint64_t(*uu____4)[5U] = self->inner.st;
    /* Passing arrays by value in Rust generates a copy in C */
    Eurydice_slice copy_of_inputs[1U];
    memcpy(copy_of_inputs, inputs, (size_t)1U * sizeof(Eurydice_slice));
    Eurydice_slice ret[1U];
    libcrux_sha3_portable_keccak_slice_n_5a(
        copy_of_inputs, input_consumed + i0 * (size_t)168U, (size_t)168U, ret);
    libcrux_sha3_portable_keccak_load_block_5a_3a(uu____4, ret);
    libcrux_sha3_generic_keccak_keccakf1600_04(&self->inner);
  }
  return remainder;
}

/**
 Absorb

 This function takes any number of bytes to absorb and buffers if it's not
 enough. The function assumes that all input slices in `blocks` have the same
 length.

 Only a multiple of `RATE` blocks are absorbed.
 For the remaining bytes [`absorb_final`] needs to be called.

 This works best with relatively small `inputs`.
*/
/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakXofState<STATE,
PARALLEL_LANES, RATE>[TraitClause@0, TraitClause@1]#2}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_8b
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_8b_c60(
    libcrux_sha3_generic_keccak_KeccakXofState_97 *self,
    Eurydice_slice inputs[1U]) {
  libcrux_sha3_generic_keccak_KeccakXofState_97 *uu____0 = self;
  /* Passing arrays by value in Rust generates a copy in C */
  Eurydice_slice copy_of_inputs[1U];
  memcpy(copy_of_inputs, inputs, (size_t)1U * sizeof(Eurydice_slice));
  size_t input_remainder_len =
      libcrux_sha3_generic_keccak_absorb_full_8b_c60(uu____0, copy_of_inputs);
  if (input_remainder_len > (size_t)0U) {
    size_t input_len = Eurydice_slice_len(inputs[0U], uint8_t);
    {
      size_t i = (size_t)0U;
      Eurydice_slice uu____2 = Eurydice_array_to_subslice2(
          self->buf[i], self->buf_len, self->buf_len + input_remainder_len,
          uint8_t);
      Eurydice_slice_copy(
          uu____2,
          Eurydice_slice_subslice_from(
              inputs[i], input_len - input_remainder_len, uint8_t, size_t),
          uint8_t);
    }
    self->buf_len = self->buf_len + input_remainder_len;
  }
}

/**
This function found in impl {(libcrux_sha3::portable::incremental::Xof<168:
usize> for libcrux_sha3::portable::incremental::Shake128Xof)}
*/
static inline void libcrux_sha3_portable_incremental_absorb_2f(
    libcrux_sha3_generic_keccak_KeccakXofState_97 *self, Eurydice_slice input) {
  Eurydice_slice buf[1U] = {input};
  libcrux_sha3_generic_keccak_absorb_8b_c60(self, buf);
}

/**
 Absorb a final block.

 The `inputs` block may be empty. Everything in the `inputs` block beyond
 `RATE` bytes is ignored.
*/
/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakXofState<STATE,
PARALLEL_LANES, RATE>[TraitClause@0, TraitClause@1]#2}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final_8b
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 168
- DELIMITER= 31
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_8b_9e0(
    libcrux_sha3_generic_keccak_KeccakXofState_97 *self,
    Eurydice_slice inputs[1U]) {
  libcrux_sha3_generic_keccak_KeccakXofState_97 *uu____0 = self;
  /* Passing arrays by value in Rust generates a copy in C */
  Eurydice_slice copy_of_inputs[1U];
  memcpy(copy_of_inputs, inputs, (size_t)1U * sizeof(Eurydice_slice));
  size_t input_remainder_len =
      libcrux_sha3_generic_keccak_absorb_full_8b_c60(uu____0, copy_of_inputs);
  size_t input_len = Eurydice_slice_len(inputs[0U], uint8_t);
  uint8_t blocks[1U][200U] = {{0U}};
  {
    size_t i = (size_t)0U;
    if (self->buf_len > (size_t)0U) {
      Eurydice_slice uu____2 = Eurydice_array_to_subslice2(
          blocks[i], (size_t)0U, self->buf_len, uint8_t);
      Eurydice_slice_copy(uu____2,
                          Eurydice_array_to_subslice2(self->buf[i], (size_t)0U,
                                                      self->buf_len, uint8_t),
                          uint8_t);
    }
    if (input_remainder_len > (size_t)0U) {
      Eurydice_slice uu____3 = Eurydice_array_to_subslice2(
          blocks[i], self->buf_len, self->buf_len + input_remainder_len,
          uint8_t);
      Eurydice_slice_copy(
          uu____3,
          Eurydice_slice_subslice_from(
              inputs[i], input_len - input_remainder_len, uint8_t, size_t),
          uint8_t);
    }
    blocks[i][self->buf_len + input_remainder_len] = 31U;
    size_t uu____4 = i;
    size_t uu____5 = (size_t)168U - (size_t)1U;
    blocks[uu____4][uu____5] = (uint32_t)blocks[uu____4][uu____5] | 128U;
  }
  uint64_t(*uu____6)[5U] = self->inner.st;
  uint8_t uu____7[1U][200U];
  memcpy(uu____7, blocks, (size_t)1U * sizeof(uint8_t[200U]));
  libcrux_sha3_portable_keccak_load_block_full_5a_3a(uu____6, uu____7);
  libcrux_sha3_generic_keccak_keccakf1600_04(&self->inner);
}

/**
This function found in impl {(libcrux_sha3::portable::incremental::Xof<168:
usize> for libcrux_sha3::portable::incremental::Shake128Xof)}
*/
static inline void libcrux_sha3_portable_incremental_absorb_final_2f(
    libcrux_sha3_generic_keccak_KeccakXofState_97 *self, Eurydice_slice input) {
  Eurydice_slice buf[1U] = {input};
  libcrux_sha3_generic_keccak_absorb_final_8b_9e0(self, buf);
}

/**
 An all zero block
*/
/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakXofState<STATE,
PARALLEL_LANES, RATE>[TraitClause@0, TraitClause@1]#2}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.zero_block_8b
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 168
*/
static inline void libcrux_sha3_generic_keccak_zero_block_8b_c60(
    uint8_t ret[168U]) {
  uint8_t repeat_expression[168U] = {0U};
  memcpy(ret, repeat_expression, (size_t)168U * sizeof(uint8_t));
}

/**
 Generate a new keccak xof state.
*/
/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakXofState<STATE,
PARALLEL_LANES, RATE>[TraitClause@0, TraitClause@1]#2}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.new_8b
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 168
*/
static inline libcrux_sha3_generic_keccak_KeccakXofState_97
libcrux_sha3_generic_keccak_new_8b_c60(void) {
  libcrux_sha3_generic_keccak_KeccakXofState_97 lit;
  lit.inner = libcrux_sha3_generic_keccak_new_89_04();
  uint8_t repeat_expression[1U][168U];
  { libcrux_sha3_generic_keccak_zero_block_8b_c60(repeat_expression[0U]); }
  memcpy(lit.buf, repeat_expression, (size_t)1U * sizeof(uint8_t[168U]));
  lit.buf_len = (size_t)0U;
  lit.sponge = false;
  return lit;
}

/**
This function found in impl {(libcrux_sha3::portable::incremental::Xof<168:
usize> for libcrux_sha3::portable::incremental::Shake128Xof)}
*/
static inline libcrux_sha3_generic_keccak_KeccakXofState_97
libcrux_sha3_portable_incremental_new_2f(void) {
  return libcrux_sha3_generic_keccak_new_8b_c60();
}

/**
 `out` has the exact size we want here. It must be less than or equal to `RATE`.
*/
/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_5a
with const generics
- RATE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_5a_3a(
    uint64_t (*state)[5U], Eurydice_slice out[1U]) {
  size_t num_full_blocks = Eurydice_slice_len(out[0U], uint8_t) / (size_t)8U;
  size_t last_block_len = Eurydice_slice_len(out[0U], uint8_t) % (size_t)8U;
  for (size_t i = (size_t)0U; i < num_full_blocks; i++) {
    size_t i0 = i;
    Eurydice_slice uu____0 = Eurydice_slice_subslice2(
        out[0U], i0 * (size_t)8U, i0 * (size_t)8U + (size_t)8U, uint8_t);
    uint8_t ret[8U];
    core_num__u64_9__to_le_bytes(state[i0 / (size_t)5U][i0 % (size_t)5U], ret);
    Eurydice_slice_copy(
        uu____0, Eurydice_array_to_slice((size_t)8U, ret, uint8_t), uint8_t);
  }
  if (last_block_len != (size_t)0U) {
    Eurydice_slice uu____1 = Eurydice_slice_subslice2(
        out[0U], num_full_blocks * (size_t)8U,
        num_full_blocks * (size_t)8U + last_block_len, uint8_t);
    uint8_t ret[8U];
    core_num__u64_9__to_le_bytes(
        state[num_full_blocks / (size_t)5U][num_full_blocks % (size_t)5U], ret);
    Eurydice_slice_copy(
        uu____1,
        Eurydice_array_to_subslice2(ret, (size_t)0U, last_block_len, uint8_t),
        uint8_t);
  }
}

/**
 Squeeze `N` x `LEN` bytes.
*/
/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakXofState<STATE,
PARALLEL_LANES, RATE>[TraitClause@0, TraitClause@1]#2}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_8b
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_8b_c60(
    libcrux_sha3_generic_keccak_KeccakXofState_97 *self,
    Eurydice_slice out[1U]) {
  if (self->sponge) {
    libcrux_sha3_generic_keccak_keccakf1600_04(&self->inner);
  }
  size_t out_len = Eurydice_slice_len(out[0U], uint8_t);
  size_t blocks = out_len / (size_t)168U;
  size_t last = out_len - out_len % (size_t)168U;
  size_t mid;
  if ((size_t)168U >= out_len) {
    mid = out_len;
  } else {
    mid = (size_t)168U;
  }
  Eurydice_slice_uint8_t_1size_t__x2 uu____0 =
      libcrux_sha3_portable_keccak_split_at_mut_n_5a(out, mid);
  Eurydice_slice out00[1U];
  memcpy(out00, uu____0.fst, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice out_rest[1U];
  memcpy(out_rest, uu____0.snd, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_portable_keccak_store_5a_3a(self->inner.st, out00);
  core_ops_range_Range_08 iter =
      core_iter_traits_collect___core__iter__traits__collect__IntoIterator_for_I__1__into_iter(
          (CLITERAL(core_ops_range_Range_08){.start = (size_t)1U,
                                             .end = blocks}),
          core_ops_range_Range_08, core_ops_range_Range_08);
  while (true) {
    if (core_iter_range___core__iter__traits__iterator__Iterator_for_core__ops__range__Range_A__TraitClause_0___6__next(
            &iter, size_t, core_option_Option_08)
            .tag == core_option_None) {
      break;
    } else {
      Eurydice_slice_uint8_t_1size_t__x2 uu____1 =
          libcrux_sha3_portable_keccak_split_at_mut_n_5a(out_rest,
                                                         (size_t)168U);
      Eurydice_slice out0[1U];
      memcpy(out0, uu____1.fst, (size_t)1U * sizeof(Eurydice_slice));
      Eurydice_slice tmp[1U];
      memcpy(tmp, uu____1.snd, (size_t)1U * sizeof(Eurydice_slice));
      libcrux_sha3_generic_keccak_keccakf1600_04(&self->inner);
      libcrux_sha3_portable_keccak_store_5a_3a(self->inner.st, out0);
      memcpy(out_rest, tmp, (size_t)1U * sizeof(Eurydice_slice));
    }
  }
  if (last < out_len) {
    libcrux_sha3_generic_keccak_keccakf1600_04(&self->inner);
    libcrux_sha3_portable_keccak_store_5a_3a(self->inner.st, out_rest);
  }
  self->sponge = true;
}

/**
 Shake128 squeeze
*/
/**
This function found in impl {(libcrux_sha3::portable::incremental::Xof<168:
usize> for libcrux_sha3::portable::incremental::Shake128Xof)}
*/
static inline void libcrux_sha3_portable_incremental_squeeze_2f(
    libcrux_sha3_generic_keccak_KeccakXofState_97 *self, Eurydice_slice out) {
  Eurydice_slice buf[1U] = {out};
  libcrux_sha3_generic_keccak_squeeze_8b_c60(self, buf);
}

/**
This function found in impl {(core::clone::Clone for
libcrux_sha3::portable::KeccakState)}
*/
static inline libcrux_sha3_generic_keccak_KeccakState_17
libcrux_sha3_portable_clone_3d(
    libcrux_sha3_generic_keccak_KeccakState_17 *self) {
  return self[0U];
}

/**
This function found in impl {(core::convert::From<libcrux_sha3::Algorithm> for
u32)#1}
*/
static inline uint32_t libcrux_sha3_from_eb(libcrux_sha3_Algorithm v) {
  if (!(v == libcrux_sha3_Algorithm_Sha224)) {
    if (v == libcrux_sha3_Algorithm_Sha256) {
      return 2U;
    } else if (v == libcrux_sha3_Algorithm_Sha384) {
      return 3U;
    } else {
      return 4U;
    }
  }
  return 1U;
}

/**
This function found in impl {(core::convert::From<u32> for
libcrux_sha3::Algorithm)}
*/
static inline libcrux_sha3_Algorithm libcrux_sha3_from_2d(uint32_t v) {
  switch (v) {
    case 1U: {
      break;
    }
    case 2U: {
      return libcrux_sha3_Algorithm_Sha256;
    }
    case 3U: {
      return libcrux_sha3_Algorithm_Sha384;
    }
    case 4U: {
      return libcrux_sha3_Algorithm_Sha512;
    }
    default: {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                        "panic!");
      KRML_HOST_EXIT(255U);
    }
  }
  return libcrux_sha3_Algorithm_Sha224;
}

typedef uint8_t libcrux_sha3_Sha3_512Digest[64U];

typedef uint8_t libcrux_sha3_Sha3_384Digest[48U];

typedef uint8_t libcrux_sha3_Sha3_256Digest[32U];

typedef uint8_t libcrux_sha3_Sha3_224Digest[28U];

#if defined(__cplusplus)
}
#endif

#define __internal_libcrux_sha3_internal_H_DEFINED
#endif
