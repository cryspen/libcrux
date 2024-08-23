/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 962f26311ccdf09a6a3cfeacbccafba22bf3d405
 * Eurydice: e66abbc2119485abfafa17c1911bdbdada5b04f3
 * Karamel: 7862fdc3899b718d39ec98568f78ec40592a622a
 * F*: a32b316e521fa4f239b610ec8f1d15e78d62cbe8-dirty
 * Libcrux: 9a130a852767d2f8881c458e022bf35fec1f6afe
 */

#ifndef __internal_libcrux_sha3_internal_H
#define __internal_libcrux_sha3_internal_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "../libcrux_sha3_internal.h"
#include "eurydice_glue.h"

typedef libcrux_sha3_generic_keccak_KeccakState_48
    libcrux_sha3_portable_KeccakState;

/**
 Create a new SHAKE-128 state object.
*/
static KRML_MUSTINLINE libcrux_sha3_generic_keccak_KeccakState_48
libcrux_sha3_portable_incremental_shake128_init(void) {
  return libcrux_sha3_generic_keccak_new_1e_f4();
}

/**
 Absorb
*/
static KRML_MUSTINLINE void
libcrux_sha3_portable_incremental_shake128_absorb_final(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice data0) {
  Eurydice_slice buf[1U] = {data0};
  libcrux_sha3_generic_keccak_absorb_final_c7(s, buf);
}

/**
 Squeeze another block
*/
static KRML_MUSTINLINE void
libcrux_sha3_portable_incremental_shake128_squeeze_next_block(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice out0) {
  Eurydice_slice buf[1U] = {out0};
  libcrux_sha3_generic_keccak_squeeze_next_block_fc(s, buf);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_three_blocks
with types uint64_t
with const generics
- N= 1
- RATE= 168
*/
static KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_squeeze_first_three_blocks_cc(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice out[1U]) {
  Eurydice_slice_uint8_t_1size_t__x2 uu____0 =
      libcrux_sha3_portable_keccak_split_at_mut_n_5a(out, (size_t)168U);
  Eurydice_slice o0[1U];
  memcpy(o0, uu____0.fst, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice o10[1U];
  memcpy(o10, uu____0.snd, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_squeeze_first_block_84(s, o0);
  Eurydice_slice_uint8_t_1size_t__x2 uu____1 =
      libcrux_sha3_portable_keccak_split_at_mut_n_5a(o10, (size_t)168U);
  Eurydice_slice o1[1U];
  memcpy(o1, uu____1.fst, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice o2[1U];
  memcpy(o2, uu____1.snd, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_squeeze_next_block_fc(s, o1);
  libcrux_sha3_generic_keccak_squeeze_next_block_fc(s, o2);
}

/**
 Squeeze three blocks
*/
static KRML_MUSTINLINE void
libcrux_sha3_portable_incremental_shake128_squeeze_first_three_blocks(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice out0) {
  Eurydice_slice buf[1U] = {out0};
  libcrux_sha3_generic_keccak_squeeze_first_three_blocks_cc(s, buf);
}

#define libcrux_sha3_Sha224 0
#define libcrux_sha3_Sha256 1
#define libcrux_sha3_Sha384 2
#define libcrux_sha3_Sha512 3

typedef uint8_t libcrux_sha3_Algorithm;

/**
 Returns the output size of a digest.
*/
static inline size_t libcrux_sha3_digest_size(libcrux_sha3_Algorithm mode) {
  size_t uu____0;
  switch (mode) {
    case libcrux_sha3_Sha224: {
      uu____0 = (size_t)28U;
      break;
    }
    case libcrux_sha3_Sha256: {
      uu____0 = (size_t)32U;
      break;
    }
    case libcrux_sha3_Sha384: {
      uu____0 = (size_t)48U;
      break;
    }
    case libcrux_sha3_Sha512: {
      uu____0 = (size_t)64U;
      break;
    }
    default: {
      KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__,
                        __LINE__);
      KRML_HOST_EXIT(253U);
    }
  }
  return uu____0;
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
libcrux_sha3_generic_keccak_squeeze_first_five_blocks_4f(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice out[1U]) {
  Eurydice_slice_uint8_t_1size_t__x2 uu____0 =
      libcrux_sha3_portable_keccak_split_at_mut_n_5a(out, (size_t)168U);
  Eurydice_slice o0[1U];
  memcpy(o0, uu____0.fst, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice o10[1U];
  memcpy(o10, uu____0.snd, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_squeeze_first_block_84(s, o0);
  Eurydice_slice_uint8_t_1size_t__x2 uu____1 =
      libcrux_sha3_portable_keccak_split_at_mut_n_5a(o10, (size_t)168U);
  Eurydice_slice o1[1U];
  memcpy(o1, uu____1.fst, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice o20[1U];
  memcpy(o20, uu____1.snd, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_squeeze_next_block_fc(s, o1);
  Eurydice_slice_uint8_t_1size_t__x2 uu____2 =
      libcrux_sha3_portable_keccak_split_at_mut_n_5a(o20, (size_t)168U);
  Eurydice_slice o2[1U];
  memcpy(o2, uu____2.fst, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice o30[1U];
  memcpy(o30, uu____2.snd, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_squeeze_next_block_fc(s, o2);
  Eurydice_slice_uint8_t_1size_t__x2 uu____3 =
      libcrux_sha3_portable_keccak_split_at_mut_n_5a(o30, (size_t)168U);
  Eurydice_slice o3[1U];
  memcpy(o3, uu____3.fst, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice o4[1U];
  memcpy(o4, uu____3.snd, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_squeeze_next_block_fc(s, o3);
  libcrux_sha3_generic_keccak_squeeze_next_block_fc(s, o4);
}

/**
 Squeeze five blocks
*/
static KRML_MUSTINLINE void
libcrux_sha3_portable_incremental_shake128_squeeze_first_five_blocks(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice out0) {
  Eurydice_slice buf[1U] = {out0};
  libcrux_sha3_generic_keccak_squeeze_first_five_blocks_4f(s, buf);
}

/**
 Absorb some data for SHAKE-256 for the last time
*/
static KRML_MUSTINLINE void
libcrux_sha3_portable_incremental_shake256_absorb_final(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice data) {
  Eurydice_slice buf[1U] = {data};
  libcrux_sha3_generic_keccak_absorb_final_c70(s, buf);
}

/**
 Create a new SHAKE-256 state object.
*/
static KRML_MUSTINLINE libcrux_sha3_generic_keccak_KeccakState_48
libcrux_sha3_portable_incremental_shake256_init(void) {
  return libcrux_sha3_generic_keccak_new_1e_f4();
}

/**
 Squeeze the first SHAKE-256 block
*/
static KRML_MUSTINLINE void
libcrux_sha3_portable_incremental_shake256_squeeze_first_block(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice out) {
  Eurydice_slice buf[1U] = {out};
  libcrux_sha3_generic_keccak_squeeze_first_block_840(s, buf);
}

/**
 Squeeze the next SHAKE-256 block
*/
static KRML_MUSTINLINE void
libcrux_sha3_portable_incremental_shake256_squeeze_next_block(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice out) {
  Eurydice_slice buf[1U] = {out};
  libcrux_sha3_generic_keccak_squeeze_next_block_fc0(s, buf);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.KeccakXofState
with types uint64_t
with const generics
- $1size_t
- $136size_t
*/
typedef struct libcrux_sha3_generic_keccak_KeccakXofState_4f_s {
  libcrux_sha3_generic_keccak_KeccakState_48 inner;
  uint8_t buf[1U][136U];
  size_t buf_len;
  bool sponge;
} libcrux_sha3_generic_keccak_KeccakXofState_4f;

typedef libcrux_sha3_generic_keccak_KeccakXofState_4f
    libcrux_sha3_portable_incremental_Shake256Absorb;

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
PARALLEL_LANES, RATE>[TraitClause@0]#2}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.fill_buffer_9d
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 136
*/
static inline size_t libcrux_sha3_generic_keccak_fill_buffer_9d_b0(
    libcrux_sha3_generic_keccak_KeccakXofState_4f *self,
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
PARALLEL_LANES, RATE>[TraitClause@0]#2}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_full_9d
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 136
*/
static inline size_t libcrux_sha3_generic_keccak_absorb_full_9d_f8(
    libcrux_sha3_generic_keccak_KeccakXofState_4f *self,
    Eurydice_slice inputs[1U]) {
  libcrux_sha3_generic_keccak_KeccakXofState_4f *uu____0 = self;
  /* Passing arrays by value in Rust generates a copy in C */
  Eurydice_slice copy_of_inputs0[1U];
  memcpy(copy_of_inputs0, inputs, (size_t)1U * sizeof(Eurydice_slice));
  size_t input_consumed =
      libcrux_sha3_generic_keccak_fill_buffer_9d_b0(uu____0, copy_of_inputs0);
  if (input_consumed > (size_t)0U) {
    Eurydice_slice borrowed[1U];
    {
      uint8_t buf[136U] = {0U};
      borrowed[0U] = core_array___Array_T__N__23__as_slice(
          (size_t)136U, buf, uint8_t, Eurydice_slice);
    }
    {
      size_t i = (size_t)0U;
      borrowed[i] =
          Eurydice_array_to_slice((size_t)136U, self->buf[i], uint8_t);
    }
    uint64_t(*uu____2)[5U] = self->inner.st;
    Eurydice_slice uu____3[1U];
    memcpy(uu____3, borrowed, (size_t)1U * sizeof(Eurydice_slice));
    libcrux_sha3_portable_keccak_load_block_5a_b8(uu____2, uu____3);
    libcrux_sha3_generic_keccak_keccakf1600_21(&self->inner);
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
    libcrux_sha3_portable_keccak_load_block_5a_b8(uu____4, ret);
    libcrux_sha3_generic_keccak_keccakf1600_21(&self->inner);
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
PARALLEL_LANES, RATE>[TraitClause@0]#2}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_9d
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_9d_7b(
    libcrux_sha3_generic_keccak_KeccakXofState_4f *self,
    Eurydice_slice inputs[1U]) {
  libcrux_sha3_generic_keccak_KeccakXofState_4f *uu____0 = self;
  /* Passing arrays by value in Rust generates a copy in C */
  Eurydice_slice copy_of_inputs[1U];
  memcpy(copy_of_inputs, inputs, (size_t)1U * sizeof(Eurydice_slice));
  size_t input_remainder_len =
      libcrux_sha3_generic_keccak_absorb_full_9d_f8(uu____0, copy_of_inputs);
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
This function found in impl
{(libcrux_sha3::portable::incremental::XofAbsorb<136: usize> for
libcrux_sha3::portable::incremental::Shake256Absorb)#2}
*/
static inline void libcrux_sha3_portable_incremental_absorb_7d(
    libcrux_sha3_generic_keccak_KeccakXofState_4f *self, Eurydice_slice input) {
  Eurydice_slice buf[1U] = {input};
  libcrux_sha3_generic_keccak_absorb_9d_7b(self, buf);
}

typedef libcrux_sha3_generic_keccak_KeccakXofState_4f
    libcrux_sha3_portable_incremental_Shake256Squeeze;

/**
 Absorb a final block.

 The `inputs` block may be empty. Everything in the `inputs` block beyond
 `RATE` bytes is ignored.
*/
/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakXofState<STATE,
PARALLEL_LANES, RATE>[TraitClause@0]#2}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final_9d
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 136
- DELIMITER= 31
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_9d_25(
    libcrux_sha3_generic_keccak_KeccakXofState_4f *self,
    Eurydice_slice inputs[1U]) {
  libcrux_sha3_generic_keccak_KeccakXofState_4f *uu____0 = self;
  /* Passing arrays by value in Rust generates a copy in C */
  Eurydice_slice copy_of_inputs[1U];
  memcpy(copy_of_inputs, inputs, (size_t)1U * sizeof(Eurydice_slice));
  size_t input_remainder_len =
      libcrux_sha3_generic_keccak_absorb_full_9d_f8(uu____0, copy_of_inputs);
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
  libcrux_sha3_portable_keccak_load_block_full_5a_d20(uu____6, uu____7);
  libcrux_sha3_generic_keccak_keccakf1600_21(&self->inner);
}

/**
 Shake256 absorb final
*/
/**
This function found in impl
{(libcrux_sha3::portable::incremental::XofAbsorb<136: usize> for
libcrux_sha3::portable::incremental::Shake256Absorb)#2}
*/
static inline libcrux_sha3_generic_keccak_KeccakXofState_4f
libcrux_sha3_portable_incremental_absorb_final_7d(
    libcrux_sha3_generic_keccak_KeccakXofState_4f self, Eurydice_slice input) {
  Eurydice_slice buf[1U] = {input};
  libcrux_sha3_generic_keccak_absorb_final_9d_25(&self, buf);
  return self;
}

/**
 An all zero block
*/
/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakXofState<STATE,
PARALLEL_LANES, RATE>[TraitClause@0]#2}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.zero_block_9d
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 136
*/
static inline void libcrux_sha3_generic_keccak_zero_block_9d_e6(
    uint8_t ret[136U]) {
  ret[0U] = 0U;
  ret[1U] = 0U;
  ret[2U] = 0U;
  ret[3U] = 0U;
  ret[4U] = 0U;
  ret[5U] = 0U;
  ret[6U] = 0U;
  ret[7U] = 0U;
  ret[8U] = 0U;
  ret[9U] = 0U;
  ret[10U] = 0U;
  ret[11U] = 0U;
  ret[12U] = 0U;
  ret[13U] = 0U;
  ret[14U] = 0U;
  ret[15U] = 0U;
  ret[16U] = 0U;
  ret[17U] = 0U;
  ret[18U] = 0U;
  ret[19U] = 0U;
  ret[20U] = 0U;
  ret[21U] = 0U;
  ret[22U] = 0U;
  ret[23U] = 0U;
  ret[24U] = 0U;
  ret[25U] = 0U;
  ret[26U] = 0U;
  ret[27U] = 0U;
  ret[28U] = 0U;
  ret[29U] = 0U;
  ret[30U] = 0U;
  ret[31U] = 0U;
  ret[32U] = 0U;
  ret[33U] = 0U;
  ret[34U] = 0U;
  ret[35U] = 0U;
  ret[36U] = 0U;
  ret[37U] = 0U;
  ret[38U] = 0U;
  ret[39U] = 0U;
  ret[40U] = 0U;
  ret[41U] = 0U;
  ret[42U] = 0U;
  ret[43U] = 0U;
  ret[44U] = 0U;
  ret[45U] = 0U;
  ret[46U] = 0U;
  ret[47U] = 0U;
  ret[48U] = 0U;
  ret[49U] = 0U;
  ret[50U] = 0U;
  ret[51U] = 0U;
  ret[52U] = 0U;
  ret[53U] = 0U;
  ret[54U] = 0U;
  ret[55U] = 0U;
  ret[56U] = 0U;
  ret[57U] = 0U;
  ret[58U] = 0U;
  ret[59U] = 0U;
  ret[60U] = 0U;
  ret[61U] = 0U;
  ret[62U] = 0U;
  ret[63U] = 0U;
  ret[64U] = 0U;
  ret[65U] = 0U;
  ret[66U] = 0U;
  ret[67U] = 0U;
  ret[68U] = 0U;
  ret[69U] = 0U;
  ret[70U] = 0U;
  ret[71U] = 0U;
  ret[72U] = 0U;
  ret[73U] = 0U;
  ret[74U] = 0U;
  ret[75U] = 0U;
  ret[76U] = 0U;
  ret[77U] = 0U;
  ret[78U] = 0U;
  ret[79U] = 0U;
  ret[80U] = 0U;
  ret[81U] = 0U;
  ret[82U] = 0U;
  ret[83U] = 0U;
  ret[84U] = 0U;
  ret[85U] = 0U;
  ret[86U] = 0U;
  ret[87U] = 0U;
  ret[88U] = 0U;
  ret[89U] = 0U;
  ret[90U] = 0U;
  ret[91U] = 0U;
  ret[92U] = 0U;
  ret[93U] = 0U;
  ret[94U] = 0U;
  ret[95U] = 0U;
  ret[96U] = 0U;
  ret[97U] = 0U;
  ret[98U] = 0U;
  ret[99U] = 0U;
  ret[100U] = 0U;
  ret[101U] = 0U;
  ret[102U] = 0U;
  ret[103U] = 0U;
  ret[104U] = 0U;
  ret[105U] = 0U;
  ret[106U] = 0U;
  ret[107U] = 0U;
  ret[108U] = 0U;
  ret[109U] = 0U;
  ret[110U] = 0U;
  ret[111U] = 0U;
  ret[112U] = 0U;
  ret[113U] = 0U;
  ret[114U] = 0U;
  ret[115U] = 0U;
  ret[116U] = 0U;
  ret[117U] = 0U;
  ret[118U] = 0U;
  ret[119U] = 0U;
  ret[120U] = 0U;
  ret[121U] = 0U;
  ret[122U] = 0U;
  ret[123U] = 0U;
  ret[124U] = 0U;
  ret[125U] = 0U;
  ret[126U] = 0U;
  ret[127U] = 0U;
  ret[128U] = 0U;
  ret[129U] = 0U;
  ret[130U] = 0U;
  ret[131U] = 0U;
  ret[132U] = 0U;
  ret[133U] = 0U;
  ret[134U] = 0U;
  ret[135U] = 0U;
}

/**
 Generate a new keccak xof state.
*/
/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakXofState<STATE,
PARALLEL_LANES, RATE>[TraitClause@0]#2}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.new_9d
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 136
*/
static inline libcrux_sha3_generic_keccak_KeccakXofState_4f
libcrux_sha3_generic_keccak_new_9d_7e(void) {
  libcrux_sha3_generic_keccak_KeccakXofState_4f lit;
  lit.inner = libcrux_sha3_generic_keccak_new_1e_f4();
  uint8_t ret[136U];
  libcrux_sha3_generic_keccak_zero_block_9d_e6(ret);
  memcpy(lit.buf[0U], ret, (size_t)136U * sizeof(uint8_t));
  lit.buf_len = (size_t)0U;
  lit.sponge = false;
  return lit;
}

/**
 Shake256 new state
*/
/**
This function found in impl
{(libcrux_sha3::portable::incremental::XofAbsorb<136: usize> for
libcrux_sha3::portable::incremental::Shake256Absorb)#2}
*/
static inline libcrux_sha3_generic_keccak_KeccakXofState_4f
libcrux_sha3_portable_incremental_new_7d(void) {
  return libcrux_sha3_generic_keccak_new_9d_7e();
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.KeccakXofState
with types uint64_t
with const generics
- $1size_t
- $168size_t
*/
typedef struct libcrux_sha3_generic_keccak_KeccakXofState_78_s {
  libcrux_sha3_generic_keccak_KeccakState_48 inner;
  uint8_t buf[1U][168U];
  size_t buf_len;
  bool sponge;
} libcrux_sha3_generic_keccak_KeccakXofState_78;

typedef libcrux_sha3_generic_keccak_KeccakXofState_78
    libcrux_sha3_portable_incremental_Shake128Absorb;

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
PARALLEL_LANES, RATE>[TraitClause@0]#2}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.fill_buffer_9d
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 168
*/
static inline size_t libcrux_sha3_generic_keccak_fill_buffer_9d_b00(
    libcrux_sha3_generic_keccak_KeccakXofState_78 *self,
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
PARALLEL_LANES, RATE>[TraitClause@0]#2}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_full_9d
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 168
*/
static inline size_t libcrux_sha3_generic_keccak_absorb_full_9d_f80(
    libcrux_sha3_generic_keccak_KeccakXofState_78 *self,
    Eurydice_slice inputs[1U]) {
  libcrux_sha3_generic_keccak_KeccakXofState_78 *uu____0 = self;
  /* Passing arrays by value in Rust generates a copy in C */
  Eurydice_slice copy_of_inputs0[1U];
  memcpy(copy_of_inputs0, inputs, (size_t)1U * sizeof(Eurydice_slice));
  size_t input_consumed =
      libcrux_sha3_generic_keccak_fill_buffer_9d_b00(uu____0, copy_of_inputs0);
  if (input_consumed > (size_t)0U) {
    Eurydice_slice borrowed[1U];
    {
      uint8_t buf[168U] = {0U};
      borrowed[0U] = core_array___Array_T__N__23__as_slice(
          (size_t)168U, buf, uint8_t, Eurydice_slice);
    }
    {
      size_t i = (size_t)0U;
      borrowed[i] =
          Eurydice_array_to_slice((size_t)168U, self->buf[i], uint8_t);
    }
    uint64_t(*uu____2)[5U] = self->inner.st;
    Eurydice_slice uu____3[1U];
    memcpy(uu____3, borrowed, (size_t)1U * sizeof(Eurydice_slice));
    libcrux_sha3_portable_keccak_load_block_5a_b80(uu____2, uu____3);
    libcrux_sha3_generic_keccak_keccakf1600_21(&self->inner);
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
    libcrux_sha3_portable_keccak_load_block_5a_b80(uu____4, ret);
    libcrux_sha3_generic_keccak_keccakf1600_21(&self->inner);
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
PARALLEL_LANES, RATE>[TraitClause@0]#2}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_9d
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_9d_7b0(
    libcrux_sha3_generic_keccak_KeccakXofState_78 *self,
    Eurydice_slice inputs[1U]) {
  libcrux_sha3_generic_keccak_KeccakXofState_78 *uu____0 = self;
  /* Passing arrays by value in Rust generates a copy in C */
  Eurydice_slice copy_of_inputs[1U];
  memcpy(copy_of_inputs, inputs, (size_t)1U * sizeof(Eurydice_slice));
  size_t input_remainder_len =
      libcrux_sha3_generic_keccak_absorb_full_9d_f80(uu____0, copy_of_inputs);
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
This function found in impl
{(libcrux_sha3::portable::incremental::XofAbsorb<168: usize> for
libcrux_sha3::portable::incremental::Shake128Absorb)}
*/
static inline void libcrux_sha3_portable_incremental_absorb_1c(
    libcrux_sha3_generic_keccak_KeccakXofState_78 *self, Eurydice_slice input) {
  Eurydice_slice buf[1U] = {input};
  libcrux_sha3_generic_keccak_absorb_9d_7b0(self, buf);
}

typedef libcrux_sha3_generic_keccak_KeccakXofState_78
    libcrux_sha3_portable_incremental_Shake128Squeeze;

/**
 Absorb a final block.

 The `inputs` block may be empty. Everything in the `inputs` block beyond
 `RATE` bytes is ignored.
*/
/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakXofState<STATE,
PARALLEL_LANES, RATE>[TraitClause@0]#2}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final_9d
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 168
- DELIMITER= 31
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_9d_250(
    libcrux_sha3_generic_keccak_KeccakXofState_78 *self,
    Eurydice_slice inputs[1U]) {
  libcrux_sha3_generic_keccak_KeccakXofState_78 *uu____0 = self;
  /* Passing arrays by value in Rust generates a copy in C */
  Eurydice_slice copy_of_inputs[1U];
  memcpy(copy_of_inputs, inputs, (size_t)1U * sizeof(Eurydice_slice));
  size_t input_remainder_len =
      libcrux_sha3_generic_keccak_absorb_full_9d_f80(uu____0, copy_of_inputs);
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
  libcrux_sha3_portable_keccak_load_block_full_5a_d2(uu____6, uu____7);
  libcrux_sha3_generic_keccak_keccakf1600_21(&self->inner);
}

/**
This function found in impl
{(libcrux_sha3::portable::incremental::XofAbsorb<168: usize> for
libcrux_sha3::portable::incremental::Shake128Absorb)}
*/
static inline libcrux_sha3_generic_keccak_KeccakXofState_78
libcrux_sha3_portable_incremental_absorb_final_1c(
    libcrux_sha3_generic_keccak_KeccakXofState_78 self, Eurydice_slice input) {
  Eurydice_slice buf[1U] = {input};
  libcrux_sha3_generic_keccak_absorb_final_9d_250(&self, buf);
  return self;
}

/**
 An all zero block
*/
/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakXofState<STATE,
PARALLEL_LANES, RATE>[TraitClause@0]#2}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.zero_block_9d
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 168
*/
static inline void libcrux_sha3_generic_keccak_zero_block_9d_e60(
    uint8_t ret[168U]) {
  ret[0U] = 0U;
  ret[1U] = 0U;
  ret[2U] = 0U;
  ret[3U] = 0U;
  ret[4U] = 0U;
  ret[5U] = 0U;
  ret[6U] = 0U;
  ret[7U] = 0U;
  ret[8U] = 0U;
  ret[9U] = 0U;
  ret[10U] = 0U;
  ret[11U] = 0U;
  ret[12U] = 0U;
  ret[13U] = 0U;
  ret[14U] = 0U;
  ret[15U] = 0U;
  ret[16U] = 0U;
  ret[17U] = 0U;
  ret[18U] = 0U;
  ret[19U] = 0U;
  ret[20U] = 0U;
  ret[21U] = 0U;
  ret[22U] = 0U;
  ret[23U] = 0U;
  ret[24U] = 0U;
  ret[25U] = 0U;
  ret[26U] = 0U;
  ret[27U] = 0U;
  ret[28U] = 0U;
  ret[29U] = 0U;
  ret[30U] = 0U;
  ret[31U] = 0U;
  ret[32U] = 0U;
  ret[33U] = 0U;
  ret[34U] = 0U;
  ret[35U] = 0U;
  ret[36U] = 0U;
  ret[37U] = 0U;
  ret[38U] = 0U;
  ret[39U] = 0U;
  ret[40U] = 0U;
  ret[41U] = 0U;
  ret[42U] = 0U;
  ret[43U] = 0U;
  ret[44U] = 0U;
  ret[45U] = 0U;
  ret[46U] = 0U;
  ret[47U] = 0U;
  ret[48U] = 0U;
  ret[49U] = 0U;
  ret[50U] = 0U;
  ret[51U] = 0U;
  ret[52U] = 0U;
  ret[53U] = 0U;
  ret[54U] = 0U;
  ret[55U] = 0U;
  ret[56U] = 0U;
  ret[57U] = 0U;
  ret[58U] = 0U;
  ret[59U] = 0U;
  ret[60U] = 0U;
  ret[61U] = 0U;
  ret[62U] = 0U;
  ret[63U] = 0U;
  ret[64U] = 0U;
  ret[65U] = 0U;
  ret[66U] = 0U;
  ret[67U] = 0U;
  ret[68U] = 0U;
  ret[69U] = 0U;
  ret[70U] = 0U;
  ret[71U] = 0U;
  ret[72U] = 0U;
  ret[73U] = 0U;
  ret[74U] = 0U;
  ret[75U] = 0U;
  ret[76U] = 0U;
  ret[77U] = 0U;
  ret[78U] = 0U;
  ret[79U] = 0U;
  ret[80U] = 0U;
  ret[81U] = 0U;
  ret[82U] = 0U;
  ret[83U] = 0U;
  ret[84U] = 0U;
  ret[85U] = 0U;
  ret[86U] = 0U;
  ret[87U] = 0U;
  ret[88U] = 0U;
  ret[89U] = 0U;
  ret[90U] = 0U;
  ret[91U] = 0U;
  ret[92U] = 0U;
  ret[93U] = 0U;
  ret[94U] = 0U;
  ret[95U] = 0U;
  ret[96U] = 0U;
  ret[97U] = 0U;
  ret[98U] = 0U;
  ret[99U] = 0U;
  ret[100U] = 0U;
  ret[101U] = 0U;
  ret[102U] = 0U;
  ret[103U] = 0U;
  ret[104U] = 0U;
  ret[105U] = 0U;
  ret[106U] = 0U;
  ret[107U] = 0U;
  ret[108U] = 0U;
  ret[109U] = 0U;
  ret[110U] = 0U;
  ret[111U] = 0U;
  ret[112U] = 0U;
  ret[113U] = 0U;
  ret[114U] = 0U;
  ret[115U] = 0U;
  ret[116U] = 0U;
  ret[117U] = 0U;
  ret[118U] = 0U;
  ret[119U] = 0U;
  ret[120U] = 0U;
  ret[121U] = 0U;
  ret[122U] = 0U;
  ret[123U] = 0U;
  ret[124U] = 0U;
  ret[125U] = 0U;
  ret[126U] = 0U;
  ret[127U] = 0U;
  ret[128U] = 0U;
  ret[129U] = 0U;
  ret[130U] = 0U;
  ret[131U] = 0U;
  ret[132U] = 0U;
  ret[133U] = 0U;
  ret[134U] = 0U;
  ret[135U] = 0U;
  ret[136U] = 0U;
  ret[137U] = 0U;
  ret[138U] = 0U;
  ret[139U] = 0U;
  ret[140U] = 0U;
  ret[141U] = 0U;
  ret[142U] = 0U;
  ret[143U] = 0U;
  ret[144U] = 0U;
  ret[145U] = 0U;
  ret[146U] = 0U;
  ret[147U] = 0U;
  ret[148U] = 0U;
  ret[149U] = 0U;
  ret[150U] = 0U;
  ret[151U] = 0U;
  ret[152U] = 0U;
  ret[153U] = 0U;
  ret[154U] = 0U;
  ret[155U] = 0U;
  ret[156U] = 0U;
  ret[157U] = 0U;
  ret[158U] = 0U;
  ret[159U] = 0U;
  ret[160U] = 0U;
  ret[161U] = 0U;
  ret[162U] = 0U;
  ret[163U] = 0U;
  ret[164U] = 0U;
  ret[165U] = 0U;
  ret[166U] = 0U;
  ret[167U] = 0U;
}

/**
 Generate a new keccak xof state.
*/
/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakXofState<STATE,
PARALLEL_LANES, RATE>[TraitClause@0]#2}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.new_9d
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 168
*/
static inline libcrux_sha3_generic_keccak_KeccakXofState_78
libcrux_sha3_generic_keccak_new_9d_7e0(void) {
  libcrux_sha3_generic_keccak_KeccakXofState_78 lit;
  lit.inner = libcrux_sha3_generic_keccak_new_1e_f4();
  uint8_t ret[168U];
  libcrux_sha3_generic_keccak_zero_block_9d_e60(ret);
  memcpy(lit.buf[0U], ret, (size_t)168U * sizeof(uint8_t));
  lit.buf_len = (size_t)0U;
  lit.sponge = false;
  return lit;
}

/**
This function found in impl
{(libcrux_sha3::portable::incremental::XofAbsorb<168: usize> for
libcrux_sha3::portable::incremental::Shake128Absorb)}
*/
static inline libcrux_sha3_generic_keccak_KeccakXofState_78
libcrux_sha3_portable_incremental_new_1c(void) {
  return libcrux_sha3_generic_keccak_new_9d_7e0();
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
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_5a_1c(
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
PARALLEL_LANES, RATE>[TraitClause@0]#2}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_9d
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_9d_96(
    libcrux_sha3_generic_keccak_KeccakXofState_4f *self,
    Eurydice_slice out[1U]) {
  if (self->sponge) {
    libcrux_sha3_generic_keccak_keccakf1600_21(&self->inner);
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
  libcrux_sha3_portable_keccak_store_5a_1c(self->inner.st, out00);
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
      Eurydice_slice_uint8_t_1size_t__x2 uu____1 =
          libcrux_sha3_portable_keccak_split_at_mut_n_5a(out_rest,
                                                         (size_t)136U);
      Eurydice_slice out0[1U];
      memcpy(out0, uu____1.fst, (size_t)1U * sizeof(Eurydice_slice));
      Eurydice_slice tmp[1U];
      memcpy(tmp, uu____1.snd, (size_t)1U * sizeof(Eurydice_slice));
      libcrux_sha3_generic_keccak_keccakf1600_21(&self->inner);
      libcrux_sha3_portable_keccak_store_5a_1c(self->inner.st, out0);
      memcpy(out_rest, tmp, (size_t)1U * sizeof(Eurydice_slice));
    }
  }
  if (last < out_len) {
    libcrux_sha3_generic_keccak_keccakf1600_21(&self->inner);
    libcrux_sha3_portable_keccak_store_5a_1c(self->inner.st, out_rest);
  }
  self->sponge = true;
}

/**
 Shake256 squeeze
*/
/**
This function found in impl
{(libcrux_sha3::portable::incremental::XofSqueeze<136: usize> for
libcrux_sha3::portable::incremental::Shake256Squeeze)#3}
*/
static inline void libcrux_sha3_portable_incremental_squeeze_8a(
    libcrux_sha3_generic_keccak_KeccakXofState_4f *self, Eurydice_slice out) {
  Eurydice_slice buf[1U] = {out};
  libcrux_sha3_generic_keccak_squeeze_9d_96(self, buf);
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
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_5a_1c0(
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
PARALLEL_LANES, RATE>[TraitClause@0]#2}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_9d
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_9d_960(
    libcrux_sha3_generic_keccak_KeccakXofState_78 *self,
    Eurydice_slice out[1U]) {
  if (self->sponge) {
    libcrux_sha3_generic_keccak_keccakf1600_21(&self->inner);
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
  libcrux_sha3_portable_keccak_store_5a_1c0(self->inner.st, out00);
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
      Eurydice_slice_uint8_t_1size_t__x2 uu____1 =
          libcrux_sha3_portable_keccak_split_at_mut_n_5a(out_rest,
                                                         (size_t)168U);
      Eurydice_slice out0[1U];
      memcpy(out0, uu____1.fst, (size_t)1U * sizeof(Eurydice_slice));
      Eurydice_slice tmp[1U];
      memcpy(tmp, uu____1.snd, (size_t)1U * sizeof(Eurydice_slice));
      libcrux_sha3_generic_keccak_keccakf1600_21(&self->inner);
      libcrux_sha3_portable_keccak_store_5a_1c0(self->inner.st, out0);
      memcpy(out_rest, tmp, (size_t)1U * sizeof(Eurydice_slice));
    }
  }
  if (last < out_len) {
    libcrux_sha3_generic_keccak_keccakf1600_21(&self->inner);
    libcrux_sha3_portable_keccak_store_5a_1c0(self->inner.st, out_rest);
  }
  self->sponge = true;
}

/**
 Shake128 squeeze
*/
/**
This function found in impl
{(libcrux_sha3::portable::incremental::XofSqueeze<168: usize> for
libcrux_sha3::portable::incremental::Shake128Squeeze)#1}
*/
static inline void libcrux_sha3_portable_incremental_squeeze_10(
    libcrux_sha3_generic_keccak_KeccakXofState_78 *self, Eurydice_slice out) {
  Eurydice_slice buf[1U] = {out};
  libcrux_sha3_generic_keccak_squeeze_9d_960(self, buf);
}

/**
This function found in impl {(core::clone::Clone for
libcrux_sha3::portable::KeccakState)}
*/
static inline libcrux_sha3_generic_keccak_KeccakState_48
libcrux_sha3_portable_clone_3d(
    libcrux_sha3_generic_keccak_KeccakState_48 *self) {
  return self[0U];
}

/**
This function found in impl {(core::convert::From<libcrux_sha3::Algorithm> for
u32)#1}
*/
static inline uint32_t libcrux_sha3_from_eb(libcrux_sha3_Algorithm v) {
  uint32_t uu____0;
  switch (v) {
    case libcrux_sha3_Sha224: {
      uu____0 = 1U;
      break;
    }
    case libcrux_sha3_Sha256: {
      uu____0 = 2U;
      break;
    }
    case libcrux_sha3_Sha384: {
      uu____0 = 3U;
      break;
    }
    case libcrux_sha3_Sha512: {
      uu____0 = 4U;
      break;
    }
    default: {
      KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__,
                        __LINE__);
      KRML_HOST_EXIT(253U);
    }
  }
  return uu____0;
}

/**
This function found in impl {(core::convert::From<u32> for
libcrux_sha3::Algorithm)}
*/
static inline libcrux_sha3_Algorithm libcrux_sha3_from_2d(uint32_t v) {
  libcrux_sha3_Algorithm uu____0;
  switch (v) {
    case 1U: {
      uu____0 = libcrux_sha3_Sha224;
      break;
    }
    case 2U: {
      uu____0 = libcrux_sha3_Sha256;
      break;
    }
    case 3U: {
      uu____0 = libcrux_sha3_Sha384;
      break;
    }
    case 4U: {
      uu____0 = libcrux_sha3_Sha512;
      break;
    }
    default: {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                        "panic!");
      KRML_HOST_EXIT(255U);
    }
  }
  return uu____0;
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
