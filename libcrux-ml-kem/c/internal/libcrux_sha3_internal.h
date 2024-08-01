/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 45b95e0f63cb830202c0b3ca00a341a3451a02ba
 * Eurydice: 0eb8a17354fd62586cb9f7515af23f4488c2267e
 * Karamel: ab466d75991f78bb7925bf97c8ee9874f67074f5
 * F*: 58c915a86a2c07c8eca8d9deafd76cb7a91f0eb7
 * Libcrux: b2314d1e996ac7a4fbda72210b4aabbd915d282a
 */

#ifndef __internal_libcrux_sha3_internal_H
#define __internal_libcrux_sha3_internal_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "../libcrux_sha3_internal.h"
#include "eurydice_glue.h"

typedef libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t
    libcrux_sha3_portable_KeccakState;

static KRML_MUSTINLINE
    libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t
    libcrux_sha3_portable_incremental_shake128_init(void) {
  return libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakState_T__N__TraitClause_0__1__new__uint64_t_1size_t();
}

static KRML_MUSTINLINE void
libcrux_sha3_portable_incremental_shake128_absorb_final(
    libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t *s,
    Eurydice_slice data0) {
  Eurydice_slice buf[1U] = {data0};
  libcrux_sha3_generic_keccak_absorb_final__uint64_t_1size_t_168size_t_31uint8_t(
      s, buf);
}

static KRML_MUSTINLINE void
libcrux_sha3_portable_incremental_shake128_squeeze_next_block(
    libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t *s,
    Eurydice_slice out0) {
  Eurydice_slice buf[1U] = {out0};
  libcrux_sha3_generic_keccak_squeeze_next_block__uint64_t_1size_t_168size_t(
      s, buf);
}

static KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_squeeze_first_three_blocks__uint64_t_1size_t_168size_t(
    libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t *s,
    Eurydice_slice out[1U]) {
  K___Eurydice_slice_uint8_t_1size_t__Eurydice_slice_uint8_t_1size_t_ uu____0 =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___split_at_mut_n(
          out, (size_t)168U);
  Eurydice_slice o0[1U];
  memcpy(o0, uu____0.fst, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice o10[1U];
  memcpy(o10, uu____0.snd, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_squeeze_first_block__uint64_t_1size_t_168size_t(
      s, o0);
  K___Eurydice_slice_uint8_t_1size_t__Eurydice_slice_uint8_t_1size_t_ uu____1 =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___split_at_mut_n(
          o10, (size_t)168U);
  Eurydice_slice o1[1U];
  memcpy(o1, uu____1.fst, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice o2[1U];
  memcpy(o2, uu____1.snd, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_squeeze_next_block__uint64_t_1size_t_168size_t(
      s, o1);
  libcrux_sha3_generic_keccak_squeeze_next_block__uint64_t_1size_t_168size_t(
      s, o2);
}

static KRML_MUSTINLINE void
libcrux_sha3_portable_incremental_shake128_squeeze_first_three_blocks(
    libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t *s,
    Eurydice_slice out0) {
  Eurydice_slice buf[1U] = {out0};
  libcrux_sha3_generic_keccak_squeeze_first_three_blocks__uint64_t_1size_t_168size_t(
      s, buf);
}

#define libcrux_sha3_Sha224 0
#define libcrux_sha3_Sha256 1
#define libcrux_sha3_Sha384 2
#define libcrux_sha3_Sha512 3

typedef uint8_t libcrux_sha3_Algorithm;

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

static KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_squeeze_first_five_blocks__uint64_t_1size_t_168size_t(
    libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t *s,
    Eurydice_slice out[1U]) {
  K___Eurydice_slice_uint8_t_1size_t__Eurydice_slice_uint8_t_1size_t_ uu____0 =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___split_at_mut_n(
          out, (size_t)168U);
  Eurydice_slice o0[1U];
  memcpy(o0, uu____0.fst, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice o10[1U];
  memcpy(o10, uu____0.snd, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_squeeze_first_block__uint64_t_1size_t_168size_t(
      s, o0);
  K___Eurydice_slice_uint8_t_1size_t__Eurydice_slice_uint8_t_1size_t_ uu____1 =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___split_at_mut_n(
          o10, (size_t)168U);
  Eurydice_slice o1[1U];
  memcpy(o1, uu____1.fst, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice o20[1U];
  memcpy(o20, uu____1.snd, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_squeeze_next_block__uint64_t_1size_t_168size_t(
      s, o1);
  K___Eurydice_slice_uint8_t_1size_t__Eurydice_slice_uint8_t_1size_t_ uu____2 =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___split_at_mut_n(
          o20, (size_t)168U);
  Eurydice_slice o2[1U];
  memcpy(o2, uu____2.fst, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice o30[1U];
  memcpy(o30, uu____2.snd, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_squeeze_next_block__uint64_t_1size_t_168size_t(
      s, o2);
  K___Eurydice_slice_uint8_t_1size_t__Eurydice_slice_uint8_t_1size_t_ uu____3 =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___split_at_mut_n(
          o30, (size_t)168U);
  Eurydice_slice o3[1U];
  memcpy(o3, uu____3.fst, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice o4[1U];
  memcpy(o4, uu____3.snd, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_squeeze_next_block__uint64_t_1size_t_168size_t(
      s, o3);
  libcrux_sha3_generic_keccak_squeeze_next_block__uint64_t_1size_t_168size_t(
      s, o4);
}

static KRML_MUSTINLINE void
libcrux_sha3_portable_incremental_shake128_squeeze_first_five_blocks(
    libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t *s,
    Eurydice_slice out0) {
  Eurydice_slice buf[1U] = {out0};
  libcrux_sha3_generic_keccak_squeeze_first_five_blocks__uint64_t_1size_t_168size_t(
      s, buf);
}

static KRML_MUSTINLINE void
libcrux_sha3_portable_incremental_shake256_absorb_final(
    libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t *s,
    Eurydice_slice data) {
  Eurydice_slice buf[1U] = {data};
  libcrux_sha3_generic_keccak_absorb_final__uint64_t_1size_t_136size_t_31uint8_t(
      s, buf);
}

static KRML_MUSTINLINE
    libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t
    libcrux_sha3_portable_incremental_shake256_init(void) {
  return libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakState_T__N__TraitClause_0__1__new__uint64_t_1size_t();
}

static KRML_MUSTINLINE void
libcrux_sha3_portable_incremental_shake256_squeeze_first_block(
    libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t *s,
    Eurydice_slice out) {
  Eurydice_slice buf[1U] = {out};
  libcrux_sha3_generic_keccak_squeeze_first_block__uint64_t_1size_t_136size_t(
      s, buf);
}

static KRML_MUSTINLINE void
libcrux_sha3_portable_incremental_shake256_squeeze_next_block(
    libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t *s,
    Eurydice_slice out) {
  Eurydice_slice buf[1U] = {out};
  libcrux_sha3_generic_keccak_squeeze_next_block__uint64_t_1size_t_136size_t(
      s, buf);
}

typedef struct
    libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__136size_t_s {
  libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t inner;
  uint8_t buf[1U][136U];
  size_t buf_len;
  bool sponge;
} libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__136size_t;

typedef libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__136size_t
    libcrux_sha3_portable_incremental_Shake256Absorb;

static inline size_t
libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__fill_buffer__uint64_t_1size_t_136size_t(
    libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__136size_t
        *self,
    Eurydice_slice inputs[1U]) {
  size_t input_len = core_slice___Slice_T___len(inputs[0U], uint8_t, size_t);
  size_t consumed = (size_t)0U;
  if (self->buf_len > (size_t)0U) {
    if (self->buf_len + input_len >= (size_t)136U) {
      consumed = (size_t)136U - self->buf_len;
      {
        size_t i = (size_t)0U;
        Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
            (size_t)136U, self->buf[i], self->buf_len, uint8_t, size_t,
            Eurydice_slice);
        core_slice___Slice_T___copy_from_slice(
            uu____0,
            Eurydice_slice_subslice_to(inputs[i], consumed, uint8_t, size_t,
                                       Eurydice_slice),
            uint8_t, void *);
      }
      self->buf_len = self->buf_len + consumed;
    }
  }
  return consumed;
}

static inline Eurydice_slice
libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__absorb_full_closure__uint64_t_1size_t_136size_t(
    uint8_t (**state)[136U], size_t i) {
  return Eurydice_array_to_slice((size_t)136U, state[0U][i], uint8_t,
                                 Eurydice_slice);
}

static inline size_t
libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__absorb_full__uint64_t_1size_t_136size_t(
    libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__136size_t
        *self,
    Eurydice_slice inputs[1U]) {
  libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__136size_t
      *uu____0 = self;
  Eurydice_slice uu____1[1U];
  memcpy(uu____1, inputs, (size_t)1U * sizeof(Eurydice_slice));
  size_t input_consumed =
      libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__fill_buffer__uint64_t_1size_t_136size_t(
          uu____0, uu____1);
  if (input_consumed > (size_t)0U) {
    Eurydice_slice borrowed[1U];
    {
      borrowed[0U] = Eurydice_array_to_slice((size_t)136U, self->buf[0U],
                                             uint8_t, Eurydice_slice);
    }
    uint64_t(*uu____2)[5U] = self->inner.st;
    Eurydice_slice uu____3[1U];
    memcpy(uu____3, borrowed, (size_t)1U * sizeof(Eurydice_slice));
    libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___load_block___136size_t(
        uu____2, uu____3);
    libcrux_sha3_generic_keccak_keccakf1600__uint64_t_1size_t(&self->inner);
    self->buf_len = (size_t)0U;
  }
  size_t input_to_consume =
      core_slice___Slice_T___len(inputs[0U], uint8_t, size_t) - input_consumed;
  size_t num_blocks = input_to_consume / (size_t)136U;
  size_t remainder = input_to_consume % (size_t)136U;
  for (size_t i = (size_t)0U; i < num_blocks; i++) {
    size_t i0 = i;
    uint64_t(*uu____4)[5U] = self->inner.st;
    Eurydice_slice uu____5[1U];
    memcpy(uu____5, inputs, (size_t)1U * sizeof(Eurydice_slice));
    Eurydice_slice ret[1U];
    libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___slice_n(
        uu____5, input_consumed + i0 * (size_t)136U, (size_t)136U, ret);
    libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___load_block___136size_t(
        uu____4, ret);
    libcrux_sha3_generic_keccak_keccakf1600__uint64_t_1size_t(&self->inner);
  }
  return remainder;
}

static KRML_MUSTINLINE void
libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__absorb__uint64_t_1size_t_136size_t(
    libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__136size_t
        *self,
    Eurydice_slice inputs[1U]) {
  libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__136size_t
      *uu____0 = self;
  Eurydice_slice uu____1[1U];
  memcpy(uu____1, inputs, (size_t)1U * sizeof(Eurydice_slice));
  size_t input_remainder_len =
      libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__absorb_full__uint64_t_1size_t_136size_t(
          uu____0, uu____1);
  if (input_remainder_len > (size_t)0U) {
    size_t input_len = core_slice___Slice_T___len(inputs[0U], uint8_t, size_t);
    {
      size_t i = (size_t)0U;
      Eurydice_slice uu____2 = Eurydice_array_to_subslice(
          (size_t)136U, self->buf[i],
          (CLITERAL(core_ops_range_Range__size_t){
              .start = self->buf_len,
              .end = self->buf_len + input_remainder_len}),
          uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
      core_slice___Slice_T___copy_from_slice(
          uu____2,
          Eurydice_slice_subslice_from(inputs[i],
                                       input_len - input_remainder_len, uint8_t,
                                       size_t, Eurydice_slice),
          uint8_t, void *);
    }
    self->buf_len = self->buf_len + input_remainder_len;
  }
}

static inline void
libcrux_sha3_portable_incremental___libcrux_sha3__portable__incremental__XofAbsorb_136__usize__for_libcrux_sha3__portable__incremental__Shake256Absorb__2__absorb(
    libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__136size_t
        *self,
    Eurydice_slice input) {
  Eurydice_slice buf[1U] = {input};
  libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__absorb__uint64_t_1size_t_136size_t(
      self, buf);
}

typedef libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__136size_t
    libcrux_sha3_portable_incremental_Shake256Squeeze;

static KRML_MUSTINLINE void
libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__absorb_final__uint64_t_1size_t_136size_t_31uint8_t(
    libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__136size_t
        *self,
    Eurydice_slice inputs[1U]) {
  libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__136size_t
      *uu____0 = self;
  Eurydice_slice uu____1[1U];
  memcpy(uu____1, inputs, (size_t)1U * sizeof(Eurydice_slice));
  size_t input_remainder_len =
      libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__absorb_full__uint64_t_1size_t_136size_t(
          uu____0, uu____1);
  size_t input_len = core_slice___Slice_T___len(inputs[0U], uint8_t, size_t);
  uint8_t blocks[1U][200U] = {{0U}};
  {
    size_t i = (size_t)0U;
    if (self->buf_len > (size_t)0U) {
      Eurydice_slice uu____2 = Eurydice_array_to_subslice(
          (size_t)200U, blocks[i],
          (CLITERAL(core_ops_range_Range__size_t){.start = (size_t)0U,
                                                  .end = self->buf_len}),
          uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
      core_slice___Slice_T___copy_from_slice(
          uu____2,
          Eurydice_array_to_subslice(
              (size_t)136U, self->buf[i],
              (CLITERAL(core_ops_range_Range__size_t){.start = (size_t)0U,
                                                      .end = self->buf_len}),
              uint8_t, core_ops_range_Range__size_t, Eurydice_slice),
          uint8_t, void *);
    }
    if (input_remainder_len > (size_t)0U) {
      Eurydice_slice uu____3 = Eurydice_array_to_subslice(
          (size_t)200U, blocks[i],
          (CLITERAL(core_ops_range_Range__size_t){
              .start = self->buf_len,
              .end = self->buf_len + input_remainder_len}),
          uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
      core_slice___Slice_T___copy_from_slice(
          uu____3,
          Eurydice_slice_subslice_from(inputs[i],
                                       input_len - input_remainder_len, uint8_t,
                                       size_t, Eurydice_slice),
          uint8_t, void *);
    }
    blocks[i][self->buf_len + input_remainder_len] = 31U;
    size_t uu____4 = i;
    size_t uu____5 = (size_t)136U - (size_t)1U;
    blocks[uu____4][uu____5] = (uint32_t)blocks[uu____4][uu____5] | 128U;
  }
  uint64_t(*uu____6)[5U] = self->inner.st;
  uint8_t uu____7[1U][200U];
  memcpy(uu____7, blocks, (size_t)1U * sizeof(uint8_t[200U]));
  libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___load_block_full___136size_t(
      uu____6, uu____7);
  libcrux_sha3_generic_keccak_keccakf1600__uint64_t_1size_t(&self->inner);
}

static inline libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__136size_t
libcrux_sha3_portable_incremental___libcrux_sha3__portable__incremental__XofAbsorb_136__usize__for_libcrux_sha3__portable__incremental__Shake256Absorb__2__absorb_final(
    libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__136size_t
        self,
    Eurydice_slice input) {
  Eurydice_slice buf[1U] = {input};
  libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__absorb_final__uint64_t_1size_t_136size_t_31uint8_t(
      &self, buf);
  return self;
}

static inline void
libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__zero_block__uint64_t_1size_t_136size_t(
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

static inline libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__136size_t
libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__new__uint64_t_1size_t_136size_t(
    void) {
  libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__136size_t lit;
  lit.inner =
      libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakState_T__N__TraitClause_0__1__new__uint64_t_1size_t();
  uint8_t ret[136U];
  libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__zero_block__uint64_t_1size_t_136size_t(
      ret);
  memcpy(lit.buf[0U], ret, (size_t)136U * sizeof(uint8_t));
  lit.buf_len = (size_t)0U;
  lit.sponge = false;
  return lit;
}

static inline libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__136size_t
libcrux_sha3_portable_incremental___libcrux_sha3__portable__incremental__XofAbsorb_136__usize__for_libcrux_sha3__portable__incremental__Shake256Absorb__2__new(
    void) {
  return libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__new__uint64_t_1size_t_136size_t();
}

typedef struct
    libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__168size_t_s {
  libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t inner;
  uint8_t buf[1U][168U];
  size_t buf_len;
  bool sponge;
} libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__168size_t;

typedef libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__168size_t
    libcrux_sha3_portable_incremental_Shake128Absorb;

static inline size_t
libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__fill_buffer__uint64_t_1size_t_168size_t(
    libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__168size_t
        *self,
    Eurydice_slice inputs[1U]) {
  size_t input_len = core_slice___Slice_T___len(inputs[0U], uint8_t, size_t);
  size_t consumed = (size_t)0U;
  if (self->buf_len > (size_t)0U) {
    if (self->buf_len + input_len >= (size_t)168U) {
      consumed = (size_t)168U - self->buf_len;
      {
        size_t i = (size_t)0U;
        Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
            (size_t)168U, self->buf[i], self->buf_len, uint8_t, size_t,
            Eurydice_slice);
        core_slice___Slice_T___copy_from_slice(
            uu____0,
            Eurydice_slice_subslice_to(inputs[i], consumed, uint8_t, size_t,
                                       Eurydice_slice),
            uint8_t, void *);
      }
      self->buf_len = self->buf_len + consumed;
    }
  }
  return consumed;
}

static inline Eurydice_slice
libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__absorb_full_closure__uint64_t_1size_t_168size_t(
    uint8_t (**state)[168U], size_t i) {
  return Eurydice_array_to_slice((size_t)168U, state[0U][i], uint8_t,
                                 Eurydice_slice);
}

static inline size_t
libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__absorb_full__uint64_t_1size_t_168size_t(
    libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__168size_t
        *self,
    Eurydice_slice inputs[1U]) {
  libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__168size_t
      *uu____0 = self;
  Eurydice_slice uu____1[1U];
  memcpy(uu____1, inputs, (size_t)1U * sizeof(Eurydice_slice));
  size_t input_consumed =
      libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__fill_buffer__uint64_t_1size_t_168size_t(
          uu____0, uu____1);
  if (input_consumed > (size_t)0U) {
    Eurydice_slice borrowed[1U];
    {
      borrowed[0U] = Eurydice_array_to_slice((size_t)168U, self->buf[0U],
                                             uint8_t, Eurydice_slice);
    }
    uint64_t(*uu____2)[5U] = self->inner.st;
    Eurydice_slice uu____3[1U];
    memcpy(uu____3, borrowed, (size_t)1U * sizeof(Eurydice_slice));
    libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___load_block___168size_t(
        uu____2, uu____3);
    libcrux_sha3_generic_keccak_keccakf1600__uint64_t_1size_t(&self->inner);
    self->buf_len = (size_t)0U;
  }
  size_t input_to_consume =
      core_slice___Slice_T___len(inputs[0U], uint8_t, size_t) - input_consumed;
  size_t num_blocks = input_to_consume / (size_t)168U;
  size_t remainder = input_to_consume % (size_t)168U;
  for (size_t i = (size_t)0U; i < num_blocks; i++) {
    size_t i0 = i;
    uint64_t(*uu____4)[5U] = self->inner.st;
    Eurydice_slice uu____5[1U];
    memcpy(uu____5, inputs, (size_t)1U * sizeof(Eurydice_slice));
    Eurydice_slice ret[1U];
    libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___slice_n(
        uu____5, input_consumed + i0 * (size_t)168U, (size_t)168U, ret);
    libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___load_block___168size_t(
        uu____4, ret);
    libcrux_sha3_generic_keccak_keccakf1600__uint64_t_1size_t(&self->inner);
  }
  return remainder;
}

static KRML_MUSTINLINE void
libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__absorb__uint64_t_1size_t_168size_t(
    libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__168size_t
        *self,
    Eurydice_slice inputs[1U]) {
  libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__168size_t
      *uu____0 = self;
  Eurydice_slice uu____1[1U];
  memcpy(uu____1, inputs, (size_t)1U * sizeof(Eurydice_slice));
  size_t input_remainder_len =
      libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__absorb_full__uint64_t_1size_t_168size_t(
          uu____0, uu____1);
  if (input_remainder_len > (size_t)0U) {
    size_t input_len = core_slice___Slice_T___len(inputs[0U], uint8_t, size_t);
    {
      size_t i = (size_t)0U;
      Eurydice_slice uu____2 = Eurydice_array_to_subslice(
          (size_t)168U, self->buf[i],
          (CLITERAL(core_ops_range_Range__size_t){
              .start = self->buf_len,
              .end = self->buf_len + input_remainder_len}),
          uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
      core_slice___Slice_T___copy_from_slice(
          uu____2,
          Eurydice_slice_subslice_from(inputs[i],
                                       input_len - input_remainder_len, uint8_t,
                                       size_t, Eurydice_slice),
          uint8_t, void *);
    }
    self->buf_len = self->buf_len + input_remainder_len;
  }
}

static inline void
libcrux_sha3_portable_incremental___libcrux_sha3__portable__incremental__XofAbsorb_168__usize__for_libcrux_sha3__portable__incremental__Shake128Absorb___absorb(
    libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__168size_t
        *self,
    Eurydice_slice input) {
  Eurydice_slice buf[1U] = {input};
  libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__absorb__uint64_t_1size_t_168size_t(
      self, buf);
}

typedef libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__168size_t
    libcrux_sha3_portable_incremental_Shake128Squeeze;

static KRML_MUSTINLINE void
libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__absorb_final__uint64_t_1size_t_168size_t_31uint8_t(
    libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__168size_t
        *self,
    Eurydice_slice inputs[1U]) {
  libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__168size_t
      *uu____0 = self;
  Eurydice_slice uu____1[1U];
  memcpy(uu____1, inputs, (size_t)1U * sizeof(Eurydice_slice));
  size_t input_remainder_len =
      libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__absorb_full__uint64_t_1size_t_168size_t(
          uu____0, uu____1);
  size_t input_len = core_slice___Slice_T___len(inputs[0U], uint8_t, size_t);
  uint8_t blocks[1U][200U] = {{0U}};
  {
    size_t i = (size_t)0U;
    if (self->buf_len > (size_t)0U) {
      Eurydice_slice uu____2 = Eurydice_array_to_subslice(
          (size_t)200U, blocks[i],
          (CLITERAL(core_ops_range_Range__size_t){.start = (size_t)0U,
                                                  .end = self->buf_len}),
          uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
      core_slice___Slice_T___copy_from_slice(
          uu____2,
          Eurydice_array_to_subslice(
              (size_t)168U, self->buf[i],
              (CLITERAL(core_ops_range_Range__size_t){.start = (size_t)0U,
                                                      .end = self->buf_len}),
              uint8_t, core_ops_range_Range__size_t, Eurydice_slice),
          uint8_t, void *);
    }
    if (input_remainder_len > (size_t)0U) {
      Eurydice_slice uu____3 = Eurydice_array_to_subslice(
          (size_t)200U, blocks[i],
          (CLITERAL(core_ops_range_Range__size_t){
              .start = self->buf_len,
              .end = self->buf_len + input_remainder_len}),
          uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
      core_slice___Slice_T___copy_from_slice(
          uu____3,
          Eurydice_slice_subslice_from(inputs[i],
                                       input_len - input_remainder_len, uint8_t,
                                       size_t, Eurydice_slice),
          uint8_t, void *);
    }
    blocks[i][self->buf_len + input_remainder_len] = 31U;
    size_t uu____4 = i;
    size_t uu____5 = (size_t)168U - (size_t)1U;
    blocks[uu____4][uu____5] = (uint32_t)blocks[uu____4][uu____5] | 128U;
  }
  uint64_t(*uu____6)[5U] = self->inner.st;
  uint8_t uu____7[1U][200U];
  memcpy(uu____7, blocks, (size_t)1U * sizeof(uint8_t[200U]));
  libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___load_block_full___168size_t(
      uu____6, uu____7);
  libcrux_sha3_generic_keccak_keccakf1600__uint64_t_1size_t(&self->inner);
}

static inline libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__168size_t
libcrux_sha3_portable_incremental___libcrux_sha3__portable__incremental__XofAbsorb_168__usize__for_libcrux_sha3__portable__incremental__Shake128Absorb___absorb_final(
    libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__168size_t
        self,
    Eurydice_slice input) {
  Eurydice_slice buf[1U] = {input};
  libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__absorb_final__uint64_t_1size_t_168size_t_31uint8_t(
      &self, buf);
  return self;
}

static inline void
libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__zero_block__uint64_t_1size_t_168size_t(
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

static inline libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__168size_t
libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__new__uint64_t_1size_t_168size_t(
    void) {
  libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__168size_t lit;
  lit.inner =
      libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakState_T__N__TraitClause_0__1__new__uint64_t_1size_t();
  uint8_t ret[168U];
  libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__zero_block__uint64_t_1size_t_168size_t(
      ret);
  memcpy(lit.buf[0U], ret, (size_t)168U * sizeof(uint8_t));
  lit.buf_len = (size_t)0U;
  lit.sponge = false;
  return lit;
}

static inline libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__168size_t
libcrux_sha3_portable_incremental___libcrux_sha3__portable__incremental__XofAbsorb_168__usize__for_libcrux_sha3__portable__incremental__Shake128Absorb___new(
    void) {
  return libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__new__uint64_t_1size_t_168size_t();
}

static KRML_MUSTINLINE void
libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___store___136size_t(
    uint64_t (*state)[5U], Eurydice_slice out[1U]) {
  size_t num_full_blocks =
      core_slice___Slice_T___len(out[0U], uint8_t, size_t) / (size_t)8U;
  size_t last_block_len =
      core_slice___Slice_T___len(out[0U], uint8_t, size_t) % (size_t)8U;
  for (size_t i = (size_t)0U; i < num_full_blocks; i++) {
    size_t i0 = i;
    Eurydice_slice uu____0 = Eurydice_slice_subslice(
        out[0U],
        (CLITERAL(core_ops_range_Range__size_t){
            .start = i0 * (size_t)8U, .end = i0 * (size_t)8U + (size_t)8U}),
        uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
    uint8_t ret[8U];
    core_num__u64_9__to_le_bytes(state[i0 / (size_t)5U][i0 % (size_t)5U], ret);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_slice((size_t)8U, ret, uint8_t, Eurydice_slice),
        uint8_t, void *);
  }
  if (last_block_len != (size_t)0U) {
    Eurydice_slice uu____1 = Eurydice_slice_subslice(
        out[0U],
        (CLITERAL(core_ops_range_Range__size_t){
            .start = num_full_blocks * (size_t)8U,
            .end = num_full_blocks * (size_t)8U + last_block_len}),
        uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
    uint8_t ret[8U];
    core_num__u64_9__to_le_bytes(
        state[num_full_blocks / (size_t)5U][num_full_blocks % (size_t)5U], ret);
    core_slice___Slice_T___copy_from_slice(
        uu____1,
        Eurydice_array_to_subslice(
            (size_t)8U, ret,
            (CLITERAL(core_ops_range_Range__size_t){.start = (size_t)0U,
                                                    .end = last_block_len}),
            uint8_t, core_ops_range_Range__size_t, Eurydice_slice),
        uint8_t, void *);
  }
}

static KRML_MUSTINLINE void
libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__squeeze__uint64_t_1size_t_136size_t(
    libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__136size_t
        *self,
    Eurydice_slice out[1U]) {
  if (self->sponge) {
    libcrux_sha3_generic_keccak_keccakf1600__uint64_t_1size_t(&self->inner);
  }
  size_t out_len = core_slice___Slice_T___len(out[0U], uint8_t, size_t);
  size_t blocks = out_len / (size_t)136U;
  size_t last = out_len - out_len % (size_t)136U;
  size_t mid;
  if ((size_t)136U >= out_len) {
    mid = out_len;
  } else {
    mid = (size_t)136U;
  }
  K___Eurydice_slice_uint8_t_1size_t__Eurydice_slice_uint8_t_1size_t_ uu____0 =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___split_at_mut_n(
          out, mid);
  Eurydice_slice out00[1U];
  memcpy(out00, uu____0.fst, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice out_rest[1U];
  memcpy(out_rest, uu____0.snd, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___store___136size_t(
      self->inner.st, out00);
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
      K___Eurydice_slice_uint8_t_1size_t__Eurydice_slice_uint8_t_1size_t_ uu____1 =
          libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___split_at_mut_n(
              out_rest, (size_t)136U);
      Eurydice_slice out0[1U];
      memcpy(out0, uu____1.fst, (size_t)1U * sizeof(Eurydice_slice));
      Eurydice_slice tmp[1U];
      memcpy(tmp, uu____1.snd, (size_t)1U * sizeof(Eurydice_slice));
      libcrux_sha3_generic_keccak_keccakf1600__uint64_t_1size_t(&self->inner);
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___store___136size_t(
          self->inner.st, out0);
      memcpy(out_rest, tmp, (size_t)1U * sizeof(Eurydice_slice));
    }
  }
  if (last < out_len) {
    libcrux_sha3_generic_keccak_keccakf1600__uint64_t_1size_t(&self->inner);
    libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___store___136size_t(
        self->inner.st, out_rest);
  }
  self->sponge = true;
}

static inline void
libcrux_sha3_portable_incremental___libcrux_sha3__portable__incremental__XofSqueeze_136__usize__for_libcrux_sha3__portable__incremental__Shake256Squeeze__3__squeeze(
    libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__136size_t
        *self,
    Eurydice_slice out) {
  Eurydice_slice buf[1U] = {out};
  libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__squeeze__uint64_t_1size_t_136size_t(
      self, buf);
}

static KRML_MUSTINLINE void
libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___store___168size_t(
    uint64_t (*state)[5U], Eurydice_slice out[1U]) {
  size_t num_full_blocks =
      core_slice___Slice_T___len(out[0U], uint8_t, size_t) / (size_t)8U;
  size_t last_block_len =
      core_slice___Slice_T___len(out[0U], uint8_t, size_t) % (size_t)8U;
  for (size_t i = (size_t)0U; i < num_full_blocks; i++) {
    size_t i0 = i;
    Eurydice_slice uu____0 = Eurydice_slice_subslice(
        out[0U],
        (CLITERAL(core_ops_range_Range__size_t){
            .start = i0 * (size_t)8U, .end = i0 * (size_t)8U + (size_t)8U}),
        uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
    uint8_t ret[8U];
    core_num__u64_9__to_le_bytes(state[i0 / (size_t)5U][i0 % (size_t)5U], ret);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_slice((size_t)8U, ret, uint8_t, Eurydice_slice),
        uint8_t, void *);
  }
  if (last_block_len != (size_t)0U) {
    Eurydice_slice uu____1 = Eurydice_slice_subslice(
        out[0U],
        (CLITERAL(core_ops_range_Range__size_t){
            .start = num_full_blocks * (size_t)8U,
            .end = num_full_blocks * (size_t)8U + last_block_len}),
        uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
    uint8_t ret[8U];
    core_num__u64_9__to_le_bytes(
        state[num_full_blocks / (size_t)5U][num_full_blocks % (size_t)5U], ret);
    core_slice___Slice_T___copy_from_slice(
        uu____1,
        Eurydice_array_to_subslice(
            (size_t)8U, ret,
            (CLITERAL(core_ops_range_Range__size_t){.start = (size_t)0U,
                                                    .end = last_block_len}),
            uint8_t, core_ops_range_Range__size_t, Eurydice_slice),
        uint8_t, void *);
  }
}

static KRML_MUSTINLINE void
libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__squeeze__uint64_t_1size_t_168size_t(
    libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__168size_t
        *self,
    Eurydice_slice out[1U]) {
  if (self->sponge) {
    libcrux_sha3_generic_keccak_keccakf1600__uint64_t_1size_t(&self->inner);
  }
  size_t out_len = core_slice___Slice_T___len(out[0U], uint8_t, size_t);
  size_t blocks = out_len / (size_t)168U;
  size_t last = out_len - out_len % (size_t)168U;
  size_t mid;
  if ((size_t)168U >= out_len) {
    mid = out_len;
  } else {
    mid = (size_t)168U;
  }
  K___Eurydice_slice_uint8_t_1size_t__Eurydice_slice_uint8_t_1size_t_ uu____0 =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___split_at_mut_n(
          out, mid);
  Eurydice_slice out00[1U];
  memcpy(out00, uu____0.fst, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice out_rest[1U];
  memcpy(out_rest, uu____0.snd, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___store___168size_t(
      self->inner.st, out00);
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
      K___Eurydice_slice_uint8_t_1size_t__Eurydice_slice_uint8_t_1size_t_ uu____1 =
          libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___split_at_mut_n(
              out_rest, (size_t)168U);
      Eurydice_slice out0[1U];
      memcpy(out0, uu____1.fst, (size_t)1U * sizeof(Eurydice_slice));
      Eurydice_slice tmp[1U];
      memcpy(tmp, uu____1.snd, (size_t)1U * sizeof(Eurydice_slice));
      libcrux_sha3_generic_keccak_keccakf1600__uint64_t_1size_t(&self->inner);
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___store___168size_t(
          self->inner.st, out0);
      memcpy(out_rest, tmp, (size_t)1U * sizeof(Eurydice_slice));
    }
  }
  if (last < out_len) {
    libcrux_sha3_generic_keccak_keccakf1600__uint64_t_1size_t(&self->inner);
    libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___store___168size_t(
        self->inner.st, out_rest);
  }
  self->sponge = true;
}

static inline void
libcrux_sha3_portable_incremental___libcrux_sha3__portable__incremental__XofSqueeze_168__usize__for_libcrux_sha3__portable__incremental__Shake128Squeeze__1__squeeze(
    libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__168size_t
        *self,
    Eurydice_slice out) {
  Eurydice_slice buf[1U] = {out};
  libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__squeeze__uint64_t_1size_t_168size_t(
      self, buf);
}

static inline libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t
libcrux_sha3_portable___core__clone__Clone_for_libcrux_sha3__portable__KeccakState___clone(
    libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t *self) {
  return self[0U];
}

static inline uint32_t
libcrux_sha3___core__convert__From_libcrux_sha3__Algorithm__for_u32__1__from(
    libcrux_sha3_Algorithm v) {
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

static inline libcrux_sha3_Algorithm
libcrux_sha3___core__convert__From_u32__for_libcrux_sha3__Algorithm___from(
    uint32_t v) {
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
