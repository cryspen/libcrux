/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 45f5a34f336e35c6cc2253bc90cbdb8d812cefa9
 * Eurydice: 7d686376ec943225ff89942978c6c3028bac689c
 * Karamel: 8c3612018c25889288da6857771be3ad03b75bcd
 * F*: 5643e656b989aca7629723653a2570c7df6252b9-dirty
 * Libcrux: dc479b888127f61fdc6af2d8524c06a6a6fb1e9c
 */

#ifndef __libcrux_core_H
#define __libcrux_core_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "eurydice_glue.h"

/**
A monomorphic instance of core.ops.range.Range
with types size_t

*/
typedef struct core_ops_range_Range_08_s {
  size_t start;
  size_t end;
} core_ops_range_Range_08;

#define Ok 0
#define Err 1

typedef uint8_t Result_a9_tags;

#define None 0
#define Some 1

typedef uint8_t Option_9e_tags;

/**
A monomorphic instance of core.option.Option
with types size_t

*/
typedef struct Option_08_s {
  Option_9e_tags tag;
  size_t f0;
} Option_08;

static inline uint16_t core_num__u16_7__wrapping_add(uint16_t x0, uint16_t x1);

#define CORE_NUM__U32_8__BITS (32U)

static inline uint64_t core_num__u64_9__from_le_bytes(uint8_t x0[8U]);

static inline void core_num__u64_9__to_le_bytes(uint64_t x0, uint8_t x1[8U]);

static inline uint32_t core_num__u8_6__count_ones(uint8_t x0);

static inline uint8_t core_num__u8_6__wrapping_sub(uint8_t x0, uint8_t x1);

#define LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE ((size_t)32U)

#define LIBCRUX_ML_KEM_CONSTANTS_BITS_PER_COEFFICIENT ((size_t)12U)

#define LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT ((size_t)256U)

#define LIBCRUX_ML_KEM_CONSTANTS_BITS_PER_RING_ELEMENT \
  (LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT * (size_t)12U)

#define LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT \
  (LIBCRUX_ML_KEM_CONSTANTS_BITS_PER_RING_ELEMENT / (size_t)8U)

#define LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE ((size_t)32U)

#define LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE ((size_t)32U)

typedef struct libcrux_ml_kem_utils_extraction_helper_Keypair768_s {
  uint8_t fst[1152U];
  uint8_t snd[1184U];
} libcrux_ml_kem_utils_extraction_helper_Keypair768;

/**
A monomorphic instance of core.result.Result
with types uint8_t[24size_t], core_array_TryFromSliceError

*/
typedef struct Result_b2_s {
  Result_a9_tags tag;
  union {
    uint8_t case_Ok[24U];
    TryFromSliceError case_Err;
  } val;
} Result_b2;

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types uint8_t[24size_t], core_array_TryFromSliceError

*/
static inline void unwrap_26_70(Result_b2 self, uint8_t ret[24U]) {
  if (self.tag == Ok) {
    uint8_t f0[24U];
    memcpy(f0, self.val.case_Ok, (size_t)24U * sizeof(uint8_t));
    memcpy(ret, f0, (size_t)24U * sizeof(uint8_t));
  } else {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                      "unwrap not Ok");
    KRML_HOST_EXIT(255U);
  }
}

/**
A monomorphic instance of core.result.Result
with types uint8_t[20size_t], core_array_TryFromSliceError

*/
typedef struct Result_e1_s {
  Result_a9_tags tag;
  union {
    uint8_t case_Ok[20U];
    TryFromSliceError case_Err;
  } val;
} Result_e1;

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types uint8_t[20size_t], core_array_TryFromSliceError

*/
static inline void unwrap_26_20(Result_e1 self, uint8_t ret[20U]) {
  if (self.tag == Ok) {
    uint8_t f0[20U];
    memcpy(f0, self.val.case_Ok, (size_t)20U * sizeof(uint8_t));
    memcpy(ret, f0, (size_t)20U * sizeof(uint8_t));
  } else {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                      "unwrap not Ok");
    KRML_HOST_EXIT(255U);
  }
}

/**
A monomorphic instance of core.result.Result
with types uint8_t[10size_t], core_array_TryFromSliceError

*/
typedef struct Result_9d_s {
  Result_a9_tags tag;
  union {
    uint8_t case_Ok[10U];
    TryFromSliceError case_Err;
  } val;
} Result_9d;

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types uint8_t[10size_t], core_array_TryFromSliceError

*/
static inline void unwrap_26_ce(Result_9d self, uint8_t ret[10U]) {
  if (self.tag == Ok) {
    uint8_t f0[10U];
    memcpy(f0, self.val.case_Ok, (size_t)10U * sizeof(uint8_t));
    memcpy(ret, f0, (size_t)10U * sizeof(uint8_t));
  } else {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                      "unwrap not Ok");
    KRML_HOST_EXIT(255U);
  }
}

typedef struct Eurydice_slice_uint8_t_4size_t__x2_s {
  Eurydice_slice fst[4U];
  Eurydice_slice snd[4U];
} Eurydice_slice_uint8_t_4size_t__x2;

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 32
*/
static KRML_MUSTINLINE void libcrux_ml_kem_utils_into_padded_array_9e(
    Eurydice_slice slice, uint8_t ret[32U]) {
  uint8_t out[32U] = {0U};
  uint8_t *uu____0 = out;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice2(uu____0, (size_t)0U,
                                  Eurydice_slice_len(slice, uint8_t), uint8_t),
      slice, uint8_t);
  memcpy(ret, out, (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.types.MlKemPrivateKey
with const generics
- $2400size_t
*/
typedef struct libcrux_ml_kem_types_MlKemPrivateKey_d9_s {
  uint8_t value[2400U];
} libcrux_ml_kem_types_MlKemPrivateKey_d9;

/**
This function found in impl {(core::default::Default for
libcrux_ml_kem::types::MlKemPrivateKey<SIZE>)#8}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.default_9e
with const generics
- SIZE= 2400
*/
static inline libcrux_ml_kem_types_MlKemPrivateKey_d9
libcrux_ml_kem_types_default_9e_28(void) {
  libcrux_ml_kem_types_MlKemPrivateKey_d9 lit;
  lit.value[0U] = 0U;
  lit.value[1U] = 0U;
  lit.value[2U] = 0U;
  lit.value[3U] = 0U;
  lit.value[4U] = 0U;
  lit.value[5U] = 0U;
  lit.value[6U] = 0U;
  lit.value[7U] = 0U;
  lit.value[8U] = 0U;
  lit.value[9U] = 0U;
  lit.value[10U] = 0U;
  lit.value[11U] = 0U;
  lit.value[12U] = 0U;
  lit.value[13U] = 0U;
  lit.value[14U] = 0U;
  lit.value[15U] = 0U;
  lit.value[16U] = 0U;
  lit.value[17U] = 0U;
  lit.value[18U] = 0U;
  lit.value[19U] = 0U;
  lit.value[20U] = 0U;
  lit.value[21U] = 0U;
  lit.value[22U] = 0U;
  lit.value[23U] = 0U;
  lit.value[24U] = 0U;
  lit.value[25U] = 0U;
  lit.value[26U] = 0U;
  lit.value[27U] = 0U;
  lit.value[28U] = 0U;
  lit.value[29U] = 0U;
  lit.value[30U] = 0U;
  lit.value[31U] = 0U;
  lit.value[32U] = 0U;
  lit.value[33U] = 0U;
  lit.value[34U] = 0U;
  lit.value[35U] = 0U;
  lit.value[36U] = 0U;
  lit.value[37U] = 0U;
  lit.value[38U] = 0U;
  lit.value[39U] = 0U;
  lit.value[40U] = 0U;
  lit.value[41U] = 0U;
  lit.value[42U] = 0U;
  lit.value[43U] = 0U;
  lit.value[44U] = 0U;
  lit.value[45U] = 0U;
  lit.value[46U] = 0U;
  lit.value[47U] = 0U;
  lit.value[48U] = 0U;
  lit.value[49U] = 0U;
  lit.value[50U] = 0U;
  lit.value[51U] = 0U;
  lit.value[52U] = 0U;
  lit.value[53U] = 0U;
  lit.value[54U] = 0U;
  lit.value[55U] = 0U;
  lit.value[56U] = 0U;
  lit.value[57U] = 0U;
  lit.value[58U] = 0U;
  lit.value[59U] = 0U;
  lit.value[60U] = 0U;
  lit.value[61U] = 0U;
  lit.value[62U] = 0U;
  lit.value[63U] = 0U;
  lit.value[64U] = 0U;
  lit.value[65U] = 0U;
  lit.value[66U] = 0U;
  lit.value[67U] = 0U;
  lit.value[68U] = 0U;
  lit.value[69U] = 0U;
  lit.value[70U] = 0U;
  lit.value[71U] = 0U;
  lit.value[72U] = 0U;
  lit.value[73U] = 0U;
  lit.value[74U] = 0U;
  lit.value[75U] = 0U;
  lit.value[76U] = 0U;
  lit.value[77U] = 0U;
  lit.value[78U] = 0U;
  lit.value[79U] = 0U;
  lit.value[80U] = 0U;
  lit.value[81U] = 0U;
  lit.value[82U] = 0U;
  lit.value[83U] = 0U;
  lit.value[84U] = 0U;
  lit.value[85U] = 0U;
  lit.value[86U] = 0U;
  lit.value[87U] = 0U;
  lit.value[88U] = 0U;
  lit.value[89U] = 0U;
  lit.value[90U] = 0U;
  lit.value[91U] = 0U;
  lit.value[92U] = 0U;
  lit.value[93U] = 0U;
  lit.value[94U] = 0U;
  lit.value[95U] = 0U;
  lit.value[96U] = 0U;
  lit.value[97U] = 0U;
  lit.value[98U] = 0U;
  lit.value[99U] = 0U;
  lit.value[100U] = 0U;
  lit.value[101U] = 0U;
  lit.value[102U] = 0U;
  lit.value[103U] = 0U;
  lit.value[104U] = 0U;
  lit.value[105U] = 0U;
  lit.value[106U] = 0U;
  lit.value[107U] = 0U;
  lit.value[108U] = 0U;
  lit.value[109U] = 0U;
  lit.value[110U] = 0U;
  lit.value[111U] = 0U;
  lit.value[112U] = 0U;
  lit.value[113U] = 0U;
  lit.value[114U] = 0U;
  lit.value[115U] = 0U;
  lit.value[116U] = 0U;
  lit.value[117U] = 0U;
  lit.value[118U] = 0U;
  lit.value[119U] = 0U;
  lit.value[120U] = 0U;
  lit.value[121U] = 0U;
  lit.value[122U] = 0U;
  lit.value[123U] = 0U;
  lit.value[124U] = 0U;
  lit.value[125U] = 0U;
  lit.value[126U] = 0U;
  lit.value[127U] = 0U;
  lit.value[128U] = 0U;
  lit.value[129U] = 0U;
  lit.value[130U] = 0U;
  lit.value[131U] = 0U;
  lit.value[132U] = 0U;
  lit.value[133U] = 0U;
  lit.value[134U] = 0U;
  lit.value[135U] = 0U;
  lit.value[136U] = 0U;
  lit.value[137U] = 0U;
  lit.value[138U] = 0U;
  lit.value[139U] = 0U;
  lit.value[140U] = 0U;
  lit.value[141U] = 0U;
  lit.value[142U] = 0U;
  lit.value[143U] = 0U;
  lit.value[144U] = 0U;
  lit.value[145U] = 0U;
  lit.value[146U] = 0U;
  lit.value[147U] = 0U;
  lit.value[148U] = 0U;
  lit.value[149U] = 0U;
  lit.value[150U] = 0U;
  lit.value[151U] = 0U;
  lit.value[152U] = 0U;
  lit.value[153U] = 0U;
  lit.value[154U] = 0U;
  lit.value[155U] = 0U;
  lit.value[156U] = 0U;
  lit.value[157U] = 0U;
  lit.value[158U] = 0U;
  lit.value[159U] = 0U;
  lit.value[160U] = 0U;
  lit.value[161U] = 0U;
  lit.value[162U] = 0U;
  lit.value[163U] = 0U;
  lit.value[164U] = 0U;
  lit.value[165U] = 0U;
  lit.value[166U] = 0U;
  lit.value[167U] = 0U;
  lit.value[168U] = 0U;
  lit.value[169U] = 0U;
  lit.value[170U] = 0U;
  lit.value[171U] = 0U;
  lit.value[172U] = 0U;
  lit.value[173U] = 0U;
  lit.value[174U] = 0U;
  lit.value[175U] = 0U;
  lit.value[176U] = 0U;
  lit.value[177U] = 0U;
  lit.value[178U] = 0U;
  lit.value[179U] = 0U;
  lit.value[180U] = 0U;
  lit.value[181U] = 0U;
  lit.value[182U] = 0U;
  lit.value[183U] = 0U;
  lit.value[184U] = 0U;
  lit.value[185U] = 0U;
  lit.value[186U] = 0U;
  lit.value[187U] = 0U;
  lit.value[188U] = 0U;
  lit.value[189U] = 0U;
  lit.value[190U] = 0U;
  lit.value[191U] = 0U;
  lit.value[192U] = 0U;
  lit.value[193U] = 0U;
  lit.value[194U] = 0U;
  lit.value[195U] = 0U;
  lit.value[196U] = 0U;
  lit.value[197U] = 0U;
  lit.value[198U] = 0U;
  lit.value[199U] = 0U;
  lit.value[200U] = 0U;
  lit.value[201U] = 0U;
  lit.value[202U] = 0U;
  lit.value[203U] = 0U;
  lit.value[204U] = 0U;
  lit.value[205U] = 0U;
  lit.value[206U] = 0U;
  lit.value[207U] = 0U;
  lit.value[208U] = 0U;
  lit.value[209U] = 0U;
  lit.value[210U] = 0U;
  lit.value[211U] = 0U;
  lit.value[212U] = 0U;
  lit.value[213U] = 0U;
  lit.value[214U] = 0U;
  lit.value[215U] = 0U;
  lit.value[216U] = 0U;
  lit.value[217U] = 0U;
  lit.value[218U] = 0U;
  lit.value[219U] = 0U;
  lit.value[220U] = 0U;
  lit.value[221U] = 0U;
  lit.value[222U] = 0U;
  lit.value[223U] = 0U;
  lit.value[224U] = 0U;
  lit.value[225U] = 0U;
  lit.value[226U] = 0U;
  lit.value[227U] = 0U;
  lit.value[228U] = 0U;
  lit.value[229U] = 0U;
  lit.value[230U] = 0U;
  lit.value[231U] = 0U;
  lit.value[232U] = 0U;
  lit.value[233U] = 0U;
  lit.value[234U] = 0U;
  lit.value[235U] = 0U;
  lit.value[236U] = 0U;
  lit.value[237U] = 0U;
  lit.value[238U] = 0U;
  lit.value[239U] = 0U;
  lit.value[240U] = 0U;
  lit.value[241U] = 0U;
  lit.value[242U] = 0U;
  lit.value[243U] = 0U;
  lit.value[244U] = 0U;
  lit.value[245U] = 0U;
  lit.value[246U] = 0U;
  lit.value[247U] = 0U;
  lit.value[248U] = 0U;
  lit.value[249U] = 0U;
  lit.value[250U] = 0U;
  lit.value[251U] = 0U;
  lit.value[252U] = 0U;
  lit.value[253U] = 0U;
  lit.value[254U] = 0U;
  lit.value[255U] = 0U;
  lit.value[256U] = 0U;
  lit.value[257U] = 0U;
  lit.value[258U] = 0U;
  lit.value[259U] = 0U;
  lit.value[260U] = 0U;
  lit.value[261U] = 0U;
  lit.value[262U] = 0U;
  lit.value[263U] = 0U;
  lit.value[264U] = 0U;
  lit.value[265U] = 0U;
  lit.value[266U] = 0U;
  lit.value[267U] = 0U;
  lit.value[268U] = 0U;
  lit.value[269U] = 0U;
  lit.value[270U] = 0U;
  lit.value[271U] = 0U;
  lit.value[272U] = 0U;
  lit.value[273U] = 0U;
  lit.value[274U] = 0U;
  lit.value[275U] = 0U;
  lit.value[276U] = 0U;
  lit.value[277U] = 0U;
  lit.value[278U] = 0U;
  lit.value[279U] = 0U;
  lit.value[280U] = 0U;
  lit.value[281U] = 0U;
  lit.value[282U] = 0U;
  lit.value[283U] = 0U;
  lit.value[284U] = 0U;
  lit.value[285U] = 0U;
  lit.value[286U] = 0U;
  lit.value[287U] = 0U;
  lit.value[288U] = 0U;
  lit.value[289U] = 0U;
  lit.value[290U] = 0U;
  lit.value[291U] = 0U;
  lit.value[292U] = 0U;
  lit.value[293U] = 0U;
  lit.value[294U] = 0U;
  lit.value[295U] = 0U;
  lit.value[296U] = 0U;
  lit.value[297U] = 0U;
  lit.value[298U] = 0U;
  lit.value[299U] = 0U;
  lit.value[300U] = 0U;
  lit.value[301U] = 0U;
  lit.value[302U] = 0U;
  lit.value[303U] = 0U;
  lit.value[304U] = 0U;
  lit.value[305U] = 0U;
  lit.value[306U] = 0U;
  lit.value[307U] = 0U;
  lit.value[308U] = 0U;
  lit.value[309U] = 0U;
  lit.value[310U] = 0U;
  lit.value[311U] = 0U;
  lit.value[312U] = 0U;
  lit.value[313U] = 0U;
  lit.value[314U] = 0U;
  lit.value[315U] = 0U;
  lit.value[316U] = 0U;
  lit.value[317U] = 0U;
  lit.value[318U] = 0U;
  lit.value[319U] = 0U;
  lit.value[320U] = 0U;
  lit.value[321U] = 0U;
  lit.value[322U] = 0U;
  lit.value[323U] = 0U;
  lit.value[324U] = 0U;
  lit.value[325U] = 0U;
  lit.value[326U] = 0U;
  lit.value[327U] = 0U;
  lit.value[328U] = 0U;
  lit.value[329U] = 0U;
  lit.value[330U] = 0U;
  lit.value[331U] = 0U;
  lit.value[332U] = 0U;
  lit.value[333U] = 0U;
  lit.value[334U] = 0U;
  lit.value[335U] = 0U;
  lit.value[336U] = 0U;
  lit.value[337U] = 0U;
  lit.value[338U] = 0U;
  lit.value[339U] = 0U;
  lit.value[340U] = 0U;
  lit.value[341U] = 0U;
  lit.value[342U] = 0U;
  lit.value[343U] = 0U;
  lit.value[344U] = 0U;
  lit.value[345U] = 0U;
  lit.value[346U] = 0U;
  lit.value[347U] = 0U;
  lit.value[348U] = 0U;
  lit.value[349U] = 0U;
  lit.value[350U] = 0U;
  lit.value[351U] = 0U;
  lit.value[352U] = 0U;
  lit.value[353U] = 0U;
  lit.value[354U] = 0U;
  lit.value[355U] = 0U;
  lit.value[356U] = 0U;
  lit.value[357U] = 0U;
  lit.value[358U] = 0U;
  lit.value[359U] = 0U;
  lit.value[360U] = 0U;
  lit.value[361U] = 0U;
  lit.value[362U] = 0U;
  lit.value[363U] = 0U;
  lit.value[364U] = 0U;
  lit.value[365U] = 0U;
  lit.value[366U] = 0U;
  lit.value[367U] = 0U;
  lit.value[368U] = 0U;
  lit.value[369U] = 0U;
  lit.value[370U] = 0U;
  lit.value[371U] = 0U;
  lit.value[372U] = 0U;
  lit.value[373U] = 0U;
  lit.value[374U] = 0U;
  lit.value[375U] = 0U;
  lit.value[376U] = 0U;
  lit.value[377U] = 0U;
  lit.value[378U] = 0U;
  lit.value[379U] = 0U;
  lit.value[380U] = 0U;
  lit.value[381U] = 0U;
  lit.value[382U] = 0U;
  lit.value[383U] = 0U;
  lit.value[384U] = 0U;
  lit.value[385U] = 0U;
  lit.value[386U] = 0U;
  lit.value[387U] = 0U;
  lit.value[388U] = 0U;
  lit.value[389U] = 0U;
  lit.value[390U] = 0U;
  lit.value[391U] = 0U;
  lit.value[392U] = 0U;
  lit.value[393U] = 0U;
  lit.value[394U] = 0U;
  lit.value[395U] = 0U;
  lit.value[396U] = 0U;
  lit.value[397U] = 0U;
  lit.value[398U] = 0U;
  lit.value[399U] = 0U;
  lit.value[400U] = 0U;
  lit.value[401U] = 0U;
  lit.value[402U] = 0U;
  lit.value[403U] = 0U;
  lit.value[404U] = 0U;
  lit.value[405U] = 0U;
  lit.value[406U] = 0U;
  lit.value[407U] = 0U;
  lit.value[408U] = 0U;
  lit.value[409U] = 0U;
  lit.value[410U] = 0U;
  lit.value[411U] = 0U;
  lit.value[412U] = 0U;
  lit.value[413U] = 0U;
  lit.value[414U] = 0U;
  lit.value[415U] = 0U;
  lit.value[416U] = 0U;
  lit.value[417U] = 0U;
  lit.value[418U] = 0U;
  lit.value[419U] = 0U;
  lit.value[420U] = 0U;
  lit.value[421U] = 0U;
  lit.value[422U] = 0U;
  lit.value[423U] = 0U;
  lit.value[424U] = 0U;
  lit.value[425U] = 0U;
  lit.value[426U] = 0U;
  lit.value[427U] = 0U;
  lit.value[428U] = 0U;
  lit.value[429U] = 0U;
  lit.value[430U] = 0U;
  lit.value[431U] = 0U;
  lit.value[432U] = 0U;
  lit.value[433U] = 0U;
  lit.value[434U] = 0U;
  lit.value[435U] = 0U;
  lit.value[436U] = 0U;
  lit.value[437U] = 0U;
  lit.value[438U] = 0U;
  lit.value[439U] = 0U;
  lit.value[440U] = 0U;
  lit.value[441U] = 0U;
  lit.value[442U] = 0U;
  lit.value[443U] = 0U;
  lit.value[444U] = 0U;
  lit.value[445U] = 0U;
  lit.value[446U] = 0U;
  lit.value[447U] = 0U;
  lit.value[448U] = 0U;
  lit.value[449U] = 0U;
  lit.value[450U] = 0U;
  lit.value[451U] = 0U;
  lit.value[452U] = 0U;
  lit.value[453U] = 0U;
  lit.value[454U] = 0U;
  lit.value[455U] = 0U;
  lit.value[456U] = 0U;
  lit.value[457U] = 0U;
  lit.value[458U] = 0U;
  lit.value[459U] = 0U;
  lit.value[460U] = 0U;
  lit.value[461U] = 0U;
  lit.value[462U] = 0U;
  lit.value[463U] = 0U;
  lit.value[464U] = 0U;
  lit.value[465U] = 0U;
  lit.value[466U] = 0U;
  lit.value[467U] = 0U;
  lit.value[468U] = 0U;
  lit.value[469U] = 0U;
  lit.value[470U] = 0U;
  lit.value[471U] = 0U;
  lit.value[472U] = 0U;
  lit.value[473U] = 0U;
  lit.value[474U] = 0U;
  lit.value[475U] = 0U;
  lit.value[476U] = 0U;
  lit.value[477U] = 0U;
  lit.value[478U] = 0U;
  lit.value[479U] = 0U;
  lit.value[480U] = 0U;
  lit.value[481U] = 0U;
  lit.value[482U] = 0U;
  lit.value[483U] = 0U;
  lit.value[484U] = 0U;
  lit.value[485U] = 0U;
  lit.value[486U] = 0U;
  lit.value[487U] = 0U;
  lit.value[488U] = 0U;
  lit.value[489U] = 0U;
  lit.value[490U] = 0U;
  lit.value[491U] = 0U;
  lit.value[492U] = 0U;
  lit.value[493U] = 0U;
  lit.value[494U] = 0U;
  lit.value[495U] = 0U;
  lit.value[496U] = 0U;
  lit.value[497U] = 0U;
  lit.value[498U] = 0U;
  lit.value[499U] = 0U;
  lit.value[500U] = 0U;
  lit.value[501U] = 0U;
  lit.value[502U] = 0U;
  lit.value[503U] = 0U;
  lit.value[504U] = 0U;
  lit.value[505U] = 0U;
  lit.value[506U] = 0U;
  lit.value[507U] = 0U;
  lit.value[508U] = 0U;
  lit.value[509U] = 0U;
  lit.value[510U] = 0U;
  lit.value[511U] = 0U;
  lit.value[512U] = 0U;
  lit.value[513U] = 0U;
  lit.value[514U] = 0U;
  lit.value[515U] = 0U;
  lit.value[516U] = 0U;
  lit.value[517U] = 0U;
  lit.value[518U] = 0U;
  lit.value[519U] = 0U;
  lit.value[520U] = 0U;
  lit.value[521U] = 0U;
  lit.value[522U] = 0U;
  lit.value[523U] = 0U;
  lit.value[524U] = 0U;
  lit.value[525U] = 0U;
  lit.value[526U] = 0U;
  lit.value[527U] = 0U;
  lit.value[528U] = 0U;
  lit.value[529U] = 0U;
  lit.value[530U] = 0U;
  lit.value[531U] = 0U;
  lit.value[532U] = 0U;
  lit.value[533U] = 0U;
  lit.value[534U] = 0U;
  lit.value[535U] = 0U;
  lit.value[536U] = 0U;
  lit.value[537U] = 0U;
  lit.value[538U] = 0U;
  lit.value[539U] = 0U;
  lit.value[540U] = 0U;
  lit.value[541U] = 0U;
  lit.value[542U] = 0U;
  lit.value[543U] = 0U;
  lit.value[544U] = 0U;
  lit.value[545U] = 0U;
  lit.value[546U] = 0U;
  lit.value[547U] = 0U;
  lit.value[548U] = 0U;
  lit.value[549U] = 0U;
  lit.value[550U] = 0U;
  lit.value[551U] = 0U;
  lit.value[552U] = 0U;
  lit.value[553U] = 0U;
  lit.value[554U] = 0U;
  lit.value[555U] = 0U;
  lit.value[556U] = 0U;
  lit.value[557U] = 0U;
  lit.value[558U] = 0U;
  lit.value[559U] = 0U;
  lit.value[560U] = 0U;
  lit.value[561U] = 0U;
  lit.value[562U] = 0U;
  lit.value[563U] = 0U;
  lit.value[564U] = 0U;
  lit.value[565U] = 0U;
  lit.value[566U] = 0U;
  lit.value[567U] = 0U;
  lit.value[568U] = 0U;
  lit.value[569U] = 0U;
  lit.value[570U] = 0U;
  lit.value[571U] = 0U;
  lit.value[572U] = 0U;
  lit.value[573U] = 0U;
  lit.value[574U] = 0U;
  lit.value[575U] = 0U;
  lit.value[576U] = 0U;
  lit.value[577U] = 0U;
  lit.value[578U] = 0U;
  lit.value[579U] = 0U;
  lit.value[580U] = 0U;
  lit.value[581U] = 0U;
  lit.value[582U] = 0U;
  lit.value[583U] = 0U;
  lit.value[584U] = 0U;
  lit.value[585U] = 0U;
  lit.value[586U] = 0U;
  lit.value[587U] = 0U;
  lit.value[588U] = 0U;
  lit.value[589U] = 0U;
  lit.value[590U] = 0U;
  lit.value[591U] = 0U;
  lit.value[592U] = 0U;
  lit.value[593U] = 0U;
  lit.value[594U] = 0U;
  lit.value[595U] = 0U;
  lit.value[596U] = 0U;
  lit.value[597U] = 0U;
  lit.value[598U] = 0U;
  lit.value[599U] = 0U;
  lit.value[600U] = 0U;
  lit.value[601U] = 0U;
  lit.value[602U] = 0U;
  lit.value[603U] = 0U;
  lit.value[604U] = 0U;
  lit.value[605U] = 0U;
  lit.value[606U] = 0U;
  lit.value[607U] = 0U;
  lit.value[608U] = 0U;
  lit.value[609U] = 0U;
  lit.value[610U] = 0U;
  lit.value[611U] = 0U;
  lit.value[612U] = 0U;
  lit.value[613U] = 0U;
  lit.value[614U] = 0U;
  lit.value[615U] = 0U;
  lit.value[616U] = 0U;
  lit.value[617U] = 0U;
  lit.value[618U] = 0U;
  lit.value[619U] = 0U;
  lit.value[620U] = 0U;
  lit.value[621U] = 0U;
  lit.value[622U] = 0U;
  lit.value[623U] = 0U;
  lit.value[624U] = 0U;
  lit.value[625U] = 0U;
  lit.value[626U] = 0U;
  lit.value[627U] = 0U;
  lit.value[628U] = 0U;
  lit.value[629U] = 0U;
  lit.value[630U] = 0U;
  lit.value[631U] = 0U;
  lit.value[632U] = 0U;
  lit.value[633U] = 0U;
  lit.value[634U] = 0U;
  lit.value[635U] = 0U;
  lit.value[636U] = 0U;
  lit.value[637U] = 0U;
  lit.value[638U] = 0U;
  lit.value[639U] = 0U;
  lit.value[640U] = 0U;
  lit.value[641U] = 0U;
  lit.value[642U] = 0U;
  lit.value[643U] = 0U;
  lit.value[644U] = 0U;
  lit.value[645U] = 0U;
  lit.value[646U] = 0U;
  lit.value[647U] = 0U;
  lit.value[648U] = 0U;
  lit.value[649U] = 0U;
  lit.value[650U] = 0U;
  lit.value[651U] = 0U;
  lit.value[652U] = 0U;
  lit.value[653U] = 0U;
  lit.value[654U] = 0U;
  lit.value[655U] = 0U;
  lit.value[656U] = 0U;
  lit.value[657U] = 0U;
  lit.value[658U] = 0U;
  lit.value[659U] = 0U;
  lit.value[660U] = 0U;
  lit.value[661U] = 0U;
  lit.value[662U] = 0U;
  lit.value[663U] = 0U;
  lit.value[664U] = 0U;
  lit.value[665U] = 0U;
  lit.value[666U] = 0U;
  lit.value[667U] = 0U;
  lit.value[668U] = 0U;
  lit.value[669U] = 0U;
  lit.value[670U] = 0U;
  lit.value[671U] = 0U;
  lit.value[672U] = 0U;
  lit.value[673U] = 0U;
  lit.value[674U] = 0U;
  lit.value[675U] = 0U;
  lit.value[676U] = 0U;
  lit.value[677U] = 0U;
  lit.value[678U] = 0U;
  lit.value[679U] = 0U;
  lit.value[680U] = 0U;
  lit.value[681U] = 0U;
  lit.value[682U] = 0U;
  lit.value[683U] = 0U;
  lit.value[684U] = 0U;
  lit.value[685U] = 0U;
  lit.value[686U] = 0U;
  lit.value[687U] = 0U;
  lit.value[688U] = 0U;
  lit.value[689U] = 0U;
  lit.value[690U] = 0U;
  lit.value[691U] = 0U;
  lit.value[692U] = 0U;
  lit.value[693U] = 0U;
  lit.value[694U] = 0U;
  lit.value[695U] = 0U;
  lit.value[696U] = 0U;
  lit.value[697U] = 0U;
  lit.value[698U] = 0U;
  lit.value[699U] = 0U;
  lit.value[700U] = 0U;
  lit.value[701U] = 0U;
  lit.value[702U] = 0U;
  lit.value[703U] = 0U;
  lit.value[704U] = 0U;
  lit.value[705U] = 0U;
  lit.value[706U] = 0U;
  lit.value[707U] = 0U;
  lit.value[708U] = 0U;
  lit.value[709U] = 0U;
  lit.value[710U] = 0U;
  lit.value[711U] = 0U;
  lit.value[712U] = 0U;
  lit.value[713U] = 0U;
  lit.value[714U] = 0U;
  lit.value[715U] = 0U;
  lit.value[716U] = 0U;
  lit.value[717U] = 0U;
  lit.value[718U] = 0U;
  lit.value[719U] = 0U;
  lit.value[720U] = 0U;
  lit.value[721U] = 0U;
  lit.value[722U] = 0U;
  lit.value[723U] = 0U;
  lit.value[724U] = 0U;
  lit.value[725U] = 0U;
  lit.value[726U] = 0U;
  lit.value[727U] = 0U;
  lit.value[728U] = 0U;
  lit.value[729U] = 0U;
  lit.value[730U] = 0U;
  lit.value[731U] = 0U;
  lit.value[732U] = 0U;
  lit.value[733U] = 0U;
  lit.value[734U] = 0U;
  lit.value[735U] = 0U;
  lit.value[736U] = 0U;
  lit.value[737U] = 0U;
  lit.value[738U] = 0U;
  lit.value[739U] = 0U;
  lit.value[740U] = 0U;
  lit.value[741U] = 0U;
  lit.value[742U] = 0U;
  lit.value[743U] = 0U;
  lit.value[744U] = 0U;
  lit.value[745U] = 0U;
  lit.value[746U] = 0U;
  lit.value[747U] = 0U;
  lit.value[748U] = 0U;
  lit.value[749U] = 0U;
  lit.value[750U] = 0U;
  lit.value[751U] = 0U;
  lit.value[752U] = 0U;
  lit.value[753U] = 0U;
  lit.value[754U] = 0U;
  lit.value[755U] = 0U;
  lit.value[756U] = 0U;
  lit.value[757U] = 0U;
  lit.value[758U] = 0U;
  lit.value[759U] = 0U;
  lit.value[760U] = 0U;
  lit.value[761U] = 0U;
  lit.value[762U] = 0U;
  lit.value[763U] = 0U;
  lit.value[764U] = 0U;
  lit.value[765U] = 0U;
  lit.value[766U] = 0U;
  lit.value[767U] = 0U;
  lit.value[768U] = 0U;
  lit.value[769U] = 0U;
  lit.value[770U] = 0U;
  lit.value[771U] = 0U;
  lit.value[772U] = 0U;
  lit.value[773U] = 0U;
  lit.value[774U] = 0U;
  lit.value[775U] = 0U;
  lit.value[776U] = 0U;
  lit.value[777U] = 0U;
  lit.value[778U] = 0U;
  lit.value[779U] = 0U;
  lit.value[780U] = 0U;
  lit.value[781U] = 0U;
  lit.value[782U] = 0U;
  lit.value[783U] = 0U;
  lit.value[784U] = 0U;
  lit.value[785U] = 0U;
  lit.value[786U] = 0U;
  lit.value[787U] = 0U;
  lit.value[788U] = 0U;
  lit.value[789U] = 0U;
  lit.value[790U] = 0U;
  lit.value[791U] = 0U;
  lit.value[792U] = 0U;
  lit.value[793U] = 0U;
  lit.value[794U] = 0U;
  lit.value[795U] = 0U;
  lit.value[796U] = 0U;
  lit.value[797U] = 0U;
  lit.value[798U] = 0U;
  lit.value[799U] = 0U;
  lit.value[800U] = 0U;
  lit.value[801U] = 0U;
  lit.value[802U] = 0U;
  lit.value[803U] = 0U;
  lit.value[804U] = 0U;
  lit.value[805U] = 0U;
  lit.value[806U] = 0U;
  lit.value[807U] = 0U;
  lit.value[808U] = 0U;
  lit.value[809U] = 0U;
  lit.value[810U] = 0U;
  lit.value[811U] = 0U;
  lit.value[812U] = 0U;
  lit.value[813U] = 0U;
  lit.value[814U] = 0U;
  lit.value[815U] = 0U;
  lit.value[816U] = 0U;
  lit.value[817U] = 0U;
  lit.value[818U] = 0U;
  lit.value[819U] = 0U;
  lit.value[820U] = 0U;
  lit.value[821U] = 0U;
  lit.value[822U] = 0U;
  lit.value[823U] = 0U;
  lit.value[824U] = 0U;
  lit.value[825U] = 0U;
  lit.value[826U] = 0U;
  lit.value[827U] = 0U;
  lit.value[828U] = 0U;
  lit.value[829U] = 0U;
  lit.value[830U] = 0U;
  lit.value[831U] = 0U;
  lit.value[832U] = 0U;
  lit.value[833U] = 0U;
  lit.value[834U] = 0U;
  lit.value[835U] = 0U;
  lit.value[836U] = 0U;
  lit.value[837U] = 0U;
  lit.value[838U] = 0U;
  lit.value[839U] = 0U;
  lit.value[840U] = 0U;
  lit.value[841U] = 0U;
  lit.value[842U] = 0U;
  lit.value[843U] = 0U;
  lit.value[844U] = 0U;
  lit.value[845U] = 0U;
  lit.value[846U] = 0U;
  lit.value[847U] = 0U;
  lit.value[848U] = 0U;
  lit.value[849U] = 0U;
  lit.value[850U] = 0U;
  lit.value[851U] = 0U;
  lit.value[852U] = 0U;
  lit.value[853U] = 0U;
  lit.value[854U] = 0U;
  lit.value[855U] = 0U;
  lit.value[856U] = 0U;
  lit.value[857U] = 0U;
  lit.value[858U] = 0U;
  lit.value[859U] = 0U;
  lit.value[860U] = 0U;
  lit.value[861U] = 0U;
  lit.value[862U] = 0U;
  lit.value[863U] = 0U;
  lit.value[864U] = 0U;
  lit.value[865U] = 0U;
  lit.value[866U] = 0U;
  lit.value[867U] = 0U;
  lit.value[868U] = 0U;
  lit.value[869U] = 0U;
  lit.value[870U] = 0U;
  lit.value[871U] = 0U;
  lit.value[872U] = 0U;
  lit.value[873U] = 0U;
  lit.value[874U] = 0U;
  lit.value[875U] = 0U;
  lit.value[876U] = 0U;
  lit.value[877U] = 0U;
  lit.value[878U] = 0U;
  lit.value[879U] = 0U;
  lit.value[880U] = 0U;
  lit.value[881U] = 0U;
  lit.value[882U] = 0U;
  lit.value[883U] = 0U;
  lit.value[884U] = 0U;
  lit.value[885U] = 0U;
  lit.value[886U] = 0U;
  lit.value[887U] = 0U;
  lit.value[888U] = 0U;
  lit.value[889U] = 0U;
  lit.value[890U] = 0U;
  lit.value[891U] = 0U;
  lit.value[892U] = 0U;
  lit.value[893U] = 0U;
  lit.value[894U] = 0U;
  lit.value[895U] = 0U;
  lit.value[896U] = 0U;
  lit.value[897U] = 0U;
  lit.value[898U] = 0U;
  lit.value[899U] = 0U;
  lit.value[900U] = 0U;
  lit.value[901U] = 0U;
  lit.value[902U] = 0U;
  lit.value[903U] = 0U;
  lit.value[904U] = 0U;
  lit.value[905U] = 0U;
  lit.value[906U] = 0U;
  lit.value[907U] = 0U;
  lit.value[908U] = 0U;
  lit.value[909U] = 0U;
  lit.value[910U] = 0U;
  lit.value[911U] = 0U;
  lit.value[912U] = 0U;
  lit.value[913U] = 0U;
  lit.value[914U] = 0U;
  lit.value[915U] = 0U;
  lit.value[916U] = 0U;
  lit.value[917U] = 0U;
  lit.value[918U] = 0U;
  lit.value[919U] = 0U;
  lit.value[920U] = 0U;
  lit.value[921U] = 0U;
  lit.value[922U] = 0U;
  lit.value[923U] = 0U;
  lit.value[924U] = 0U;
  lit.value[925U] = 0U;
  lit.value[926U] = 0U;
  lit.value[927U] = 0U;
  lit.value[928U] = 0U;
  lit.value[929U] = 0U;
  lit.value[930U] = 0U;
  lit.value[931U] = 0U;
  lit.value[932U] = 0U;
  lit.value[933U] = 0U;
  lit.value[934U] = 0U;
  lit.value[935U] = 0U;
  lit.value[936U] = 0U;
  lit.value[937U] = 0U;
  lit.value[938U] = 0U;
  lit.value[939U] = 0U;
  lit.value[940U] = 0U;
  lit.value[941U] = 0U;
  lit.value[942U] = 0U;
  lit.value[943U] = 0U;
  lit.value[944U] = 0U;
  lit.value[945U] = 0U;
  lit.value[946U] = 0U;
  lit.value[947U] = 0U;
  lit.value[948U] = 0U;
  lit.value[949U] = 0U;
  lit.value[950U] = 0U;
  lit.value[951U] = 0U;
  lit.value[952U] = 0U;
  lit.value[953U] = 0U;
  lit.value[954U] = 0U;
  lit.value[955U] = 0U;
  lit.value[956U] = 0U;
  lit.value[957U] = 0U;
  lit.value[958U] = 0U;
  lit.value[959U] = 0U;
  lit.value[960U] = 0U;
  lit.value[961U] = 0U;
  lit.value[962U] = 0U;
  lit.value[963U] = 0U;
  lit.value[964U] = 0U;
  lit.value[965U] = 0U;
  lit.value[966U] = 0U;
  lit.value[967U] = 0U;
  lit.value[968U] = 0U;
  lit.value[969U] = 0U;
  lit.value[970U] = 0U;
  lit.value[971U] = 0U;
  lit.value[972U] = 0U;
  lit.value[973U] = 0U;
  lit.value[974U] = 0U;
  lit.value[975U] = 0U;
  lit.value[976U] = 0U;
  lit.value[977U] = 0U;
  lit.value[978U] = 0U;
  lit.value[979U] = 0U;
  lit.value[980U] = 0U;
  lit.value[981U] = 0U;
  lit.value[982U] = 0U;
  lit.value[983U] = 0U;
  lit.value[984U] = 0U;
  lit.value[985U] = 0U;
  lit.value[986U] = 0U;
  lit.value[987U] = 0U;
  lit.value[988U] = 0U;
  lit.value[989U] = 0U;
  lit.value[990U] = 0U;
  lit.value[991U] = 0U;
  lit.value[992U] = 0U;
  lit.value[993U] = 0U;
  lit.value[994U] = 0U;
  lit.value[995U] = 0U;
  lit.value[996U] = 0U;
  lit.value[997U] = 0U;
  lit.value[998U] = 0U;
  lit.value[999U] = 0U;
  lit.value[1000U] = 0U;
  lit.value[1001U] = 0U;
  lit.value[1002U] = 0U;
  lit.value[1003U] = 0U;
  lit.value[1004U] = 0U;
  lit.value[1005U] = 0U;
  lit.value[1006U] = 0U;
  lit.value[1007U] = 0U;
  lit.value[1008U] = 0U;
  lit.value[1009U] = 0U;
  lit.value[1010U] = 0U;
  lit.value[1011U] = 0U;
  lit.value[1012U] = 0U;
  lit.value[1013U] = 0U;
  lit.value[1014U] = 0U;
  lit.value[1015U] = 0U;
  lit.value[1016U] = 0U;
  lit.value[1017U] = 0U;
  lit.value[1018U] = 0U;
  lit.value[1019U] = 0U;
  lit.value[1020U] = 0U;
  lit.value[1021U] = 0U;
  lit.value[1022U] = 0U;
  lit.value[1023U] = 0U;
  lit.value[1024U] = 0U;
  lit.value[1025U] = 0U;
  lit.value[1026U] = 0U;
  lit.value[1027U] = 0U;
  lit.value[1028U] = 0U;
  lit.value[1029U] = 0U;
  lit.value[1030U] = 0U;
  lit.value[1031U] = 0U;
  lit.value[1032U] = 0U;
  lit.value[1033U] = 0U;
  lit.value[1034U] = 0U;
  lit.value[1035U] = 0U;
  lit.value[1036U] = 0U;
  lit.value[1037U] = 0U;
  lit.value[1038U] = 0U;
  lit.value[1039U] = 0U;
  lit.value[1040U] = 0U;
  lit.value[1041U] = 0U;
  lit.value[1042U] = 0U;
  lit.value[1043U] = 0U;
  lit.value[1044U] = 0U;
  lit.value[1045U] = 0U;
  lit.value[1046U] = 0U;
  lit.value[1047U] = 0U;
  lit.value[1048U] = 0U;
  lit.value[1049U] = 0U;
  lit.value[1050U] = 0U;
  lit.value[1051U] = 0U;
  lit.value[1052U] = 0U;
  lit.value[1053U] = 0U;
  lit.value[1054U] = 0U;
  lit.value[1055U] = 0U;
  lit.value[1056U] = 0U;
  lit.value[1057U] = 0U;
  lit.value[1058U] = 0U;
  lit.value[1059U] = 0U;
  lit.value[1060U] = 0U;
  lit.value[1061U] = 0U;
  lit.value[1062U] = 0U;
  lit.value[1063U] = 0U;
  lit.value[1064U] = 0U;
  lit.value[1065U] = 0U;
  lit.value[1066U] = 0U;
  lit.value[1067U] = 0U;
  lit.value[1068U] = 0U;
  lit.value[1069U] = 0U;
  lit.value[1070U] = 0U;
  lit.value[1071U] = 0U;
  lit.value[1072U] = 0U;
  lit.value[1073U] = 0U;
  lit.value[1074U] = 0U;
  lit.value[1075U] = 0U;
  lit.value[1076U] = 0U;
  lit.value[1077U] = 0U;
  lit.value[1078U] = 0U;
  lit.value[1079U] = 0U;
  lit.value[1080U] = 0U;
  lit.value[1081U] = 0U;
  lit.value[1082U] = 0U;
  lit.value[1083U] = 0U;
  lit.value[1084U] = 0U;
  lit.value[1085U] = 0U;
  lit.value[1086U] = 0U;
  lit.value[1087U] = 0U;
  lit.value[1088U] = 0U;
  lit.value[1089U] = 0U;
  lit.value[1090U] = 0U;
  lit.value[1091U] = 0U;
  lit.value[1092U] = 0U;
  lit.value[1093U] = 0U;
  lit.value[1094U] = 0U;
  lit.value[1095U] = 0U;
  lit.value[1096U] = 0U;
  lit.value[1097U] = 0U;
  lit.value[1098U] = 0U;
  lit.value[1099U] = 0U;
  lit.value[1100U] = 0U;
  lit.value[1101U] = 0U;
  lit.value[1102U] = 0U;
  lit.value[1103U] = 0U;
  lit.value[1104U] = 0U;
  lit.value[1105U] = 0U;
  lit.value[1106U] = 0U;
  lit.value[1107U] = 0U;
  lit.value[1108U] = 0U;
  lit.value[1109U] = 0U;
  lit.value[1110U] = 0U;
  lit.value[1111U] = 0U;
  lit.value[1112U] = 0U;
  lit.value[1113U] = 0U;
  lit.value[1114U] = 0U;
  lit.value[1115U] = 0U;
  lit.value[1116U] = 0U;
  lit.value[1117U] = 0U;
  lit.value[1118U] = 0U;
  lit.value[1119U] = 0U;
  lit.value[1120U] = 0U;
  lit.value[1121U] = 0U;
  lit.value[1122U] = 0U;
  lit.value[1123U] = 0U;
  lit.value[1124U] = 0U;
  lit.value[1125U] = 0U;
  lit.value[1126U] = 0U;
  lit.value[1127U] = 0U;
  lit.value[1128U] = 0U;
  lit.value[1129U] = 0U;
  lit.value[1130U] = 0U;
  lit.value[1131U] = 0U;
  lit.value[1132U] = 0U;
  lit.value[1133U] = 0U;
  lit.value[1134U] = 0U;
  lit.value[1135U] = 0U;
  lit.value[1136U] = 0U;
  lit.value[1137U] = 0U;
  lit.value[1138U] = 0U;
  lit.value[1139U] = 0U;
  lit.value[1140U] = 0U;
  lit.value[1141U] = 0U;
  lit.value[1142U] = 0U;
  lit.value[1143U] = 0U;
  lit.value[1144U] = 0U;
  lit.value[1145U] = 0U;
  lit.value[1146U] = 0U;
  lit.value[1147U] = 0U;
  lit.value[1148U] = 0U;
  lit.value[1149U] = 0U;
  lit.value[1150U] = 0U;
  lit.value[1151U] = 0U;
  lit.value[1152U] = 0U;
  lit.value[1153U] = 0U;
  lit.value[1154U] = 0U;
  lit.value[1155U] = 0U;
  lit.value[1156U] = 0U;
  lit.value[1157U] = 0U;
  lit.value[1158U] = 0U;
  lit.value[1159U] = 0U;
  lit.value[1160U] = 0U;
  lit.value[1161U] = 0U;
  lit.value[1162U] = 0U;
  lit.value[1163U] = 0U;
  lit.value[1164U] = 0U;
  lit.value[1165U] = 0U;
  lit.value[1166U] = 0U;
  lit.value[1167U] = 0U;
  lit.value[1168U] = 0U;
  lit.value[1169U] = 0U;
  lit.value[1170U] = 0U;
  lit.value[1171U] = 0U;
  lit.value[1172U] = 0U;
  lit.value[1173U] = 0U;
  lit.value[1174U] = 0U;
  lit.value[1175U] = 0U;
  lit.value[1176U] = 0U;
  lit.value[1177U] = 0U;
  lit.value[1178U] = 0U;
  lit.value[1179U] = 0U;
  lit.value[1180U] = 0U;
  lit.value[1181U] = 0U;
  lit.value[1182U] = 0U;
  lit.value[1183U] = 0U;
  lit.value[1184U] = 0U;
  lit.value[1185U] = 0U;
  lit.value[1186U] = 0U;
  lit.value[1187U] = 0U;
  lit.value[1188U] = 0U;
  lit.value[1189U] = 0U;
  lit.value[1190U] = 0U;
  lit.value[1191U] = 0U;
  lit.value[1192U] = 0U;
  lit.value[1193U] = 0U;
  lit.value[1194U] = 0U;
  lit.value[1195U] = 0U;
  lit.value[1196U] = 0U;
  lit.value[1197U] = 0U;
  lit.value[1198U] = 0U;
  lit.value[1199U] = 0U;
  lit.value[1200U] = 0U;
  lit.value[1201U] = 0U;
  lit.value[1202U] = 0U;
  lit.value[1203U] = 0U;
  lit.value[1204U] = 0U;
  lit.value[1205U] = 0U;
  lit.value[1206U] = 0U;
  lit.value[1207U] = 0U;
  lit.value[1208U] = 0U;
  lit.value[1209U] = 0U;
  lit.value[1210U] = 0U;
  lit.value[1211U] = 0U;
  lit.value[1212U] = 0U;
  lit.value[1213U] = 0U;
  lit.value[1214U] = 0U;
  lit.value[1215U] = 0U;
  lit.value[1216U] = 0U;
  lit.value[1217U] = 0U;
  lit.value[1218U] = 0U;
  lit.value[1219U] = 0U;
  lit.value[1220U] = 0U;
  lit.value[1221U] = 0U;
  lit.value[1222U] = 0U;
  lit.value[1223U] = 0U;
  lit.value[1224U] = 0U;
  lit.value[1225U] = 0U;
  lit.value[1226U] = 0U;
  lit.value[1227U] = 0U;
  lit.value[1228U] = 0U;
  lit.value[1229U] = 0U;
  lit.value[1230U] = 0U;
  lit.value[1231U] = 0U;
  lit.value[1232U] = 0U;
  lit.value[1233U] = 0U;
  lit.value[1234U] = 0U;
  lit.value[1235U] = 0U;
  lit.value[1236U] = 0U;
  lit.value[1237U] = 0U;
  lit.value[1238U] = 0U;
  lit.value[1239U] = 0U;
  lit.value[1240U] = 0U;
  lit.value[1241U] = 0U;
  lit.value[1242U] = 0U;
  lit.value[1243U] = 0U;
  lit.value[1244U] = 0U;
  lit.value[1245U] = 0U;
  lit.value[1246U] = 0U;
  lit.value[1247U] = 0U;
  lit.value[1248U] = 0U;
  lit.value[1249U] = 0U;
  lit.value[1250U] = 0U;
  lit.value[1251U] = 0U;
  lit.value[1252U] = 0U;
  lit.value[1253U] = 0U;
  lit.value[1254U] = 0U;
  lit.value[1255U] = 0U;
  lit.value[1256U] = 0U;
  lit.value[1257U] = 0U;
  lit.value[1258U] = 0U;
  lit.value[1259U] = 0U;
  lit.value[1260U] = 0U;
  lit.value[1261U] = 0U;
  lit.value[1262U] = 0U;
  lit.value[1263U] = 0U;
  lit.value[1264U] = 0U;
  lit.value[1265U] = 0U;
  lit.value[1266U] = 0U;
  lit.value[1267U] = 0U;
  lit.value[1268U] = 0U;
  lit.value[1269U] = 0U;
  lit.value[1270U] = 0U;
  lit.value[1271U] = 0U;
  lit.value[1272U] = 0U;
  lit.value[1273U] = 0U;
  lit.value[1274U] = 0U;
  lit.value[1275U] = 0U;
  lit.value[1276U] = 0U;
  lit.value[1277U] = 0U;
  lit.value[1278U] = 0U;
  lit.value[1279U] = 0U;
  lit.value[1280U] = 0U;
  lit.value[1281U] = 0U;
  lit.value[1282U] = 0U;
  lit.value[1283U] = 0U;
  lit.value[1284U] = 0U;
  lit.value[1285U] = 0U;
  lit.value[1286U] = 0U;
  lit.value[1287U] = 0U;
  lit.value[1288U] = 0U;
  lit.value[1289U] = 0U;
  lit.value[1290U] = 0U;
  lit.value[1291U] = 0U;
  lit.value[1292U] = 0U;
  lit.value[1293U] = 0U;
  lit.value[1294U] = 0U;
  lit.value[1295U] = 0U;
  lit.value[1296U] = 0U;
  lit.value[1297U] = 0U;
  lit.value[1298U] = 0U;
  lit.value[1299U] = 0U;
  lit.value[1300U] = 0U;
  lit.value[1301U] = 0U;
  lit.value[1302U] = 0U;
  lit.value[1303U] = 0U;
  lit.value[1304U] = 0U;
  lit.value[1305U] = 0U;
  lit.value[1306U] = 0U;
  lit.value[1307U] = 0U;
  lit.value[1308U] = 0U;
  lit.value[1309U] = 0U;
  lit.value[1310U] = 0U;
  lit.value[1311U] = 0U;
  lit.value[1312U] = 0U;
  lit.value[1313U] = 0U;
  lit.value[1314U] = 0U;
  lit.value[1315U] = 0U;
  lit.value[1316U] = 0U;
  lit.value[1317U] = 0U;
  lit.value[1318U] = 0U;
  lit.value[1319U] = 0U;
  lit.value[1320U] = 0U;
  lit.value[1321U] = 0U;
  lit.value[1322U] = 0U;
  lit.value[1323U] = 0U;
  lit.value[1324U] = 0U;
  lit.value[1325U] = 0U;
  lit.value[1326U] = 0U;
  lit.value[1327U] = 0U;
  lit.value[1328U] = 0U;
  lit.value[1329U] = 0U;
  lit.value[1330U] = 0U;
  lit.value[1331U] = 0U;
  lit.value[1332U] = 0U;
  lit.value[1333U] = 0U;
  lit.value[1334U] = 0U;
  lit.value[1335U] = 0U;
  lit.value[1336U] = 0U;
  lit.value[1337U] = 0U;
  lit.value[1338U] = 0U;
  lit.value[1339U] = 0U;
  lit.value[1340U] = 0U;
  lit.value[1341U] = 0U;
  lit.value[1342U] = 0U;
  lit.value[1343U] = 0U;
  lit.value[1344U] = 0U;
  lit.value[1345U] = 0U;
  lit.value[1346U] = 0U;
  lit.value[1347U] = 0U;
  lit.value[1348U] = 0U;
  lit.value[1349U] = 0U;
  lit.value[1350U] = 0U;
  lit.value[1351U] = 0U;
  lit.value[1352U] = 0U;
  lit.value[1353U] = 0U;
  lit.value[1354U] = 0U;
  lit.value[1355U] = 0U;
  lit.value[1356U] = 0U;
  lit.value[1357U] = 0U;
  lit.value[1358U] = 0U;
  lit.value[1359U] = 0U;
  lit.value[1360U] = 0U;
  lit.value[1361U] = 0U;
  lit.value[1362U] = 0U;
  lit.value[1363U] = 0U;
  lit.value[1364U] = 0U;
  lit.value[1365U] = 0U;
  lit.value[1366U] = 0U;
  lit.value[1367U] = 0U;
  lit.value[1368U] = 0U;
  lit.value[1369U] = 0U;
  lit.value[1370U] = 0U;
  lit.value[1371U] = 0U;
  lit.value[1372U] = 0U;
  lit.value[1373U] = 0U;
  lit.value[1374U] = 0U;
  lit.value[1375U] = 0U;
  lit.value[1376U] = 0U;
  lit.value[1377U] = 0U;
  lit.value[1378U] = 0U;
  lit.value[1379U] = 0U;
  lit.value[1380U] = 0U;
  lit.value[1381U] = 0U;
  lit.value[1382U] = 0U;
  lit.value[1383U] = 0U;
  lit.value[1384U] = 0U;
  lit.value[1385U] = 0U;
  lit.value[1386U] = 0U;
  lit.value[1387U] = 0U;
  lit.value[1388U] = 0U;
  lit.value[1389U] = 0U;
  lit.value[1390U] = 0U;
  lit.value[1391U] = 0U;
  lit.value[1392U] = 0U;
  lit.value[1393U] = 0U;
  lit.value[1394U] = 0U;
  lit.value[1395U] = 0U;
  lit.value[1396U] = 0U;
  lit.value[1397U] = 0U;
  lit.value[1398U] = 0U;
  lit.value[1399U] = 0U;
  lit.value[1400U] = 0U;
  lit.value[1401U] = 0U;
  lit.value[1402U] = 0U;
  lit.value[1403U] = 0U;
  lit.value[1404U] = 0U;
  lit.value[1405U] = 0U;
  lit.value[1406U] = 0U;
  lit.value[1407U] = 0U;
  lit.value[1408U] = 0U;
  lit.value[1409U] = 0U;
  lit.value[1410U] = 0U;
  lit.value[1411U] = 0U;
  lit.value[1412U] = 0U;
  lit.value[1413U] = 0U;
  lit.value[1414U] = 0U;
  lit.value[1415U] = 0U;
  lit.value[1416U] = 0U;
  lit.value[1417U] = 0U;
  lit.value[1418U] = 0U;
  lit.value[1419U] = 0U;
  lit.value[1420U] = 0U;
  lit.value[1421U] = 0U;
  lit.value[1422U] = 0U;
  lit.value[1423U] = 0U;
  lit.value[1424U] = 0U;
  lit.value[1425U] = 0U;
  lit.value[1426U] = 0U;
  lit.value[1427U] = 0U;
  lit.value[1428U] = 0U;
  lit.value[1429U] = 0U;
  lit.value[1430U] = 0U;
  lit.value[1431U] = 0U;
  lit.value[1432U] = 0U;
  lit.value[1433U] = 0U;
  lit.value[1434U] = 0U;
  lit.value[1435U] = 0U;
  lit.value[1436U] = 0U;
  lit.value[1437U] = 0U;
  lit.value[1438U] = 0U;
  lit.value[1439U] = 0U;
  lit.value[1440U] = 0U;
  lit.value[1441U] = 0U;
  lit.value[1442U] = 0U;
  lit.value[1443U] = 0U;
  lit.value[1444U] = 0U;
  lit.value[1445U] = 0U;
  lit.value[1446U] = 0U;
  lit.value[1447U] = 0U;
  lit.value[1448U] = 0U;
  lit.value[1449U] = 0U;
  lit.value[1450U] = 0U;
  lit.value[1451U] = 0U;
  lit.value[1452U] = 0U;
  lit.value[1453U] = 0U;
  lit.value[1454U] = 0U;
  lit.value[1455U] = 0U;
  lit.value[1456U] = 0U;
  lit.value[1457U] = 0U;
  lit.value[1458U] = 0U;
  lit.value[1459U] = 0U;
  lit.value[1460U] = 0U;
  lit.value[1461U] = 0U;
  lit.value[1462U] = 0U;
  lit.value[1463U] = 0U;
  lit.value[1464U] = 0U;
  lit.value[1465U] = 0U;
  lit.value[1466U] = 0U;
  lit.value[1467U] = 0U;
  lit.value[1468U] = 0U;
  lit.value[1469U] = 0U;
  lit.value[1470U] = 0U;
  lit.value[1471U] = 0U;
  lit.value[1472U] = 0U;
  lit.value[1473U] = 0U;
  lit.value[1474U] = 0U;
  lit.value[1475U] = 0U;
  lit.value[1476U] = 0U;
  lit.value[1477U] = 0U;
  lit.value[1478U] = 0U;
  lit.value[1479U] = 0U;
  lit.value[1480U] = 0U;
  lit.value[1481U] = 0U;
  lit.value[1482U] = 0U;
  lit.value[1483U] = 0U;
  lit.value[1484U] = 0U;
  lit.value[1485U] = 0U;
  lit.value[1486U] = 0U;
  lit.value[1487U] = 0U;
  lit.value[1488U] = 0U;
  lit.value[1489U] = 0U;
  lit.value[1490U] = 0U;
  lit.value[1491U] = 0U;
  lit.value[1492U] = 0U;
  lit.value[1493U] = 0U;
  lit.value[1494U] = 0U;
  lit.value[1495U] = 0U;
  lit.value[1496U] = 0U;
  lit.value[1497U] = 0U;
  lit.value[1498U] = 0U;
  lit.value[1499U] = 0U;
  lit.value[1500U] = 0U;
  lit.value[1501U] = 0U;
  lit.value[1502U] = 0U;
  lit.value[1503U] = 0U;
  lit.value[1504U] = 0U;
  lit.value[1505U] = 0U;
  lit.value[1506U] = 0U;
  lit.value[1507U] = 0U;
  lit.value[1508U] = 0U;
  lit.value[1509U] = 0U;
  lit.value[1510U] = 0U;
  lit.value[1511U] = 0U;
  lit.value[1512U] = 0U;
  lit.value[1513U] = 0U;
  lit.value[1514U] = 0U;
  lit.value[1515U] = 0U;
  lit.value[1516U] = 0U;
  lit.value[1517U] = 0U;
  lit.value[1518U] = 0U;
  lit.value[1519U] = 0U;
  lit.value[1520U] = 0U;
  lit.value[1521U] = 0U;
  lit.value[1522U] = 0U;
  lit.value[1523U] = 0U;
  lit.value[1524U] = 0U;
  lit.value[1525U] = 0U;
  lit.value[1526U] = 0U;
  lit.value[1527U] = 0U;
  lit.value[1528U] = 0U;
  lit.value[1529U] = 0U;
  lit.value[1530U] = 0U;
  lit.value[1531U] = 0U;
  lit.value[1532U] = 0U;
  lit.value[1533U] = 0U;
  lit.value[1534U] = 0U;
  lit.value[1535U] = 0U;
  lit.value[1536U] = 0U;
  lit.value[1537U] = 0U;
  lit.value[1538U] = 0U;
  lit.value[1539U] = 0U;
  lit.value[1540U] = 0U;
  lit.value[1541U] = 0U;
  lit.value[1542U] = 0U;
  lit.value[1543U] = 0U;
  lit.value[1544U] = 0U;
  lit.value[1545U] = 0U;
  lit.value[1546U] = 0U;
  lit.value[1547U] = 0U;
  lit.value[1548U] = 0U;
  lit.value[1549U] = 0U;
  lit.value[1550U] = 0U;
  lit.value[1551U] = 0U;
  lit.value[1552U] = 0U;
  lit.value[1553U] = 0U;
  lit.value[1554U] = 0U;
  lit.value[1555U] = 0U;
  lit.value[1556U] = 0U;
  lit.value[1557U] = 0U;
  lit.value[1558U] = 0U;
  lit.value[1559U] = 0U;
  lit.value[1560U] = 0U;
  lit.value[1561U] = 0U;
  lit.value[1562U] = 0U;
  lit.value[1563U] = 0U;
  lit.value[1564U] = 0U;
  lit.value[1565U] = 0U;
  lit.value[1566U] = 0U;
  lit.value[1567U] = 0U;
  lit.value[1568U] = 0U;
  lit.value[1569U] = 0U;
  lit.value[1570U] = 0U;
  lit.value[1571U] = 0U;
  lit.value[1572U] = 0U;
  lit.value[1573U] = 0U;
  lit.value[1574U] = 0U;
  lit.value[1575U] = 0U;
  lit.value[1576U] = 0U;
  lit.value[1577U] = 0U;
  lit.value[1578U] = 0U;
  lit.value[1579U] = 0U;
  lit.value[1580U] = 0U;
  lit.value[1581U] = 0U;
  lit.value[1582U] = 0U;
  lit.value[1583U] = 0U;
  lit.value[1584U] = 0U;
  lit.value[1585U] = 0U;
  lit.value[1586U] = 0U;
  lit.value[1587U] = 0U;
  lit.value[1588U] = 0U;
  lit.value[1589U] = 0U;
  lit.value[1590U] = 0U;
  lit.value[1591U] = 0U;
  lit.value[1592U] = 0U;
  lit.value[1593U] = 0U;
  lit.value[1594U] = 0U;
  lit.value[1595U] = 0U;
  lit.value[1596U] = 0U;
  lit.value[1597U] = 0U;
  lit.value[1598U] = 0U;
  lit.value[1599U] = 0U;
  lit.value[1600U] = 0U;
  lit.value[1601U] = 0U;
  lit.value[1602U] = 0U;
  lit.value[1603U] = 0U;
  lit.value[1604U] = 0U;
  lit.value[1605U] = 0U;
  lit.value[1606U] = 0U;
  lit.value[1607U] = 0U;
  lit.value[1608U] = 0U;
  lit.value[1609U] = 0U;
  lit.value[1610U] = 0U;
  lit.value[1611U] = 0U;
  lit.value[1612U] = 0U;
  lit.value[1613U] = 0U;
  lit.value[1614U] = 0U;
  lit.value[1615U] = 0U;
  lit.value[1616U] = 0U;
  lit.value[1617U] = 0U;
  lit.value[1618U] = 0U;
  lit.value[1619U] = 0U;
  lit.value[1620U] = 0U;
  lit.value[1621U] = 0U;
  lit.value[1622U] = 0U;
  lit.value[1623U] = 0U;
  lit.value[1624U] = 0U;
  lit.value[1625U] = 0U;
  lit.value[1626U] = 0U;
  lit.value[1627U] = 0U;
  lit.value[1628U] = 0U;
  lit.value[1629U] = 0U;
  lit.value[1630U] = 0U;
  lit.value[1631U] = 0U;
  lit.value[1632U] = 0U;
  lit.value[1633U] = 0U;
  lit.value[1634U] = 0U;
  lit.value[1635U] = 0U;
  lit.value[1636U] = 0U;
  lit.value[1637U] = 0U;
  lit.value[1638U] = 0U;
  lit.value[1639U] = 0U;
  lit.value[1640U] = 0U;
  lit.value[1641U] = 0U;
  lit.value[1642U] = 0U;
  lit.value[1643U] = 0U;
  lit.value[1644U] = 0U;
  lit.value[1645U] = 0U;
  lit.value[1646U] = 0U;
  lit.value[1647U] = 0U;
  lit.value[1648U] = 0U;
  lit.value[1649U] = 0U;
  lit.value[1650U] = 0U;
  lit.value[1651U] = 0U;
  lit.value[1652U] = 0U;
  lit.value[1653U] = 0U;
  lit.value[1654U] = 0U;
  lit.value[1655U] = 0U;
  lit.value[1656U] = 0U;
  lit.value[1657U] = 0U;
  lit.value[1658U] = 0U;
  lit.value[1659U] = 0U;
  lit.value[1660U] = 0U;
  lit.value[1661U] = 0U;
  lit.value[1662U] = 0U;
  lit.value[1663U] = 0U;
  lit.value[1664U] = 0U;
  lit.value[1665U] = 0U;
  lit.value[1666U] = 0U;
  lit.value[1667U] = 0U;
  lit.value[1668U] = 0U;
  lit.value[1669U] = 0U;
  lit.value[1670U] = 0U;
  lit.value[1671U] = 0U;
  lit.value[1672U] = 0U;
  lit.value[1673U] = 0U;
  lit.value[1674U] = 0U;
  lit.value[1675U] = 0U;
  lit.value[1676U] = 0U;
  lit.value[1677U] = 0U;
  lit.value[1678U] = 0U;
  lit.value[1679U] = 0U;
  lit.value[1680U] = 0U;
  lit.value[1681U] = 0U;
  lit.value[1682U] = 0U;
  lit.value[1683U] = 0U;
  lit.value[1684U] = 0U;
  lit.value[1685U] = 0U;
  lit.value[1686U] = 0U;
  lit.value[1687U] = 0U;
  lit.value[1688U] = 0U;
  lit.value[1689U] = 0U;
  lit.value[1690U] = 0U;
  lit.value[1691U] = 0U;
  lit.value[1692U] = 0U;
  lit.value[1693U] = 0U;
  lit.value[1694U] = 0U;
  lit.value[1695U] = 0U;
  lit.value[1696U] = 0U;
  lit.value[1697U] = 0U;
  lit.value[1698U] = 0U;
  lit.value[1699U] = 0U;
  lit.value[1700U] = 0U;
  lit.value[1701U] = 0U;
  lit.value[1702U] = 0U;
  lit.value[1703U] = 0U;
  lit.value[1704U] = 0U;
  lit.value[1705U] = 0U;
  lit.value[1706U] = 0U;
  lit.value[1707U] = 0U;
  lit.value[1708U] = 0U;
  lit.value[1709U] = 0U;
  lit.value[1710U] = 0U;
  lit.value[1711U] = 0U;
  lit.value[1712U] = 0U;
  lit.value[1713U] = 0U;
  lit.value[1714U] = 0U;
  lit.value[1715U] = 0U;
  lit.value[1716U] = 0U;
  lit.value[1717U] = 0U;
  lit.value[1718U] = 0U;
  lit.value[1719U] = 0U;
  lit.value[1720U] = 0U;
  lit.value[1721U] = 0U;
  lit.value[1722U] = 0U;
  lit.value[1723U] = 0U;
  lit.value[1724U] = 0U;
  lit.value[1725U] = 0U;
  lit.value[1726U] = 0U;
  lit.value[1727U] = 0U;
  lit.value[1728U] = 0U;
  lit.value[1729U] = 0U;
  lit.value[1730U] = 0U;
  lit.value[1731U] = 0U;
  lit.value[1732U] = 0U;
  lit.value[1733U] = 0U;
  lit.value[1734U] = 0U;
  lit.value[1735U] = 0U;
  lit.value[1736U] = 0U;
  lit.value[1737U] = 0U;
  lit.value[1738U] = 0U;
  lit.value[1739U] = 0U;
  lit.value[1740U] = 0U;
  lit.value[1741U] = 0U;
  lit.value[1742U] = 0U;
  lit.value[1743U] = 0U;
  lit.value[1744U] = 0U;
  lit.value[1745U] = 0U;
  lit.value[1746U] = 0U;
  lit.value[1747U] = 0U;
  lit.value[1748U] = 0U;
  lit.value[1749U] = 0U;
  lit.value[1750U] = 0U;
  lit.value[1751U] = 0U;
  lit.value[1752U] = 0U;
  lit.value[1753U] = 0U;
  lit.value[1754U] = 0U;
  lit.value[1755U] = 0U;
  lit.value[1756U] = 0U;
  lit.value[1757U] = 0U;
  lit.value[1758U] = 0U;
  lit.value[1759U] = 0U;
  lit.value[1760U] = 0U;
  lit.value[1761U] = 0U;
  lit.value[1762U] = 0U;
  lit.value[1763U] = 0U;
  lit.value[1764U] = 0U;
  lit.value[1765U] = 0U;
  lit.value[1766U] = 0U;
  lit.value[1767U] = 0U;
  lit.value[1768U] = 0U;
  lit.value[1769U] = 0U;
  lit.value[1770U] = 0U;
  lit.value[1771U] = 0U;
  lit.value[1772U] = 0U;
  lit.value[1773U] = 0U;
  lit.value[1774U] = 0U;
  lit.value[1775U] = 0U;
  lit.value[1776U] = 0U;
  lit.value[1777U] = 0U;
  lit.value[1778U] = 0U;
  lit.value[1779U] = 0U;
  lit.value[1780U] = 0U;
  lit.value[1781U] = 0U;
  lit.value[1782U] = 0U;
  lit.value[1783U] = 0U;
  lit.value[1784U] = 0U;
  lit.value[1785U] = 0U;
  lit.value[1786U] = 0U;
  lit.value[1787U] = 0U;
  lit.value[1788U] = 0U;
  lit.value[1789U] = 0U;
  lit.value[1790U] = 0U;
  lit.value[1791U] = 0U;
  lit.value[1792U] = 0U;
  lit.value[1793U] = 0U;
  lit.value[1794U] = 0U;
  lit.value[1795U] = 0U;
  lit.value[1796U] = 0U;
  lit.value[1797U] = 0U;
  lit.value[1798U] = 0U;
  lit.value[1799U] = 0U;
  lit.value[1800U] = 0U;
  lit.value[1801U] = 0U;
  lit.value[1802U] = 0U;
  lit.value[1803U] = 0U;
  lit.value[1804U] = 0U;
  lit.value[1805U] = 0U;
  lit.value[1806U] = 0U;
  lit.value[1807U] = 0U;
  lit.value[1808U] = 0U;
  lit.value[1809U] = 0U;
  lit.value[1810U] = 0U;
  lit.value[1811U] = 0U;
  lit.value[1812U] = 0U;
  lit.value[1813U] = 0U;
  lit.value[1814U] = 0U;
  lit.value[1815U] = 0U;
  lit.value[1816U] = 0U;
  lit.value[1817U] = 0U;
  lit.value[1818U] = 0U;
  lit.value[1819U] = 0U;
  lit.value[1820U] = 0U;
  lit.value[1821U] = 0U;
  lit.value[1822U] = 0U;
  lit.value[1823U] = 0U;
  lit.value[1824U] = 0U;
  lit.value[1825U] = 0U;
  lit.value[1826U] = 0U;
  lit.value[1827U] = 0U;
  lit.value[1828U] = 0U;
  lit.value[1829U] = 0U;
  lit.value[1830U] = 0U;
  lit.value[1831U] = 0U;
  lit.value[1832U] = 0U;
  lit.value[1833U] = 0U;
  lit.value[1834U] = 0U;
  lit.value[1835U] = 0U;
  lit.value[1836U] = 0U;
  lit.value[1837U] = 0U;
  lit.value[1838U] = 0U;
  lit.value[1839U] = 0U;
  lit.value[1840U] = 0U;
  lit.value[1841U] = 0U;
  lit.value[1842U] = 0U;
  lit.value[1843U] = 0U;
  lit.value[1844U] = 0U;
  lit.value[1845U] = 0U;
  lit.value[1846U] = 0U;
  lit.value[1847U] = 0U;
  lit.value[1848U] = 0U;
  lit.value[1849U] = 0U;
  lit.value[1850U] = 0U;
  lit.value[1851U] = 0U;
  lit.value[1852U] = 0U;
  lit.value[1853U] = 0U;
  lit.value[1854U] = 0U;
  lit.value[1855U] = 0U;
  lit.value[1856U] = 0U;
  lit.value[1857U] = 0U;
  lit.value[1858U] = 0U;
  lit.value[1859U] = 0U;
  lit.value[1860U] = 0U;
  lit.value[1861U] = 0U;
  lit.value[1862U] = 0U;
  lit.value[1863U] = 0U;
  lit.value[1864U] = 0U;
  lit.value[1865U] = 0U;
  lit.value[1866U] = 0U;
  lit.value[1867U] = 0U;
  lit.value[1868U] = 0U;
  lit.value[1869U] = 0U;
  lit.value[1870U] = 0U;
  lit.value[1871U] = 0U;
  lit.value[1872U] = 0U;
  lit.value[1873U] = 0U;
  lit.value[1874U] = 0U;
  lit.value[1875U] = 0U;
  lit.value[1876U] = 0U;
  lit.value[1877U] = 0U;
  lit.value[1878U] = 0U;
  lit.value[1879U] = 0U;
  lit.value[1880U] = 0U;
  lit.value[1881U] = 0U;
  lit.value[1882U] = 0U;
  lit.value[1883U] = 0U;
  lit.value[1884U] = 0U;
  lit.value[1885U] = 0U;
  lit.value[1886U] = 0U;
  lit.value[1887U] = 0U;
  lit.value[1888U] = 0U;
  lit.value[1889U] = 0U;
  lit.value[1890U] = 0U;
  lit.value[1891U] = 0U;
  lit.value[1892U] = 0U;
  lit.value[1893U] = 0U;
  lit.value[1894U] = 0U;
  lit.value[1895U] = 0U;
  lit.value[1896U] = 0U;
  lit.value[1897U] = 0U;
  lit.value[1898U] = 0U;
  lit.value[1899U] = 0U;
  lit.value[1900U] = 0U;
  lit.value[1901U] = 0U;
  lit.value[1902U] = 0U;
  lit.value[1903U] = 0U;
  lit.value[1904U] = 0U;
  lit.value[1905U] = 0U;
  lit.value[1906U] = 0U;
  lit.value[1907U] = 0U;
  lit.value[1908U] = 0U;
  lit.value[1909U] = 0U;
  lit.value[1910U] = 0U;
  lit.value[1911U] = 0U;
  lit.value[1912U] = 0U;
  lit.value[1913U] = 0U;
  lit.value[1914U] = 0U;
  lit.value[1915U] = 0U;
  lit.value[1916U] = 0U;
  lit.value[1917U] = 0U;
  lit.value[1918U] = 0U;
  lit.value[1919U] = 0U;
  lit.value[1920U] = 0U;
  lit.value[1921U] = 0U;
  lit.value[1922U] = 0U;
  lit.value[1923U] = 0U;
  lit.value[1924U] = 0U;
  lit.value[1925U] = 0U;
  lit.value[1926U] = 0U;
  lit.value[1927U] = 0U;
  lit.value[1928U] = 0U;
  lit.value[1929U] = 0U;
  lit.value[1930U] = 0U;
  lit.value[1931U] = 0U;
  lit.value[1932U] = 0U;
  lit.value[1933U] = 0U;
  lit.value[1934U] = 0U;
  lit.value[1935U] = 0U;
  lit.value[1936U] = 0U;
  lit.value[1937U] = 0U;
  lit.value[1938U] = 0U;
  lit.value[1939U] = 0U;
  lit.value[1940U] = 0U;
  lit.value[1941U] = 0U;
  lit.value[1942U] = 0U;
  lit.value[1943U] = 0U;
  lit.value[1944U] = 0U;
  lit.value[1945U] = 0U;
  lit.value[1946U] = 0U;
  lit.value[1947U] = 0U;
  lit.value[1948U] = 0U;
  lit.value[1949U] = 0U;
  lit.value[1950U] = 0U;
  lit.value[1951U] = 0U;
  lit.value[1952U] = 0U;
  lit.value[1953U] = 0U;
  lit.value[1954U] = 0U;
  lit.value[1955U] = 0U;
  lit.value[1956U] = 0U;
  lit.value[1957U] = 0U;
  lit.value[1958U] = 0U;
  lit.value[1959U] = 0U;
  lit.value[1960U] = 0U;
  lit.value[1961U] = 0U;
  lit.value[1962U] = 0U;
  lit.value[1963U] = 0U;
  lit.value[1964U] = 0U;
  lit.value[1965U] = 0U;
  lit.value[1966U] = 0U;
  lit.value[1967U] = 0U;
  lit.value[1968U] = 0U;
  lit.value[1969U] = 0U;
  lit.value[1970U] = 0U;
  lit.value[1971U] = 0U;
  lit.value[1972U] = 0U;
  lit.value[1973U] = 0U;
  lit.value[1974U] = 0U;
  lit.value[1975U] = 0U;
  lit.value[1976U] = 0U;
  lit.value[1977U] = 0U;
  lit.value[1978U] = 0U;
  lit.value[1979U] = 0U;
  lit.value[1980U] = 0U;
  lit.value[1981U] = 0U;
  lit.value[1982U] = 0U;
  lit.value[1983U] = 0U;
  lit.value[1984U] = 0U;
  lit.value[1985U] = 0U;
  lit.value[1986U] = 0U;
  lit.value[1987U] = 0U;
  lit.value[1988U] = 0U;
  lit.value[1989U] = 0U;
  lit.value[1990U] = 0U;
  lit.value[1991U] = 0U;
  lit.value[1992U] = 0U;
  lit.value[1993U] = 0U;
  lit.value[1994U] = 0U;
  lit.value[1995U] = 0U;
  lit.value[1996U] = 0U;
  lit.value[1997U] = 0U;
  lit.value[1998U] = 0U;
  lit.value[1999U] = 0U;
  lit.value[2000U] = 0U;
  lit.value[2001U] = 0U;
  lit.value[2002U] = 0U;
  lit.value[2003U] = 0U;
  lit.value[2004U] = 0U;
  lit.value[2005U] = 0U;
  lit.value[2006U] = 0U;
  lit.value[2007U] = 0U;
  lit.value[2008U] = 0U;
  lit.value[2009U] = 0U;
  lit.value[2010U] = 0U;
  lit.value[2011U] = 0U;
  lit.value[2012U] = 0U;
  lit.value[2013U] = 0U;
  lit.value[2014U] = 0U;
  lit.value[2015U] = 0U;
  lit.value[2016U] = 0U;
  lit.value[2017U] = 0U;
  lit.value[2018U] = 0U;
  lit.value[2019U] = 0U;
  lit.value[2020U] = 0U;
  lit.value[2021U] = 0U;
  lit.value[2022U] = 0U;
  lit.value[2023U] = 0U;
  lit.value[2024U] = 0U;
  lit.value[2025U] = 0U;
  lit.value[2026U] = 0U;
  lit.value[2027U] = 0U;
  lit.value[2028U] = 0U;
  lit.value[2029U] = 0U;
  lit.value[2030U] = 0U;
  lit.value[2031U] = 0U;
  lit.value[2032U] = 0U;
  lit.value[2033U] = 0U;
  lit.value[2034U] = 0U;
  lit.value[2035U] = 0U;
  lit.value[2036U] = 0U;
  lit.value[2037U] = 0U;
  lit.value[2038U] = 0U;
  lit.value[2039U] = 0U;
  lit.value[2040U] = 0U;
  lit.value[2041U] = 0U;
  lit.value[2042U] = 0U;
  lit.value[2043U] = 0U;
  lit.value[2044U] = 0U;
  lit.value[2045U] = 0U;
  lit.value[2046U] = 0U;
  lit.value[2047U] = 0U;
  lit.value[2048U] = 0U;
  lit.value[2049U] = 0U;
  lit.value[2050U] = 0U;
  lit.value[2051U] = 0U;
  lit.value[2052U] = 0U;
  lit.value[2053U] = 0U;
  lit.value[2054U] = 0U;
  lit.value[2055U] = 0U;
  lit.value[2056U] = 0U;
  lit.value[2057U] = 0U;
  lit.value[2058U] = 0U;
  lit.value[2059U] = 0U;
  lit.value[2060U] = 0U;
  lit.value[2061U] = 0U;
  lit.value[2062U] = 0U;
  lit.value[2063U] = 0U;
  lit.value[2064U] = 0U;
  lit.value[2065U] = 0U;
  lit.value[2066U] = 0U;
  lit.value[2067U] = 0U;
  lit.value[2068U] = 0U;
  lit.value[2069U] = 0U;
  lit.value[2070U] = 0U;
  lit.value[2071U] = 0U;
  lit.value[2072U] = 0U;
  lit.value[2073U] = 0U;
  lit.value[2074U] = 0U;
  lit.value[2075U] = 0U;
  lit.value[2076U] = 0U;
  lit.value[2077U] = 0U;
  lit.value[2078U] = 0U;
  lit.value[2079U] = 0U;
  lit.value[2080U] = 0U;
  lit.value[2081U] = 0U;
  lit.value[2082U] = 0U;
  lit.value[2083U] = 0U;
  lit.value[2084U] = 0U;
  lit.value[2085U] = 0U;
  lit.value[2086U] = 0U;
  lit.value[2087U] = 0U;
  lit.value[2088U] = 0U;
  lit.value[2089U] = 0U;
  lit.value[2090U] = 0U;
  lit.value[2091U] = 0U;
  lit.value[2092U] = 0U;
  lit.value[2093U] = 0U;
  lit.value[2094U] = 0U;
  lit.value[2095U] = 0U;
  lit.value[2096U] = 0U;
  lit.value[2097U] = 0U;
  lit.value[2098U] = 0U;
  lit.value[2099U] = 0U;
  lit.value[2100U] = 0U;
  lit.value[2101U] = 0U;
  lit.value[2102U] = 0U;
  lit.value[2103U] = 0U;
  lit.value[2104U] = 0U;
  lit.value[2105U] = 0U;
  lit.value[2106U] = 0U;
  lit.value[2107U] = 0U;
  lit.value[2108U] = 0U;
  lit.value[2109U] = 0U;
  lit.value[2110U] = 0U;
  lit.value[2111U] = 0U;
  lit.value[2112U] = 0U;
  lit.value[2113U] = 0U;
  lit.value[2114U] = 0U;
  lit.value[2115U] = 0U;
  lit.value[2116U] = 0U;
  lit.value[2117U] = 0U;
  lit.value[2118U] = 0U;
  lit.value[2119U] = 0U;
  lit.value[2120U] = 0U;
  lit.value[2121U] = 0U;
  lit.value[2122U] = 0U;
  lit.value[2123U] = 0U;
  lit.value[2124U] = 0U;
  lit.value[2125U] = 0U;
  lit.value[2126U] = 0U;
  lit.value[2127U] = 0U;
  lit.value[2128U] = 0U;
  lit.value[2129U] = 0U;
  lit.value[2130U] = 0U;
  lit.value[2131U] = 0U;
  lit.value[2132U] = 0U;
  lit.value[2133U] = 0U;
  lit.value[2134U] = 0U;
  lit.value[2135U] = 0U;
  lit.value[2136U] = 0U;
  lit.value[2137U] = 0U;
  lit.value[2138U] = 0U;
  lit.value[2139U] = 0U;
  lit.value[2140U] = 0U;
  lit.value[2141U] = 0U;
  lit.value[2142U] = 0U;
  lit.value[2143U] = 0U;
  lit.value[2144U] = 0U;
  lit.value[2145U] = 0U;
  lit.value[2146U] = 0U;
  lit.value[2147U] = 0U;
  lit.value[2148U] = 0U;
  lit.value[2149U] = 0U;
  lit.value[2150U] = 0U;
  lit.value[2151U] = 0U;
  lit.value[2152U] = 0U;
  lit.value[2153U] = 0U;
  lit.value[2154U] = 0U;
  lit.value[2155U] = 0U;
  lit.value[2156U] = 0U;
  lit.value[2157U] = 0U;
  lit.value[2158U] = 0U;
  lit.value[2159U] = 0U;
  lit.value[2160U] = 0U;
  lit.value[2161U] = 0U;
  lit.value[2162U] = 0U;
  lit.value[2163U] = 0U;
  lit.value[2164U] = 0U;
  lit.value[2165U] = 0U;
  lit.value[2166U] = 0U;
  lit.value[2167U] = 0U;
  lit.value[2168U] = 0U;
  lit.value[2169U] = 0U;
  lit.value[2170U] = 0U;
  lit.value[2171U] = 0U;
  lit.value[2172U] = 0U;
  lit.value[2173U] = 0U;
  lit.value[2174U] = 0U;
  lit.value[2175U] = 0U;
  lit.value[2176U] = 0U;
  lit.value[2177U] = 0U;
  lit.value[2178U] = 0U;
  lit.value[2179U] = 0U;
  lit.value[2180U] = 0U;
  lit.value[2181U] = 0U;
  lit.value[2182U] = 0U;
  lit.value[2183U] = 0U;
  lit.value[2184U] = 0U;
  lit.value[2185U] = 0U;
  lit.value[2186U] = 0U;
  lit.value[2187U] = 0U;
  lit.value[2188U] = 0U;
  lit.value[2189U] = 0U;
  lit.value[2190U] = 0U;
  lit.value[2191U] = 0U;
  lit.value[2192U] = 0U;
  lit.value[2193U] = 0U;
  lit.value[2194U] = 0U;
  lit.value[2195U] = 0U;
  lit.value[2196U] = 0U;
  lit.value[2197U] = 0U;
  lit.value[2198U] = 0U;
  lit.value[2199U] = 0U;
  lit.value[2200U] = 0U;
  lit.value[2201U] = 0U;
  lit.value[2202U] = 0U;
  lit.value[2203U] = 0U;
  lit.value[2204U] = 0U;
  lit.value[2205U] = 0U;
  lit.value[2206U] = 0U;
  lit.value[2207U] = 0U;
  lit.value[2208U] = 0U;
  lit.value[2209U] = 0U;
  lit.value[2210U] = 0U;
  lit.value[2211U] = 0U;
  lit.value[2212U] = 0U;
  lit.value[2213U] = 0U;
  lit.value[2214U] = 0U;
  lit.value[2215U] = 0U;
  lit.value[2216U] = 0U;
  lit.value[2217U] = 0U;
  lit.value[2218U] = 0U;
  lit.value[2219U] = 0U;
  lit.value[2220U] = 0U;
  lit.value[2221U] = 0U;
  lit.value[2222U] = 0U;
  lit.value[2223U] = 0U;
  lit.value[2224U] = 0U;
  lit.value[2225U] = 0U;
  lit.value[2226U] = 0U;
  lit.value[2227U] = 0U;
  lit.value[2228U] = 0U;
  lit.value[2229U] = 0U;
  lit.value[2230U] = 0U;
  lit.value[2231U] = 0U;
  lit.value[2232U] = 0U;
  lit.value[2233U] = 0U;
  lit.value[2234U] = 0U;
  lit.value[2235U] = 0U;
  lit.value[2236U] = 0U;
  lit.value[2237U] = 0U;
  lit.value[2238U] = 0U;
  lit.value[2239U] = 0U;
  lit.value[2240U] = 0U;
  lit.value[2241U] = 0U;
  lit.value[2242U] = 0U;
  lit.value[2243U] = 0U;
  lit.value[2244U] = 0U;
  lit.value[2245U] = 0U;
  lit.value[2246U] = 0U;
  lit.value[2247U] = 0U;
  lit.value[2248U] = 0U;
  lit.value[2249U] = 0U;
  lit.value[2250U] = 0U;
  lit.value[2251U] = 0U;
  lit.value[2252U] = 0U;
  lit.value[2253U] = 0U;
  lit.value[2254U] = 0U;
  lit.value[2255U] = 0U;
  lit.value[2256U] = 0U;
  lit.value[2257U] = 0U;
  lit.value[2258U] = 0U;
  lit.value[2259U] = 0U;
  lit.value[2260U] = 0U;
  lit.value[2261U] = 0U;
  lit.value[2262U] = 0U;
  lit.value[2263U] = 0U;
  lit.value[2264U] = 0U;
  lit.value[2265U] = 0U;
  lit.value[2266U] = 0U;
  lit.value[2267U] = 0U;
  lit.value[2268U] = 0U;
  lit.value[2269U] = 0U;
  lit.value[2270U] = 0U;
  lit.value[2271U] = 0U;
  lit.value[2272U] = 0U;
  lit.value[2273U] = 0U;
  lit.value[2274U] = 0U;
  lit.value[2275U] = 0U;
  lit.value[2276U] = 0U;
  lit.value[2277U] = 0U;
  lit.value[2278U] = 0U;
  lit.value[2279U] = 0U;
  lit.value[2280U] = 0U;
  lit.value[2281U] = 0U;
  lit.value[2282U] = 0U;
  lit.value[2283U] = 0U;
  lit.value[2284U] = 0U;
  lit.value[2285U] = 0U;
  lit.value[2286U] = 0U;
  lit.value[2287U] = 0U;
  lit.value[2288U] = 0U;
  lit.value[2289U] = 0U;
  lit.value[2290U] = 0U;
  lit.value[2291U] = 0U;
  lit.value[2292U] = 0U;
  lit.value[2293U] = 0U;
  lit.value[2294U] = 0U;
  lit.value[2295U] = 0U;
  lit.value[2296U] = 0U;
  lit.value[2297U] = 0U;
  lit.value[2298U] = 0U;
  lit.value[2299U] = 0U;
  lit.value[2300U] = 0U;
  lit.value[2301U] = 0U;
  lit.value[2302U] = 0U;
  lit.value[2303U] = 0U;
  lit.value[2304U] = 0U;
  lit.value[2305U] = 0U;
  lit.value[2306U] = 0U;
  lit.value[2307U] = 0U;
  lit.value[2308U] = 0U;
  lit.value[2309U] = 0U;
  lit.value[2310U] = 0U;
  lit.value[2311U] = 0U;
  lit.value[2312U] = 0U;
  lit.value[2313U] = 0U;
  lit.value[2314U] = 0U;
  lit.value[2315U] = 0U;
  lit.value[2316U] = 0U;
  lit.value[2317U] = 0U;
  lit.value[2318U] = 0U;
  lit.value[2319U] = 0U;
  lit.value[2320U] = 0U;
  lit.value[2321U] = 0U;
  lit.value[2322U] = 0U;
  lit.value[2323U] = 0U;
  lit.value[2324U] = 0U;
  lit.value[2325U] = 0U;
  lit.value[2326U] = 0U;
  lit.value[2327U] = 0U;
  lit.value[2328U] = 0U;
  lit.value[2329U] = 0U;
  lit.value[2330U] = 0U;
  lit.value[2331U] = 0U;
  lit.value[2332U] = 0U;
  lit.value[2333U] = 0U;
  lit.value[2334U] = 0U;
  lit.value[2335U] = 0U;
  lit.value[2336U] = 0U;
  lit.value[2337U] = 0U;
  lit.value[2338U] = 0U;
  lit.value[2339U] = 0U;
  lit.value[2340U] = 0U;
  lit.value[2341U] = 0U;
  lit.value[2342U] = 0U;
  lit.value[2343U] = 0U;
  lit.value[2344U] = 0U;
  lit.value[2345U] = 0U;
  lit.value[2346U] = 0U;
  lit.value[2347U] = 0U;
  lit.value[2348U] = 0U;
  lit.value[2349U] = 0U;
  lit.value[2350U] = 0U;
  lit.value[2351U] = 0U;
  lit.value[2352U] = 0U;
  lit.value[2353U] = 0U;
  lit.value[2354U] = 0U;
  lit.value[2355U] = 0U;
  lit.value[2356U] = 0U;
  lit.value[2357U] = 0U;
  lit.value[2358U] = 0U;
  lit.value[2359U] = 0U;
  lit.value[2360U] = 0U;
  lit.value[2361U] = 0U;
  lit.value[2362U] = 0U;
  lit.value[2363U] = 0U;
  lit.value[2364U] = 0U;
  lit.value[2365U] = 0U;
  lit.value[2366U] = 0U;
  lit.value[2367U] = 0U;
  lit.value[2368U] = 0U;
  lit.value[2369U] = 0U;
  lit.value[2370U] = 0U;
  lit.value[2371U] = 0U;
  lit.value[2372U] = 0U;
  lit.value[2373U] = 0U;
  lit.value[2374U] = 0U;
  lit.value[2375U] = 0U;
  lit.value[2376U] = 0U;
  lit.value[2377U] = 0U;
  lit.value[2378U] = 0U;
  lit.value[2379U] = 0U;
  lit.value[2380U] = 0U;
  lit.value[2381U] = 0U;
  lit.value[2382U] = 0U;
  lit.value[2383U] = 0U;
  lit.value[2384U] = 0U;
  lit.value[2385U] = 0U;
  lit.value[2386U] = 0U;
  lit.value[2387U] = 0U;
  lit.value[2388U] = 0U;
  lit.value[2389U] = 0U;
  lit.value[2390U] = 0U;
  lit.value[2391U] = 0U;
  lit.value[2392U] = 0U;
  lit.value[2393U] = 0U;
  lit.value[2394U] = 0U;
  lit.value[2395U] = 0U;
  lit.value[2396U] = 0U;
  lit.value[2397U] = 0U;
  lit.value[2398U] = 0U;
  lit.value[2399U] = 0U;
  return lit;
}

typedef struct libcrux_ml_kem_mlkem768_MlKem768Ciphertext_s {
  uint8_t value[1088U];
} libcrux_ml_kem_mlkem768_MlKem768Ciphertext;

/**
 A reference to the raw byte slice.
*/
/**
This function found in impl {libcrux_ml_kem::types::MlKemCiphertext<SIZE>#7}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_slice_07
with const generics
- SIZE= 1088
*/
static inline uint8_t *libcrux_ml_kem_types_as_slice_07_80(
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *self) {
  return self->value;
}

/**
A monomorphic instance of libcrux_ml_kem.types.MlKemPublicKey
with const generics
- $1184size_t
*/
typedef struct libcrux_ml_kem_types_MlKemPublicKey_30_s {
  uint8_t value[1184U];
} libcrux_ml_kem_types_MlKemPublicKey_30;

/**
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemPublicKey<SIZE>)#17}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_40
with const generics
- SIZE= 1184
*/
static inline libcrux_ml_kem_types_MlKemPublicKey_30
libcrux_ml_kem_types_from_40_d0(uint8_t value[1184U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_value[1184U];
  memcpy(copy_of_value, value, (size_t)1184U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemPublicKey_30 lit;
  memcpy(lit.value, copy_of_value, (size_t)1184U * sizeof(uint8_t));
  return lit;
}

typedef struct libcrux_ml_kem_mlkem768_MlKem768KeyPair_s {
  libcrux_ml_kem_types_MlKemPrivateKey_d9 sk;
  libcrux_ml_kem_types_MlKemPublicKey_30 pk;
} libcrux_ml_kem_mlkem768_MlKem768KeyPair;

/**
 Create a new [`MlKemKeyPair`] from the secret and public key.
*/
/**
This function found in impl
{libcrux_ml_kem::types::MlKemKeyPair<PRIVATE_KEY_SIZE, PUBLIC_KEY_SIZE>}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_17
with const generics
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
*/
static inline libcrux_ml_kem_mlkem768_MlKem768KeyPair
libcrux_ml_kem_types_from_17_74(libcrux_ml_kem_types_MlKemPrivateKey_d9 sk,
                                libcrux_ml_kem_types_MlKemPublicKey_30 pk) {
  return (
      CLITERAL(libcrux_ml_kem_mlkem768_MlKem768KeyPair){.sk = sk, .pk = pk});
}

/**
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemPrivateKey<SIZE>)#10}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_88
with const generics
- SIZE= 2400
*/
static inline libcrux_ml_kem_types_MlKemPrivateKey_d9
libcrux_ml_kem_types_from_88_28(uint8_t value[2400U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_value[2400U];
  memcpy(copy_of_value, value, (size_t)2400U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemPrivateKey_d9 lit;
  memcpy(lit.value, copy_of_value, (size_t)2400U * sizeof(uint8_t));
  return lit;
}

/**
A monomorphic instance of core.result.Result
with types uint8_t[32size_t], core_array_TryFromSliceError

*/
typedef struct Result_fb_s {
  Result_a9_tags tag;
  union {
    uint8_t case_Ok[32U];
    TryFromSliceError case_Err;
  } val;
} Result_fb;

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types uint8_t[32size_t], core_array_TryFromSliceError

*/
static inline void unwrap_26_b3(Result_fb self, uint8_t ret[32U]) {
  if (self.tag == Ok) {
    uint8_t f0[32U];
    memcpy(f0, self.val.case_Ok, (size_t)32U * sizeof(uint8_t));
    memcpy(ret, f0, (size_t)32U * sizeof(uint8_t));
  } else {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                      "unwrap not Ok");
    KRML_HOST_EXIT(255U);
  }
}

/**
A monomorphic instance of K.
with types libcrux_ml_kem_types_MlKemCiphertext[[$1088size_t]],
uint8_t[32size_t]

*/
typedef struct tuple_c2_s {
  libcrux_ml_kem_mlkem768_MlKem768Ciphertext fst;
  uint8_t snd[32U];
} tuple_c2;

/**
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemCiphertext<SIZE>)#3}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_fc
with const generics
- SIZE= 1088
*/
static inline libcrux_ml_kem_mlkem768_MlKem768Ciphertext
libcrux_ml_kem_types_from_fc_80(uint8_t value[1088U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_value[1088U];
  memcpy(copy_of_value, value, (size_t)1088U * sizeof(uint8_t));
  libcrux_ml_kem_mlkem768_MlKem768Ciphertext lit;
  memcpy(lit.value, copy_of_value, (size_t)1088U * sizeof(uint8_t));
  return lit;
}

/**
 A reference to the raw byte slice.
*/
/**
This function found in impl {libcrux_ml_kem::types::MlKemPublicKey<SIZE>#21}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_slice_ba
with const generics
- SIZE= 1184
*/
static inline uint8_t *libcrux_ml_kem_types_as_slice_ba_d0(
    libcrux_ml_kem_types_MlKemPublicKey_30 *self) {
  return self->value;
}

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 33
*/
static KRML_MUSTINLINE void libcrux_ml_kem_utils_into_padded_array_c8(
    Eurydice_slice slice, uint8_t ret[33U]) {
  uint8_t out[33U] = {0U};
  uint8_t *uu____0 = out;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice2(uu____0, (size_t)0U,
                                  Eurydice_slice_len(slice, uint8_t), uint8_t),
      slice, uint8_t);
  memcpy(ret, out, (size_t)33U * sizeof(uint8_t));
}

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 34
*/
static KRML_MUSTINLINE void libcrux_ml_kem_utils_into_padded_array_b6(
    Eurydice_slice slice, uint8_t ret[34U]) {
  uint8_t out[34U] = {0U};
  uint8_t *uu____0 = out;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice2(uu____0, (size_t)0U,
                                  Eurydice_slice_len(slice, uint8_t), uint8_t),
      slice, uint8_t);
  memcpy(ret, out, (size_t)34U * sizeof(uint8_t));
}

/**
This function found in impl {(core::convert::AsRef<@Slice<u8>> for
libcrux_ml_kem::types::MlKemCiphertext<SIZE>)#2}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_ref_fd
with const generics
- SIZE= 1088
*/
static inline Eurydice_slice libcrux_ml_kem_types_as_ref_fd_80(
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *self) {
  return Eurydice_array_to_slice((size_t)1088U, self->value, uint8_t);
}

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 1120
*/
static KRML_MUSTINLINE void libcrux_ml_kem_utils_into_padded_array_15(
    Eurydice_slice slice, uint8_t ret[1120U]) {
  uint8_t out[1120U] = {0U};
  uint8_t *uu____0 = out;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice2(uu____0, (size_t)0U,
                                  Eurydice_slice_len(slice, uint8_t), uint8_t),
      slice, uint8_t);
  memcpy(ret, out, (size_t)1120U * sizeof(uint8_t));
}

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 64
*/
static KRML_MUSTINLINE void libcrux_ml_kem_utils_into_padded_array_24(
    Eurydice_slice slice, uint8_t ret[64U]) {
  uint8_t out[64U] = {0U};
  uint8_t *uu____0 = out;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice2(uu____0, (size_t)0U,
                                  Eurydice_slice_len(slice, uint8_t), uint8_t),
      slice, uint8_t);
  memcpy(ret, out, (size_t)64U * sizeof(uint8_t));
}

typedef struct Eurydice_slice_uint8_t_x4_s {
  Eurydice_slice fst;
  Eurydice_slice snd;
  Eurydice_slice thd;
  Eurydice_slice f3;
} Eurydice_slice_uint8_t_x4;

typedef struct Eurydice_slice_uint8_t_x2_s {
  Eurydice_slice fst;
  Eurydice_slice snd;
} Eurydice_slice_uint8_t_x2;

/**
 Unpack an incoming private key into it's different parts.

 We have this here in types to extract into a common core for C.
*/
/**
A monomorphic instance of libcrux_ml_kem.types.unpack_private_key
with const generics
- CPA_SECRET_KEY_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
*/
static inline Eurydice_slice_uint8_t_x4
libcrux_ml_kem_types_unpack_private_key_b4(Eurydice_slice private_key) {
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      private_key, (size_t)1152U, uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice ind_cpa_secret_key = uu____0.fst;
  Eurydice_slice secret_key0 = uu____0.snd;
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      secret_key0, (size_t)1184U, uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice ind_cpa_public_key = uu____1.fst;
  Eurydice_slice secret_key = uu____1.snd;
  Eurydice_slice_uint8_t_x2 uu____2 = Eurydice_slice_split_at(
      secret_key, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice ind_cpa_public_key_hash = uu____2.fst;
  Eurydice_slice implicit_rejection_value = uu____2.snd;
  return (CLITERAL(Eurydice_slice_uint8_t_x4){.fst = ind_cpa_secret_key,
                                              .snd = ind_cpa_public_key,
                                              .thd = ind_cpa_public_key_hash,
                                              .f3 = implicit_rejection_value});
}

/**
A monomorphic instance of core.result.Result
with types int16_t[16size_t], core_array_TryFromSliceError

*/
typedef struct Result_0a_s {
  Result_a9_tags tag;
  union {
    int16_t case_Ok[16U];
    TryFromSliceError case_Err;
  } val;
} Result_0a;

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types int16_t[16size_t], core_array_TryFromSliceError

*/
static inline void unwrap_26_00(Result_0a self, int16_t ret[16U]) {
  if (self.tag == Ok) {
    int16_t f0[16U];
    memcpy(f0, self.val.case_Ok, (size_t)16U * sizeof(int16_t));
    memcpy(ret, f0, (size_t)16U * sizeof(int16_t));
  } else {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                      "unwrap not Ok");
    KRML_HOST_EXIT(255U);
  }
}

/**
A monomorphic instance of core.result.Result
with types uint8_t[8size_t], core_array_TryFromSliceError

*/
typedef struct Result_15_s {
  Result_a9_tags tag;
  union {
    uint8_t case_Ok[8U];
    TryFromSliceError case_Err;
  } val;
} Result_15;

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types uint8_t[8size_t], core_array_TryFromSliceError

*/
static inline void unwrap_26_68(Result_15 self, uint8_t ret[8U]) {
  if (self.tag == Ok) {
    uint8_t f0[8U];
    memcpy(f0, self.val.case_Ok, (size_t)8U * sizeof(uint8_t));
    memcpy(ret, f0, (size_t)8U * sizeof(uint8_t));
  } else {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                      "unwrap not Ok");
    KRML_HOST_EXIT(255U);
  }
}

typedef struct Eurydice_slice_uint8_t_1size_t__x2_s {
  Eurydice_slice fst[1U];
  Eurydice_slice snd[1U];
} Eurydice_slice_uint8_t_1size_t__x2;

#if defined(__cplusplus)
}
#endif

#define __libcrux_core_H_DEFINED
#endif
