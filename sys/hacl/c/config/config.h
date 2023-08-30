#pragma once

#if defined(SIMD128) && !defined(HACL_CAN_COMPILE_VEC128)
#define HACL_CAN_COMPILE_VEC128 1
#endif

#if defined(SIMD256) && !defined(HACL_CAN_COMPILE_VEC256)
#define HACL_CAN_COMPILE_VEC256 1
#endif

#if defined(__x86_64__) || defined(_M_X64)
// We always assume inline assembly for now
#define HACL_CAN_COMPILE_INLINE_ASM 1
#include "Hacl_Curve25519_64.h"
#endif
