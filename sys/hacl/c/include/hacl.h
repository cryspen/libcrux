/*
 * Meta header to include all the main header files we care about.
 */
// #pragma once

#if defined(SIMD128) && !defined(HACL_CAN_COMPILE_VEC128)
#define HACL_CAN_COMPILE_VEC128 1
#endif

#if defined(SIMD256) && !defined(HACL_CAN_COMPILE_VEC256)
#define HACL_CAN_COMPILE_VEC256 1
#endif

#include "Hacl_Chacha20Poly1305_32.h"
#include "Hacl_Curve25519_51.h"
#include "Hacl_Hash_SHA2.h"
#include "Hacl_Streaming_SHA2.h"
#include "Hacl_SHA3.h"
#include "Hacl_Streaming_SHA3.h"

#if defined(__x86_64__) || defined(_M_X64)
// We always asume inline assembly for now
#define HACL_CAN_COMPILE_INLINE_ASM 1
#include "Hacl_Curve25519_64.h"
#endif

#ifdef SIMD128
#include "Hacl_Chacha20Poly1305_128.h"
#endif

#ifdef SIMD256
#include "Hacl_Chacha20Poly1305_256.h"
#endif
