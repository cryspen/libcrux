/*
 * Meta header to include all the main header files we care about.
 */
#pragma once

#include "Hacl_Chacha20Poly1305_32.h"

#ifdef SIMD128
#define HACL_CAN_COMPILE_VEC128 1
#include "Hacl_Chacha20Poly1305_128.h"
#endif

#ifdef SIMD256
#define HACL_CAN_COMPILE_VEC256 1
#include "Hacl_Chacha20Poly1305_256.h"
#endif
