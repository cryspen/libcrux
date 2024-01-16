/*
 * Meta header to include all the header files for SIMD 256 we care about.
 */
#pragma once

#include "config.h"
#define HACL_CAN_COMPILE_VEC256 1

#include "Hacl_AEAD_Chacha20Poly1305_Simd256.h"
#include "Hacl_Hash_Blake2b_Simd256.h"
#include "Hacl_Hash_SHA3_Simd256.h"
