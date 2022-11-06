/*
 * Meta header to include all the main header files we care about.
 */
#pragma once

#include "config.h"

#include "Hacl_Chacha20Poly1305_32.h"
#include "Hacl_Curve25519_51.h"
#include "Hacl_Hash_SHA2.h"
#include "Hacl_Streaming_SHA2.h"
#include "Hacl_SHA3.h"
#include "Hacl_Streaming_SHA3.h"


#ifdef SIMD128
#include "Hacl_Chacha20Poly1305_128.h"
#endif

#ifdef SIMD256
#include "Hacl_Chacha20Poly1305_256.h"
#endif
