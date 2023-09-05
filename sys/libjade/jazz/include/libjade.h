#pragma once

///// SYNC_WITH_UPSTREAM_GENERATE_REF_HEADER_NAMES_START
#include "sha256_ref.h"
#include "sha3_224_ref.h"
///// SYNC_WITH_UPSTREAM_GENERATE_REF_HEADER_NAMES_END
#include "x25519_ref.h"
#include "x25519_mulx.h"
#include "sha3_256_ref.h"
#include "sha3_384_ref.h"
#include "sha3_512_ref.h"
#include "poly1305_ref.h"
#include "chacha20_ref.h"
#include "kyber_kyber768_ref.h"

#ifdef SIMD256
///// SYNC_WITH_UPSTREAM_GENERATE_SIMD256_HEADER_NAMES_START
#include "sha3_224_avx2.h"
///// SYNC_WITH_UPSTREAM_GENERATE_SIMD256_HEADER_NAMES_END
#include "sha3_256_avx2.h"
#include "sha3_384_avx2.h"
#include "sha3_512_avx2.h"
#include "poly1305_avx2.h"
#include "chacha20_avx2.h"
#endif

#ifdef SIMD128
#include "poly1305_avx.h"
#include "chacha20_avx.h"
#endif
