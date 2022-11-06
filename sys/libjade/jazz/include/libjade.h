#pragma once

#include "sha256.h"
#include "x25519_ref.h"
#include "x25519_mulx.h"
#include "sha3_224_ref.h"
#include "sha3_256_ref.h"
#include "sha3_384_ref.h"
#include "sha3_512_ref.h"

#ifdef SIMD256
#include "sha3_224_avx2.h"
#include "sha3_256_avx2.h"
#include "sha3_384_avx2.h"
#include "sha3_512_avx2.h"
#endif
