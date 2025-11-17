#ifndef JADE_HASH_SHA3_256_AMD64_AVX2_API_H
#define JADE_HASH_SHA3_256_AMD64_AVX2_API_H

#define JADE_HASH_SHA3_256_AMD64_AVX2_BYTES 32
#define JADE_HASH_SHA3_256_AMD64_AVX2_ALGNAME "SHA3-256"

#include <stdint.h>

int jade_hash_sha3_256_amd64_avx2(
 uint8_t *out,
 uint8_t *in,
 uint64_t length
);

#endif
