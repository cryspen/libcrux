#ifndef JADE_HASH_SHA3_224_AMD64_REF_API_H
#define JADE_HASH_SHA3_224_AMD64_REF_API_H

#define JADE_HASH_SHA3_224_AMD64_REF_BYTES 28
#define JADE_HASH_SHA3_224_AMD64_REF_ALGNAME "SHA3-224"

#include <stdint.h>

int jade_hash_sha3_224_amd64_ref(
 uint8_t *hash,
 const uint8_t *input,
 uint64_t input_length
);

#endif
