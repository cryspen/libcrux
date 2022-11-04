#ifndef JADE_HASH_SHA256_AMD64_REF_API_H
#define JADE_HASH_SHA256_AMD64_REF_API_H

#define JADE_HASH_SHA256_AMD64_REF_BYTES 32
#define JADE_HASH_SHA256_AMD64_REF_ALGNAME "SHA256"

#include <stdint.h>

int jade_hash_sha256_amd64_ref(
 uint8_t *out,
 uint8_t *in,
 uint64_t length
);

#endif
