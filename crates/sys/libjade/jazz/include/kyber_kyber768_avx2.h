#ifndef JADE_KEM_kyber_kyber768_amd64_avx2_API_H
#define JADE_KEM_kyber_kyber768_amd64_avx2_API_H

#if defined(__cplusplus)
extern "C"
{
#endif

#include <stdint.h>

#define JADE_KEM_kyber_kyber768_amd64_avx2_SECRETKEYBYTES    2400
#define JADE_KEM_kyber_kyber768_amd64_avx2_PUBLICKEYBYTES    1184
#define JADE_KEM_kyber_kyber768_amd64_avx2_CIPHERTEXTBYTES   1088
#define JADE_KEM_kyber_kyber768_amd64_avx2_KEYPAIRCOINBYTES  64
#define JADE_KEM_kyber_kyber768_amd64_avx2_ENCCOINBYTES      32
#define JADE_KEM_kyber_kyber768_amd64_avx2_BYTES             32

#define JADE_KEM_kyber_kyber768_amd64_avx2_ALGNAME           "Kyber768"
#define JADE_KEM_kyber_kyber768_amd64_avx2_ARCH              "amd64"
#define JADE_KEM_kyber_kyber768_amd64_avx2_IMPL              "avx2"

int jade_kem_kyber_kyber768_amd64_avx2_keypair_derand(
  uint8_t *public_key,
  uint8_t *secret_key,
  const uint8_t *coins
);

int jade_kem_kyber_kyber768_amd64_avx2_keypair(
  uint8_t *public_key,
  uint8_t *secret_key
);

int jade_kem_kyber_kyber768_amd64_avx2_enc_derand(
  uint8_t *ciphertext,
  uint8_t *shared_secret,
  const uint8_t *public_key,
  const uint8_t *coins
);

int jade_kem_kyber_kyber768_amd64_avx2_enc(
  uint8_t *ciphertext,
  uint8_t *shared_secret,
  const uint8_t *public_key
);

int jade_kem_kyber_kyber768_amd64_avx2_dec(
  uint8_t *shared_secret,
  const uint8_t *ciphertext,
  const uint8_t *secret_key
);

#if defined(__cplusplus)
}
#endif

#endif
