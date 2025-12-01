#ifndef JADE_KEM_KYBER_KYBER768_AMD64_REF_API_H
#define JADE_KEM_KYBER_KYBER768_AMD64_REF_API_H

#include <stdint.h>

#define JADE_KEM_KYBER_KYBER768_AMD64_REF_SECRETKEYBYTES   2400
#define JADE_KEM_KYBER_KYBER768_AMD64_REF_PUBLICKEYBYTES   1184
#define JADE_KEM_KYBER_KYBER768_AMD64_REF_CIPHERTEXTBYTES  1088
#define JADE_KEM_KYBER_KYBER768_AMD64_REF_KEYPAIRCOINBYTES 64
#define JADE_KEM_KYBER_KYBER768_AMD64_REF_ENCCOINBYTES     32
#define JADE_KEM_KYBER_KYBER768_AMD64_REF_BYTES            32

#define JADE_KEM_KYBER_KYBER768_AMD64_REF_ALGNAME         "Kyber768"

int jade_kem_kyber_kyber768_amd64_ref_keypair_derand(
  uint8_t *public_key,
  uint8_t *secret_key,
  const uint8_t *coins
);

int jade_kem_kyber_kyber768_amd64_ref_enc_derand(
  uint8_t *ciphertext,
  uint8_t *shared_secret,
  const uint8_t *public_key,
  const uint8_t *coins
);

int jade_kem_kyber_kyber768_amd64_ref_dec(
  uint8_t *shared_secret,
  const uint8_t *ciphertext,
  const uint8_t *secret_key
);

#endif
