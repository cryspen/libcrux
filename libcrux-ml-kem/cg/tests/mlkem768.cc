/*
 *    Copyright 2023 Cryspen Sarl
 *
 *    Licensed under the Apache License, Version 2.0 or MIT.
 *    - http://www.apache.org/licenses/LICENSE-2.0
 *    - http://opensource.org/licenses/MIT
 */

#include "util.h"

void modify_ciphertext(uint8_t *ciphertext, size_t ciphertext_size)
{
    uint8_t randomness[3];
    generate_random(randomness, 3);

    uint8_t random_byte = randomness[0];
    if (random_byte == 0)
    {
        random_byte += 1;
    }

    uint16_t random_u16 = (randomness[2] << 8) | randomness[1];

    uint16_t random_position = random_u16 % ciphertext_size;

    ciphertext[random_position] ^= random_byte;
}

void modify_secret_key(uint8_t *secret_key,
                       size_t secret_key_size,
                       bool modify_implicit_rejection_value)
{
    uint8_t randomness[3];
    generate_random(randomness, 3);

    uint8_t random_byte = randomness[0];
    if (random_byte == 0)
    {
        random_byte += 1;
    }

    uint16_t random_u16 = (randomness[2] << 8) | randomness[1];

    uint16_t random_position = 0;

    if (modify_implicit_rejection_value == true)
    {
        random_position = (secret_key_size - 32) + (random_u16 % 32);
    }
    else
    {
        random_position = random_u16 % (secret_key_size - 32);
    }

    secret_key[random_position] ^= random_byte;
}

uint8_t *
compute_implicit_rejection_shared_secret(uint8_t *ciphertext,
                                         size_t ciphertext_size,
                                         uint8_t *secret_key,
                                         size_t secret_key_size)
{
    uint8_t *hashInput = new uint8_t[32 + ciphertext_size];
    uint8_t *sharedSecret = new uint8_t[32];
    Eurydice_slice ss;
    ss.ptr = (void *)sharedSecret;
    ss.len = 32;

    std::copy(secret_key + (secret_key_size - 32),
              secret_key + secret_key_size,
              hashInput);
    std::copy(ciphertext, ciphertext + ciphertext_size, hashInput + 32);

    libcrux_sha3_portable_shake256(ss, mk_slice(hashInput, 32 + ciphertext_size));

    delete[] hashInput;
    return sharedSecret;
}

TEST(MlKem768TestPortable, ConsistencyTest)
{
    uint8_t randomness[64];
    for (int i = 0; i < 64; i++)
    {
        randomness[i] = 13;
    }
    auto key_pair = libcrux_ml_kem_mlkem768_portable_generate_key_pair(randomness);

    auto ctxt = libcrux_ml_kem_mlkem768_portable_encapsulate(&key_pair.pk, randomness);

    uint8_t sharedSecret2[LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE];
    libcrux_ml_kem_mlkem768_portable_decapsulate(&key_pair.sk, &ctxt.fst, sharedSecret2);

    EXPECT_EQ(0,
              memcmp(ctxt.snd,
                     sharedSecret2,
                     LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE));
}

TEST(MlKem768TestPortableUnpacked, ConsistencyTest)
{
    uint8_t keygen_randomness[64];
    for (int i = 0; i < 64; i++)
    {
        keygen_randomness[i] = 13;
    }
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked key_pair = libcrux_ml_kem_mlkem768_portable_unpacked_init_key_pair() ;
    libcrux_ml_kem_mlkem768_portable_unpacked_generate_key_pair(keygen_randomness, &key_pair);

    uint8_t encap_randomness[32];
    for (int i = 0; i < 32; i++)
    {
        encap_randomness[i] = 15;
    }
    auto ctxt = libcrux_ml_kem_mlkem768_portable_unpacked_encapsulate(&key_pair.public_key, encap_randomness);

    uint8_t sharedSecret2[LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE];
    libcrux_ml_kem_mlkem768_portable_unpacked_decapsulate(&key_pair, &ctxt.fst, sharedSecret2);

    EXPECT_EQ(0,
              memcmp(ctxt.snd,
                     sharedSecret2,
                     LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE));
}

TEST(Kyber768TestPortable, ModifiedCiphertextTest)
{
    uint8_t randomness[64];
    generate_random(randomness, 64);
    auto key_pair = libcrux_ml_kem_mlkem768_portable_generate_key_pair(randomness);

    generate_random(randomness, 32);
    auto ctxt = libcrux_ml_kem_mlkem768_portable_encapsulate(&key_pair.pk, randomness);

    uint8_t sharedSecret2[LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE];
    modify_ciphertext(ctxt.fst.value,
                      LIBCRUX_ML_KEM_MLKEM768_CPA_PKE_CIPHERTEXT_SIZE_768);
    libcrux_ml_kem_mlkem768_portable_decapsulate(&key_pair.sk, &ctxt.fst, sharedSecret2);

    EXPECT_NE(0,
              memcmp(ctxt.snd,
                     sharedSecret2,
                     LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE));

    uint8_t *implicitRejectionSharedSecret =
        compute_implicit_rejection_shared_secret(
            ctxt.fst.value,
            LIBCRUX_ML_KEM_MLKEM768_CPA_PKE_CIPHERTEXT_SIZE_768,
            key_pair.sk.value,
            LIBCRUX_ML_KEM_MLKEM768_SECRET_KEY_SIZE_768);

    EXPECT_EQ(0,
              memcmp(implicitRejectionSharedSecret,
                     sharedSecret2,
                     LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE));
    delete[] implicitRejectionSharedSecret;
}

TEST(Kyber768TestPortable, ModifiedSecretKeyTest)
{
    uint8_t randomness[64];
    generate_random(randomness, 64);
    auto key_pair = libcrux_ml_kem_mlkem768_portable_generate_key_pair(randomness);

    generate_random(randomness, 32);
    auto ctxt = libcrux_ml_kem_mlkem768_portable_encapsulate(&key_pair.pk, randomness);

    uint8_t sharedSecret2[LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE];
    modify_secret_key(
        key_pair.sk.value, LIBCRUX_ML_KEM_MLKEM768_SECRET_KEY_SIZE_768, false);
    libcrux_ml_kem_mlkem768_portable_decapsulate(&key_pair.sk, &ctxt.fst, sharedSecret2);

    EXPECT_NE(0,
              memcmp(ctxt.snd,
                     sharedSecret2,
                     LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE));

    modify_secret_key(
        ctxt.snd, LIBCRUX_ML_KEM_MLKEM768_SECRET_KEY_SIZE_768, true);
    libcrux_ml_kem_mlkem768_portable_decapsulate(&key_pair.sk, &ctxt.fst, sharedSecret2);

    uint8_t *implicitRejectionSharedSecret =
        compute_implicit_rejection_shared_secret(
            ctxt.fst.value,
            LIBCRUX_ML_KEM_MLKEM768_CPA_PKE_CIPHERTEXT_SIZE_768,
            key_pair.sk.value,
            LIBCRUX_ML_KEM_MLKEM768_SECRET_KEY_SIZE_768);
    EXPECT_EQ(0,
              memcmp(implicitRejectionSharedSecret,
                     sharedSecret2,
                     LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE));
    delete[] implicitRejectionSharedSecret;
}

TEST(MlKem768TestPortable, NISTKnownAnswerTest)
{
    // XXX: This should be done in a portable way.
    auto kats = read_kats("tests/mlkem768_nistkats.json");

    for (auto kat : kats)
    {
        auto key_pair =
            libcrux_ml_kem_mlkem768_portable_generate_key_pair(kat.key_generation_seed.data());

        uint8_t pk_hash[32];
        libcrux_sha3_sha256(
            mk_slice(key_pair.pk.value,
                     LIBCRUX_ML_KEM_MLKEM768_CPA_PKE_PUBLIC_KEY_SIZE_768),
            pk_hash);
        EXPECT_EQ(0, memcmp(pk_hash, kat.sha3_256_hash_of_public_key.data(), 32));

        uint8_t sk_hash[32];
        libcrux_sha3_sha256(
            mk_slice(key_pair.sk.value, LIBCRUX_ML_KEM_MLKEM768_SECRET_KEY_SIZE_768), sk_hash);
        EXPECT_EQ(0, memcmp(sk_hash, kat.sha3_256_hash_of_secret_key.data(), 32));

        auto ctxt = libcrux_ml_kem_mlkem768_portable_encapsulate(
            &key_pair.pk, kat.encapsulation_seed.data());
        uint8_t ct_hash[32];
        libcrux_sha3_sha256(
            mk_slice(ctxt.fst.value,
                     LIBCRUX_ML_KEM_MLKEM768_CPA_PKE_CIPHERTEXT_SIZE_768),
            ct_hash);
        EXPECT_EQ(0, memcmp(ct_hash, kat.sha3_256_hash_of_ciphertext.data(), 32));
        EXPECT_EQ(0,
                  memcmp(ctxt.snd,
                         kat.shared_secret.data(),
                         LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE));

        uint8_t sharedSecret2[LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE];
        libcrux_ml_kem_mlkem768_portable_decapsulate(&key_pair.sk, &ctxt.fst, sharedSecret2);

        EXPECT_EQ(0,
                  memcmp(ctxt.snd,
                         sharedSecret2,
                         LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE));
    }
}

#ifdef LIBCRUX_X64
#include "libcrux_mlkem768_avx2.h"

TEST(MlKem768TestAvx2, ConsistencyTest)
{
    uint8_t randomness[64];
    for (int i = 0; i < 64; i++)
        randomness[i] = 13;
    auto key_pair = libcrux_ml_kem_mlkem768_avx2_generate_key_pair(randomness);
    auto ctxt = libcrux_ml_kem_mlkem768_avx2_encapsulate(&key_pair.pk, randomness);

    uint8_t sharedSecret2[LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE];
    libcrux_ml_kem_mlkem768_avx2_decapsulate(&key_pair.sk, &ctxt.fst, sharedSecret2);

    EXPECT_EQ(0,
              memcmp(ctxt.snd,
                     sharedSecret2,
                     LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE));
}

TEST(MlKem768TestAvx2Unpacked, ConsistencyTest)
{
    uint8_t keygen_randomness[64];
    for (int i = 0; i < 64; i++)
    {
        keygen_randomness[i] = 13;
    }
    libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked key_pair = libcrux_ml_kem_mlkem768_avx2_unpacked_init_key_pair() ;
    libcrux_ml_kem_mlkem768_avx2_unpacked_generate_key_pair(keygen_randomness, &key_pair);

    uint8_t encap_randomness[32];
    for (int i = 0; i < 32; i++)
    {
        encap_randomness[i] = 15;
    }
    auto ctxt = libcrux_ml_kem_mlkem768_avx2_unpacked_encapsulate(&key_pair.public_key, encap_randomness);

    uint8_t sharedSecret2[LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE];
    libcrux_ml_kem_mlkem768_avx2_unpacked_decapsulate(&key_pair, &ctxt.fst, sharedSecret2);

    EXPECT_EQ(0,
              memcmp(ctxt.snd,
                     sharedSecret2,
                     LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE));
}

TEST(Kyber768TestAvx2, ModifiedCiphertextTest)
{
    uint8_t randomness[64];
    generate_random(randomness, 64);
    auto key_pair = libcrux_ml_kem_mlkem768_avx2_generate_key_pair(randomness);

    generate_random(randomness, 32);
    auto ctxt = libcrux_ml_kem_mlkem768_avx2_encapsulate(&key_pair.pk, randomness);

    uint8_t sharedSecret2[LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE];
    modify_ciphertext(ctxt.fst.value,
                      LIBCRUX_ML_KEM_MLKEM768_CPA_PKE_CIPHERTEXT_SIZE_768);
    libcrux_ml_kem_mlkem768_avx2_decapsulate(&key_pair.sk, &ctxt.fst, sharedSecret2);

    EXPECT_NE(0,
              memcmp(ctxt.snd,
                     sharedSecret2,
                     LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE));

    uint8_t *implicitRejectionSharedSecret =
        compute_implicit_rejection_shared_secret(
            ctxt.fst.value,
            LIBCRUX_ML_KEM_MLKEM768_CPA_PKE_CIPHERTEXT_SIZE_768,
            key_pair.sk.value,
            LIBCRUX_ML_KEM_MLKEM768_SECRET_KEY_SIZE_768);

    EXPECT_EQ(0,
              memcmp(implicitRejectionSharedSecret,
                     sharedSecret2,
                     LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE));
    delete[] implicitRejectionSharedSecret;
}

TEST(Kyber768TestAvx2, ModifiedSecretKeyTest)
{
    uint8_t randomness[64];
    generate_random(randomness, 64);
    auto key_pair = libcrux_ml_kem_mlkem768_avx2_generate_key_pair(randomness);

    generate_random(randomness, 32);
    auto ctxt = libcrux_ml_kem_mlkem768_avx2_encapsulate(&key_pair.pk, randomness);

    uint8_t sharedSecret2[LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE];
    modify_secret_key(
        key_pair.sk.value, LIBCRUX_ML_KEM_MLKEM768_SECRET_KEY_SIZE_768, false);
    libcrux_ml_kem_mlkem768_avx2_decapsulate(&key_pair.sk, &ctxt.fst, sharedSecret2);

    EXPECT_NE(0,
              memcmp(ctxt.snd,
                     sharedSecret2,
                     LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE));

    modify_secret_key(
        ctxt.snd, LIBCRUX_ML_KEM_MLKEM768_SECRET_KEY_SIZE_768, true);
    libcrux_ml_kem_mlkem768_avx2_decapsulate(&key_pair.sk, &ctxt.fst, sharedSecret2);

    uint8_t *implicitRejectionSharedSecret =
        compute_implicit_rejection_shared_secret(
            ctxt.fst.value,
            LIBCRUX_ML_KEM_MLKEM768_CPA_PKE_CIPHERTEXT_SIZE_768,
            key_pair.sk.value,
            LIBCRUX_ML_KEM_MLKEM768_SECRET_KEY_SIZE_768);
    EXPECT_EQ(0,
              memcmp(implicitRejectionSharedSecret,
                     sharedSecret2,
                     LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE));
    delete[] implicitRejectionSharedSecret;
}

TEST(MlKem768TestAvx2, NISTKnownAnswerTest)
{
    // XXX: This should be done in a portable way.
    auto kats = read_kats("tests/mlkem768_nistkats.json");

    for (auto kat : kats)
    {
        auto key_pair = libcrux_ml_kem_mlkem768_avx2_generate_key_pair(kat.key_generation_seed.data());

        uint8_t pk_hash[32];
        libcrux_sha3_sha256(
            mk_slice(key_pair.pk.value,
                     LIBCRUX_ML_KEM_MLKEM768_CPA_PKE_PUBLIC_KEY_SIZE_768),
            pk_hash);
        EXPECT_EQ(0, memcmp(pk_hash, kat.sha3_256_hash_of_public_key.data(), 32));

        uint8_t sk_hash[32];
        libcrux_sha3_sha256(
            mk_slice(key_pair.sk.value, LIBCRUX_ML_KEM_MLKEM768_SECRET_KEY_SIZE_768), sk_hash);
        EXPECT_EQ(0, memcmp(sk_hash, kat.sha3_256_hash_of_secret_key.data(), 32));

        auto ctxt = libcrux_ml_kem_mlkem768_avx2_encapsulate(
            &key_pair.pk, kat.encapsulation_seed.data());
        uint8_t ct_hash[32];
        libcrux_sha3_sha256(
            mk_slice(ctxt.fst.value,
                     LIBCRUX_ML_KEM_MLKEM768_CPA_PKE_CIPHERTEXT_SIZE_768),
            ct_hash);
        EXPECT_EQ(0, memcmp(ct_hash, kat.sha3_256_hash_of_ciphertext.data(), 32));
        EXPECT_EQ(0,
                  memcmp(ctxt.snd,
                         kat.shared_secret.data(),
                         LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE));

        uint8_t sharedSecret2[LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE];
        libcrux_ml_kem_mlkem768_avx2_decapsulate(&key_pair.sk, &ctxt.fst, sharedSecret2);

        EXPECT_EQ(0,
                  memcmp(ctxt.snd,
                         sharedSecret2,
                         LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE));
    }
}
#endif // LIBCRUX_X64

#ifdef LIBCRUX_AARCH64
#include "libcrux_mlkem768_neon.h"

TEST(MlKem768TestNeon, ConsistencyTest)
{
    uint8_t randomness[64];
    for (int i = 0; i < 64; i++)
        randomness[i] = 13;
    auto key_pair = libcrux_ml_kem_mlkem768_neon_generate_key_pair(randomness);
    auto ctxt = libcrux_ml_kem_mlkem768_neon_encapsulate(&key_pair.pk, randomness);

    uint8_t sharedSecret2[LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE];
    libcrux_ml_kem_mlkem768_neon_decapsulate(&key_pair.sk, &ctxt.fst, sharedSecret2);

    EXPECT_EQ(0,
              memcmp(ctxt.snd,
                     sharedSecret2,
                     LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE));
}

TEST(MlKem768TestNeon, NISTKnownAnswerTest)
{
    // XXX: This should be done in a portable way.
    auto kats = read_kats("tests/mlkem768_nistkats.json");

    for (auto kat : kats)
    {
        auto key_pair = libcrux_ml_kem_mlkem768_neon_generate_key_pair(kat.key_generation_seed.data());

        uint8_t pk_hash[32];
        libcrux_sha3_sha256(
            mk_slice(key_pair.pk.value,
                     LIBCRUX_ML_KEM_MLKEM768_CPA_PKE_PUBLIC_KEY_SIZE_768),
            pk_hash);
        EXPECT_EQ(0, memcmp(pk_hash, kat.sha3_256_hash_of_public_key.data(), 32));

        uint8_t sk_hash[32];
        libcrux_sha3_sha256(
            mk_slice(key_pair.sk.value, LIBCRUX_ML_KEM_MLKEM768_SECRET_KEY_SIZE_768), sk_hash);
        EXPECT_EQ(0, memcmp(sk_hash, kat.sha3_256_hash_of_secret_key.data(), 32));

        auto ctxt = libcrux_ml_kem_mlkem768_neon_encapsulate(
            &key_pair.pk, kat.encapsulation_seed.data());
        uint8_t ct_hash[32];
        libcrux_sha3_sha256(
            mk_slice(ctxt.fst.value,
                     LIBCRUX_ML_KEM_MLKEM768_CPA_PKE_CIPHERTEXT_SIZE_768),
            ct_hash);
        EXPECT_EQ(0, memcmp(ct_hash, kat.sha3_256_hash_of_ciphertext.data(), 32));
        EXPECT_EQ(0,
                  memcmp(ctxt.snd,
                         kat.shared_secret.data(),
                         LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE));

        uint8_t sharedSecret2[LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE];
        libcrux_ml_kem_mlkem768_neon_decapsulate(&key_pair.sk, &ctxt.fst, sharedSecret2);

        EXPECT_EQ(0,
                  memcmp(ctxt.snd,
                         sharedSecret2,
                         LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE));
    }
}
#endif // LIBCRUX_AARCH64
