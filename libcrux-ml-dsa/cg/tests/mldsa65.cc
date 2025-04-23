/*
 *    Copyright 2023 Cryspen Sarl
 *
 *    Licensed under the Apache License, Version 2.0 or MIT.
 *    - http://www.apache.org/licenses/LICENSE-2.0
 *    - http://opensource.org/licenses/MIT
 */

#include <gtest/gtest.h>
#include <vector>

#include "libcrux_mldsa65_portable.h"

using namespace std;

typedef vector<uint8_t> bytes;

template <typename T>
Eurydice_slice mk_slice(T *x, size_t len)
{
    Eurydice_slice s;
    s.ptr = (void *)x;
    s.len = len;
    return s;
}

TEST(MlDsa65TestPortable, ConsistencyTest)
{
    // Generate key pair
    uint8_t randomness[32];
    for (int i = 0; i < 32; i++)
    {
        randomness[i] = 13;
    }

    bytes signing_key(LIBCRUX_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_SIGNING_KEY_SIZE);
    bytes verification_key(LIBCRUX_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_VERIFICATION_KEY_SIZE);
    libcrux_ml_dsa_ml_dsa_65_portable_generate_key_pair_mut(
        randomness,
        signing_key.data(),
        verification_key.data());

    // Sign
    uint8_t msg[79] = {0};
    for (int i = 0; i < 32; i++)
    {
        randomness[i] = 0x55;
    }
    uint8_t context[3];

    auto msg_slice = mk_slice(&msg, 79);
    auto context_slice = mk_slice(&context, 3);
    bytes signature(LIBCRUX_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_SIGNATURE_SIZE);
    auto signature_result = libcrux_ml_dsa_ml_dsa_65_portable_sign_mut(
        signing_key.data(),
        msg_slice,
        context_slice,
        randomness,
        signature.data());
    EXPECT_EQ(signature_result.tag, Ok);

    // Verify
    // XXX: Make better APIs so we don't have to copy the values here.
    libcrux_ml_dsa_ml_dsa_generic_ml_dsa_65_MLDSA65VerificationKey verification_key_struct;
    memcpy(verification_key_struct.value, verification_key.data(), verification_key.size());
    libcrux_ml_dsa_ml_dsa_generic_ml_dsa_65_MLDSA65Signature signature_struct;
    memcpy(signature_struct.value, signature.data(), signature.size());

    auto result = libcrux_ml_dsa_ml_dsa_65_portable_verify(
        &verification_key_struct,
        msg_slice,
        context_slice,
        &signature_struct);

    EXPECT_EQ(result.tag, Ok);
}

#ifdef LIBCRUX_X64
#include "libcrux_mldsa65_avx2.h"

TEST(MlDsa65TestAvx2, ConsistencyTest)
{
    // Generate key pair
    uint8_t randomness[32];
    for (int i = 0; i < 32; i++)
    {
        randomness[i] = 13;
    }
    auto key_pair = libcrux_ml_dsa_ml_dsa_65_avx2_generate_key_pair(randomness);

    // Sign
    uint8_t msg[79] = {0};
    for (int i = 0; i < 32; i++)
    {
        randomness[i] = 0x55;
    }
    uint8_t context[3];

    auto msg_slice = mk_slice(&msg, 79);
    auto context_slice = mk_slice(&context, 3);
    auto signature_result = libcrux_ml_dsa_ml_dsa_65_avx2_sign(
        &key_pair.signing_key, msg_slice,
        context_slice,
        randomness);
    EXPECT_EQ(signature_result.tag, Ok);
    auto signature = signature_result.val.case_Ok;

    // Verify
    auto result = libcrux_ml_dsa_ml_dsa_65_avx2_verify(
        &key_pair.verification_key,
        msg_slice,
        context_slice,
        &signature);

    EXPECT_EQ(result.tag, Ok);
}
#endif // LIBCRUX_X64
