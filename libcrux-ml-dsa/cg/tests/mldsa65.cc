/*
 *    Copyright 2023 Cryspen Sarl
 *
 *    Licensed under the Apache License, Version 2.0 or MIT.
 *    - http://www.apache.org/licenses/LICENSE-2.0
 *    - http://opensource.org/licenses/MIT
 */

#include <gtest/gtest.h>

#include "libcrux_mldsa65_portable.h"

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
    auto key_pair = libcrux_ml_dsa_ml_dsa_65_portable_generate_key_pair(randomness);

    // Sign
    uint8_t msg[79] = {0};
    for (int i = 0; i < 32; i++)
    {
        randomness[i] = 0x55;
    }
    uint8_t context[3];

    auto msg_slice = mk_slice(&msg, 79);
    auto context_slice = mk_slice(&context, 3);
    auto signature_result = libcrux_ml_dsa_ml_dsa_65_portable_sign(
        &key_pair.signing_key, msg_slice,
        context_slice,
        randomness);
    EXPECT_EQ(signature_result.tag, Ok);
    auto signature = signature_result.val.case_Ok;

    // Verify
    auto result = libcrux_ml_dsa_ml_dsa_65_portable_verify(
        &key_pair.verification_key,
        msg_slice,
        context_slice,
        &signature);

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
