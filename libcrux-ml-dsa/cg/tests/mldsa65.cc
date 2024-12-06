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
    uint8_t context[0];
    auto ctxt = libcrux_ml_dsa_ml_dsa_65_portable_sign(
        &key_pair.signing_key,
        mk_slice(&msg, 79),
        mk_slice(&context, 0),
        randomness);

    // // Verify
    // uint8_t sharedSecret2[LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE];
    // libcrux_ml_kem_mlkem768_portable_decapsulate(&key_pair.sk, &ctxt.fst, sharedSecret2);

    // EXPECT_EQ(0,
    //           memcmp(ctxt.snd,
    //                  sharedSecret2,
    //                  LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE));
}
