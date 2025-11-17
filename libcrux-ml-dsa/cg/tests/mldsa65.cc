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

Eurydice_borrow_slice_u8 mk_borrow_slice_u8(const uint8_t *x, size_t len) {
  Eurydice_borrow_slice_u8 s;
  s.ptr = x;
  s.meta = len;
  return s;
}


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
    Eurydice_arr_60
 keygen_rand;
    memset(keygen_rand.data, 0x13, 32);

    Eurydice_arr_d10 signing_key;
    Eurydice_arr_4a verification_key;
    libcrux_ml_dsa_ml_dsa_65_portable_generate_key_pair_mut(
        keygen_rand,
        &signing_key,
        &verification_key);

    // Sign
    uint8_t msg[79] = {0};
    Eurydice_arr_60
 sign_rand;
    memset(sign_rand.data, 0x13, 32);
    uint8_t context[3];

    auto msg_slice = mk_borrow_slice_u8((uint8_t*)msg, 79);
    auto context_slice = mk_borrow_slice_u8((uint8_t*)context, 3);
    Eurydice_arr_96 signature;
    auto signature_result = libcrux_ml_dsa_ml_dsa_65_portable_sign_mut(
        &signing_key,
        msg_slice,
        context_slice,
        sign_rand,
        &signature);
    EXPECT_EQ(signature_result.tag, Ok);

    // Verify
    auto result = libcrux_ml_dsa_ml_dsa_65_portable_verify(
        &verification_key,
        msg_slice,
        context_slice,
        &signature);

    EXPECT_EQ(result.tag, Ok);
}

#ifdef LIBCRUX_X64
#include "libcrux_mldsa65_avx2.h"

TEST(MlDsa65TestAvx2, ConsistencyTest)
{
    Eurydice_arr_60
 keygen_rand;
    memset(keygen_rand.data, 0x13, 32);
    auto key_pair = libcrux_ml_dsa_ml_dsa_65_avx2_generate_key_pair(keygen_rand);

    // Sign
    uint8_t msg[79] = {0};
    Eurydice_arr_60
 sign_rand;
    memset(sign_rand.data, 0x13, 32);
    uint8_t context[3];

    auto msg_slice = mk_borrow_slice_u8((uint8_t*)msg, 79);
    auto context_slice = mk_borrow_slice_u8((uint8_t*)context, 3);
    auto signature_result = libcrux_ml_dsa_ml_dsa_65_avx2_sign(
        &key_pair.signing_key, msg_slice,
        context_slice,
        sign_rand);
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
