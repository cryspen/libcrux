/*
 *    Copyright 2026 CE Labs
 *
 *    Licensed under the Apache License, Version 2.0 or MIT.
 *    - http://www.apache.org/licenses/LICENSE-2.0
 *    - http://opensource.org/licenses/MIT
 */

// Single source file for all ML-DSA sizes. Each test binary is built from
// this file with MLDSA_VARIANT defined to 44, 65, or 87 (see
// CMakeLists.txt), which selects the right headers, key/signature sizes, and,
// via the MLDSA_* macros below, the right variant-specific symbol names.

#include <gtest/gtest.h>

#include <fstream>
#include <nlohmann/json.hpp>
#include <vector>

#ifndef MLDSA_VARIANT
#error "MLDSA_VARIANT must be defined to 44, 65, or 87"
#endif

#if MLDSA_VARIANT == 44
#include "libcrux_mldsa44_portable.h"
#define MLDSA_VERIFICATION_KEY_SIZE 1312U
#define MLDSA_SIGNING_KEY_SIZE 2560U
#define MLDSA_SIGNATURE_SIZE 2420U
#elif MLDSA_VARIANT == 65
#include "libcrux_mldsa65_portable.h"
#define MLDSA_VERIFICATION_KEY_SIZE 1952U
#define MLDSA_SIGNING_KEY_SIZE 4032U
#define MLDSA_SIGNATURE_SIZE 3309U
#elif MLDSA_VARIANT == 87
#include "libcrux_mldsa87_portable.h"
#define MLDSA_VERIFICATION_KEY_SIZE 2592U
#define MLDSA_SIGNING_KEY_SIZE 4896U
#define MLDSA_SIGNATURE_SIZE 4627U
#else
#error "Unsupported MLDSA_VARIANT (expected 44, 65, or 87)"
#endif

#include "libcrux_sha3_portable.h"

using namespace std;

typedef vector<uint8_t> bytes;

#define MLDSA_CAT_(a, b) a##b
#define MLDSA_CAT(a, b) MLDSA_CAT_(a, b)
#define MLDSA_STRINGIFY(x) #x
#define MLDSA_TOSTRING(x) MLDSA_STRINGIFY(x)

// libcrux_ml_dsa_ml_dsa_<VARIANT><suffix>, e.g. _portable_generate_key_pair
#define MLDSA_SYM(suffix) \
  MLDSA_CAT(MLDSA_CAT(libcrux_ml_dsa_ml_dsa_, MLDSA_VARIANT), suffix)
// MlDsa<VARIANT><suffix> test-suite names
#define MLDSA_SUITE(suffix) MLDSA_CAT(MLDSA_CAT(MlDsa, MLDSA_VARIANT), suffix)
// tests/nistkats-<VARIANT>.json
#define MLDSA_KATS_PATH "tests/nistkats-" MLDSA_TOSTRING(MLDSA_VARIANT) ".json"

Eurydice_borrow_slice_u8 mk_borrow_slice_u8(const uint8_t *x, size_t len) {
  Eurydice_borrow_slice_u8 s = {0};
  s.ptr = x;
  s.meta = len;
  return s;
}

TEST(MLDSA_SUITE(TestPortable), ConsistencyTest) {
  // Generate key pair
  Eurydice_arr_ec keygen_rand = {0};
  memset(keygen_rand.data, 0x13, 32);

  auto key_pair = MLDSA_SYM(_portable_generate_key_pair)(keygen_rand);

  // Sign
  uint8_t msg[79] = {0};
  Eurydice_arr_ec sign_rand = {0};
  memset(sign_rand.data, 0x13, 32);
  uint8_t context[3] = {0};

  auto msg_slice = mk_borrow_slice_u8((uint8_t *)msg, 79);
  auto context_slice = mk_borrow_slice_u8((uint8_t *)context, 3);
  auto signature_result = MLDSA_SYM(_portable_sign)(
      &key_pair.signing_key, msg_slice, context_slice, sign_rand);
  EXPECT_EQ(signature_result.tag, core_result_Ok);
  auto signature = signature_result.val.case_Ok;

  // Verify
  auto result = MLDSA_SYM(_portable_verify)(
      &key_pair.verification_key, msg_slice, context_slice, &signature);

  EXPECT_EQ(result.tag, core_result_Ok);
}

#ifdef LIBCRUX_X64
#if MLDSA_VARIANT == 44
#include "libcrux_mldsa44_avx2.h"
#elif MLDSA_VARIANT == 65
#include "libcrux_mldsa65_avx2.h"
#elif MLDSA_VARIANT == 87
#include "libcrux_mldsa87_avx2.h"
#endif

TEST(MLDSA_SUITE(TestAvx2), ConsistencyTest) {
  Eurydice_arr_ec keygen_rand = {0};
  memset(keygen_rand.data, 0x13, 32);
  auto key_pair = MLDSA_SYM(_avx2_generate_key_pair)(keygen_rand);

  // Sign
  uint8_t msg[79] = {0};
  Eurydice_arr_ec sign_rand = {0};
  memset(sign_rand.data, 0x13, 32);
  uint8_t context[3] = {0};

  auto msg_slice = mk_borrow_slice_u8((uint8_t *)msg, 79);
  auto context_slice = mk_borrow_slice_u8((uint8_t *)context, 3);
  auto signature_result = MLDSA_SYM(_avx2_sign)(
      &key_pair.signing_key, msg_slice, context_slice, sign_rand);
  EXPECT_EQ(signature_result.tag, core_result_Ok);
  auto signature = signature_result.val.case_Ok;

  // Verify
  auto result = MLDSA_SYM(_avx2_verify)(
      &key_pair.verification_key, msg_slice, context_slice, &signature);

  EXPECT_EQ(result.tag, core_result_Ok);
}
#endif  // LIBCRUX_X64

class KAT {
 public:
  bytes key_generation_seed;
  bytes sha3_256_hash_of_verification_key;
  bytes sha3_256_hash_of_signing_key;
  bytes message;
  bytes signing_randomness;
  bytes sha3_256_hash_of_signature;
};

vector<uint8_t> from_hex(const string &hex) {
  if (hex.length() % 2 == 1) {
    throw invalid_argument("Odd-length hex string");
  }

  int len = static_cast<int>(hex.length()) / 2;
  vector<uint8_t> out(len);
  for (int i = 0; i < len; i += 1) {
    string byte = hex.substr(2 * i, 2);
    out[i] = static_cast<uint8_t>(strtol(byte.c_str(), nullptr, 16));
  }

  return out;
}

string bytes_to_hex(const vector<uint8_t> &data) {
  stringstream hex(ios_base::out);
  hex.flags(ios::hex);
  for (const auto &byte : data) {
    hex << setw(2) << setfill('0') << int(byte);
  }
  return hex.str();
}

string bytes_to_hex(const uint8_t *data, size_t len) {
  stringstream hex(ios_base::out);
  hex.flags(ios::hex);
  for (size_t i = 0; i < len; ++i) {
    hex << setw(2) << setfill('0') << int(data[i]);
  }
  return hex.str();
}

vector<KAT> read_kats(string path) {
  ifstream kat_file(path);
  nlohmann::json kats_raw;
  kat_file >> kats_raw;

  vector<KAT> kats;

  // Read test group
  for (auto &kat_raw : kats_raw.items()) {
    auto kat_raw_value = kat_raw.value();

    kats.push_back(KAT{
        from_hex(kat_raw_value["key_generation_seed"]),
        from_hex(kat_raw_value["sha3_256_hash_of_verification_key"]),
        from_hex(kat_raw_value["sha3_256_hash_of_signing_key"]),
        from_hex(kat_raw_value["message"]),
        from_hex(kat_raw_value["signing_randomness"]),
        from_hex(kat_raw_value["sha3_256_hash_of_signature"]),
    });
  }

  return kats;
}

TEST(MLDSA_SUITE(TestPortable), NISTKnownAnswerTest) {
  // XXX: This should be done in a portable way.
  auto kats = read_kats(MLDSA_KATS_PATH);

  Eurydice_arr_ec keygen_rand = {0};
  Eurydice_arr_ec sign_rand = {0};

  for (auto kat : kats) {
    // Generate key pair
    memcpy(keygen_rand.data, kat.key_generation_seed.data(), 32);

    auto key_pair = MLDSA_SYM(_portable_generate_key_pair)(keygen_rand);

    auto vk_hash = libcrux_sha3_sha256(mk_borrow_slice_u8(
        key_pair.verification_key.data, MLDSA_VERIFICATION_KEY_SIZE));
    EXPECT_EQ(0, memcmp(vk_hash.data,
                        kat.sha3_256_hash_of_verification_key.data(), 32));

    auto sk_hash = libcrux_sha3_sha256(
        mk_borrow_slice_u8(key_pair.signing_key.data, MLDSA_SIGNING_KEY_SIZE));
    EXPECT_EQ(
        0, memcmp(sk_hash.data, kat.sha3_256_hash_of_signing_key.data(), 32));

    // Sign
    memcpy(sign_rand.data, kat.signing_randomness.data(), 32);
    Eurydice_borrow_slice_u8 context = {0};

    auto msg_slice = mk_borrow_slice_u8(kat.message.data(), kat.message.size());
    auto signature_result = MLDSA_SYM(_portable_sign)(
        &key_pair.signing_key, msg_slice, context, sign_rand);
    EXPECT_EQ(signature_result.tag, core_result_Ok);
    auto signature = signature_result.val.case_Ok;

    auto sig_hash =
        libcrux_sha3_sha256(mk_borrow_slice_u8(signature.data, MLDSA_SIGNATURE_SIZE));
    EXPECT_EQ(0,
              memcmp(sig_hash.data, kat.sha3_256_hash_of_signature.data(), 32));

    // Verify
    auto result = MLDSA_SYM(_portable_verify)(
        &key_pair.verification_key, msg_slice, context, &signature);

    EXPECT_EQ(result.tag, core_result_Ok);
  }
}

#ifdef LIBCRUX_X64
TEST(MLDSA_SUITE(TestAvx2), NISTKnownAnswerTest) {
  // XXX: This should be done in a portable way.
  auto kats = read_kats(MLDSA_KATS_PATH);

  Eurydice_arr_ec keygen_rand = {0};
  Eurydice_arr_ec sign_rand = {0};

  for (auto kat : kats) {
    // Generate key pair
    memcpy(keygen_rand.data, kat.key_generation_seed.data(), 32);

    auto key_pair = MLDSA_SYM(_avx2_generate_key_pair)(keygen_rand);

    auto vk_hash = libcrux_sha3_sha256(mk_borrow_slice_u8(
        key_pair.verification_key.data, MLDSA_VERIFICATION_KEY_SIZE));
    EXPECT_EQ(0, memcmp(vk_hash.data,
                        kat.sha3_256_hash_of_verification_key.data(), 32));

    auto sk_hash = libcrux_sha3_sha256(
        mk_borrow_slice_u8(key_pair.signing_key.data, MLDSA_SIGNING_KEY_SIZE));
    EXPECT_EQ(
        0, memcmp(sk_hash.data, kat.sha3_256_hash_of_signing_key.data(), 32));

    // Sign
    memcpy(sign_rand.data, kat.signing_randomness.data(), 32);
    Eurydice_borrow_slice_u8 context = {0};

    auto msg_slice = mk_borrow_slice_u8(kat.message.data(), kat.message.size());
    auto signature_result = MLDSA_SYM(_avx2_sign)(
        &key_pair.signing_key, msg_slice, context, sign_rand);
    EXPECT_EQ(signature_result.tag, core_result_Ok);
    auto signature = signature_result.val.case_Ok;

    auto sig_hash =
        libcrux_sha3_sha256(mk_borrow_slice_u8(signature.data, MLDSA_SIGNATURE_SIZE));
    EXPECT_EQ(0,
              memcmp(sig_hash.data, kat.sha3_256_hash_of_signature.data(), 32));

    // Verify
    auto result = MLDSA_SYM(_avx2_verify)(
        &key_pair.verification_key, msg_slice, context, &signature);

    EXPECT_EQ(result.tag, core_result_Ok);
  }
}
#endif  // LIBCRUX_X64
