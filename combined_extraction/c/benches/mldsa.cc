/*
 *    Copyright 2026 CE Labs
 *
 *    Licensed under the Apache License, Version 2.0 or MIT.
 *    - http://www.apache.org/licenses/LICENSE-2.0
 *    - http://opensource.org/licenses/MIT
 */

// Single source file for all ML-DSA sizes. Each benchmark binary is built
// from this file with MLDSA_VARIANT defined to 44, 65, or 87 (see
// CMakeLists.txt), which selects the right headers and, via the MLDSA_*
// macros below, the right variant-specific symbol names. This mirrors the
// approach used in tests/mldsa.cc.

#include <benchmark/benchmark.h>

#include <cstring>

#ifndef MLDSA_VARIANT
#error "MLDSA_VARIANT must be defined to 44, 65, or 87"
#endif

#if MLDSA_VARIANT == 44
#include "libcrux_mldsa44_portable.h"
#elif MLDSA_VARIANT == 65
#include "libcrux_mldsa65_portable.h"
#elif MLDSA_VARIANT == 87
#include "libcrux_mldsa87_portable.h"
#else
#error "Unsupported MLDSA_VARIANT (expected 44, 65, or 87)"
#endif

#define MLDSA_CAT_(a, b) a##b
#define MLDSA_CAT(a, b) MLDSA_CAT_(a, b)

#define MLDSA_STRINGIFY(x) #x
#define MLDSA_TOSTRING(x) MLDSA_STRINGIFY(x)

// libcrux_ml_dsa_ml_dsa_<VARIANT><suffix>, e.g. _portable_generate_key_pair
#define MLDSA_SYM(suffix) \
  MLDSA_CAT(MLDSA_CAT(libcrux_ml_dsa_ml_dsa_, MLDSA_VARIANT), suffix)
// MlDsa<VARIANT><suffix> benchmark names
#define MLDSA_SUITE(suffix) MLDSA_CAT(MLDSA_CAT(MlDsa, MLDSA_VARIANT), suffix)
// Registers a benchmark under its fully-expanded name (BENCHMARK() would
// otherwise stringify the unexpanded "MLDSA_SUITE(...)" macro call).
#define MLDSA_BENCHMARK(suffix) \
  benchmark::RegisterBenchmark(MLDSA_TOSTRING(MLDSA_SUITE(suffix)), \
                                MLDSA_SUITE(suffix))

static Eurydice_borrow_slice_u8 mk_borrow_slice_u8(const uint8_t *x,
                                                    size_t len) {
  Eurydice_borrow_slice_u8 s = {0};
  s.ptr = x;
  s.meta = len;
  return s;
}

static uint8_t g_msg[79] = {0};
static uint8_t g_context[3] = {0};

static void MLDSA_SUITE(_portable_key_generation)(benchmark::State &state) {
  Eurydice_arr_ec randomness = {0};
  memset(randomness.data, 0x13, 32);

  auto key_pair = MLDSA_SYM(_portable_generate_key_pair)(randomness);

  for (auto _ : state) {
    key_pair = MLDSA_SYM(_portable_generate_key_pair)(randomness);
    benchmark::DoNotOptimize(key_pair);
  }
}

static void MLDSA_SUITE(_portable_sign)(benchmark::State &state) {
  Eurydice_arr_ec keygen_rand = {0};
  memset(keygen_rand.data, 0x13, 32);
  auto key_pair = MLDSA_SYM(_portable_generate_key_pair)(keygen_rand);

  Eurydice_arr_ec sign_rand = {0};
  memset(sign_rand.data, 0x13, 32);
  auto msg_slice = mk_borrow_slice_u8(g_msg, sizeof(g_msg));
  auto context_slice = mk_borrow_slice_u8(g_context, sizeof(g_context));

  auto signature_result = MLDSA_SYM(_portable_sign)(
      &key_pair.signing_key, msg_slice, context_slice, sign_rand);

  for (auto _ : state) {
    signature_result = MLDSA_SYM(_portable_sign)(
        &key_pair.signing_key, msg_slice, context_slice, sign_rand);
    benchmark::DoNotOptimize(signature_result);
  }
}

static void MLDSA_SUITE(_portable_verify)(benchmark::State &state) {
  Eurydice_arr_ec keygen_rand = {0};
  memset(keygen_rand.data, 0x13, 32);
  auto key_pair = MLDSA_SYM(_portable_generate_key_pair)(keygen_rand);

  Eurydice_arr_ec sign_rand = {0};
  memset(sign_rand.data, 0x13, 32);
  auto msg_slice = mk_borrow_slice_u8(g_msg, sizeof(g_msg));
  auto context_slice = mk_borrow_slice_u8(g_context, sizeof(g_context));

  auto signature_result = MLDSA_SYM(_portable_sign)(
      &key_pair.signing_key, msg_slice, context_slice, sign_rand);
  auto signature = signature_result.val.case_Ok;

  auto result = MLDSA_SYM(_portable_verify)(&key_pair.verification_key,
                                             msg_slice, context_slice,
                                             &signature);

  for (auto _ : state) {
    result = MLDSA_SYM(_portable_verify)(&key_pair.verification_key,
                                          msg_slice, context_slice,
                                          &signature);
    benchmark::DoNotOptimize(result);
  }
}

namespace {
int register_portable_benchmarks = [] {
  MLDSA_BENCHMARK(_portable_key_generation);
  MLDSA_BENCHMARK(_portable_sign);
  MLDSA_BENCHMARK(_portable_verify);
  return 0;
}();
}  // namespace

#ifdef LIBCRUX_X64
#if MLDSA_VARIANT == 44
#include "libcrux_mldsa44_avx2.h"
#elif MLDSA_VARIANT == 65
#include "libcrux_mldsa65_avx2.h"
#elif MLDSA_VARIANT == 87
#include "libcrux_mldsa87_avx2.h"
#endif

static void MLDSA_SUITE(_avx2_key_generation)(benchmark::State &state) {
  Eurydice_arr_ec randomness = {0};
  memset(randomness.data, 0x13, 32);

  auto key_pair = MLDSA_SYM(_avx2_generate_key_pair)(randomness);

  for (auto _ : state) {
    key_pair = MLDSA_SYM(_avx2_generate_key_pair)(randomness);
    benchmark::DoNotOptimize(key_pair);
  }
}

static void MLDSA_SUITE(_avx2_sign)(benchmark::State &state) {
  Eurydice_arr_ec keygen_rand = {0};
  memset(keygen_rand.data, 0x13, 32);
  auto key_pair = MLDSA_SYM(_avx2_generate_key_pair)(keygen_rand);

  Eurydice_arr_ec sign_rand = {0};
  memset(sign_rand.data, 0x13, 32);
  auto msg_slice = mk_borrow_slice_u8(g_msg, sizeof(g_msg));
  auto context_slice = mk_borrow_slice_u8(g_context, sizeof(g_context));

  auto signature_result = MLDSA_SYM(_avx2_sign)(
      &key_pair.signing_key, msg_slice, context_slice, sign_rand);

  for (auto _ : state) {
    signature_result = MLDSA_SYM(_avx2_sign)(
        &key_pair.signing_key, msg_slice, context_slice, sign_rand);
    benchmark::DoNotOptimize(signature_result);
  }
}

static void MLDSA_SUITE(_avx2_verify)(benchmark::State &state) {
  Eurydice_arr_ec keygen_rand = {0};
  memset(keygen_rand.data, 0x13, 32);
  auto key_pair = MLDSA_SYM(_avx2_generate_key_pair)(keygen_rand);

  Eurydice_arr_ec sign_rand = {0};
  memset(sign_rand.data, 0x13, 32);
  auto msg_slice = mk_borrow_slice_u8(g_msg, sizeof(g_msg));
  auto context_slice = mk_borrow_slice_u8(g_context, sizeof(g_context));

  auto signature_result = MLDSA_SYM(_avx2_sign)(
      &key_pair.signing_key, msg_slice, context_slice, sign_rand);
  auto signature = signature_result.val.case_Ok;

  auto result = MLDSA_SYM(_avx2_verify)(&key_pair.verification_key, msg_slice,
                                         context_slice, &signature);

  for (auto _ : state) {
    result = MLDSA_SYM(_avx2_verify)(&key_pair.verification_key, msg_slice,
                                      context_slice, &signature);
    benchmark::DoNotOptimize(result);
  }
}

namespace {
int register_avx2_benchmarks = [] {
  MLDSA_BENCHMARK(_avx2_key_generation);
  MLDSA_BENCHMARK(_avx2_sign);
  MLDSA_BENCHMARK(_avx2_verify);
  return 0;
}();
}  // namespace
#endif  // LIBCRUX_X64

BENCHMARK_MAIN();
