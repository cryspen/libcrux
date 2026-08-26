/*
 *    Copyright 2026 CE Labs
 *
 *    Licensed under the Apache License, Version 2.0 or MIT.
 *    - http://www.apache.org/licenses/LICENSE-2.0
 *    - http://opensource.org/licenses/MIT
 */

// Single source file for all ML-KEM sizes. Each benchmark binary is built
// from this file with MLKEM_VARIANT defined to 512, 768, or 1024 (see
// CMakeLists.txt), which selects the right headers and, via the MLKEM_*
// macros below, the right variant-specific symbol names. This mirrors the
// approach used in tests/mlkem.cc.

#include <benchmark/benchmark.h>

#include <cstring>

#ifndef MLKEM_VARIANT
#error "MLKEM_VARIANT must be defined to 512, 768, or 1024"
#endif

#if MLKEM_VARIANT == 512
#include "libcrux_mlkem512.h"
#include "libcrux_mlkem512_portable.h"
#elif MLKEM_VARIANT == 768
#include "libcrux_mlkem768.h"
#include "libcrux_mlkem768_portable.h"
#elif MLKEM_VARIANT == 1024
#include "libcrux_mlkem1024.h"
#include "libcrux_mlkem1024_portable.h"
#else
#error "Unsupported MLKEM_VARIANT (expected 512, 768, or 1024)"
#endif

#define MLKEM_CAT_(a, b) a##b
#define MLKEM_CAT(a, b) MLKEM_CAT_(a, b)

#define MLKEM_STRINGIFY(x) #x
#define MLKEM_TOSTRING(x) MLKEM_STRINGIFY(x)

// libcrux_ml_kem_mlkem<VARIANT><suffix>, e.g. _portable_generate_key_pair
#define MLKEM_SYM(suffix) \
  MLKEM_CAT(MLKEM_CAT(libcrux_ml_kem_mlkem, MLKEM_VARIANT), suffix)
// MlKem<VARIANT><suffix> benchmark names
#define MLKEM_SUITE(suffix) MLKEM_CAT(MLKEM_CAT(MlKem, MLKEM_VARIANT), suffix)
// Registers a benchmark under its fully-expanded name (BENCHMARK() would
// otherwise stringify the unexpanded "MLKEM_SUITE(...)" macro call).
#define MLKEM_BENCHMARK(suffix) \
  benchmark::RegisterBenchmark(MLKEM_TOSTRING(MLKEM_SUITE(suffix)), \
                                MLKEM_SUITE(suffix))

static void MLKEM_SUITE(_portable_key_generation)(benchmark::State &state) {
  Eurydice_arr_c7 randomness = {0};
  memset(randomness.data, 0x13, 64);

  auto key_pair = MLKEM_SYM(_portable_generate_key_pair)(randomness);

  for (auto _ : state) {
    key_pair = MLKEM_SYM(_portable_generate_key_pair)(randomness);
    benchmark::DoNotOptimize(key_pair);
  }
}

static void MLKEM_SUITE(_portable_encapsulation)(benchmark::State &state) {
  Eurydice_arr_c7 randomness = {0};
  memset(randomness.data, 0x13, 64);
  auto key_pair = MLKEM_SYM(_portable_generate_key_pair)(randomness);

  Eurydice_arr_ec randomness2 = {0};
  memset(randomness2.data, 0x15, 32);
  auto ctxt = MLKEM_SYM(_portable_encapsulate)(&key_pair.pk, randomness2);

  for (auto _ : state) {
    ctxt = MLKEM_SYM(_portable_encapsulate)(&key_pair.pk, randomness2);
    benchmark::DoNotOptimize(ctxt);
  }
}

static void MLKEM_SUITE(_portable_decapsulation)(benchmark::State &state) {
  Eurydice_arr_c7 randomness = {0};
  memset(randomness.data, 0x13, 64);
  auto key_pair = MLKEM_SYM(_portable_generate_key_pair)(randomness);

  Eurydice_arr_ec randomness2 = {0};
  memset(randomness2.data, 0x15, 32);
  auto ctxt = MLKEM_SYM(_portable_encapsulate)(&key_pair.pk, randomness2);

  auto shared_secret = MLKEM_SYM(_portable_decapsulate)(&key_pair.sk, &ctxt.fst);

  for (auto _ : state) {
    shared_secret = MLKEM_SYM(_portable_decapsulate)(&key_pair.sk, &ctxt.fst);
    benchmark::DoNotOptimize(shared_secret);
  }
}

namespace {
int register_portable_benchmarks = [] {
  MLKEM_BENCHMARK(_portable_key_generation);
  MLKEM_BENCHMARK(_portable_encapsulation);
  MLKEM_BENCHMARK(_portable_decapsulation);
  return 0;
}();
}  // namespace

#ifdef LIBCRUX_X64
#if MLKEM_VARIANT == 512
#include "libcrux_mlkem512_avx2.h"
#elif MLKEM_VARIANT == 768
#include "libcrux_mlkem768_avx2.h"
#elif MLKEM_VARIANT == 1024
#include "libcrux_mlkem1024_avx2.h"
#endif

static void MLKEM_SUITE(_avx2_key_generation)(benchmark::State &state) {
  Eurydice_arr_c7 randomness = {0};
  memset(randomness.data, 0x13, 64);

  auto key_pair = MLKEM_SYM(_avx2_generate_key_pair)(randomness);

  for (auto _ : state) {
    key_pair = MLKEM_SYM(_avx2_generate_key_pair)(randomness);
    benchmark::DoNotOptimize(key_pair);
  }
}

static void MLKEM_SUITE(_avx2_encapsulation)(benchmark::State &state) {
  Eurydice_arr_c7 randomness = {0};
  memset(randomness.data, 0x13, 64);
  auto key_pair = MLKEM_SYM(_avx2_generate_key_pair)(randomness);

  Eurydice_arr_ec randomness2 = {0};
  memset(randomness2.data, 0x15, 32);
  auto ctxt = MLKEM_SYM(_avx2_encapsulate)(&key_pair.pk, randomness2);

  for (auto _ : state) {
    ctxt = MLKEM_SYM(_avx2_encapsulate)(&key_pair.pk, randomness2);
    benchmark::DoNotOptimize(ctxt);
  }
}

static void MLKEM_SUITE(_avx2_decapsulation)(benchmark::State &state) {
  Eurydice_arr_c7 randomness = {0};
  memset(randomness.data, 0x13, 64);
  auto key_pair = MLKEM_SYM(_avx2_generate_key_pair)(randomness);

  Eurydice_arr_ec randomness2 = {0};
  memset(randomness2.data, 0x15, 32);
  auto ctxt = MLKEM_SYM(_avx2_encapsulate)(&key_pair.pk, randomness2);

  auto shared_secret = MLKEM_SYM(_avx2_decapsulate)(&key_pair.sk, &ctxt.fst);

  for (auto _ : state) {
    shared_secret = MLKEM_SYM(_avx2_decapsulate)(&key_pair.sk, &ctxt.fst);
    benchmark::DoNotOptimize(shared_secret);
  }
}

namespace {
int register_avx2_benchmarks = [] {
  MLKEM_BENCHMARK(_avx2_key_generation);
  MLKEM_BENCHMARK(_avx2_encapsulation);
  MLKEM_BENCHMARK(_avx2_decapsulation);
  return 0;
}();
}  // namespace
#endif  // LIBCRUX_X64

BENCHMARK_MAIN();
