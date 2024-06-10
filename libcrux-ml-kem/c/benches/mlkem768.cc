/*
 *    Copyright 2022 Cryspen Sarl
 *
 *    Licensed under the Apache License, Version 2.0 or MIT.
 *    - http://www.apache.org/licenses/LICENSE-2.0
 *    - http://opensource.org/licenses/MIT
 */

#include <benchmark/benchmark.h>

#include "libcrux_mlkem768.h"
#include "libcrux_mlkem768_portable.h"
#include "internal/libcrux_core.h"

void generate_random(uint8_t *output, uint32_t output_len)
{
  for (int i = 0; i < output_len; i++)
    output[i] = 13;
}

static void
kyber768_key_generation(benchmark::State &state)
{
  uint8_t randomness[64];
  generate_random(randomness, 64);
  auto key_pair = libcrux_ml_kem_mlkem768_portable_generate_key_pair(randomness);

  for (auto _ : state)
  {
    key_pair = libcrux_ml_kem_mlkem768_portable_generate_key_pair(randomness);
  }
}

static void
kyber768_encapsulation(benchmark::State &state)
{
  uint8_t randomness[64];
  generate_random(randomness, 64);

  auto key_pair = libcrux_ml_kem_mlkem768_portable_generate_key_pair(randomness);
  generate_random(randomness, 32);
  auto ctxt = libcrux_ml_kem_mlkem768_portable_encapsulate(&key_pair.pk, randomness);

  for (auto _ : state)
  {
    ctxt = libcrux_ml_kem_mlkem768_portable_encapsulate(&key_pair.pk, randomness);
  }
}

static void
kyber768_decapsulation(benchmark::State &state)
{
  uint8_t randomness[64];
  generate_random(randomness, 64);

  auto key_pair = libcrux_ml_kem_mlkem768_portable_generate_key_pair(randomness);
  generate_random(randomness, 32);
  auto ctxt = libcrux_ml_kem_mlkem768_portable_encapsulate(&key_pair.pk, randomness);

  uint8_t sharedSecret2[LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE];

  for (auto _ : state)
  {
    libcrux_ml_kem_mlkem768_portable_decapsulate(&key_pair.sk, &ctxt.fst, sharedSecret2);
  }
}

BENCHMARK(kyber768_key_generation);
BENCHMARK(kyber768_encapsulation);
BENCHMARK(kyber768_decapsulation);

#ifdef LIBCRUX_AARCH64
#include "libcrux_mlkem768_neon.h"

static void
kyber768_key_generation_neon(benchmark::State &state)
{
  uint8_t randomness[64];
  generate_random(randomness, 64);
  auto key_pair = libcrux_ml_kem_mlkem768_neon_generate_key_pair(randomness);

  for (auto _ : state)
  {
    key_pair = libcrux_ml_kem_mlkem768_neon_generate_key_pair(randomness);
  }
}

static void
kyber768_encapsulation_neon(benchmark::State &state)
{
  uint8_t randomness[64];
  generate_random(randomness, 64);

  auto key_pair = libcrux_ml_kem_mlkem768_neon_generate_key_pair(randomness);
  generate_random(randomness, 32);
  auto ctxt = libcrux_ml_kem_mlkem768_neon_encapsulate(&key_pair.pk, randomness);

  for (auto _ : state)
  {
    ctxt = libcrux_ml_kem_mlkem768_neon_encapsulate(&key_pair.pk, randomness);
  }
}

static void
kyber768_decapsulation_neon(benchmark::State &state)
{
  uint8_t randomness[64];
  generate_random(randomness, 64);

  auto key_pair = libcrux_ml_kem_mlkem768_neon_generate_key_pair(randomness);
  generate_random(randomness, 32);
  auto ctxt = libcrux_ml_kem_mlkem768_neon_encapsulate(&key_pair.pk, randomness);

  uint8_t sharedSecret2[LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE];

  for (auto _ : state)
  {
    libcrux_ml_kem_mlkem768_neon_decapsulate(&key_pair.sk, &ctxt.fst, sharedSecret2);
  }
}

BENCHMARK(kyber768_key_generation_neon);
BENCHMARK(kyber768_encapsulation_neon);
BENCHMARK(kyber768_decapsulation_neon);
#endif

#ifdef LIBCRUX_X64
#include "libcrux_mlkem768_avx2.h"

static void
kyber768_key_generation_avx2(benchmark::State &state)
{
  uint8_t randomness[64];
  generate_random(randomness, 64);
  auto key_pair = libcrux_ml_kem_mlkem768_avx2_generate_key_pair(randomness);

  for (auto _ : state)
  {
    key_pair = libcrux_ml_kem_mlkem768_avx2_generate_key_pair(randomness);
  }
}

static void
kyber768_encapsulation_avx2(benchmark::State &state)
{
  uint8_t randomness[64];
  generate_random(randomness, 64);

  auto key_pair = libcrux_ml_kem_mlkem768_avx2_generate_key_pair(randomness);
  generate_random(randomness, 32);
  auto ctxt = libcrux_ml_kem_mlkem768_avx2_encapsulate(&key_pair.pk, randomness);

  for (auto _ : state)
  {
    ctxt = libcrux_ml_kem_mlkem768_avx2_encapsulate(&key_pair.pk, randomness);
  }
}

static void
kyber768_decapsulation_avx2(benchmark::State &state)
{
  uint8_t randomness[64];
  generate_random(randomness, 64);

  auto key_pair = libcrux_ml_kem_mlkem768_avx2_generate_key_pair(randomness);
  generate_random(randomness, 32);
  auto ctxt = libcrux_ml_kem_mlkem768_avx2_encapsulate(&key_pair.pk, randomness);

  uint8_t sharedSecret2[LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE];

  for (auto _ : state)
  {
    libcrux_ml_kem_mlkem768_avx2_decapsulate(&key_pair.sk, &ctxt.fst, sharedSecret2);
  }
}

BENCHMARK(kyber768_key_generation_avx2);
BENCHMARK(kyber768_encapsulation_avx2);
BENCHMARK(kyber768_decapsulation_avx2);
#endif

BENCHMARK_MAIN();
