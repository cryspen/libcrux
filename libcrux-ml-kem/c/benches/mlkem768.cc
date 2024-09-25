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

#ifdef LIBCRUX_UNPACKED
static void
kyber768_key_generation_unpacked(benchmark::State &state)
{
  uint8_t randomness[64];
  generate_random(randomness, 64);
  auto key_pair = libcrux_ml_kem_mlkem768_portable_generate_key_pair_unpacked(randomness);

  for (auto _ : state)
  {
    key_pair = libcrux_ml_kem_mlkem768_portable_generate_key_pair_unpacked(randomness);
  }
}

static void
kyber768_encapsulation_unpacked(benchmark::State &state)
{
  uint8_t randomness[64];
  generate_random(randomness, 64);

  auto key_pair = libcrux_ml_kem_mlkem768_portable_generate_key_pair_unpacked(randomness);
  generate_random(randomness, 32);
  auto ctxt = libcrux_ml_kem_mlkem768_portable_encapsulate_unpacked(&key_pair.public_key, randomness);

  for (auto _ : state)
  {
    ctxt = libcrux_ml_kem_mlkem768_portable_encapsulate_unpacked(&key_pair.public_key, randomness);
  }
}

static void
kyber768_decapsulation_unpacked(benchmark::State &state)
{
  uint8_t randomness[64];
  generate_random(randomness, 64);

  auto key_pair = libcrux_ml_kem_mlkem768_portable_generate_key_pair_unpacked(randomness);
  generate_random(randomness, 32);
  auto ctxt = libcrux_ml_kem_mlkem768_portable_encapsulate_unpacked(&key_pair.public_key, randomness);

  uint8_t sharedSecret2[LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE];

  for (auto _ : state)
  {
    libcrux_ml_kem_mlkem768_portable_decapsulate_unpacked(&key_pair, &ctxt.fst, sharedSecret2);
  }
}

BENCHMARK(kyber768_key_generation_unpacked);
BENCHMARK(kyber768_encapsulation_unpacked);
BENCHMARK(kyber768_decapsulation_unpacked);
#endif // #ifdef LIBCRUX_UNPACKED

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

#ifdef LIBCRUX_UNPACKED
static void
kyber768_key_generation_avx2_unpacked(benchmark::State &state)
{
  uint8_t randomness[64];
  generate_random(randomness, 64);
  auto key_pair = libcrux_ml_kem_mlkem768_avx2_generate_key_pair_unpacked(randomness);

  for (auto _ : state)
  {
    key_pair = libcrux_ml_kem_mlkem768_avx2_generate_key_pair_unpacked(randomness);
  }
}

static void
kyber768_encapsulation_avx2_unpacked(benchmark::State &state)
{
  uint8_t randomness[64];
  generate_random(randomness, 64);

  auto key_pair = libcrux_ml_kem_mlkem768_avx2_generate_key_pair_unpacked(randomness);
  generate_random(randomness, 32);
  auto ctxt = libcrux_ml_kem_mlkem768_avx2_encapsulate_unpacked(&key_pair.public_key, randomness);

  for (auto _ : state)
  {
    ctxt = libcrux_ml_kem_mlkem768_avx2_encapsulate_unpacked(&key_pair.public_key, randomness);
  }
}

static void
kyber768_decapsulation_avx2_unpacked(benchmark::State &state)
{
  uint8_t randomness[64];
  generate_random(randomness, 64);

  auto key_pair = libcrux_ml_kem_mlkem768_avx2_generate_key_pair_unpacked(randomness);
  generate_random(randomness, 32);
  auto ctxt = libcrux_ml_kem_mlkem768_avx2_encapsulate_unpacked(&key_pair.public_key, randomness);

  uint8_t sharedSecret2[LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE];

  for (auto _ : state)
  {
    libcrux_ml_kem_mlkem768_avx2_decapsulate_unpacked(&key_pair, &ctxt.fst, sharedSecret2);
  }
}

BENCHMARK(kyber768_key_generation_avx2_unpacked);
BENCHMARK(kyber768_encapsulation_avx2_unpacked);
BENCHMARK(kyber768_decapsulation_avx2_unpacked);
#endif // #ifdef LIBCRUX_UNPACKED

#endif

#ifdef LIBCRUX_SYMCRYPT
#include "inc/symcrypt.h"

static void
symcrypt_kyber768_key_generation(benchmark::State &state)
{
  uint8_t randomness[64];
  generate_random(randomness, 64);
  auto pKey = SymCryptMlKemkeyAllocate(SymCryptMlKemParamsDraft203MlKem768);
  SymCryptMlKemkeyGenerate(pKey, 0);

  for (auto _ : state)
  {
    pKey = SymCryptMlKemkeyAllocate(SymCryptMlKemParamsDraft203MlKem768);
    SymCryptMlKemkeyGenerate(pKey, 0);
  }
}

static void
symcrypt_kyber768_encapsulation(benchmark::State &state)
{
  uint8_t randomness[64];
  generate_random(randomness, 64);

  auto pKey = SymCryptMlKemkeyAllocate(SymCryptMlKemParamsDraft203MlKem768);
  SymCryptMlKemkeyGenerate(pKey, 0);
  generate_random(randomness, 32);

  BYTE secret[32];
  BYTE cipher[1088];
  SymCryptMlKemEncapsulate(pKey, secret, 32, cipher, 1088);

  for (auto _ : state)
  {
    SymCryptMlKemEncapsulate(pKey, secret, 32, cipher, 1088);
  }
}

static void
symcrypt_kyber768_decapsulation(benchmark::State &state)
{
  uint8_t randomness[64];
  generate_random(randomness, 64);

  auto pKey = SymCryptMlKemkeyAllocate(SymCryptMlKemParamsDraft203MlKem768);
  SymCryptMlKemkeyGenerate(pKey, 0);

  generate_random(randomness, 32);
  BYTE secret[32];
  BYTE cipher[1088];
  SymCryptMlKemEncapsulate(pKey, secret, 32, cipher, 1088);

  BYTE sharedSecret2[32];

  for (auto _ : state)
  {
    SymCryptMlKemDecapsulate(pKey, cipher, 1088, sharedSecret2, 32);
  }
}

BENCHMARK(symcrypt_kyber768_key_generation);
BENCHMARK(symcrypt_kyber768_encapsulation);
BENCHMARK(symcrypt_kyber768_decapsulation);
#endif

BENCHMARK_MAIN();
