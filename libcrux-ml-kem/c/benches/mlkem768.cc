/*
 *    Copyright 2022 Cryspen Sarl
 *
 *    Licensed under the Apache License, Version 2.0 or MIT.
 *    - http://www.apache.org/licenses/LICENSE-2.0
 *    - http://opensource.org/licenses/MIT
 */

#include <benchmark/benchmark.h>

#include "libcrux_sha3.h"
#include "libcrux_mlkem768.h"
#include "internal/libcrux_core.h"
#include "inc/symcrypt.h"

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
  auto key_pair = libcrux_ml_kem_mlkem768_generate_key_pair(randomness);

  for (auto _ : state)
  {
    key_pair = libcrux_ml_kem_mlkem768_generate_key_pair(randomness);
  }
}

static void
kyber768_encapsulation(benchmark::State &state)
{
  uint8_t randomness[64];
  generate_random(randomness, 64);

  auto key_pair = libcrux_ml_kem_mlkem768_generate_key_pair(randomness);
  generate_random(randomness, 32);
  auto ctxt = libcrux_ml_kem_mlkem768_encapsulate(&key_pair.pk, randomness);

  for (auto _ : state)
  {
    ctxt = libcrux_ml_kem_mlkem768_encapsulate(&key_pair.pk, randomness);
  }
}

static void
kyber768_decapsulation(benchmark::State &state)
{
  uint8_t randomness[64];
  generate_random(randomness, 64);

  auto key_pair = libcrux_ml_kem_mlkem768_generate_key_pair(randomness);
  generate_random(randomness, 32);
  auto ctxt = libcrux_ml_kem_mlkem768_encapsulate(&key_pair.pk, randomness);

  uint8_t sharedSecret2[LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE];

  for (auto _ : state)
  {
    libcrux_ml_kem_mlkem768_decapsulate(&key_pair.sk, &ctxt.fst, sharedSecret2);
  }
}

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

BENCHMARK(kyber768_key_generation);
BENCHMARK(kyber768_encapsulation);
BENCHMARK(kyber768_decapsulation);
BENCHMARK(symcrypt_kyber768_key_generation);
BENCHMARK(symcrypt_kyber768_encapsulation);
BENCHMARK(symcrypt_kyber768_decapsulation);

BENCHMARK_MAIN();
