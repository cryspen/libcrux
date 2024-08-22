#include <stdlib.h>
#include <string>

#include "crypto/keccak/internal.h"

#include <benchmark/benchmark.h>

#define SHAKE128_BYTES_TO_OUTPUT 840

static void BM_SHAKE128(benchmark::State &state) {
  uint8_t input[34] = {0};
  for (uint8_t i = 0; i < sizeof(input); i++) {
    input[i] = i;
  }

  uint8_t output[SHAKE128_BYTES_TO_OUTPUT];

  for (auto _ : state) {
      struct BORINGSSL_keccak_st keccak_ctx;
      BORINGSSL_keccak_init(&keccak_ctx, boringssl_shake128);
      BORINGSSL_keccak_absorb(&keccak_ctx, input, sizeof(input));
      BORINGSSL_keccak_squeeze(&keccak_ctx, output, sizeof(output));
  }
}

#define SHAKE256_BYTES_TO_OUTPUT 128

static void BM_SHAKE256(benchmark::State &state) {
  uint8_t input[33] = {0};
  for (uint8_t i = 0; i < sizeof(input); i++) {
    input[i] = i;
  }

  uint8_t output[SHAKE256_BYTES_TO_OUTPUT];

  for (auto _ : state) {
      struct BORINGSSL_keccak_st keccak_ctx;
      BORINGSSL_keccak_init(&keccak_ctx, boringssl_shake256);
      BORINGSSL_keccak_absorb(&keccak_ctx, input, sizeof(input));
      BORINGSSL_keccak_squeeze(&keccak_ctx, output, sizeof(output));
  }
}

BENCHMARK(BM_SHAKE128);
BENCHMARK(BM_SHAKE256);

BENCHMARK_MAIN();
