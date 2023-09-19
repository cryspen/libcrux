#include <stdlib.h>
#include <string>

#include "crypto/kyber/internal.h"

#include <benchmark/benchmark.h>

#define SHAKE128_BYTES_TO_OUTPUT 840

static void BM_SHAKE128(benchmark::State &state) {
  uint8_t input[34] = {0};
  for (uint8_t i = 0; i < sizeof(input); i++) {
    input[i] = i;
  }

  uint8_t output[SHAKE128_BYTES_TO_OUTPUT];

  for (auto _ : state) {
    BORINGSSL_keccak(output, SHAKE128_BYTES_TO_OUTPUT, input, sizeof(input),
                     boringssl_shake128);
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
    BORINGSSL_keccak(output, SHAKE256_BYTES_TO_OUTPUT, input, sizeof(input),
                     boringssl_shake256);
  }
}

BENCHMARK(BM_SHAKE128);
BENCHMARK(BM_SHAKE256);

BENCHMARK_MAIN();
