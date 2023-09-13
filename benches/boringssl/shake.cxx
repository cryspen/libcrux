#include <stdlib.h>
#include <string>

#include "crypto/kyber/internal.h"

#include <benchmark/benchmark.h>

#define BYTES_TO_OUTPUT 10000

static void BM_SHAKE128(benchmark::State &state) {
  uint8_t input[34] = {0};
  uint8_t output[BYTES_TO_OUTPUT];

  for (auto _ : state) {
    BORINGSSL_keccak(output, BYTES_TO_OUTPUT, input, sizeof(input),
                     boringssl_shake128);
  }
}

static void BM_SHAKE256(benchmark::State &state) {
  uint8_t input[34] = {0};
  uint8_t output[BYTES_TO_OUTPUT];

  for (auto _ : state) {
    BORINGSSL_keccak(output, BYTES_TO_OUTPUT, input, sizeof(input),
                     boringssl_shake256);
  }
}

BENCHMARK(BM_SHAKE128);
BENCHMARK(BM_SHAKE256);

BENCHMARK_MAIN();
