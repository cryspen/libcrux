/*
 *    Copyright 2022 Cryspen Sarl
 *
 *    Licensed under the Apache License, Version 2.0 or MIT.
 *    - http://www.apache.org/licenses/LICENSE-2.0
 *    - http://opensource.org/licenses/MIT
 */

#include <benchmark/benchmark.h>

// TODO: FIXME: why is the macro definition in
// karamel/include/krml/internal/target.h not working?
// This is only broken in C++
#define KRML_HOST_EPRINTF(...) fprintf(stderr, __VA_ARGS__)

#include "libcrux_sha3.h"
#include "libcrux_mlkem768.h"
#include "internal/libcrux_core.h"

#ifdef LIBCRUX_X64
#include "internal/libcrux_sha3_avx2.h"
#endif

void generate_random(uint8_t *output, uint32_t output_len)
{
    for (uint32_t i = 0; i < output_len; i++)
        output[i] = 13;
}

static void
sha3_256_1184(benchmark::State &state)
{
    uint8_t digest[32];
    uint8_t input[1184];
    generate_random(input, 1184);

    libcrux_sha3_portable_sha256(EURYDICE_SLICE(input, 0, 32), EURYDICE_SLICE(digest, 0, 32));

    for (auto _ : state)
    {
        libcrux_sha3_portable_sha256(EURYDICE_SLICE(input, 0, 32), EURYDICE_SLICE(digest, 0, 32));
    }
}

static void
sha3_512_64(benchmark::State &state)
{
    uint8_t digest[64];
    uint8_t input[64];
    generate_random(input, 64);

    libcrux_sha3_portable_sha512(EURYDICE_SLICE(input, 0, 64), EURYDICE_SLICE(digest, 0, 64));

    for (auto _ : state)
    {
        libcrux_sha3_portable_sha512(EURYDICE_SLICE(input, 0, 64), EURYDICE_SLICE(digest, 0, 64));
    }
}

#ifdef LIBCRUX_X64
// __attribute__((target("avx2"))) static void
// shake128_34_504(benchmark::State &state)
// {
//     uint8_t digest0[504];
//     uint8_t digest1[504];
//     uint8_t digest2[504];
//     uint8_t digest3[504];
//     uint8_t input[34];
//     generate_random(input, 34);

//     Eurydice_slice last[4] = {EURYDICE_SLICE(input, 0, 34), EURYDICE_SLICE(input, 0, 34), EURYDICE_SLICE(input, 0, 34), EURYDICE_SLICE(input, 0, 34)};
//     Eurydice_slice out[4] = {EURYDICE_SLICE(digest0, 0, 504), EURYDICE_SLICE(digest1, 0, 504), EURYDICE_SLICE(digest2, 0, 504), EURYDICE_SLICE(digest3, 0, 504)};
//     auto st = libcrux_sha3_avx2_x4_incremental_init();
//     libcrux_sha3_generic_keccak_absorb_final_7f(&st, last);
//     libcrux_sha3_generic_keccak_squeeze_first_three_blocks_ed(&st, out);

//     for (auto _ : state)
//     {
//         auto st = libcrux_sha3_avx2_x4_incremental_init();
//         libcrux_sha3_generic_keccak_absorb_final_7f(&st, last);
//         libcrux_sha3_generic_keccak_squeeze_first_three_blocks_ed(&st, out);
//     }
// }

__attribute__((target("avx2"))) static void
shake256_1120_32(benchmark::State &state)
{
    uint8_t input[1120];
    generate_random(input, 1120);

    uint8_t digest0[32];
    uint8_t digest1[32];
    uint8_t digest2[32];
    uint8_t digest3[32];
    Eurydice_slice out0 = EURYDICE_SLICE(digest0, 0, 32);
    Eurydice_slice out1 = EURYDICE_SLICE(digest1, 0, 32);
    Eurydice_slice out2 = EURYDICE_SLICE(digest2, 0, 32);
    Eurydice_slice out3 = EURYDICE_SLICE(digest3, 0, 32);

    libcrux_sha3_avx2_x4_shake256(EURYDICE_SLICE(input, 0, 1120), EURYDICE_SLICE(input, 0, 1120), EURYDICE_SLICE(input, 0, 1120), EURYDICE_SLICE(input, 0, 1120), out0, out1, out2, out3);

    for (auto _ : state)
    {
        libcrux_sha3_avx2_x4_shake256(EURYDICE_SLICE(input, 0, 1120), EURYDICE_SLICE(input, 0, 1120), EURYDICE_SLICE(input, 0, 1120), EURYDICE_SLICE(input, 0, 1120), out0, out1, out2, out3);
    }
}

__attribute__((target("avx2"))) static void
shake256_33_128(benchmark::State &state)
{
    uint8_t input[33];
    generate_random(input, 33);

    uint8_t digest0[128];
    uint8_t digest1[128];
    uint8_t digest2[128];
    uint8_t digest3[128];
    Eurydice_slice out0 = EURYDICE_SLICE(digest0, 0, 128);
    Eurydice_slice out1 = EURYDICE_SLICE(digest1, 0, 128);
    Eurydice_slice out2 = EURYDICE_SLICE(digest2, 0, 128);
    Eurydice_slice out3 = EURYDICE_SLICE(digest3, 0, 128);

    libcrux_sha3_avx2_x4_shake256(EURYDICE_SLICE(input, 0, 128), EURYDICE_SLICE(input, 0, 128), EURYDICE_SLICE(input, 0, 128), EURYDICE_SLICE(input, 0, 128), out0, out1, out2, out3);

    for (auto _ : state)
    {
        libcrux_sha3_avx2_x4_shake256(EURYDICE_SLICE(input, 0, 128), EURYDICE_SLICE(input, 0, 128), EURYDICE_SLICE(input, 0, 128), EURYDICE_SLICE(input, 0, 128), out0, out1, out2, out3);
    }
}

BENCHMARK(sha3_256_1184);
BENCHMARK(sha3_512_64);
// BENCHMARK(shake128_34_504);
BENCHMARK(shake256_1120_32);
BENCHMARK(shake256_33_128);
#endif

BENCHMARK_MAIN();
