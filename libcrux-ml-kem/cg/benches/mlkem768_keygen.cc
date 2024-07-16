// SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
//
// SPDX-License-Identifier: Apache-2.0

#include <benchmark/benchmark.h>

#include "libcrux_mlkem768_portable.h"

void generate_random(uint8_t *output, uint32_t output_len)
{
    for (int i = 0; i < output_len; i++)
        output[i] = 13;
}

int main(int argc, char const *argv[])
{
    uint8_t randomness[64];
    generate_random(randomness, 64);
    auto key_pair = libcrux_ml_kem_mlkem768_portable_generate_key_pair(randomness);

    for (size_t i = 0; i < 100000; i++)
    {
        key_pair = libcrux_ml_kem_mlkem768_portable_generate_key_pair(randomness);
    }
    return 0;
}
