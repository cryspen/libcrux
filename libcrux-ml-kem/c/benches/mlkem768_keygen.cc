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
#include "Hacl_Hash_SHA3_Scalar.h"

void generate_random(uint8_t *output, uint32_t output_len)
{
    for (int i = 0; i < output_len; i++)
        output[i] = 13;
}

int main(int argc, char const *argv[])
{
    uint8_t randomness[64];
    generate_random(randomness, 64);
    auto key_pair = libcrux_ml_kem_mlkem768_generate_key_pair(randomness);

    for (size_t i = 0; i < 100000; i++)
    {
        key_pair = libcrux_ml_kem_mlkem768_generate_key_pair(randomness);
    }
    return 0;
}
