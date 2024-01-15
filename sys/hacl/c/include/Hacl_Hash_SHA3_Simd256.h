/* MIT License
 *
 * Copyright (c) 2016-2022 INRIA, CMU and Microsoft Corporation
 * Copyright (c) 2022-2023 HACL* Contributors
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */


#ifndef __Hacl_Hash_SHA3_Simd256_H
#define __Hacl_Hash_SHA3_Simd256_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <string.h>
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include "krml/internal/target.h"

typedef struct K____uint8_t___uint8_t__s
{
  uint8_t *fst;
  uint8_t *snd;
}
K____uint8_t___uint8_t_;

typedef struct K____uint8_t__K____uint8_t___uint8_t__s
{
  uint8_t *fst;
  K____uint8_t___uint8_t_ snd;
}
K____uint8_t__K____uint8_t___uint8_t_;

typedef struct K____uint8_t___uint8_t____K____uint8_t___uint8_t__s
{
  uint8_t *fst;
  K____uint8_t__K____uint8_t___uint8_t_ snd;
}
K____uint8_t___uint8_t____K____uint8_t___uint8_t_;

void
Hacl_Hash_SHA3_Simd256_shake128(
  uint32_t inputByteLen,
  uint8_t *input0,
  uint8_t *input1,
  uint8_t *input2,
  uint8_t *input3,
  uint32_t outputByteLen,
  uint8_t *output0,
  uint8_t *output1,
  uint8_t *output2,
  uint8_t *output3
);

void
Hacl_Hash_SHA3_Simd256_shake256(
  uint32_t inputByteLen,
  uint8_t *input0,
  uint8_t *input1,
  uint8_t *input2,
  uint8_t *input3,
  uint32_t outputByteLen,
  uint8_t *output0,
  uint8_t *output1,
  uint8_t *output2,
  uint8_t *output3
);

void
Hacl_Hash_SHA3_Simd256_sha3_224(
  uint32_t inputByteLen,
  uint8_t *input0,
  uint8_t *input1,
  uint8_t *input2,
  uint8_t *input3,
  uint8_t *output0,
  uint8_t *output1,
  uint8_t *output2,
  uint8_t *output3
);

void
Hacl_Hash_SHA3_Simd256_sha3_256(
  uint32_t inputByteLen,
  uint8_t *input0,
  uint8_t *input1,
  uint8_t *input2,
  uint8_t *input3,
  uint8_t *output0,
  uint8_t *output1,
  uint8_t *output2,
  uint8_t *output3
);

void
Hacl_Hash_SHA3_Simd256_sha3_384(
  uint32_t inputByteLen,
  uint8_t *input0,
  uint8_t *input1,
  uint8_t *input2,
  uint8_t *input3,
  uint8_t *output0,
  uint8_t *output1,
  uint8_t *output2,
  uint8_t *output3
);

void
Hacl_Hash_SHA3_Simd256_sha3_512(
  uint32_t inputByteLen,
  uint8_t *input0,
  uint8_t *input1,
  uint8_t *input2,
  uint8_t *input3,
  uint8_t *output0,
  uint8_t *output1,
  uint8_t *output2,
  uint8_t *output3
);

#if defined(__cplusplus)
}
#endif

#define __Hacl_Hash_SHA3_Simd256_H_DEFINED
#endif
