/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
<<<<<<< HEAD
 * Charon: b351338f6a84c7a1afc27433eb0ffdc668b3581d
 * Eurydice: 7efec1624422fd5e94388ef06b9c76dfe7a48d46
 * Karamel: c96fb69d15693284644d6aecaa90afa37e4de8f0
 * F*: 86be6d1083452ef1a2c8991bcf72e36e8f6f5efb
 * Libcrux: e8928fc5424f83c8cb35b980033be17621fc0ef0
=======
 * Charon: 962f26311ccdf09a6a3cfeacbccafba22bf3d405
 * Eurydice: e66abbc2119485abfafa17c1911bdbdada5b04f3
 * Karamel: 7862fdc3899b718d39ec98568f78ec40592a622a
 * F*: 58c915a86a2c07c8eca8d9deafd76cb7a91f0eb7
 * Libcrux: 6b71b5fae48b400c6dac49234638dd52385d111d
>>>>>>> main
 */

#include "libcrux_mlkem_neon.h"

KRML_MUSTINLINE void libcrux_ml_kem_hash_functions_neon_G(Eurydice_slice input,
                                                          uint8_t ret[64U]) {
  uint8_t digest[64U] = {0U};
  libcrux_sha3_neon_sha512(
      Eurydice_array_to_slice((size_t)64U, digest, uint8_t), input);
  memcpy(ret, digest, (size_t)64U * sizeof(uint8_t));
}

KRML_MUSTINLINE void libcrux_ml_kem_hash_functions_neon_H(Eurydice_slice input,
                                                          uint8_t ret[32U]) {
  uint8_t digest[32U] = {0U};
  libcrux_sha3_neon_sha256(
      Eurydice_array_to_slice((size_t)32U, digest, uint8_t), input);
  memcpy(ret, digest, (size_t)32U * sizeof(uint8_t));
}
