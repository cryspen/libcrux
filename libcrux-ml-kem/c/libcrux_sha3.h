/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 45b95e0f63cb830202c0b3ca00a341a3451a02ba
 * Eurydice: 0eb8a17354fd62586cb9f7515af23f4488c2267e
 * Karamel: 1ed8ba551e8c65fdbad1bb7833bd7837be0d89b9
 * F*: a32b316e521fa4f239b610ec8f1d15e78d62cbe8-dirty
 * Libcrux: 59864a878d97174338edf8868672aac0555a8814
 */

#ifndef __libcrux_sha3_H
#define __libcrux_sha3_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "eurydice_glue.h"
#include "libcrux_core.h"
#include "libcrux_sha3_internal.h"

static KRML_MUSTINLINE void libcrux_sha3_portable_sha512(Eurydice_slice digest,
                                                         Eurydice_slice data) {
  Eurydice_slice buf0[1U] = {data};
  Eurydice_slice buf[1U] = {digest};
  libcrux_sha3_portable_keccakx1___72size_t_6uint8_t(buf0, buf);
}

static KRML_MUSTINLINE void libcrux_sha3_portable_sha256(Eurydice_slice digest,
                                                         Eurydice_slice data) {
  Eurydice_slice buf0[1U] = {data};
  Eurydice_slice buf[1U] = {digest};
  libcrux_sha3_portable_keccakx1___136size_t_6uint8_t(buf0, buf);
}

static KRML_MUSTINLINE void libcrux_sha3_portable_shake256(
    Eurydice_slice digest, Eurydice_slice data) {
  Eurydice_slice buf0[1U] = {data};
  Eurydice_slice buf[1U] = {digest};
  libcrux_sha3_portable_keccakx1___136size_t_31uint8_t(buf0, buf);
}

static KRML_MUSTINLINE void libcrux_sha3_portable_sha224(Eurydice_slice digest,
                                                         Eurydice_slice data) {
  Eurydice_slice buf0[1U] = {data};
  Eurydice_slice buf[1U] = {digest};
  libcrux_sha3_portable_keccakx1___144size_t_6uint8_t(buf0, buf);
}

static KRML_MUSTINLINE void libcrux_sha3_portable_sha384(Eurydice_slice digest,
                                                         Eurydice_slice data) {
  Eurydice_slice buf0[1U] = {data};
  Eurydice_slice buf[1U] = {digest};
  libcrux_sha3_portable_keccakx1___104size_t_6uint8_t(buf0, buf);
}

static KRML_MUSTINLINE void libcrux_sha3_sha224_ema(Eurydice_slice digest,
                                                    Eurydice_slice payload) {
  libcrux_sha3_portable_sha224(digest, payload);
}

static KRML_MUSTINLINE void libcrux_sha3_sha224(Eurydice_slice data,
                                                uint8_t ret[28U]) {
  uint8_t out[28U] = {0U};
  libcrux_sha3_sha224_ema(
      Eurydice_array_to_slice((size_t)28U, out, uint8_t, Eurydice_slice), data);
  memcpy(ret, out, (size_t)28U * sizeof(uint8_t));
}

static KRML_MUSTINLINE void libcrux_sha3_sha256_ema(Eurydice_slice digest,
                                                    Eurydice_slice payload) {
  libcrux_sha3_portable_sha256(digest, payload);
}

static KRML_MUSTINLINE void libcrux_sha3_sha256(Eurydice_slice data,
                                                uint8_t ret[32U]) {
  uint8_t out[32U] = {0U};
  libcrux_sha3_sha256_ema(
      Eurydice_array_to_slice((size_t)32U, out, uint8_t, Eurydice_slice), data);
  memcpy(ret, out, (size_t)32U * sizeof(uint8_t));
}

static KRML_MUSTINLINE void libcrux_sha3_sha384_ema(Eurydice_slice digest,
                                                    Eurydice_slice payload) {
  libcrux_sha3_portable_sha384(digest, payload);
}

static KRML_MUSTINLINE void libcrux_sha3_sha384(Eurydice_slice data,
                                                uint8_t ret[48U]) {
  uint8_t out[48U] = {0U};
  libcrux_sha3_sha384_ema(
      Eurydice_array_to_slice((size_t)48U, out, uint8_t, Eurydice_slice), data);
  memcpy(ret, out, (size_t)48U * sizeof(uint8_t));
}

static KRML_MUSTINLINE void libcrux_sha3_sha512_ema(Eurydice_slice digest,
                                                    Eurydice_slice payload) {
  libcrux_sha3_portable_sha512(digest, payload);
}

static KRML_MUSTINLINE void libcrux_sha3_sha512(Eurydice_slice data,
                                                uint8_t ret[64U]) {
  uint8_t out[64U] = {0U};
  libcrux_sha3_sha512_ema(
      Eurydice_array_to_slice((size_t)64U, out, uint8_t, Eurydice_slice), data);
  memcpy(ret, out, (size_t)64U * sizeof(uint8_t));
}

static KRML_MUSTINLINE void libcrux_sha3_portable_shake128(
    Eurydice_slice digest, Eurydice_slice data) {
  Eurydice_slice buf0[1U] = {data};
  Eurydice_slice buf[1U] = {digest};
  libcrux_sha3_portable_keccakx1___168size_t_31uint8_t(buf0, buf);
}

static KRML_MUSTINLINE void libcrux_sha3_shake128_ema(Eurydice_slice out,
                                                      Eurydice_slice data) {
  libcrux_sha3_portable_shake128(out, data);
}

static KRML_MUSTINLINE void libcrux_sha3_shake256_ema(Eurydice_slice out,
                                                      Eurydice_slice data) {
  libcrux_sha3_portable_shake256(out, data);
}

#if defined(__cplusplus)
}
#endif

#define __libcrux_sha3_H_DEFINED
#endif
