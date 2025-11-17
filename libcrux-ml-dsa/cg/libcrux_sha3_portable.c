/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 146b7dce58cb11ca8010b1c947c3437a959dcd88
 * Eurydice: c06863573e1818808527b23b44e244d8b0c8e3f1
 * Karamel: 732e3ac91245451fc441754737eef729e2b01c2a
 * F*: 71d8221589d4d438af3706d89cb653cf53e18aab
 * Libcrux: 701d5efeb75491a48b041375a40e74e74d2cb9a7
 */

#include "libcrux_sha3_portable.h"

#include "libcrux_mldsa_core.h"

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types Eurydice_arr uint8_t[[$8size_t]], core_array_TryFromSliceError

*/
Eurydice_array_u8x8 unwrap_26_ab(Result_a4 self) {
  if (self.tag == Ok) {
    return self.val.case_Ok;
  } else {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                      "unwrap not Ok");
    KRML_HOST_EXIT(255U);
  }
}
