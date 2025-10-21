/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 92c93e1cb1aa299c44eb039374098c8dd598c640
 * Eurydice: 1a15deb0a4af5c10c90c974891a6300b57adef8b
 * Karamel: d55e3f86aa758514f610dfe74f4f1807cdc7244f
 * F*: unset
 * Libcrux: 7627a1f4e6a01f57af3e70129ffa06d3d8e5db72
 */

#ifndef libcrux_intrinsics_x86_64_H
#define libcrux_intrinsics_x86_64_H

#include "eurydice_glue.h"
#include "libcrux_core.h"

#define core_core_arch_x86_64_amx__tile_cmmimfp16ps(x_0, x_1, x_2, _ret_t) \
  core_core_arch_x86_64_amx__tile_cmmimfp16ps_(x_0, x_1, x_2)

extern void core_core_arch_x86_64_amx__tile_cmmimfp16ps_(int32_t x0, int32_t x1,
                                                         int32_t x2);

#define core_core_arch_x86_64_amx__tile_cmmrlfp16ps(x_0, x_1, x_2, _ret_t) \
  core_core_arch_x86_64_amx__tile_cmmrlfp16ps_(x_0, x_1, x_2)

extern void core_core_arch_x86_64_amx__tile_cmmrlfp16ps_(int32_t x0, int32_t x1,
                                                         int32_t x2);

#define core_core_arch_x86_64_amx__tile_dpbf16ps(x_0, x_1, x_2, _ret_t) \
  core_core_arch_x86_64_amx__tile_dpbf16ps_(x_0, x_1, x_2)

extern void core_core_arch_x86_64_amx__tile_dpbf16ps_(int32_t x0, int32_t x1,
                                                      int32_t x2);

#define core_core_arch_x86_64_amx__tile_dpbssd(x_0, x_1, x_2, _ret_t) \
  core_core_arch_x86_64_amx__tile_dpbssd_(x_0, x_1, x_2)

extern void core_core_arch_x86_64_amx__tile_dpbssd_(int32_t x0, int32_t x1,
                                                    int32_t x2);

#define core_core_arch_x86_64_amx__tile_dpbsud(x_0, x_1, x_2, _ret_t) \
  core_core_arch_x86_64_amx__tile_dpbsud_(x_0, x_1, x_2)

extern void core_core_arch_x86_64_amx__tile_dpbsud_(int32_t x0, int32_t x1,
                                                    int32_t x2);

#define core_core_arch_x86_64_amx__tile_dpbusd(x_0, x_1, x_2, _ret_t) \
  core_core_arch_x86_64_amx__tile_dpbusd_(x_0, x_1, x_2)

extern void core_core_arch_x86_64_amx__tile_dpbusd_(int32_t x0, int32_t x1,
                                                    int32_t x2);

#define core_core_arch_x86_64_amx__tile_dpbuud(x_0, x_1, x_2, _ret_t) \
  core_core_arch_x86_64_amx__tile_dpbuud_(x_0, x_1, x_2)

extern void core_core_arch_x86_64_amx__tile_dpbuud_(int32_t x0, int32_t x1,
                                                    int32_t x2);

#define core_core_arch_x86_64_amx__tile_dpfp16ps(x_0, x_1, x_2, _ret_t) \
  core_core_arch_x86_64_amx__tile_dpfp16ps_(x_0, x_1, x_2)

extern void core_core_arch_x86_64_amx__tile_dpfp16ps_(int32_t x0, int32_t x1,
                                                      int32_t x2);

#define core_core_arch_x86_64_amx__tile_loadd(x_0, x_1, x_2, _ret_t) \
  core_core_arch_x86_64_amx__tile_loadd_(x_0, x_1, x_2)

extern void core_core_arch_x86_64_amx__tile_loadd_(int32_t x0, uint8_t *x1,
                                                   size_t x2);

#define core_core_arch_x86_64_amx__tile_stored(x_0, x_1, x_2, _ret_t) \
  core_core_arch_x86_64_amx__tile_stored_(x_0, x_1, x_2)

extern void core_core_arch_x86_64_amx__tile_stored_(int32_t x0, uint8_t *x1,
                                                    size_t x2);

#define core_core_arch_x86_64_amx__tile_stream_loadd(x_0, x_1, x_2, _ret_t) \
  core_core_arch_x86_64_amx__tile_stream_loadd_(x_0, x_1, x_2)

extern void core_core_arch_x86_64_amx__tile_stream_loadd_(int32_t x0,
                                                          uint8_t *x1,
                                                          size_t x2);

#define core_core_arch_x86_64_amx__tile_zero(x_0, _ret_t) \
  core_core_arch_x86_64_amx__tile_zero_(x_0)

extern void core_core_arch_x86_64_amx__tile_zero_(int32_t x0);

#define libcrux_intrinsics_x86_64_H_DEFINED
#endif /* libcrux_intrinsics_x86_64_H */
