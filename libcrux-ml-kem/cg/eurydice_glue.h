/*
 * SPDX-FileCopyrightText: 2024 Eurydice Contributors
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 */

#pragma once

#include <inttypes.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#ifdef _MSC_VER
// For __popcnt
#include <intrin.h>
#endif

#include "karamel.h"

// C++ HELPERS

#if defined(__cplusplus)
#include "eurydice/cpp.h"
#endif

// GENERAL-PURPOSE STUFF

#define LowStar_Ignore_ignore(e, t, _ret_t) ((void)e)

// SLICES, ARRAYS, ETC.

#include "eurydice/slice.h"

// CORE STUFF (conversions, endianness, ...)

#include "eurydice/core.h"

// ITERATORS

#include "eurydice/iterators.h"
