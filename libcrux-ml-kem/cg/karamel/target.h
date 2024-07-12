// SPDX-FileCopyrightText: INRIA and Microsoft Corporation
//
// SPDX-License-Identifier: Apache-2.0

#ifndef __KRML_TARGET_H
#define __KRML_TARGET_H

#ifndef KRML_HOST_PRINTF
#define KRML_HOST_PRINTF printf
#endif

#if ((defined(__STDC_VERSION__) && __STDC_VERSION__ >= 199901L) || \
     (defined(__cplusplus) && __cplusplus > 199711L)) &&           \
    (!defined(KRML_HOST_EPRINTF))
#define KRML_HOST_EPRINTF(...) fprintf(stderr, __VA_ARGS__)
#elif !(defined KRML_HOST_EPRINTF) && defined(_MSC_VER)
#define KRML_HOST_EPRINTF(...) fprintf(stderr, __VA_ARGS__)
#endif

#ifndef KRML_HOST_EXIT
#define KRML_HOST_EXIT exit
#endif

#endif
