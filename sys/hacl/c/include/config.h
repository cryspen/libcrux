#pragma once

#ifdef SIMD128
#define HACL_CAN_COMPILE_VEC128 1
#endif

#ifdef SIMD256
#define HACL_CAN_COMPILE_VEC256 1
#endif
