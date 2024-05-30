#include "eurydice_glue.h"
#include "libcrux_sha3.h"
#include "Hacl_Hash_SHA3_Scalar.h"

typedef uint64_t* libcrux_sha3_portable_KeccakState1;

void libcrux_sha3_portable_sha512(Eurydice_slice x0, Eurydice_slice x1){
    Hacl_Hash_SHA3_Scalar_sha3_512(x0.ptr, x1.ptr, x1.len);
}

void libcrux_sha3_portable_sha256(Eurydice_slice x0, Eurydice_slice x1){
    Hacl_Hash_SHA3_Scalar_sha3_256(x0.ptr, x1.ptr, x1.len);
}

void libcrux_sha3_portable_shake256(Eurydice_slice x0, Eurydice_slice x1){{
    Hacl_Hash_SHA3_Scalar_shake256(x0.ptr, x0.len, x1.ptr, x1.len);
}

libcrux_sha3_portable_KeccakState1
libcrux_sha3_portable_incremental_shake128_init(void){
    return Hacl_Hash_SHA3_Scalar_state_malloc();
}

void
libcrux_sha3_portable_incremental_shake128_absorb_final(
  libcrux_sha3_portable_KeccakState1 *x0,
  Eurydice_slice x1
){
    Hacl_Hash_SHA3_Scalar_shake128_absorb_final(x0, x1.ptr, x1.len);
}

void
libcrux_sha3_portable_incremental_shake128_squeeze_next_block(
  libcrux_sha3_portable_KeccakState1 *x0,
  Eurydice_slice x1
){
    Hacl_Hash_SHA3_Scalar_shake128_squeeze_nblocks(x0, x1.ptr, x1.len);
}

void
libcrux_sha3_portable_incremental_shake128_squeeze_first_three_blocks(
  libcrux_sha3_portable_KeccakState1 *x0,
  Eurydice_slice x1
){
    Hacl_Hash_SHA3_Scalar_shake128_squeeze_nblocks(x0, x1.ptr, x1.len);
}