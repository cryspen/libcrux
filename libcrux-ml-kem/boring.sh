#!/bin/bash

set -e

SED=$(which gsed &>/dev/null && echo gsed || echo sed)

# Extract the C code
# cargo clean
./c.sh --config cg.yaml --out cg --mlkem768 --no-glue --no-unrolling --no-charon

# Fixup code
# TODO: This should go away as soon as the code generation is fixed.
sed -i -E 's/static inline/__attribute__((target("avx2")))\nstatic inline/g' cg/libcrux_sha3_avx2.h
sed -i -E 's/static inline/__attribute__((target("avx2")))\nstatic inline/g' cg/libcrux_mlkem768_avx2.h

sed -i -E 's/.*libcrux_ml_kem_types_MlKemCiphertext_s.*//g' cg/libcrux_core.h
sed -i -E 's/.*Eurydice_error_t_cg_array.*//g' cg/libcrux_core.h
sed -i -E 's/.*libcrux_ml_kem_types_MlKemCiphertext;//g' cg/libcrux_core.h
sed -i -E 's/.*libcrux_ml_kem_ind_cca_MlKem_s.*//g' cg/libcrux_core.h
sed -i -E 's/.*libcrux_ml_kem_ind_cca_MlKem;;//g' cg/libcrux_core.h
