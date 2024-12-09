# ML-KEM Verification Status

This file keeps track of the current verification status of the modules in the ML-KEM implementation.

## Generic modules
* constant_time_ops: Verified
* hash_functions: Verified
* ind_cca: Verified 
* ind_cpa: Verified
* ind_cca/instaniations: Verified
* ind_cca/instaniations/avx2: Verified
* ind_cca/multiplexing: Verified

* invert_ntt: Panic Free, Not linked to spec
* ntt: Panic Free, Not linked to spec
* mlkem*: Panic Free, Not linked to spec

* matrix: Needs proofs
* sampling: Needs proofs
* polynomial: Needs proofs
* serialize: Needs proofs

## Portable modules
* arithmetic: Verified
* compress: Verified
* ntt: Verified
* serialize: Verified
* sampling: Needs proofs

## AVX2 modules
* arithmetic: Verified
* serialize: Verified
* compress: Panic Free
* ntt: Needs proofs
* sampling: Needs proofs
