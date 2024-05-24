This file lists the changes I did to make progres extracting & compiling ml-kem
 
For each problem in `libcrux_ml_kem.c`, I added a `FIXME` comment there as well.
 
 - `src/polynomial.rs`: rewrote `add_message_error_reduce`, makes eurydice crash
 - `c/libcrux_ml_kem.c`: commented out `libcrux_ml_kem_libcrux_polynomials_from_i16_array`, contains a `core_result_Result` type what should have been monomorphized
 - `c/libcrux_ml_kem.c`: `libcrux_ml_kem_polynomial__libcrux_ml_kem__polynomial__PolynomialRingElement_Vector__TraitClause_0___ZERO__libcrux_ml_kem_libcrux_polynomials_PortableVector`: replace assignments with `memcpy`s (tried to assign array LHS)
 - `c/eurydice_glue.h` added `core_slice___Slice_T___split_at_mut`
 - `c/eurydice_glue.h` added `core_core_arch_x86___m256i`
 - `c/eurydice_glue.h` added `core_convert___core__convert__AsMut__Slice_T___for__Slice_T___9__as_mut`
 
