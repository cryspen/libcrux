SLOW_MODULES +=

ADMIT_MODULES = \
	Libcrux_ml_dsa.Constants.Ml_dsa_44_.fst                               \
	Libcrux_ml_dsa.Constants.Ml_dsa_65_.fst                               \
	Libcrux_ml_dsa.Constants.Ml_dsa_87_.fst                               \
	Libcrux_ml_dsa.Encoding.Error.fst                                     \
	Libcrux_ml_dsa.Encoding.Gamma1.fst                                    \
	Libcrux_ml_dsa.Encoding.Signature.fst                                 \
	Libcrux_ml_dsa.Encoding.Signing_key.fst                               \
	Libcrux_ml_dsa.Encoding.T0.fst                                        \
	Libcrux_ml_dsa.Encoding.T1.fst                                        \
	Libcrux_ml_dsa.Encoding.Verification_key.fst                          \
	Libcrux_ml_dsa.Hash_functions.Neon.fst                                \
	Libcrux_ml_dsa.Hash_functions.Portable.fst                            \
	Libcrux_ml_dsa.Hash_functions.Shake128.fst                            \
	Libcrux_ml_dsa.Hash_functions.Shake256.fst                            \
	Libcrux_ml_dsa.Hash_functions.Simd256.fst                             \
	Libcrux_ml_dsa.Matrix.fst                                             \
	Libcrux_ml_dsa.Ml_dsa_44_.Avx2.fst                                    \
	Libcrux_ml_dsa.Ml_dsa_44_.Neon.fst                                    \
	Libcrux_ml_dsa.Ml_dsa_44_.Portable.fst                                \
	Libcrux_ml_dsa.Ml_dsa_44_.fst                                         \
	Libcrux_ml_dsa.Ml_dsa_65_.Avx2.fst                                    \
	Libcrux_ml_dsa.Ml_dsa_65_.Neon.fst                                    \
	Libcrux_ml_dsa.Ml_dsa_65_.Portable.fst                                \
	Libcrux_ml_dsa.Ml_dsa_65_.fst                                         \
	Libcrux_ml_dsa.Ml_dsa_87_.Avx2.fst                                    \
	Libcrux_ml_dsa.Ml_dsa_87_.Neon.fst                                    \
	Libcrux_ml_dsa.Ml_dsa_87_.Portable.fst                                \
	Libcrux_ml_dsa.Ml_dsa_87_.fst                                         \
	Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Avx2.Ml_dsa_44_.fst      \
	Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Avx2.Ml_dsa_65_.fst      \
	Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Avx2.Ml_dsa_87_.fst      \
	Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Neon.Ml_dsa_44_.fst      \
	Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Neon.Ml_dsa_65_.fst      \
	Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Neon.Ml_dsa_87_.fst      \
	Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Portable.Ml_dsa_44_.fst  \
	Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Portable.Ml_dsa_65_.fst  \
	Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Portable.Ml_dsa_87_.fst  \
	Libcrux_ml_dsa.Ml_dsa_generic.Ml_dsa_44_.fst                          \
	Libcrux_ml_dsa.Ml_dsa_generic.Ml_dsa_65_.fst                          \
	Libcrux_ml_dsa.Ml_dsa_generic.Ml_dsa_87_.fst                          \
	Libcrux_ml_dsa.Ml_dsa_generic.Multiplexing.Ml_dsa_44_.fst             \
	Libcrux_ml_dsa.Ml_dsa_generic.Multiplexing.Ml_dsa_65_.fst             \
	Libcrux_ml_dsa.Ml_dsa_generic.Multiplexing.Ml_dsa_87_.fst             \
	Libcrux_ml_dsa.Ml_dsa_generic.fst                                     \
	Libcrux_ml_dsa.Ntt.fst                                                \
	Libcrux_ml_dsa.Pre_hash.fst                                           \
	Libcrux_ml_dsa.Sample.fst                                             \
	Libcrux_ml_dsa.Samplex4.Avx2.fst                                      \
	Libcrux_ml_dsa.Samplex4.Neon.fst                                      \
	Libcrux_ml_dsa.Samplex4.Portable.fst                                  \
	Libcrux_ml_dsa.Samplex4.fst                                           \
	Libcrux_ml_dsa.Simd.Avx2.Rejection_sample.Less_than_eta.fst           \
	Libcrux_ml_dsa.Simd.Avx2.Rejection_sample.Less_than_field_modulus.fst \
	Libcrux_ml_dsa.Simd.Avx2.Rejection_sample.Shuffle_table.fst

FSTAR_INCLUDE_DIRS_EXTRA += ../spec \
	      $(shell git rev-parse --show-toplevel)/fstar-helpers/fstar-bitvec \
	      $(shell git rev-parse --show-toplevel)/libcrux-ml-kem/proofs/fstar/spec \
	      $(shell git rev-parse --show-toplevel)/libcrux-intrinsics/proofs/fstar/extraction

include $(shell git rev-parse --show-toplevel)/fstar-helpers/Makefile.base
