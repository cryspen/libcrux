SLOW_MODULES += Libcrux_ml_kem.Vector.Portable.Serialize.fst

ADMIT_MODULES = Libcrux_ml_kem.Vector.Avx2.fsti \
              Libcrux_ml_kem.Ind_cca.Instantiations.Avx2.fst \
              Libcrux_ml_kem.Ind_cca.Instantiations.Avx2.Unpacked.fst \
              Libcrux_ml_kem.Ind_cca.Instantiations.Neon.Unpacked.fst \
              Libcrux_ml_kem.Ind_cca.Instantiations.Portable.Unpacked.fst \
              Libcrux_ml_kem.Mlkem1024.Avx2.Unpacked.fst \
              Libcrux_ml_kem.Mlkem1024.Neon.Unpacked.fst \
              Libcrux_ml_kem.Mlkem1024.Portable.Unpacked.fst \
              Libcrux_ml_kem.Mlkem768.Avx2.Unpacked.fst \
              Libcrux_ml_kem.Mlkem768.Neon.Unpacked.fst \
              Libcrux_ml_kem.Mlkem768.Portable.Unpacked.fst \
              Libcrux_ml_kem.Mlkem512.Avx2.Unpacked.fst \
              Libcrux_ml_kem.Mlkem512.Neon.Unpacked.fst \
              Libcrux_ml_kem.Mlkem512.Portable.Unpacked.fst \
              Libcrux_ml_kem.Vector.Avx2.Serialize.fst \
              Libcrux_ml_kem.Vector.Avx2.fst \
              Libcrux_ml_kem.Vector.Avx2.Ntt.fst \
              Libcrux_ml_kem.Vector.Avx2.Sampling.fst \
              Libcrux_ml_kem.Vector.Rej_sample_table.fsti \
              Libcrux_ml_kem.Vector.Neon.Arithmetic.fst \
              Libcrux_ml_kem.Vector.Neon.Compress.fst \
              Libcrux_ml_kem.Vector.Neon.fsti \
              Libcrux_ml_kem.Vector.Neon.fst \
              Libcrux_ml_kem.Vector.Neon.Ntt.fst \
              Libcrux_ml_kem.Vector.Neon.Serialize.fst \
              Libcrux_ml_kem.Vector.Neon.Vector_type.fst

FSTAR_INCLUDE_DIRS_EXTRA += ../spec \
	      $(shell git rev-parse --show-toplevel)/fstar-helpers/fstar-bitvec \
	      $(shell git rev-parse --show-toplevel)/libcrux-intrinsics/proofs/fstar/extraction

include $(shell git rev-parse --show-toplevel)/fstar-helpers/Makefile.base
