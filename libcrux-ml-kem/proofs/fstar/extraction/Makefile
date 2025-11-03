SLOW_MODULES += Libcrux_ml_kem.Vector.Portable.Serialize.fst \
                Libcrux_ml_kem.Vector.Rej_sample_table.fsti

ADMIT_MODULES = Libcrux_ml_kem.Ind_cpa.fst \
	      Libcrux_ml_kem.Ind_cca.fst \
	      Libcrux_ml_kem.Ind_cca.Unpacked.fst \
	      Libcrux_ml_kem.Ntt.fst \
	      Libcrux_ml_kem.Invert_ntt.fst \
	      Libcrux_ml_kem.Polynomial.fst \
	      Libcrux_ml_kem.Matrix.fst \
	      Libcrux_ml_kem.Sampling.fst \
              Libcrux_ml_kem.Vector.Portable.fst \
              Libcrux_ml_kem.Vector.Portable.Arithmetic.fst \
              Libcrux_ml_kem.Vector.Portable.Ntt.fst \
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
