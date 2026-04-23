SLOW_MODULES += Libcrux_ml_kem.Vector.Rej_sample_table.fsti
SLOW_MODULES += Libcrux_ml_kem.Matrix.fst

ADMIT_MODULES = Libcrux_ml_kem.Ind_cca.Unpacked.fst \
	      Libcrux_ml_kem.Ind_cpa.fst \
              Libcrux_ml_kem.Vector.Neon.Arithmetic.fst \
              Libcrux_ml_kem.Vector.Neon.Compress.fst \
              Libcrux_ml_kem.Vector.Neon.fsti \
              Libcrux_ml_kem.Vector.Neon.fst \
              Libcrux_ml_kem.Vector.Neon.Ntt.fst \
              Libcrux_ml_kem.Vector.Neon.Serialize.fst \
              Libcrux_ml_kem.Vector.Neon.Vector_type.fst

FSTAR_INCLUDE_DIRS_EXTRA += ../spec \
	      $(shell git rev-parse --show-toplevel)/fstar-helpers/fstar-bitvec \
	      $(shell git rev-parse --show-toplevel)/libcrux-intrinsics/proofs/fstar/extraction \
	      $(shell git rev-parse --show-toplevel)/specs/ml-kem/proofs/fstar/commute

include $(shell git rev-parse --show-toplevel)/fstar-helpers/Makefile.base
