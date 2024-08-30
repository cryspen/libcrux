# This is the list of modules that are fully admitted.
# All other modules have individual annotations on their functions indicating verification status
ADMIT_MODULES = Libcrux_ml_kem.Ind_cca.Unpacked.fst \
              Libcrux_ml_kem.Invert_ntt.fst \
              Libcrux_ml_kem.Ntt.fst \
              Libcrux_ml_kem.Sampling.fst \
              Libcrux_ml_kem.Polynomial.fst \
              Libcrux_ml_kem.Vector.Avx2.fst \
              Libcrux_ml_kem.Vector.Avx2.Sampling.fst \
              Libcrux_ml_kem.Vector.Avx2.Serialize.fst \
              Libcrux_ml_kem.Vector.Portable.Compress.fst \
              Libcrux_ml_kem.Vector.Portable.Ntt.fst \
              Libcrux_ml_kem.Vector.Portable.Sampling.fst \
              Libcrux_ml_kem.Vector.Portable.Serialize.fst \
              Libcrux_ml_kem.Vector.Portable.Vector_type.fst \
              Libcrux_ml_kem.Vector.Rej_sample_table.fsti \
              Libcrux_ml_kem.Vector.Neon.Arithmetic.fst \
              Libcrux_ml_kem.Vector.Neon.Compress.fst \
              Libcrux_ml_kem.Vector.Neon.fsti \
              Libcrux_ml_kem.Vector.Neon.fst \
              Libcrux_ml_kem.Vector.Neon.Ntt.fst \
              Libcrux_ml_kem.Vector.Neon.Serialize.fst \
              Libcrux_ml_kem.Vector.Neon.Vector_type.fst \

OTHERFLAGS="--query_stats"
FSTAR_INCLUDE_DIRS_EXTRA = $(shell git rev-parse --show-toplevel)/libcrux-ml-kem/proofs/fstar/spec
include $(shell git rev-parse --show-toplevel)/fstar-helpers/Makefile.template
