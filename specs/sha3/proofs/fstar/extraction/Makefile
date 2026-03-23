FSTAR_INCLUDE_DIRS_EXTRA += \
	      $(shell git rev-parse --show-toplevel)/crates/algorithms/sha3/proofs/fstar/extraction

# Only verify spec + equivalence files in this directory.
# Implementation files (Libcrux_sha3.*) are verified from crates/algorithms/sha3.
ROOTS = Hacspec_sha3.fst \
        Hacspec_sha3.Keccak_f.fst \
        Hacspec_sha3.Sha3.fst \
        Hacspec_sha3.Sponge.fst \
        Sha3_Equivalence.fst \
        Sha3_Equivalence_Neon.fst \
        Sha3_Equivalence_Avx2.fst

# Equivalence proofs are slow (many SMT queries); skip by default.
# Run with VERIFY_SLOW_MODULES=yes to verify them.
SLOW_MODULES += Sha3_Equivalence.fst Sha3_Equivalence_Neon.fst

# Impl modules that fail non-lax (debug_assert! issues) or are deep
# transitive deps not reachable from this directory. Admit them.
ADMIT_MODULES += Libcrux_sha3.Simd.Arm64.fst \
                 Libcrux_sha3.Generic_keccak.Simd128.fst \
                 Libcrux_sha3.Neon.fst \
                 Libcrux_sha3.Generic_keccak.Portable.fst

# Deep transitive deps that Make can't locate from this directory.
# Tell F* they're already cached so it doesn't try to build .checked for them.
OTHERFLAGS += --already_cached \
  "+Libcrux_sha3.Generic_keccak.Xof\
  +Libcrux_sha3.Neon.X2\
  +Libcrux_sha3.Neon.X2.Incremental\
  +Libcrux_sha3.Portable.Incremental\
  +Libcrux_sha3.Portable.Incremental.Private\
  +Libcrux_sha3.Portable.Incremental.Bundle\
  +Libcrux_sha3.fst"

include $(shell git rev-parse --show-toplevel)/fstar-helpers/Makefile.base
