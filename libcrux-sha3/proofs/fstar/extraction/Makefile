# If HAX_HOME is set, add HAX_HOME dirs and disable finding LIBS
ifdef HAX_HOME
FINDLIBS_OUTPUT =
FSTAR_INCLUDE_DIRS_EXTRA += \
	$(HAX_HOME)/proof-libs/fstar/rust_primitives \
	$(HAX_HOME)/proof-libs/fstar/core \
	$(HAX_HOME)/hax-lib/proofs/fstar/extraction
endif

# Always include these directories
FSTAR_INCLUDE_DIRS_EXTRA += \
	$(shell git rev-parse --show-toplevel)/fstar-helpers/fstar-bitvec \
	$(shell git rev-parse --show-toplevel)/libcrux-intrinsics/proofs/fstar/extraction \
	$(shell git rev-parse --show-toplevel)/fstar-helpers/core-models/proofs/fstar/extraction

include $(shell git rev-parse --show-toplevel)/fstar-helpers/Makefile.base
