# Disable auto-discovery of F* paths
FINDLIBS_OUTPUT =

# Explicit F* include paths
FSTAR_INCLUDE_DIRS_EXTRA = \
	$(HAX_HOME)/proof-libs/fstar-secret-integers/core \
	$(HAX_HOME)/proof-libs/fstar/rust_primitives \
	$(HAX_HOME)/proof-libs/fstar/core \
	$(HAX_HOME)/hax-lib/proofs/fstar/extraction

include $(shell git rev-parse --show-toplevel)/fstar-helpers/Makefile.base
