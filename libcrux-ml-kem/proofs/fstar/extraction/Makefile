# This is a generically useful Makefile for F* that is self-contained
#
# It is tempting to factor this out into multiple Makefiles but that
# makes it less portable, so resist temptation, or move to a more
# sophisticated build system.
#
# We expect FSTAR_HOME to be set to your FSTAR repo/install directory
# We expect HACL_HOME to be set to your HACL* repo location
# We expect HAX_LIBS_HOME to be set to the folder containing core, rust_primitives etc.
#
# ROOTS contains all the top-level F* files you wish to verify
# The default target `verify` verified ROOTS and its dependencies
# To lax-check instead, set `OTHERFLAGS="--lax"` on the command-line
#
#
# To make F* emacs mode use the settings in this file, you need to
# add the following lines to your .emacs
#
# (setq-default fstar-executable "<YOUR_FSTAR_HOME>/bin/fstar.exe")
# (setq-default fstar-smt-executable "<YOUR_Z3_HOME>/bin/z3")
#
# (defun my-fstar-compute-prover-args-using-make ()
#   "Construct arguments to pass to F* by calling make."
#   (with-demoted-errors "Error when constructing arg string: %S"
#     (let* ((fname (file-name-nondirectory buffer-file-name))
# 	   (target (concat fname "-in"))
# 	   (argstr (car (process-lines "make" "--quiet" target))))
#       (split-string argstr))))
# (setq fstar-subp-prover-args #'my-fstar-compute-prover-args-using-make)
#

WORKSPACE_ROOT ?= $(shell git rev-parse --show-toplevel)/..

HAX_HOME ?= $(WORKSPACE_ROOT)/hax
HAX_PROOF_LIBS_HOME ?= $(HAX_HOME)/proof-libs/fstar
HAX_LIBS_HOME ?= $(HAX_HOME)/hax-lib/proofs/fstar/extraction
FSTAR_HOME    ?= $(WORKSPACE_ROOT)/FStar
HACL_HOME     ?= $(WORKSPACE_ROOT)/hacl-star
FSTAR_BIN     ?= $(shell command -v fstar.exe 1>&2 2> /dev/null && echo "fstar.exe" || echo "$(FSTAR_HOME)/bin/fstar.exe")

CACHE_DIR     ?= .cache
HINT_DIR      ?= .hints

.PHONY: all verify verify-lax clean

all:
	rm -f .depend && $(MAKE) .depend
	$(MAKE) verify

VERIFIED = 
PANIC_FREE = Libcrux_ml_kem.Constant_time_ops.fst \
             Libcrux_ml_kem.Constant_time_ops.fsti \
             Libcrux_ml_kem.Constants.fsti \
             Libcrux_ml_kem.Hash_functions.Avx2.fsti \
             Libcrux_ml_kem.Hash_functions.fsti \
             Libcrux_ml_kem.Hash_functions.Neon.fsti \
             Libcrux_ml_kem.Hash_functions.Portable.fsti \
             Libcrux_ml_kem.Ind_cca.fsti \
             Libcrux_ml_kem.Ind_cca.Instantiations.Avx2.fst \
             Libcrux_ml_kem.Ind_cca.Instantiations.Avx2.fsti \
             Libcrux_ml_kem.Ind_cca.Instantiations.Neon.fst \
             Libcrux_ml_kem.Ind_cca.Instantiations.Neon.fsti \
             Libcrux_ml_kem.Ind_cca.Instantiations.Portable.fst \
             Libcrux_ml_kem.Ind_cca.Instantiations.Portable.fsti \
             Libcrux_ml_kem.Ind_cca.Multiplexing.fst \
             Libcrux_ml_kem.Ind_cca.Multiplexing.fsti \
             Libcrux_ml_kem.Ind_cpa.fsti \
             Libcrux_ml_kem.Ind_cpa.Unpacked.fsti \
             Libcrux_ml_kem.Invert_ntt.fsti \
             Libcrux_ml_kem.Matrix.fsti \
             Libcrux_ml_kem.Mlkem512.Avx2.fst \
             Libcrux_ml_kem.Mlkem512.Avx2.fsti \
             Libcrux_ml_kem.Mlkem512.fst \
             Libcrux_ml_kem.Mlkem512.fsti \
             Libcrux_ml_kem.Mlkem512.Neon.fst \
             Libcrux_ml_kem.Mlkem512.Neon.fsti \
             Libcrux_ml_kem.Mlkem512.Portable.fst \
             Libcrux_ml_kem.Mlkem512.Portable.fsti \
             Libcrux_ml_kem.Mlkem768.Avx2.fst \
             Libcrux_ml_kem.Mlkem768.Avx2.fsti \
             Libcrux_ml_kem.Mlkem768.fst \
             Libcrux_ml_kem.Mlkem768.fsti \
             Libcrux_ml_kem.Mlkem768.Neon.fst \
             Libcrux_ml_kem.Mlkem768.Neon.fsti \
             Libcrux_ml_kem.Mlkem768.Portable.fst \
             Libcrux_ml_kem.Mlkem768.Portable.fsti \
             Libcrux_ml_kem.Mlkem1024.Avx2.fst \
             Libcrux_ml_kem.Mlkem1024.Avx2.fsti \
             Libcrux_ml_kem.Mlkem1024.fst \
             Libcrux_ml_kem.Mlkem1024.fsti \
             Libcrux_ml_kem.Mlkem1024.Neon.fst \
             Libcrux_ml_kem.Mlkem1024.Neon.fsti \
             Libcrux_ml_kem.Mlkem1024.Portable.fst \
             Libcrux_ml_kem.Mlkem1024.Portable.fsti \
             Libcrux_ml_kem.Ntt.fsti \
             Libcrux_ml_kem.Polynomial.fsti \
             Libcrux_ml_kem.Sampling.fsti \
             Libcrux_ml_kem.Serialize.fsti \
             Libcrux_ml_kem.Types.fst \
             Libcrux_ml_kem.Types.fsti \
             Libcrux_ml_kem.Utils.fst \
             Libcrux_ml_kem.Utils.fsti \
             Libcrux_ml_kem.Vector.Avx2.Arithmetic.fsti \
             Libcrux_ml_kem.Vector.Avx2.Compress.fsti \
             Libcrux_ml_kem.Vector.Avx2.fsti \
             Libcrux_ml_kem.Vector.Avx2.Ntt.fsti \
             Libcrux_ml_kem.Vector.Avx2.Sampling.fsti \
             Libcrux_ml_kem.Vector.Avx2.Serialize.fsti \
             Libcrux_ml_kem.Vector.Neon.Arithmetic.fsti \
             Libcrux_ml_kem.Vector.Neon.Compress.fsti \
             Libcrux_ml_kem.Vector.Neon.fsti \
             Libcrux_ml_kem.Vector.Neon.Ntt.fsti \
             Libcrux_ml_kem.Vector.Neon.Serialize.fsti \
             Libcrux_ml_kem.Vector.Neon.Vector_type.fsti \
             Libcrux_ml_kem.Vector.Portable.Arithmetic.fsti \
             Libcrux_ml_kem.Vector.Portable.Compress.fsti \
             Libcrux_ml_kem.Vector.Portable.fsti \
             Libcrux_ml_kem.Vector.Portable.Ntt.fsti \
             Libcrux_ml_kem.Vector.Portable.Sampling.fsti \
             Libcrux_ml_kem.Vector.Portable.Serialize.fsti \
             Libcrux_ml_kem.Vector.Portable.Vector_type.fsti \
             Libcrux_ml_kem.Vector.Rej_sample_table.fsti \
             Libcrux_ml_kem.Vector.Traits.fsti
             
UNVERIFIED = $(filter-out $(PANIC_FREE),$(wildcard *.fst))

VERIFIED_CHECKED = $(addsuffix .checked, $(addprefix $(CACHE_DIR)/,$(VERIFIED)))
PANIC_FREE_CHECKED = $(addsuffix .checked, $(addprefix $(CACHE_DIR)/,$(PANIC_FREE)))
UNVERIFIED_CHECKED = $(addsuffix .checked, $(addprefix $(CACHE_DIR)/,$(UNVERIFIED)))

# By default, we process all the files in the current directory. Here, we
# *extend* the set of relevant files with the tests.
ROOTS = $(UNVERIFIED) $(PANIC_FREE) $(VERIFIED)

FSTAR_INCLUDE_DIRS = $(HACL_HOME)/lib $(HAX_PROOF_LIBS_HOME)/rust_primitives \
	$(HAX_PROOF_LIBS_HOME)/core $(HAX_LIBS_HOME) \
	../../../../sys/platform/proofs/fstar/extraction/ \
	../../../../libcrux-intrinsics/proofs/fstar/extraction/ \
	../../../../libcrux-sha3/proofs/fstar/extraction/

FSTAR_FLAGS = --cmi \
  --warn_error -331-321-274 \
  --cache_checked_modules --cache_dir $(CACHE_DIR) \
  --already_cached "+Prims+FStar+LowStar+C+Spec.Loops+TestLib" \
  $(addprefix --include ,$(FSTAR_INCLUDE_DIRS))

FSTAR = $(FSTAR_BIN) $(FSTAR_FLAGS)


.depend: $(HINT_DIR) $(CACHE_DIR) $(ROOTS)
	$(info $(ROOTS))
	$(FSTAR) --cmi --dep full $(ROOTS) --extract '* -Prims -LowStar -FStar' > $@

include .depend

$(HINT_DIR):
	mkdir -p $@

$(CACHE_DIR):
	mkdir -p $@

$(UNVERIFIED_CHECKED): OTHERFLAGS=--admit_smt_queries true
$(CACHE_DIR)/%.checked: | .depend $(HINT_DIR) $(CACHE_DIR)
	$(FSTAR) $(OTHERFLAGS) $< $(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(notdir $*).hints

verify: $(UNVERIFIED_CHECKED) $(PANIC_FREE_CHECKED) $(VERIFIED_CHECKED)

# Targets for interactive mode

%.fst-in:
	$(info $(FSTAR_FLAGS) \
	  $(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(basename $@).fst.hints)

%.fsti-in:
	$(info $(FSTAR_FLAGS) \
	  $(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(basename $@).fsti.hints)


# Clean targets

SHELL=/usr/bin/env bash

clean:
	rm -rf $(CACHE_DIR)/*
	rm *.fst
