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
HAX_PROOF_LIBS_HOME ?= $(HAX_HOME)/proof-libs/fstar-secret-integers
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


SECRET_INDEPENDENT = \
	Libcrux.Kem.Kyber.Constants.fsti \
	Libcrux.Digest.fsti \
	Libcrux.Kem.Kyber.Hash_functions.fsti \
	Libcrux.Kem.Kyber.Hash_functions.fst \
	Libcrux.Kem.Kyber.Kyber768.fsti \
	Libcrux.Kem.Kyber.Kyber768.fst \
	Libcrux.Kem.Kyber.Kyber1024.fsti \
	Libcrux.Kem.Kyber.Kyber1024.fst \
	Libcrux.Kem.Kyber.Kyber512.fsti \
	Libcrux.Kem.Kyber.Kyber512.fst \
	Libcrux.Kem.Kyber.Types.fst \
	Libcrux.Kem.Kyber.fsti \
	Libcrux.Kem.Kyber.fst \
	Libcrux.Kem.Kyber.Ind_cpa.fsti \
	Libcrux.Kem.Kyber.Ind_cpa.fst \
	Libcrux.Kem.Kyber.Arithmetic.fsti \
	Libcrux.Kem.Kyber.Arithmetic.fst \
	Libcrux.Kem.Kyber.Compress.fsti \
	Libcrux.Kem.Kyber.Compress.fst \
	Libcrux.Kem.Kyber.Constant_time_ops.fsti \
	Libcrux.Kem.Kyber.Constant_time_ops.fst \
	Libcrux.Kem.Kyber.Matrix.fsti \
	Libcrux.Kem.Kyber.Matrix.fst \
	Libcrux.Kem.Kyber.Ntt.fsti \
	Libcrux.Kem.Kyber.Ntt.fst \
	Libcrux.Kem.Kyber.Sampling.fst \
	Libcrux.Kem.Kyber.Serialize.fsti \
	Libcrux.Kem.Kyber.Serialize.fst

SECRET_INDEPENDENT_CHECKED = $(addsuffix .checked, $(addprefix $(CACHE_DIR)/,$(SECRET_INDEPENDENT)))

# By default, we process all the files in the current directory. Here, we
# *extend* the set of relevant files with the tests.
ROOTS = $(SECRET_INDEPENDENT)

FSTAR_INCLUDE_DIRS = $(HACL_HOME)/lib $(HAX_PROOF_LIBS_HOME)/rust_primitives $(HAX_PROOF_LIBS_HOME)/core $(HAX_LIBS_HOME)

FSTAR_FLAGS = --cmi \
  --warn_error -331-321-274 \
  --admit_smt_queries true \
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

$(SECRET_INDEPENDENT_CHECKED): OTHERFLAGS=--admit_smt_queries true
$(CACHE_DIR)/%.checked: | .depend $(HINT_DIR) $(CACHE_DIR)
	$(FSTAR) $(OTHERFLAGS) $< $(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(notdir $*).hints

verify: $(SECRET_INDEPENDENT_CHECKED)

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
