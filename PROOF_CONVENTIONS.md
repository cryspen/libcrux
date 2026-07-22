# Proof-annotation conventions

This document explains **why F\* fragments appear in the Rust source** and
**where every piece of a proof lives**, for the crates verified with hax
(currently `libcrux-ml-kem` and `libcrux-ml-dsa`; see [PROOFS.md](PROOFS.md)
for what is verified). The rule set is deliberately small enough to check by
eye: placement is decided by *what kind of thing an annotation is*, never by
its size or by solver convenience.

## The placement rule

| What | Where | Why |
|---|---|---|
| Function contracts (`#[hax_lib::requires]`, `#[ensures]`) | On the function | The contract *is* the function's specification; it must be readable where the function is read. |
| Solver settings (`#[hax_lib::fstar::options]`) | On the function | Per-declaration resource limits; one line. |
| Loop invariants (`hax_lib::loop_invariant!`) and decreases clauses | In the loop | Syntactically bound to their position. |
| Ghost snapshots (`#[cfg(hax)] let …`) | In the body | Name an intermediate state so a later proof step can refer to it; erased from compiled code. |
| Body proof scripts (`proof!(…)`) | In the body, at the step they justify | The position-bound proof of *this* function's obligations: revealing an opaque definition, instantiating a named lemma at concrete arguments, asserting a bridging fact. Everything not position-bound is *not* here. |
| Named theory — every reusable F\* definition (`val`, `let`, `Lemma`) | Hand-written companion modules in `proofs/fstar/spec/` | Real, independently verified F\* with a name; reviewed as ordinary F\* files, reused across functions. |
| Reference specifications | `specs/<algorithm>/` (Hacspec style), plus `#[cfg(hax)]` spec modules in-crate | What the code is proven *against*. |

`#[hax_lib::fstar::before]`/`after` attributes are **reserved** for text that
hax must inject verbatim and that cannot be a named definition: one-line
solver/visibility directives (`[@@ "opaque_to_smt"]`, `#restart-solver`) and
interface includes. A multi-line F\* definition inside a `before`/`after`
string is a convention violation unless it carries an exception tag (below).

Body proof scripts are **never** relocated into companion modules, even when
technically possible: partial factoring produces two conventions whose
discriminator is solver behaviour, which cannot be explained or predicted.
Scripts *call* named companion lemmas; they don't move into them.

## Exception tags

Some theory blocks cannot move out of the Rust source for hard technical
reasons. Each such block carries an in-code tag on the line above it:

```rust
// proof-residence: locked(own-const)   — cites this module's extracted constants/types/
//                                        functions (moving it would create a module cycle)
// proof-residence: spec-host           — this module's own spec-predicate vocabulary and
//                                        its lemma API, cited by same-file contracts
// proof-residence: clean-context       — proof saturates in a companion's clean context;
//                                        kept where the host function's ambient facts hold
// proof-residence: hint-keystone       — proof is cold-fragile; relocation shifts
//                                        recorded solver hints (needs restructure first)
// proof-residence: cold-gate           — file keeps --z3refresh for cold-start stability
```

`scripts/annotation_lint.py` scans both crates and reports every multi-line
definition block in a `before`/`after` attribute that lacks a tag. (Reporting
mode during the migration; CI-enforcing once the sweep is complete.)

## The trust surface

Unproven obligations (`admit`, `assume`, lax-checked modules) are enumerable
mechanically (e.g. `grep`, or the `fstar_admits` tooling) and are tracked as a
monotonically non-increasing ledger. A postcondition on a function whose proof
is admitted is a *trusted assumption* and must carry a source comment
justifying it against the code. See each crate's
`proofs/…verification_status.md` for the per-function result.

## Reading a verified function (reviewer quick answers)

- *"Why is this F\* fragment in the code?"* — Every F\* fragment in a `.rs`
  file is one of: the function's contract, a loop invariant, a `proof!`
  script (position-bound by construction), a one-line solver directive, or a
  tagged exception with its reason at the site.
- *"Where are the proof annotations?"* — Contracts and scripts at each
  function; all named theory in `proofs/fstar/spec/*.fst`; reference specs in
  `specs/`; nothing proof-related hides anywhere else.
