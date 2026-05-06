# Portable keccakf1600 ↔ Hacspec equivalence proofs

F\* proofs that the libcrux SHA-3 **portable** keccakf1600 permutation
(`Libcrux_sha3.Generic_keccak.impl_2__keccakf1600` instantiated at `N=1, T=u64`)
agrees with the Hacspec specification (`Hacspec_sha3.Keccak_f.keccak_f`) on
every input state.

## Top-level theorems

The portable instantiation:

```fstar
val lemma_keccakf1600_portable
      (ks: Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) u64)
  : Lemma
      ((Libcrux_sha3.Generic_keccak.impl_2__keccakf1600 (mk_usize 1) #u64 ks)
         .Libcrux_sha3.Generic_keccak.f_st ==
       Hacspec_sha3.Keccak_f.keccak_f ks.Libcrux_sha3.Generic_keccak.f_st)
```

(Source: `EquivImplSpec.Keccakf.Portable.fst`.)

The generic theorem, parametric over any `KeccakItem` backend that supplies
a `lane_correctness` record:

```fstar
val lemma_keccakf1600_to_spec
      (v_N: usize) (#v_T: Type0)
      {| inst: Libcrux_sha3.Traits.t_KeccakItem v_T v_N |}
      (lc: lane_correctness v_N #v_T)
      (ks: Libcrux_sha3.Generic_keccak.t_KeccakState v_N v_T)
      (l: nat{l < v v_N})
  : Lemma
      (extract_lane v_N lc
        (Libcrux_sha3.Generic_keccak.impl_2__keccakf1600 v_N #v_T ks)
          .Libcrux_sha3.Generic_keccak.f_st l ==
       Hacspec_sha3.Keccak_f.keccak_f
        (extract_lane v_N lc ks.Libcrux_sha3.Generic_keccak.f_st l))
```

(Source: `EquivImplSpec.Keccakf.Generic.fst`.)

The generic theorem is the reusable boundary: future Arm64 (Neon) and
AVX2 PRs only need to populate a `lane_correctness` record at their
respective `(N=2, T=uint64x2_t)` and `(N=4, T=__m256i)` to inherit the
keccakf1600 ↔ spec equivalence.

## Scope

PR-2 establishes two distinct claims:

### Panic-freedom (Spec + Implementation)

Both the Hacspec SHA-3 specification and the libcrux SHA-3 implementation
panic-free typecheck under hax → F\*. That is: every `requires` precondition
is sufficient to discharge any panic-introducing operation in the body
(slice indexing, integer overflow, `unwrap`, etc.) — no runtime panics
are reachable from any Rust call site that satisfies the documented
preconditions.

| Module | Status |
| --- | --- |
| `Hacspec_sha3.{Keccak_f, Sha3, Sponge}` (spec) | Panic-free typecheck |
| `Libcrux_sha3.{lib, traits, proof_utils, simd.portable}` (generic / portable utilities) | Panic-free typecheck |
| `Libcrux_sha3.Generic_keccak.{Constants, Portable, Xof}` (sponge + state) | Panic-free typecheck |
| `Libcrux_sha3.Portable.{Incremental.*}` (top-level portable API + XOF wrappers) | Panic-free typecheck |

This claim covers the entire portable surface — including the sponge
layer, XOF API, and SHA-3/SHAKE digest wrappers — even though no
equivalence theorem about them is proven yet.

### Implementation ↔ Spec correctness

The portable `keccakf1600` permutation is proven to compute exactly the
same value as the Hacspec specification on every input state.

| Layer | Status in this PR |
| --- | --- |
| Portable keccakf1600 ↔ `Hacspec_sha3.Keccak_f.keccak_f` | **Proven** (`lemma_keccakf1600_portable`) |
| Generic-over-`T` keccakf1600 ↔ spec | **Proven** (`lemma_keccakf1600_to_spec`, parametric on `lane_correctness`) |
| Sponge layer (absorb / squeeze / XOF) ↔ `Hacspec_sha3.Sponge.*` | Out of scope; ships separately |
| Top-level digest API (`sha3_*`, `shake*`) ↔ `Hacspec_sha3.Sha3.*` | Out of scope; depends on sponge equivalence |
| Arm64 Neon backend ↔ spec | Out of scope; ships separately |
| AVX2 backend ↔ spec | Out of scope; ships separately |

## Modules

| File | Purpose |
| --- | --- |
| `EquivImplSpec.Keccakf.Generic.fst` | 2024 LoC, ~72 lemmas — `lane_correctness` boundary, per-step `theta`/`rho`/`pi`/`chi`/`iota` extract-lane lemmas, and `lemma_keccakf1600_to_spec`. |
| `EquivImplSpec.Keccakf.Portable.fst` | Instantiates `Generic` for `(N=1, T=u64)` (all 7 `lane_correctness` fields by reflexivity) and exports `lemma_keccakf1600_portable`. |
| `EquivImplSpec.Keccakf.ChiFold.fst` | Per-position equality lemma chaining the impl's chi unrolled form to the spec's `chi_inner_val`. |
| `EquivImplSpec.Keccakf.SpecRounds.fst` | Spec-side iteration helper: `lemma_keccak_f_is_rounds`. |
| `Proof_Utils.NatFold.fst` | Reusable lemmas about natural-number folds over ranges. |
| `Proof_Utils.FoldRange.fst` | Single step lemma for `fold_range` chunk decomposition. |
| `Proof_Utils.Lemmas.fst` | Thin wrappers around upstream hax-lib lemmas (`logand_commutative`, `lemma_rotate_left_zero`, `lemma_index_update_at_range`). |

The `../stubs/Spec.Utils.{fst,fsti}` workaround keeps a small surface of
the cross-crate `Libcrux_intrinsics.Avx2_extract.fsti` references resolved
without pulling in libcrux-ml-kem's full `Spec.Utils`.

## Dependencies

- **hax-lib**: pinned to the `cryspen/hax:integer-lemmas` branch (workspace
  `Cargo.toml`). Several `Proof_Utils.Lemmas` wrappers cite upstream lemmas
  that today live only on that branch; an upstream PR is in flight to merge
  these into hax main, after which the pin will move to a tagged release.
- **Spec**: the Hacspec SHA-3 specification at `specs/sha3/`, extracted to
  `Hacspec_sha3.{Keccak_f, Sponge, Sha3}` modules.

## Building

From the crate root, with the workspace's `fstar-helpers/Makefile.base` set up:

```sh
make -C proofs/fstar/equivalence
```

Or, equivalently, via the wrapper script:

```sh
bash hax.sh prove   # extraction + sponge-and-above panic-free typecheck
make -C proofs/fstar/equivalence   # equivalence proofs
```

A cold-cache full build of the seven equivalence ROOTs takes roughly
**7–8 minutes** on a 12-thread laptop with `JOBS=2`; the panic-free
typecheck of sponge-and-above takes another **~90 seconds**.

Per-module verification times (cold cache, no hint replay):

| Module | Wall time | Notes |
| --- | --- | --- |
| `EquivImplSpec.Keccakf.Generic` | ~175 s | 72 lemmas; rho/theta/pi extract-lane, `lemma_keccakf1600_to_spec`. |
| `EquivImplSpec.Keccakf.ChiFold` | ~127 s | dominated by `lemma_chi_outer_unfolds_generic` (one query at fuel=6, rlimit=800, ~108 s). |
| `EquivImplSpec.Keccakf.SpecRounds` | ~3 s | spec-side `fold_range` bridge. |
| `EquivImplSpec.Keccakf.Portable` | <1 s | `lane_correctness` instantiation by reflexivity. |
| `Proof_Utils.{NatFold, FoldRange, Lemmas}` | <1 s combined | thin upstream-lemma wrappers. |

Hint files (`*.hints`) are recorded under the workspace
`.fstar-cache/hints/` directory after the first successful build; F\*
replays them on subsequent runs and the wall time drops to seconds.

## Verification status

The crate ships a `proofs/generate_verification_status.sh` helper that
classifies each Rust function by its proof tier (lax / unverified /
panic-free / math / bounds / hacspec) and writes a Markdown table to
`proofs/verification_status.md`. Run it any time after re-extraction:

```sh
bash proofs/generate_verification_status.sh --config proofs/verification_status.config.json --root .
```

## Future work (out of scope for this PR)

- Sponge-level equivalence: `EquivImplSpec.Sponge.{Generic, Portable}.*`
  (load_block / store_block / absorb / squeeze ↔ spec).
- Arm64 (Neon) `lane_correctness` instance; AVX2 `lane_correctness` instance.
- Top-level digest API equivalence (`sha3_224`, `sha3_256`, `shake128`,
  `shake256`, …) once the sponge layer is proven.
