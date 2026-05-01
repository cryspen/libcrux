# Spec audit — `hacspec_ml_kem` vs `libcrux-ml-kem` impl

**Session:** 2026-05-01
**Branch:** `libcrux-ml-kem-proofs` (tip on entry: `723539e40`)
**Scope:** every annotated function in
  `libcrux-ml-kem/src/ind_cpa.rs` and `libcrux-ml-kem/src/ind_cca.rs`
mapped against its `hacspec_ml_kem::*` counterpart in
  `specs/ml-kem/src/{ind_cpa,ind_cca,serialize,sampling,compress,parameters,matrix}.rs`.

The goal of the migration that drives this audit: rewrite every
`#[hax_lib::requires(fstar!(...))]` and
`#[hax_lib::ensures(fstar!(...))]` in the two `src/ind_*.rs` files
from `Spec.MLKEM.*` citations to pure Rust citing `hacspec_ml_kem::*`.
The audit identifies the structural mismatches that block clean
mechanical translation.

Two mismatch patterns dominate (the prompt's "Blocker A" and "Blocker B"):

  - **Blocker A — redundant size const-generic.** Hacspec function
    declares `<const RANK, const EK_SIZE, const T_SIZE>` where
    `T_SIZE = EK_SIZE - 32 = RANK * BYTES_PER_RING_ELEMENT` is structurally
    derivable. From a libcrux call site, instantiating `T_SIZE` requires
    `K * BYTES_PER_RING_ELEMENT` — a const-expression that needs nightly
    `generic_const_exprs`. The crate is on stable. Fix: inline the
    typed-array intermediate, drop the redundant generic.
  - **Blocker B — slice vs sized-array.** Libcrux passes `&[u8]`
    (often a slice of a larger buffer); Hacspec demands `&[u8; N]`. The
    pure-Rust ensures would need `try_into().unwrap()`, which has zero
    precedent in the codebase's `requires`/`ensures` annotations.
    Spec-side fix: relax to `&[u8]` with a `len() == N` requires.

Other recurring patterns flagged in the audit:

  - **Blocker C — params-instance vs raw rank.** Hacspec functions take
    `params: &MlKemParams`; libcrux uses `const K: usize`. The bridge
    `parameters::rank_to_params(K)` already exists for this case (per
    commit `9dce36d6b`). Cited as **leave-as-is** when the bridge works.
  - **Blocker D — Result wrapper / return-type reshape.** Hacspec
    returns `Result<(ek, dk), BadRejectionSamplingRandomnessError>`
    (FIPS 203 modeling — sampling can fail with insufficient
    randomness). Libcrux returns `(sk, pk)` (sampling failure is
    encoded by an out-parameter `valid` bit in the `Spec.MLKEM` model).
    Pattern: pure-Rust ensures uses
    `match Hacspec_ml_kem.Ind_cca.generate_keypair ... with | Ok (ek, dk) -> ... | _ -> True`
    (see existing `ind_cca::generate_keypair` migration in commit
    `9ffc850db`).
  - **Blocker E — no Hacspec equivalent.** Several `Spec.MLKEM` symbols
    have no `hacspec_ml_kem::*` counterpart. Per the workflow, add
    helpers to `specs/ml-kem/src/parameters.rs` (rank-only) or
    appropriate spec module. Inventory below.

## Phase 1 audit table

### `libcrux-ml-kem/src/ind_cpa.rs`

| # | Function (file:line) | Hacspec counterpart | Mismatches | Recommendation |
|---|---|---|---|---|
| 1 | `serialize_public_key` (66) | `hacspec_ml_kem::serialize::serialize_public_key` (`serialize.rs:367`) | A: redundant `T_SIZE` const-generic (= `EK_SIZE - 32`). | **Refactor spec** — drop `T_SIZE`, inline `vector_encode_12` body or call its derivation from `EK_SIZE`. |
| 2 | `serialize_public_key_mut` (95) | none — no `*_mut` variant in spec | Spec only has the value-returning shape. | **Add spec helper** OR leave-as-is and bridge via `result == old_serialized.with_overwrite(serialize_public_key(...))`. Mechanical: cite `serialize_public_key` for the post-state value. |
| 3 | `serialize_vector` (130) `[lax]` | `hacspec_ml_kem::serialize::serialize_secret_key` (`serialize.rs:357`) ≅ `vector_encode_12` (`serialize.rs:200`) | A: redundant `T_SIZE` (= `RANK * BYTES_PER_RING_ELEMENT`). Slot-shape: spec returns `[u8; T_SIZE]`, impl writes into `&mut [u8]` — Blocker B mirror. | **Refactor spec** — split `serialize_secret_key_into(&mut [u8])` + drop `T_SIZE` from value-returning helper. Mechanical translation otherwise. |
| 4 | `sample_ring_element_cbd` (249) `[lax]` | spec `sample_secret(eta, prf_input)` (`ind_cpa.rs:19`) (single ring element) | Spec returns one polynomial; impl mutates a vector slot. Spec is `dyn-eta`, impl has `const ETA1, const ETA2`. | **Mechanical** with `K`-loop in ensures; cite `sample_secret(ETA2 as usize, prf_input)` per index. No spec edit. |
| 5 | `sample_vector_cbd_then_ntt` (365) `[lax]` | spec inlines via `createi(\|i\| sample_secret(...))` + `vector_ntt` (`ind_cpa.rs:97-114`) | No standalone `sample_vector_cbd_then_ntt` helper. | **Add spec helper** — `pub fn sample_vector_cbd_then_ntt<RANK>(prf_input: &[u8;33], eta, ds) -> Vector<RANK>` in `specs/ml-kem/src/sampling.rs`, mirroring the inlined form. |
| 6 | `generate_keypair_unpacked` (456) `[lax]` | none — spec `generate_keypair` returns serialized bytes only | Spec returns `Result<([u8; EK], [u8; DK])>`; impl mutates `IndCpaPrivateKeyUnpacked` + `IndCpaPublicKeyUnpacked` (which expose `t_as_ntt`, `seed_for_A`, `A` fields). | **Add spec helper** — extract `generate_keypair_unpacked<RANK>(d, k) -> Result<(t_as_ntt, seed_for_A, A_as_ntt, secret_as_ntt), _>` in `specs/ml-kem/src/ind_cpa.rs`, then have current `generate_keypair` call it. |
| 7 | `generate_keypair` (550) | `hacspec_ml_kem::ind_cca::generate_keypair` (`ind_cca.rs:219`) — note: matches CCA shape, not CPA | B: spec takes `&[u8; 64]` (full randomness), impl takes `&[u8]` (32-byte CPA seed). C: spec takes `&MlKemParams`. D: Result wrapper. **Different layer** — spec is CCA-level (calls `keygen_internal` which calls `ind_cpa::generate_keypair`). | **Add spec re-export** for `ind_cpa::generate_keypair` to expose CPA-level keygen externally; OR spec consumer cites `Hacspec_ml_kem.Ind_cpa.generate_keypair` directly. Slice issue: relax `&[u8; 32]` to `&[u8]` with len-requires. |
| 8 | `serialize_unpacked_secret_key` (587) `[lax]` | none — composition of `serialize_public_key` + `serialize_secret_key` | Pure mechanical wrap. | **Mechanical** — `result == (serialize_secret_key(secret_as_ntt), serialize_public_key(t_as_ntt, seed_for_A))`. |
| 9 | `compress_then_serialize_u` (610) `[lax]` | `hacspec_ml_kem::serialize::compress_then_serialize_u` (`serialize.rs:292`) | A: redundant `BLOCK_LEN`, `OUT_LEN` (derivable from `RANK * du * 32`). C: spec uses runtime `du: usize`, impl uses `const COMPRESSION_FACTOR`. Spec returns owned, impl writes into `&mut [u8]`. | **Refactor spec** — add `compress_then_serialize_u_into(&mut[u8])` variant; drop `OUT_LEN` from value-returning shape (already `const RANK, const U_SIZE`, so OK). |
| 10 | `encrypt_unpacked` (715) `[lax]` | none — spec inlines unpacked encrypt into `encrypt` (no separation) | Same shape gap as `generate_keypair_unpacked`. | **Add spec helper** — extract `encrypt_unpacked<RANK>(t_as_ntt, A, message, randomness) -> Result<[u8; CT_SIZE], _>`. |
| 11 | `encrypt_c1` (782) `[lax]` | none — internal step | Internal-only function (no FIPS 203 algorithm number). | **Mechanical / leave-as-is** — no functional ensures yet. |
| 12 | `encrypt_c2` (851) `[lax]` | none — internal step | Same as above. | **Mechanical / leave-as-is**. |
| 13 | `encrypt` (876) `[lax]` | `hacspec_ml_kem::ind_cpa::encrypt` (`ind_cpa.rs:180`) | B: spec takes `ek: &[u8]` (good), but with size-requires `RANK * BYTES_PER_RING_ELEMENT + 32`; impl `public_key: &[u8]` matches. C: `MlKemParams`. D: Result. A: Hacspec has redundant `U_SIZE, V_SIZE, CT_SIZE` const-generics (`U_SIZE = (RANK*256*du)/8` etc.). | **Refactor spec** — drop `U_SIZE`, `V_SIZE` const-generics by composing `[u8; CT_SIZE]` directly from compress→serialize ops; keep `CT_SIZE` since it's the return type. |
| 14 | `build_unpacked_public_key` (940) `[lax]` | none | Internal step. | **Mechanical**. |
| 15 | `build_unpacked_public_key_mut` (967) `[lax]` | none | Internal step. | **Mechanical**. |
| 16 | `deserialize_then_decompress_u` (1015) `[lax]` | `hacspec_ml_kem::serialize::deserialize_then_decompress_u` (`serialize.rs:322`) | C: runtime `du` vs `const`. Output: spec returns `Vector<RANK>` (decompressed only); impl ALSO does NTT (different name). | **Add spec helper** — `deserialize_then_decompress_u_then_ntt<RANK>(ciphertext, du)` that composes existing `deserialize_then_decompress_u` + `vector_ntt`. |
| 17 | `deserialize_vector` (1063) `[lax]` | `hacspec_ml_kem::serialize::vector_decode_12` (`serialize.rs:214`) | Spec returns `Vector<RANK>`; impl writes into `&mut [PolynomialRingElement; K]`. Slice/array OK on input. | **Mechanical** — cite `vector_decode_12` for post-state value. |
| 18 | `decrypt_unpacked` (1124) `[lax]` | none — spec only has packed `decrypt` | Same gap pattern. | **Add spec helper** — `decrypt_unpacked<RANK>(secret_as_ntt: Vector<RANK>, ciphertext) -> [u8; 32]`. |
| 19 | `decrypt` (1162) `[lax]` | `hacspec_ml_kem::ind_cpa::decrypt` (`ind_cpa.rs:280`) | B: spec uses `dk: &[u8]` ✓. C: `MlKemParams`. A: spec has runtime `du, dv` not const; OK because impl has `const U_COMPRESSION_FACTOR, V_COMPRESSION_FACTOR`. | **Mechanical** via `rank_to_params(K)`. |

### `libcrux-ml-kem/src/ind_cca.rs`

| # | Function (file:line) | Hacspec counterpart | Mismatches | Recommendation |
|---|---|---|---|---|
| 20 | `serialize_kem_secret_key_mut` (45) | none — internal serialization | Internal step (composition: cpa-sk ‖ cpa-pk ‖ H(pk) ‖ z). Already cites `Hacspec_ml_kem.Parameters.Sizes.*` (legacy). | **Mechanical migration** — replace `Parameters.Sizes` references with `MlKemParams::*` methods and `cpa_ciphertext_size`/`rank_to_params` helpers. |
| 21 | `serialize_kem_secret_key` (99) | same | same | Mechanical. |
| 22 | `validate_public_key` (131) | `hacspec_ml_kem::ind_cca::public_key_modulus_check` (`ind_cca.rs:246`) | C: `MlKemParams`. B: impl `&[u8; PUBLIC_KEY_SIZE]` matches spec exactly. **Already wired correctly!** | **Mechanical / already done** — uses `Parameters.Sizes` legacy alias; migrate to `rank_to_params(K).ek_size()`. Spec function shape is good. |
| 23 | `validate_private_key` (157) | none — no spec function for this hash check | Pure check, no functional ensures yet. | **Mechanical** — keep as `is_rank` + size requires; no functional ensures needed. |
| 24 | `validate_private_key_only` (176) | same | same | Mechanical. |
| 25 | `generate_keypair` (199) | `hacspec_ml_kem::ind_cca::generate_keypair` (`ind_cca.rs:219`) | **ALREADY MIGRATED** in commit `9ffc850db`. Currently cites `Hacspec_ml_kem.Ind_cca.generate_keypair` and `rank_to_params`. C: spec uses `MlKemParams` ✓. D: Result ✓. B: spec `&[u8; 64]` vs impl `&[u8; KEY_GENERATION_SEED_SIZE]` ✓ (sizes match). | **Done** — pattern reference for other migrations. |
| 26 | `encapsulate` (251) | `hacspec_ml_kem::ind_cca::encapsulate` (`ind_cca.rs:279`) | C: `MlKemParams`. D: Result. B: spec `ek: &[u8; EK_SIZE]` matches impl `MlKemPublicKey<PUBLIC_KEY_SIZE>::value: &[u8; SIZE]`. A: spec has redundant `U_SIZE, V_SIZE` (derivable). Return shape: spec `(shared, ct)` vs impl `(MlKemCiphertext, shared)` — **order swap**. | **Refactor spec** — drop `U_SIZE, V_SIZE` from `encapsulate` signature (compose internally). Then mechanical with `rank_to_params(K)` and order-swap in ensures. |
| 27 | `decapsulate` (326) `[panic_free]` | `hacspec_ml_kem::ind_cca::decapsulate` (`ind_cca.rs:321`) | C: `MlKemParams`. D: Result. A: spec has redundant `EK_SIZE, DK_PKE_SIZE, U_SIZE, V_SIZE, CT_SIZE, J_INPUT_SIZE` const-generics (all derivable). | **Refactor spec** — drop all redundant size const-generics; keep only `RANK` and the user-facing `DK_SIZE`/`CT_SIZE` if they need to stay in the signature. |
| 28 | `unpacked::unpack_public_key` (498) | none | Spec doesn't model unpacked APIs at all. | **Add spec helper** — `unpack_public_key<RANK>(ek) -> (t_as_ntt, A, seed, hash)`. Or leave-as-is; this is impl-internal. |
| 29 | `unpacked::serialized_mut/serialized` (561, 587) | `hacspec_ml_kem::serialize::serialize_public_key` | Same as #1, #2. | Same as #1, #2. |
| 30 | `unpacked::keys_from_private_key` (612) | none | Internal step. | **Mechanical**. |
| 31 | `unpacked::serialized_public_key_mut/serialized_public_key` (704, 727) | `serialize_public_key` | Same as #1, #2 + `MlKemKeyPairUnpacked` field-access. | Same. |
| 32 | `unpacked::serialized_private_key_mut/serialized_private_key` (751, 783) | none | Composition of `serialize_unpacked_secret_key` + `serialize_kem_secret_key`. | **Mechanical**. |
| 33 | `unpacked::transpose_a` (817) | `hacspec_ml_kem::matrix::transpose` (`matrix.rs:56`) | Spec is generic, takes `&Matrix<RANK>`, returns `Matrix<RANK>`; impl takes by value, returns by value. Otherwise compatible. | **Mechanical** — cite `transpose(&ind_cpa_a)`. |
| 34 | `unpacked::generate_keypair` (871) | `hacspec_ml_kem::ind_cca::generate_keypair` + spec extension for unpacked | Spec only models packed keygen; the unpacked variant exposes `m_A`, `public_key_hash`, `implicit_rejection_value` separately. | **Add spec helper** — `ind_cca_unpack_generate_keypair<RANK>(randomness) -> Result<((m_A, hash), implicit_rejection), _>` in `specs/ml-kem/src/ind_cca.rs`. |
| 35 | `unpacked::encapsulate` (948) | `hacspec_ml_kem::ind_cca::encapsulate` extension | Spec consumes raw `ek: &[u8]`; impl consumes `MlKemPublicKeyUnpacked` (with t_as_ntt, A, hash). | **Add spec helper** — `ind_cca_unpack_encapsulate<RANK>(hash, t_as_ntt, A, randomness) -> ([u8; CT], shared)`. |
| 36 | `unpacked::encaps_prepare` (996) | `parameters::hash_functions::G` | Trivially `result == G(concat(randomness, pk_hash))`. | **Mechanical**. |
| 37 | `unpacked::decapsulate` (1040) | `hacspec_ml_kem::ind_cca::decapsulate` extension | Same shape gap as #34. | **Add spec helper** — `ind_cca_unpack_decapsulate<RANK>(hash, implicit_rejection, ct, secret_as_ntt, t_as_ntt, A) -> [u8; 32]`. |

## Missing Hacspec equivalents — proposed parameters.rs additions

The following `Spec.MLKEM` symbols appear in `requires`/`ensures` but
have no `hacspec_ml_kem::*` analogue. All are rank-derivable, so they
become free functions in `specs/ml-kem/src/parameters.rs`:

| `Spec.MLKEM` symbol | Proposed `hacspec_ml_kem` form | Where used |
|---|---|---|
| `v_T_AS_NTT_ENCODED_SIZE $K` | `MlKemParams::t_as_ntt_encoded_size()` ✓ already exists; need rank-generic `t_as_ntt_encoded_size(rank)` free fn | encrypt, decapsulate, unpack |
| `v_C1_SIZE $K` | new `c1_size(rank: usize) -> usize` | encrypt, decrypt, decapsulate |
| `v_C2_SIZE $K` | new `c2_size(rank: usize) -> usize` (constant 128 or 160) | encrypt, decrypt, decapsulate |
| `v_VECTOR_U_COMPRESSION_FACTOR $K` | new `vector_u_compression_factor(rank: usize) -> usize` | encrypt, decrypt |
| `v_VECTOR_V_COMPRESSION_FACTOR $K` | new `vector_v_compression_factor(rank: usize) -> usize` | encrypt, decrypt |
| `v_C1_BLOCK_SIZE $K` | new `c1_block_size(rank: usize) -> usize` | encrypt, deserialize |
| `v_ETA1 $K`, `v_ETA2 $K` | new `eta1(rank)`, `eta2(rank)` | sample_*, generate_keypair |
| `v_ETA1_RANDOMNESS_SIZE $K` | new `eta1_randomness_size(rank)` | encrypt |
| `v_ETA2_RANDOMNESS_SIZE $K` | new `eta2_randomness_size(rank)` | encrypt |
| `v_CCA_PRIVATE_KEY_SIZE $K` | new `cca_private_key_size(rank)` | serialize_kem, validate, decapsulate |
| `v_CPA_PRIVATE_KEY_SIZE $K` | new `cpa_private_key_size(rank)` | generate_keypair, decrypt |
| `v_CPA_KEY_GENERATION_SEED_SIZE` (constant 32) | already `parameters::hash_functions::H_DIGEST_SIZE` adjacent; add `CPA_KEY_GENERATION_SEED_SIZE: usize = 32` | generate_keypair |
| `v_SHARED_SECRET_SIZE` (constant 32) | add `SHARED_SECRET_SIZE: usize = 32` | encapsulate, decapsulate |
| `v_IMPLICIT_REJECTION_HASH_INPUT_SIZE $K` | new `implicit_rejection_hash_input_size(rank)` = `32 + cpa_ciphertext_size(rank)` | decapsulate |
| `v_RANKED_BYTES_PER_RING_ELEMENT $K` | new `ranked_bytes_per_ring_element(rank)` = `rank * 384` | serialize_public_key_mut |

All of these compose trivially: the rank-only functions follow the
`cpa_ciphertext_size` pattern (commit `9dce36d6b`), with a 3-way `if`
on rank ∈ {2,3,4}.

## Disposition / sequencing for Phase 2

Priority order for spec edits (smallest blast radius first):

  **P1 — additive: parameters.rs helpers.** Adds new free functions;
  no breaking changes to extracted F* signatures. Single commit covers
  all the rows in the Missing-Hacspec-equivalents table. Validates by
  re-extract + verifying `Hacspec_ml_kem.Parameters.fst.checked` builds.

  **P2 — Blocker A fixes for serialize.rs.** Drop `T_SIZE` from
  `serialize_public_key`, `serialize_secret_key`, `vector_encode_12`.
  Affects 3 spec functions, 3 commute-side files maybe. Re-extract and
  verify `Hacspec_ml_kem.Serialize.fst.checked` + downstream.

  **P3 — Blocker A fixes for ind_cpa.rs.** Drop `U_SIZE, V_SIZE` from
  `encrypt`. Drop `DK_PKE_SIZE` from `generate_keypair` (still needed?
  it's a parallel-named const that = `RANK * 384`). Re-verify.

  **P4 — Blocker A fixes for ind_cca.rs.** Drop redundant generics
  from `encapsulate`, `decapsulate`. Re-verify.

  **P5 — add unpacked-shape spec helpers** (`generate_keypair_unpacked`,
  `encrypt_unpacked`, `decrypt_unpacked`, plus `ind_cca_unpack_*`
  versions). These are functional-correctness scaffolding for the
  unpacked-API ensures; they unblock items 6, 10, 18, 34, 35, 37.
  Adds new spec functions; no breaking changes to existing.

Each Phase 2 step should commit separately under `agent-mlkem:` prefix.

## Phase 3 — strengthening inventory

`grep` from briefing produced these matches:

  - `specs/ml-kem/src/parameters.rs:155,162,167,172,177` —
    `#[hax_lib::opaque]` on `G`, `H`, `PRF`, `XOF`, `J` hash-function
    wrappers. **Justified** — these wrap `hacspec_sha3::*` which is a
    different verification crate; opacity here is the spec-side
    interface to those primitives. **Leave as-is.**
  - `specs/ml-kem/src/ntt.rs:225` — `verification_status(panic_free)`
    on (line below to be confirmed). Means the body verifies but the
    `ensures` is admitted. The `Hacspec_ml_kem.Ntt.fst:254` extracted
    file shows `let _:Prims.unit = admit () (* Panic freedom *) in`
    confirming the panic-freedom obligation is the only admit.
    **Disposition: confirm if there are any non-trivial ensures
    being skipped; if only panic-freedom of indexing into bounded
    arrays, write the proof. Else leave with comment.**
  - `specs/ml-kem/src/serialize.rs:187` —
    `verification_status(panic_free)` on `byte_decode`. Has a
    real ensures (`hax_lib::forall(|i| ... result[i].val < (1u16 << d))`)
    that IS being verified (panic_free admits ensures? per
    `feedback_panic_free_vs_lax` panic_free admits ensures). Wait —
    this would mean the `forall` ensures is actually admitted.
    **Investigate and discharge if feasible.**
  - Extracted F* admits:
    - `Hacspec_ml_kem.Serialize.fst:313` — `admit () (* Panic freedom *)`
    - `Hacspec_ml_kem.Ntt.fst:254` — `admit () (* Panic freedom *)`

Action plan:
  1. Audit `serialize.rs:byte_decode` — check whether the `forall`
     post is provable inline or needs a lemma. If a lemma, factor it
     into a separate `pub fn` with its own panic_free + own proof.
  2. Audit `ntt.rs:225` — likely an indexing panic-freedom claim.
     If the structural index-bound is obvious from a loop invariant,
     replace `panic_free` with the default and add the invariant.
  3. Both are bounded-effort: ~30 min cap each.

---

# Session execution log (Phase 2 + Phase 3)

## Phase 2 spec changes

| Step | Commit | File | Before / After | Validation |
|---|---|---|---|---|
| **P1** | `329d4195e` | `specs/ml-kem/src/parameters.rs` | Added 16 rank-generic free-fn helpers + 2 constants (`SHARED_SECRET_SIZE`, `CPA_KEY_GENERATION_SEED_SIZE`, `t_as_ntt_encoded_size`, `ranked_bytes_per_ring_element`, `cpa_public_key_size`, `cpa_private_key_size`, `cca_private_key_size`, `vector_u_compression_factor`, `vector_v_compression_factor`, `c1_block_size`, `c1_size`, `c2_size`, `eta1`, `eta2`, `eta1_randomness_size`, `eta2_randomness_size`, `implicit_rejection_hash_input_size`).  All follow the `cpa_ciphertext_size`/`rank_to_params` 3-way `if` pattern. | `Hacspec_ml_kem.Parameters.fst.checked` re-verifies in 7s; max rlimit ≤15. |
| **P2** | `57d1a5e61` | `specs/ml-kem/src/serialize.rs:367-376` | `serialize_public_key<RANK, EK_SIZE, T_SIZE>` → `serialize_public_key<RANK, EK_SIZE>`.  Body inlines per-ring-element `byte_encode` writes directly into `ek` instead of constructing a typed `[u8; T_SIZE]` intermediate. | `Hacspec_ml_kem.Serialize.fst.checked` re-verifies in 4.7s.  No changes to commute lemmas needed (no commute references to `serialize_public_key`). |
| **P3** | `e63973e54` | `specs/ml-kem/src/ind_cpa.rs:79-82` | `ind_cpa::generate_keypair(..., key_generation_seed: &[u8; 32])` → `(..., key_generation_seed: &[u8])` with `len() == 32` requires.  Body unchanged. | `Hacspec_ml_kem.Ind_cpa.fst.checked` and `Hacspec_ml_kem.Ind_cca.fst.checked` re-verify clean.  Sole internal caller (`ind_cca::keygen_internal`) unchanged — Rust auto-coerces `&[u8;32]` → `&[u8]`. |

### Why P3/P4 (audit's Blocker A on encrypt/encapsulate/decapsulate) was skipped

After P2 the audit table flagged `encrypt::<RANK, U_SIZE, V_SIZE,
CT_SIZE>` and `encapsulate::<RANK, EK_SIZE, U_SIZE, V_SIZE, CT_SIZE>`
as Blocker A candidates (drop `U_SIZE, V_SIZE`).  Closer inspection of
the libcrux call sites reversed this recommendation:

- `libcrux-ml-kem/src/ind_cpa.rs:898` declares `encrypt<K, CIPHERTEXT_SIZE,
  T_AS_NTT_ENCODED_SIZE, C1_LEN, C2_LEN, ...>` — **already** carries
  `C1_LEN`/`C2_LEN` as separate const-generics.
- `libcrux-ml-kem/src/ind_cca.rs:268` declares `encapsulate<K,
  CIPHERTEXT_SIZE, PUBLIC_KEY_SIZE, T_AS_NTT_ENCODED_SIZE, C1_SIZE,
  C2_SIZE, ...>` — same shape.

So the Hacspec `<RANK, U_SIZE, V_SIZE, CT_SIZE>` is a **structural
match** for the libcrux call site, not a mismatch.  Dropping them would
introduce a mismatch.  P3/P4 in the original audit plan were
**inverted recommendations**; this session corrects them by leaving
those signatures unchanged and instead applying P3 to the genuine
Blocker B (slice vs sized-array on `key_generation_seed`).

### P5 (unpacked-shape spec helpers) — deferred

Adding `generate_keypair_unpacked`, `encrypt_unpacked`,
`decrypt_unpacked`, `ind_cca_unpack_*` would unblock unpacked-API
ensures (audit rows 6, 10, 18, 34, 35, 37).  Each is a non-trivial new
spec function defining its own `Result<(...), _>` shape.  Estimated
30-60 min per helper × 6 helpers = out of session budget.  Deferred to
a follow-up session.

## Phase 3 strengthenings

| Item | Outcome | Commit | Reason |
|---|---|---|---|
| `parameters.rs` `#[hax_lib::opaque]` on G/H/PRF/XOF/J | **Leave as-is** | — | Wrap `hacspec_sha3::*` (different verification crate); opacity is the intended spec-side interface to SHA-3 primitives. |
| `ntt.rs:225` `get_zeta` `panic_free` (ensures `r.val >= 1`) | **Documented; kept `panic_free`** | `a4890d89a` | Tried removing `panic_free`.  Z3 fails: it knows ZETAS is a 128-element array but cannot materialize the contents to prove the per-element bound for an arbitrary index.  Bumping rlimit to 400 + fuel/ifuel didn't help (used rlimit 1).  Discharge requires a per-index `match` rewrite or an array-content axiom (R3 forbids axioms).  Out of 30-min budget. |
| `serialize.rs:187` `byte_decode` `panic_free` (ensures `forall i. result[i].val < (1u16 << d)`) | **Documented; kept `panic_free`** | `76baea2b1` | A clean discharge needs (1) ensures on `bitvector_to_bounded_ints`, (2) propagation through `byte_decode_generic`, (3) case-split on `d == 12` vs `d < 12` at `byte_decode` (because `1u16 << d` for symbolic `d` resists Z3 simplification).  Estimated >30 min, out of budget. |
| `Hacspec_ml_kem.Serialize.fst:313` extracted `admit ()` | Same as above (it's the panic-freedom admit injected by `panic_free`) | — | — |
| `Hacspec_ml_kem.Ntt.fst:254` extracted `admit ()` | Same as above | — | — |

No `lax`, no `ADMIT_MODULES`, no `--admit_smt_queries` markers in the
spec extraction.  The two `admit ()` lines are the standard panic-freedom
admits emitted by `verification_status(panic_free)`.

## Open items / blockers / suggested next-session work

### Blockers carried over (not introduced this session)

1. **`Libcrux_ml_kem.Ind_cca.fsti:165`** — `Spec.MLKEM` not resolved.
   Pre-existing impl-side blocker.  User has indicated they'll fix via
   "additional conditions" in the .fsti requires/ensures rather than a
   full migration.  Per the existing next-session prompt.

2. **`Hacspec_ml_kem.Commute.Chunk.fst:1046`** —
   `lemma_compress_1_chunk_commutes` fails with `Assertion failed` on
   the `reveal_opaque (\`%TS.compress_1_lane_post)` call.  Confirmed
   pre-existing (`git stash` baseline reproduces).  Blocks
   `Hacspec_ml_kem.Commute.Bridges.fst.checked` transitively.  Likely
   tied to the `hax-lib` upgrade since the audit was written.  Needs a
   targeted lemma fix or a `--split_queries always` per-branch
   workaround.

### Suggested next-session work (priority order)

1. **Per-function pure-Rust migration of `ind_cpa.rs` annotations**
   using the new P1 helpers.  Mechanical; the helpers are now in place.
   The `key_generation_seed: &[u8]` shape (P3) means `generate_keypair`
   and `keygen_internal` migrations are now trivial (no `try_into`).

2. **Per-function pure-Rust migration of `ind_cca.rs` annotations**.
   `encapsulate` / `decapsulate` are now ready: their Hacspec
   counterparts have signatures that structurally match the libcrux
   call site.  Cite `rank_to_params(K)` for the `MlKemParams` arg.

3. **Resolve Commute.Chunk failure** (separate session, separate
   sprint) — would unblock the full commute-side build.

4. **P5 unpacked-shape spec helpers** — only needed when the
   `ind_cca::unpacked::*` migration is on the critical path.

## Final tip / commits added

Tip SHA: `76baea2b1`.

Commits added this session (in order):

- `16ab471a4` — `agent-mlkem: spec audit before refactor` (Phase 1)
- `329d4195e` — `agent-mlkem: specs/ml-kem — add rank-generic size helpers (P1)`
- `57d1a5e61` — `agent-mlkem: specs/ml-kem — drop redundant T_SIZE generic from serialize_public_key (P2)`
- `e63973e54` — `agent-mlkem: specs/ml-kem — relax ind_cpa::generate_keypair seed to slice (P3)`
- `a4890d89a` — `agent-mlkem: specs/ml-kem — document why get_zeta keeps panic_free (Phase 3)`
- `76baea2b1` — `agent-mlkem: specs/ml-kem — document why byte_decode keeps panic_free (Phase 3)`

Total: **6 commits**, all on `libcrux-ml-kem-proofs`, branch tip 5
ahead of `origin/libcrux-ml-kem-proofs`.

### Self-audit (R10 + R11)

- **R10 (no wrappers, no namespace squatting)**: All P1 additions are
  free functions in the existing `specs/ml-kem/src/parameters.rs` —
  no new top-level Hacspec_ml_kem F* file created, no `unfold let`
  alias over `Spec.MLKEM`, no wrapper.
- **R11 (no `fstar!` escape in ind_cpa/ind_cca annotations)**: This
  session edited `specs/ml-kem/src/*` only; did NOT touch
  `libcrux-ml-kem/src/{ind_cpa,ind_cca}.rs` annotations.
- **R3 (no new axioms)**: None introduced.  The `--fuel 0 --ifuel 0`
  attempt on `get_zeta` was reverted.
- **R4 (rlimit ≤ 800)**: Max rlimit used in any new annotation: 400
  (the abandoned `get_zeta` attempt).  All shipped annotations use
  the default 150 inherited from the existing module options.
- **R6 (touch unchanged checked files)**: Done after every
  `cargo hax into fstar` invocation in this session.
- **R8 (no fstar-mcp)**: Confirmed; used `make` only.

