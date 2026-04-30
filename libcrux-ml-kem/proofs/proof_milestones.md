# ML-KEM Proof Milestones

Hand-curated tracker of *meaningful* proof outcomes, complementing the
mechanical `verification_status.md` tier counts. Each row is a named
proof goal; status is a judgment call based on inspecting the owning
function's `#[ensures(...)]` text and body annotations on
`trait-opacify` (HEAD `19ac49f8e`).

## Status legend

- ✅ **Proven** — ensures cites `Hacspec_ml_kem.*` (or equivalent),
  body verifies (no admits).
- 🔶 **Spec stated, body admitted** — ensures is the right shape but
  the body has `--admit_smt_queries true` or inline `admit ()`. Tracked
  as USER-N. Distance: closing the named user task.
- ⚠️ **Bounds only** — ensures proves a range/interval predicate; no
  hacspec equivalence.
- ❌ **No claim** — function has no ensures (panic-free only) or is
  unverified at any tier.

## Distance bands

- *(done)* — proof complete.
- *1 user-task* — known scope, filed as USER-N; ~0.5-1 sprint each.
- *~1 sprint* — needs spec definition + ensures + proof for a single
  function or small group.
- *~2-3 sprints* — multi-component (whole module).
- *many sprints* — needs design + spec + multi-fn proof; not started.

---

## Layer 1 — NTT (forward & inverse)

| # | Milestone | Owner fn (file:line) | Status | Distance |
|---|---|---|---|---|
| 1 | Forward NTT layer 1-7 correct vs hacspec | `src/ntt.rs::ntt_at_layer_{1,2,3,4_plus,7}` | ⚠️ partial — layers 1 ✅ (commit `c32653051`, 349 s) and 2 ✅ (this session, bridge + impl, ~500 s combined) closed via mirror of inverse pattern. Layers 3/4_plus/7 ❌ no claim. Layer 3 needs bridge `lemma_ntt_layer_3_step_to_hacspec` (mirror inverse `fa2151ea8` then impl wiring). Layer 4_plus is multi-step like inverse — spec design needed. Layer 7 (single-zeta, between-chunk butterfly) is structurally novel — needs its own bridge design. | ~1-2 sprints — author bridge for layer 3 (~1 session), wire impl (~1 session); layer 4_plus + 7 are separate design efforts. |
| 2 | Top-level forward NTT correct | `src/polynomial.rs::ntt` (top-level) | ❌ no top-level ensures | composes off (1); 1 session once (1) is done |
| 3 | Inverse NTT layer 1 correct vs hacspec | `src/invert_ntt.rs:36 invert_ntt_at_layer_1` | ✅ proven — ensures cites `Hacspec_ml_kem.Invert_ntt.ntt_inverse_layer_n`, body uses `lemma_inv_ntt_layer_1_step_to_hacspec` | *(done)* |
| 4 | Inverse NTT layer 2 correct vs hacspec | `src/invert_ntt.rs:168 invert_ntt_at_layer_2` | ⚠️ bounds only at this layer; per-chunk hacspec via trait `inv_ntt_layer_2_step_branch_post`; body proven today (USER-13, commit `200b01f66`) | ~1 session to upgrade post from bounds to per-chunk-hacspec equality (`lemma_inv_ntt_layer_2_step_to_hacspec` exists in Bridges; just plumb it into the function ensures) |
| 5 | Inverse NTT layer 3 correct vs hacspec | `src/invert_ntt.rs:228 invert_ntt_at_layer_3` | ✅ proven — ensures cites `Hacspec_ml_kem.Invert_ntt.ntt_inverse_layer_n`, body uses `lemma_inv_ntt_layer_3_step_to_hacspec` (and SD4 fix today) | *(done)* |
| 6 | Inverse NTT layer 4+ correct vs hacspec | `src/invert_ntt.rs:451 invert_ntt_at_layer_4_plus` | 🔶 ensures cites `IN.ntt_inverse_layer p layer`; body `--admit_smt_queries true` (USER-14) | **1 user-task: USER-14** — discharge body chain from 16 chunk-pair `inv_ntt_layer_int_vec_step_reduce` posts to polynomial-level claim (the chunk-pair bridge already exists; gap is the lift) |
| 7 | Top-level inverse NTT correct (Montgomery form) | `src/invert_ntt.rs:589 invert_ntt_montgomery` | 🔶 ensures cites `Hacspec_ml_kem.Invert_ntt.ntt_inverse_butterflies`; body `--admit_smt_queries true` (USER-15) | **1 user-task: USER-15** — definitional unfolding lemma chaining 7 layer calls into `ntt_inverse_butterflies`; spec exists, ~1-2 sessions |
| 8 | NTT multiply correct vs hacspec | `src/polynomial.rs:920 ntt_multiply` | ❌ no hacspec citation in ensures (only bounds) | ~1 sprint — needs hacspec spec citation + per-fn proof |
| 9 | Per-vector NTT bridge (16-lane → polynomial) | `Hacspec_ml_kem.Commute.Bridges.lemma_inv_ntt_layer_*_step_to_hacspec` | ✅ proven for layers 1, 2, 3 (commit `b7b49c358`) | *(done for inverse)* — forward direction's per-layer Bridges lemmas don't exist yet |

## Layer 2 — Serialization / Encoding

ml-kem operates on 256-coefficient ring elements with several
compression widths: `d ∈ {1, 4, 5, 10, 11, 12}` for serialize,
`d ∈ {1, 4, 5, 10, 11}` for compress/decompress. The trait-level
`serialize_d`/`deserialize_d` posts wire to the spec via
`Spec.Utils.bit_vec_of_*` axioms (USER-9a/b).

| # | Milestone | Owner fn (file:line) | Status | Distance |
|---|---|---|---|---|
| 10 | Trait `serialize_d`/`deserialize_d` correct vs spec (per width) | `src/vector/traits.rs:1357-1407` (per width) | ⚠️ **partial** — widths 5 + 11 wired (USER-9a/b, commit `107c76641`); widths 1 + 4 + 10 + 12 + the d-arg `compress_d` family still panic-free only | ~2 sessions per width — write `bit_vec_of_int_t_array` axiom + wire trait post |
| 11 | `compress_then_serialize_message` correct vs hacspec | `src/serialize.rs:25` | ❌ panic-free only | ~1-2 sessions — needs `Hacspec_ml_kem.Serialize.compress_then_serialize_message` spec + ensures |
| 12 | `deserialize_then_decompress_message` correct vs hacspec | `src/serialize.rs:64` | ❌ panic-free only | ~1-2 sessions — same shape as (11) |
| 13 | `serialize_uncompressed_ring_element` correct vs hacspec | `src/serialize.rs:90` | ❌ panic-free only | ~1 session |
| 14 | `deserialize_to_uncompressed_ring_element` correct vs hacspec | `src/serialize.rs:120` | ❌ panic-free only | ~1 session |
| 15 | `compress_then_serialize_ring_element_u/v` correct vs hacspec | `src/serialize.rs:266, 353` | ❌ panic-free only | ~2 sessions each (compose per-coefficient compress + per-width serialize) |
| 16 | `deserialize_then_decompress_ring_element_u/v` correct vs hacspec | `src/serialize.rs:440, 523` | ❌ panic-free only | ~2 sessions each |
| 17 | `compress_d`/`decompress_d` per-width correct vs hacspec | `src/vector/portable/compress.rs` (5 widths × 2 directions) | ⚠️ **partial** — 1 hacspec, rest panic-free; USER-13 originally tracked the 3 chunk wrappers (`compress_1`, `compress_d`, `decompress_d`) — Z3-walled, deferred | ~1 sprint — re-attempt under SD4 (Rule SD4 from today's commit may unlock) |
| 18 | `Hacspec_ml_kem.Serialize.HacspecBridge` (axiom-bridge layer) | `Hacspec_ml_kem.Serialize.HacspecBridge.fst` | ❌ **abandoned approach** — branch `agent/phase-7c-serialize` (11 commits, not merged); Wave-B A1 took the per-fn `panic_free` strategy instead | superseded — the per-width route in (10) is the active path |

## Layer 3 — Top-level KEM API

| # | Milestone | Owner fn (file:line) | Status | Distance |
|---|---|---|---|---|
| 19 | `MlKem*::generate_key_pair` panic-free | `src/mlkem512.rs:105`, `mlkem768.rs:105`, `mlkem1024.rs:105` | 🔶 extracted, body admitted — milestone #0 closed: `incremental` cargo feature added to `hax.py`; new modules `Mlkem*.Incremental.*` and `Ind_cca.Incremental.*` extract and are admitted in `Makefile` ADMIT_MODULES pending per-fn PF | ~1 session — strengthen `pk1_len()`/`pk2_len()`/`key_pair_len()` ensures with usize bounds, then drop ADMIT_MODULES entries. The Box<dyn>/`try_fill_bytes` runtime-dispatch helpers (`.Alloc`, `.Incremental.Rand`) are deleted post-extraction. |
| 20 | `MlKem*::generate_key_pair` correct vs hacspec | same | ❌ no claim possible until (19) | needs hacspec spec for `kem_keygen_d`; ~2 sprints once extraction lands |
| 21 | `MlKem*::encapsulate` panic-free | `src/mlkem768.rs:139` etc. | ❌ unverified — same extraction gap | gated on (19) |
| 22 | `MlKem*::encapsulate` correct vs hacspec | same | ❌ no claim | gated on (19); needs `Hacspec_ml_kem.encapsulate` spec finalized |
| 23 | `MlKem*::decapsulate` panic-free | `src/mlkem768.rs:192` etc. | ❌ unverified — same | gated on (19) |
| 24 | `MlKem*::decapsulate` correct vs hacspec | same | ❌ no claim | gated on (19) |
| 25 | `MlKem*::validate_public_key/private_key` correct | `src/mlkem768.rs:71, 81, 95` | ❌ unverified | gated on (19) |
| 26 | `Ind_cca::encapsulate` correct vs hacspec | `src/ind_cca.rs` | ⚠️ partial — 11 hacspec / 27 fns; 14 PF, 3 Math (Hacspec_ml_kem citations exist for some but not the top-level entries) | ~1-2 sprints |
| 27 | `Ind_cpa::encapsulate/decapsulate` panic-free | `src/ind_cpa.rs` | 🔶 **all 21 fns lax** — `Ind_cpa.fst` is in `ADMIT_MODULES`. Milestone #1 attempted bulk un-admit on 2026-04-30; failed because `serialize_vector` (line 25-108, rlimit 1000) hit "incomplete quantifiers" at the line-105 assertion after 202 s — known blocker. Other 18 fns may be PF-clean already; needs per-fn audit. | ~2 sprints — surface `serialize_vector` as `verification_status(lax)` per-fn (or strengthen its loop invariants), then drop module-level admit; remaining fns likely verify. |
| 28 | `Ind_cca` correct vs hacspec (composition) | top-level over (19)-(27) | ❌ blocked on (19) + (26) + (27) | many sprints |

## Headline interpretation

The script's "Hacspec: 98/934 (10.5%)" on trait-opacify is concentrated
in:
- 4 inverse-NTT layers (rows 3, 5; row 4's per-chunk fact via trait branch_post)
- Trait-level `inv_ntt_layer_*_step_branch_post` (per-lane / per-branch
  predicates wired via SD3) — the 27 + 23 in Portable/Avx2 vectors are
  these trait posts.
- Hash_functions (28 of 49 fns) and Ind_cca (11 of 27).

What the count does NOT reflect:
- Inverse NTT layers 4+ and Montgomery have hacspec ensures but body
  admitted (rows 6, 7) — they show as Lax in the script. The contract
  is in place; the proof is the gap.
- The forward NTT has ZERO hacspec claims. Adding the spec citation is
  the missing first step.
- The KEM API has zero claims AND zero extraction.

## Next-priority order (for closing high-value milestones)

1. **USER-13 follow-up: row 4** — upgrade `invert_ntt_at_layer_2`'s
   bounds-only post to hacspec equality. Cheapest milestone (~1
   session). The `lemma_inv_ntt_layer_2_step_to_hacspec` is already
   proven; just thread it into the function ensures.
2. **USER-15: row 7** — close `invert_ntt_montgomery` body. Unblocks
   the consumer chain (Polynomial.subtract_reduce, Matrix.compute_message).
3. **USER-14: row 6** — close `invert_ntt_at_layer_4_plus` body.
4. **Forward NTT spec wiring (rows 1, 2, 8)** — the bounds-only ensures
   are already there; adding hacspec citations is mechanical once
   `Hacspec_ml_kem.Ntt.ntt_at_layer_n` is finalized.
5. **mlkem.rs extraction (row 19)** — gates the entire KEM API.
6. **Serialize per-width hacspec (rows 10, 17)** — methodical width-by-width.
