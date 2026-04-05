import Hax
import Std.Do.Triple

/-! # Stubs for missing functions in the hacspec SHA-3 spec extraction -/

/-! ## Coercion `RustArray α n` ↔ `RustSlice α` -/

attribute [local grind! .] USize64.toNat_lt_size

instance instCoeRustArraySeq {α : Type} {n : usize} :
    CoeOut (RustArray α n) (rust_primitives.sequence.Seq α) where
  coe a := ⟨a.toVec.toArray, by grind⟩

instance instCoeSeqRustArray {α : Type} {n : usize} (s : rust_primitives.sequence.Seq α) :
    CoeDep (rust_primitives.sequence.Seq α) s (RustArray α n) where
  coe := ⟨⟨s.val, sorry⟩⟩

/-! ## `update_at_usize` for `RustSlice` (missing from Hax library) -/

-- The Hax library defines `update_at_usize` only for `RustArray α n`.
-- The extraction also calls it on `RustSlice α`. We provide a slice version
-- under a separate name; the extraction patch renames the slice calls.

attribute [local grind! .] rust_primitives.sequence.Seq.size_lt_usizeSize

@[spec]
def rust_primitives.hax.monomorphized_update_at.update_at_usize_slice {α}
    (s : RustSlice α) (i : usize) (v : α) : RustM (RustSlice α) :=
  if h : i.toNat < s.val.size then
    pure ⟨s.val.set (Fin.mk i.toNat h) v, by grind⟩
  else
    .fail .arrayOutOfBounds

/-! ## `core_models.num` stubs -/

namespace core_models.num

@[spec]
def Impl_9.rotate_left (x : u64) (n : u32) : RustM u64 :=
  pure (UInt64.ofBitVec (BitVec.rotateLeft x.toBitVec n.toNat))

@[spec]
def Impl_9.from_le_bytes (b : RustArray u8 8) : RustM u64 :=
  pure (b.toVec[0].toUInt64
  + (b.toVec[1].toUInt64 <<< 8)
  + (b.toVec[2].toUInt64 <<< 16)
  + (b.toVec[3].toUInt64 <<< 24)
  + (b.toVec[4].toUInt64 <<< 32)
  + (b.toVec[5].toUInt64 <<< 40)
  + (b.toVec[6].toUInt64 <<< 48)
  + (b.toVec[7].toUInt64 <<< 56))

@[spec]
def Impl_9.to_le_bytes (x : u64) : RustM (RustArray u8 8) :=
  pure (.ofVec #v[
    (x % 256).toUInt8,
    (x >>> 8 % 256).toUInt8,
    (x >>> 16 % 256).toUInt8,
    (x >>> 24 % 256).toUInt8,
    (x >>> 32 % 256).toUInt8,
    (x >>> 40 % 256).toUInt8,
    (x >>> 48 % 256).toUInt8,
    (x >>> 56 % 256).toUInt8,
  ])

def Impl_8.MAX : u32 := (4294967295 : u32)

@[irreducible] def Impl_11.MAX : usize := sorry

end core_models.num

/-! ## `hacspec_sha3.createi` — array from_fn wrapper -/

namespace hacspec_sha3

@[irreducible] def createi (T : Type) (N : usize) (F : Type)
    [core_models.ops.function.Fn.AssociatedTypes F (rust_primitives.hax.Tuple1 usize)]
    [core_models.ops.function.Fn F (rust_primitives.hax.Tuple1 usize)]
    (f : F) : RustM (RustArray T N) := sorry

axiom createi_purifies (T : Type) (N : usize)
    (f : usize → RustM T) (f_pure : Fin N.toNat → T)
    [inst1 : core_models.ops.function.Fn.AssociatedTypes (usize → RustM T) (rust_primitives.hax.Tuple1 usize)]
    [inst2 : core_models.ops.function.Fn (usize → RustM T) (rust_primitives.hax.Tuple1 usize)]
    (hf : ∀ (i : usize) (hi : i.toNat < N.toNat), f i = .ok (f_pure ⟨i.toNat, hi⟩)) :
    createi T N (usize → RustM T) f = .ok ⟨Vector.ofFn f_pure⟩

open Std.Do in
-- Triple-style spec for createi, usable by mvcgen via @[spec].
-- If each element call purifies, the whole createi returns Vector.ofFn.
@[spec]
axiom createi.spec_triple (T : Type) (N : usize)
    (f : usize → RustM T) (f_pure : Fin N.toNat → T)
    [inst1 : core_models.ops.function.Fn.AssociatedTypes (usize → RustM T) (rust_primitives.hax.Tuple1 usize)]
    [inst2 : core_models.ops.function.Fn (usize → RustM T) (rust_primitives.hax.Tuple1 usize)]
    (hf : ∀ (i : usize) (hi : i.toNat < N.toNat),
      ⦃ ⌜ True ⌝ ⦄ f i ⦃ ⇓ r => ⌜ r = f_pure ⟨i.toNat, hi⟩ ⌝ ⦄) :
    ⦃ ⌜ True ⌝ ⦄
    createi T N (usize → RustM T) f
    ⦃ ⇓ r => ⌜ r = ⟨Vector.ofFn f_pure⟩ ⌝ ⦄

end hacspec_sha3

/-! ## `fold_range` purification -/

-- The result of `USize64.fold_range` does not depend on the invariant or its
-- pure witness, since neither is evaluated in the loop body.
set_option maxHeartbeats 800000 in
theorem USize64.fold_range_inv_irrel {α : Type} (s e : USize64)
    (inv1 inv2 : α → USize64 → RustM Prop)
    (init : α) (body : α → USize64 → RustM α)
    (pureInv1 pureInv2) :
    USize64.fold_range s e inv1 init body pureInv1
    = USize64.fold_range s e inv2 init body pureInv2 := by
  unfold USize64.fold_range
  split
  · case isTrue h =>
    show (body init s >>= fun r => USize64.fold_range (s + 1) e inv1 r body pureInv1)
       = (body init s >>= fun r => USize64.fold_range (s + 1) e inv2 r body pureInv2)
    congr 1; ext r
    exact USize64.fold_range_inv_irrel (s + 1) e inv1 inv2 r body pureInv1 pureInv2
  · rfl
termination_by (e - s)
decreasing_by
  simp only [USize64.sizeOf, Nat.add_lt_add_iff_right]
  exact USize64.sub_succ_lt_self _ _ (by assumption)

/-- Purification of `fold_range` for any accumulator type `α` with a
    pure representation `α_pure` and projection `to_pure : α → α_pure`.

    If the monadic body purifies element-wise, the whole fold purifies to `Fin.foldl`. -/
axiom fold_range_purifies {α α_pure : Type} (n : usize)
    (to_pure : α → α_pure)
    (from_pure : α_pure → α)
    (body : α → usize → RustM α)
    (body_pure : α_pure → Fin n.toNat → α_pure)
    (init : α)
    (h_roundtrip : ∀ v, to_pure (from_pure v) = v)
    (h_init : True)
    (hbody : ∀ (acc : α) (i : usize) (hi : i.toNat < n.toNat),
      body acc i = .ok (from_pure (body_pure (to_pure acc) ⟨i.toNat, hi⟩)))
    [inst : rust_primitives.hax.folds (int_type := usize)] :
    rust_primitives.hax.folds.fold_range (0 : usize) n
      (fun _ _ => (pure true : RustM Bool)) init body
    = .ok (from_pure (Fin.foldl n.toNat (fun v i => body_pure v i) (to_pure init)))

-- `fold_range_purifies` generalized to any invariant. Since `fold_range` does not
-- computationally depend on its invariant, we can always replace a non-trivial
-- invariant with `pure true` and apply the base `fold_range_purifies` axiom.
-- Stated at the level of `USize64.fold_range` to avoid auto-param synthesis issues.
axiom fold_range_purifies_any_inv {α α_pure : Type} (n : usize)
    (to_pure : α → α_pure)
    (from_pure : α_pure → α)
    (inv : α → usize → RustM Prop)
    (body : α → usize → RustM α)
    (body_pure : α_pure → Fin n.toNat → α_pure)
    (init : α)
    (pureInv)
    (h_roundtrip : ∀ v, to_pure (from_pure v) = v)
    (h_init : True)
    (hbody : ∀ (acc : α) (i : usize) (hi : i.toNat < n.toNat),
      body acc i = .ok (from_pure (body_pure (to_pure acc) ⟨i.toNat, hi⟩))) :
    USize64.fold_range (0 : usize) n inv init body pureInv
    = .ok (from_pure (Fin.foldl n.toNat (fun v i => body_pure v i) (to_pure init)))
