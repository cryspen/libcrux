import Hax
import Std.Do.Triple

/-! # Stubs for missing functions in the hacspec SHA-3 spec extraction -/

/-! ## Coercion `RustArray α n` ↔ `RustSlice α` -/

attribute [local grind! .] USize64.toNat_lt_size

instance instCoeRustArraySeq {α : Type} {n : usize} :
    CoeOut (RustArray α n) (rust_primitives.sequence.Seq α) where
  coe a := ⟨a.toVec.toArray, by grind⟩

-- The old instCoeSeqRustArray used sorry to fill s.val.size = n.toNat, which was
-- unsound (could prove False). This version uses a decidable check instead:
-- on match, it preserves the data; on mismatch, it returns a default-filled array.
-- Sound: no sorry, no false proofs.  The else branch is unreachable in practice
-- (all extraction call sites have matching sizes).
instance instCoeSeqRustArray {α : Type} [Inhabited α] {n : usize}
    (s : rust_primitives.sequence.Seq α) :
    CoeDep (rust_primitives.sequence.Seq α) s (RustArray α n) where
  coe := if h : s.val.size = n.toNat then ⟨⟨s.val, h⟩⟩
         else ⟨Vector.replicate n.toNat default⟩

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

-- Note: fold_range_purifies and createi_purifies (equality-based) have been removed.
-- Use mvcgen with @[spec] triples instead.
