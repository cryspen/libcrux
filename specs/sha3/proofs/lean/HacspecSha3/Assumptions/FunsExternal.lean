-- External function definitions for `hacspec_sha3` (hand-written).
-- The `CoreModels` library (cryspen/hax-lean) supplies the shared `Index`
-- instances and range bridges (as its own `slice.index.SliceIndex`, which
-- exposes only `get`/`index`). The mutable-index helpers below reconstruct the
-- write-back from the range value using aeneas's `update_subslice`, plus the
-- `unwrap` / `copy_from_slice` / `TryFromSliceError` `Debug` models. These are
-- the single source of truth, reused by libcrux-iot's proof via `import HacspecSha3`.
import Aeneas
import CoreModels
import HacspecSha3.Extraction.Types
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error
open Std.Do
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
open hacspec_sha3

noncomputable section

/-- Recover concrete `[start, end)` bounds (as an aeneas `Range`) from the
    `CoreModels` range value used to index; `len` is the length of the indexed
    container, used to close open-ended ranges. -/
class HaxToRange (I : Type) where
  toRange : I → Usize → Aeneas.Std.core.ops.range.Range Usize

instance : HaxToRange (CoreModels.core.ops.range.Range Usize) where
  toRange r _ := { start := r.start, «end» := r.«end» }
instance : HaxToRange (CoreModels.core.ops.range.RangeFrom Usize) where
  toRange r len := { start := r.start, «end» := len }
instance : HaxToRange (CoreModels.core.ops.range.RangeTo Usize) where
  toRange r _ := { start := 0#usize, «end» := r.«end» }
-- `x[..]`: `RangeFull` is `Unit`, so the whole container is the range.
-- Needed by consumers of this spec (libcrux-iot sha3 indexes with `..`), not by
-- the spec's own extraction.
instance : HaxToRange CoreModels.core.ops.range.RangeFull where
  toRange _ len := { start := 0#usize, «end» := len }

namespace CoreModels.core

/-- `&mut arr[i]` on an array: analogous, via `Array.update_subslice`. -/
def Array.Insts.CoreOpsIndexIndexMut.index_mut
  {T I : Type} {N : Usize} [HaxToRange I]
  (inst : ops.index.IndexMut (Slice T) I (Slice T))
  (arr : Array T N) (i : I) : RustM ((Slice T) × ((Slice T) → Array T N)) := do
  -- via `index_mut`, not `IndexInst.index`: for `Range<usize>` the former is
  -- `slice_slice_mut` (a plain `subslice`), while the latter routes through the
  -- bounds-checked `get`, which no proof here wants to unfold.
  let sub ← Prod.fst <$> inst.index_mut (Array.to_slice arr) i
  let r := HaxToRange.toRange i (Aeneas.Std.Slice.len (Array.to_slice arr))
  ok (sub, fun sub' =>
    match Aeneas.Std.Array.update_subslice arr r sub' with
    | .ok a => a
    | _ => arr)

/-- Trivial `Debug` for `array.TryFromSliceError` (= `Unit`). -/
@[reducible]
def array.TryFromSliceError.Insts.CoreFmtDebug :
    CoreModels.core.fmt.Debug CoreModels.core.array.TryFromSliceError :=
  { fmt := fun _ f => Aeneas.Std.RustM.ok (.Ok (), f) }

end CoreModels.core

end
