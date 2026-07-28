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
open Result ControlFlow Error
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

namespace CoreModels.core

/-- Mutable-index selector for slices (identity: `CoreModels` ships only the
    shared `SliceIndex`, so the mutable path reuses it). -/
def Slice.Insts.CoreOpsIndexIndexMut
  {T I O : Type} (inst : slice.index.SliceIndex I (Slice T) O) :
  slice.index.SliceIndex I (Slice T) O := inst

/-- `&mut s[i]` on a slice: read the sub-slice via the `CoreModels` `index`, and
    write the (possibly modified) sub-slice back with `Slice.update_subslice`. -/
def Slice.Insts.CoreOpsIndexIndexMut.index_mut
  {T I : Type} [HaxToRange I]
  (inst : slice.index.SliceIndex I (Slice T) (Slice T))
  (s : Slice T) (i : I) : Result ((Slice T) × ((Slice T) → Slice T)) := do
  let sub ← inst.index i s
  let r := HaxToRange.toRange i (Aeneas.Std.Slice.len s)
  ok (sub, fun sub' =>
    match Aeneas.Std.Slice.update_subslice s r sub' with
    | .ok s'' => s''
    | _ => s)

/-- `&mut arr[i]` on an array: analogous, via `Array.update_subslice`. -/
def Array.Insts.CoreOpsIndexIndexMut.index_mut
  {T I : Type} {N : Usize} [HaxToRange I]
  (inst : slice.index.SliceIndex I (Slice T) (Slice T))
  (arr : Array T N) (i : I) : Result ((Slice T) × ((Slice T) → Array T N)) := do
  let sub ← inst.index i (Array.to_slice arr)
  let r := HaxToRange.toRange i (Aeneas.Std.Slice.len (Array.to_slice arr))
  ok (sub, fun sub' =>
    match Aeneas.Std.Array.update_subslice arr r sub' with
    | .ok a => a
    | _ => arr)

/-- `Result.unwrap` model: panic on `Err`. -/
def result.Result.unwrap
    {T E : Type} (_dbg : CoreModels.core.fmt.Debug E)
    (r : CoreModels.core.result.Result T E) : Aeneas.Std.Result T :=
  match r with
  | .Ok x => Aeneas.Std.Result.ok x
  | .Err _ => Aeneas.Std.Result.fail Aeneas.Std.Error.panic

/-- `copy_from_slice` — panics on length mismatch. -/
def slice.Slice.copy_from_slice
    {T : Type} (_cpy : CoreModels.core.marker.Copy T)
    (dst src : Aeneas.Std.Slice T) : Aeneas.Std.Result (Aeneas.Std.Slice T) :=
  if Aeneas.Std.Slice.len dst = Aeneas.Std.Slice.len src then
    Aeneas.Std.Result.ok src
  else Aeneas.Std.Result.fail Aeneas.Std.Error.panic

/-- Trivial `Debug` for `array.TryFromSliceError` (= `Unit`). -/
@[reducible]
def array.TryFromSliceError.Insts.CoreFmtDebug :
    CoreModels.core.fmt.Debug CoreModels.core.array.TryFromSliceError :=
  { fmt := fun _ f => Aeneas.Std.Result.ok (.Ok (), f) }

end CoreModels.core

end
