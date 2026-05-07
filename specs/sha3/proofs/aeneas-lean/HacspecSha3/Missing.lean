import Aeneas
import CoreModels

open Aeneas Aeneas.Std Result

noncomputable section

namespace core_models

def Slice.Insts.Core_modelsOpsIndexIndex.index
  {T I Output : Type}
  (inst : core.slice.index.SliceIndex I (Slice T) Output)
  (s : Slice T) (i : I) : Result Output :=
  core.slice.index.Slice.index inst s i

def Slice.Insts.Core_modelsOpsIndexIndexMut.index_mut
  {T I Output : Type}
  (inst : core.slice.index.SliceIndex I (Slice T) Output)
  (s : Slice T) (i : I) : Result (Output × (Output → Slice T)) :=
  core.slice.index.Slice.index_mut inst s i

def Array.Insts.Core_modelsOpsIndexIndex.index
  {T I Output : Type} {N : Usize}
  (inst : core.slice.index.SliceIndex I (Slice T) Output)
  (arr : Array T N) (i : I) : Result Output :=
  core.slice.index.Slice.index inst (Array.to_slice arr) i

def Array.Insts.Core_modelsOpsIndexIndexMut.index_mut
  {T I Output : Type} {N : Usize}
  (inst : core.slice.index.SliceIndex I (Slice T) Output)
  (arr : Array T N) (i : I) : Result (Output × (Output → Array T N)) := do
  let (s, to_arr) := Array.to_slice_mut arr
  let (out, to_slice) ← core.slice.index.Slice.index_mut inst s i
  ok (out, fun o => to_arr (to_slice o))

def Slice.Insts.Core_modelsOpsIndexIndex
  {T I O : Type} (inst : core.slice.index.SliceIndex I (Slice T) O) :
  core.slice.index.SliceIndex I (Slice T) O := inst

def Slice.Insts.Core_modelsOpsIndexIndexMut
  {T I O : Type} (inst : core.slice.index.SliceIndex I (Slice T) O) :
  core.slice.index.SliceIndex I (Slice T) O := inst

def slice.Slice.copy_from_slice
  {T : Type} (_cpy : marker.Copy T)
  (dst : Aeneas.Std.Slice T) (src : Aeneas.Std.Slice T) :
  Aeneas.Std.Result (Aeneas.Std.Slice T) :=
  if Aeneas.Std.Slice.len dst = Aeneas.Std.Slice.len src then
    Aeneas.Std.Result.ok src
  else Aeneas.Std.Result.fail Aeneas.Std.Error.panic

def result.Result.unwrap
  {T E : Type} (_dbg : fmt.Debug E) (r : result.Result T E) :
  Aeneas.Std.Result T :=
  match r with
  | .Ok x => Aeneas.Std.Result.ok x
  | .Err _ => Aeneas.Std.Result.fail Aeneas.Std.Error.panic

@[reducible] def array.TryFromSliceError.Insts.Core_modelsFmtDebug :
  fmt.Debug array.TryFromSliceError :=
  { dbg_fmt := fun _ f => Aeneas.Std.Result.ok (.Ok (), f) }

def cmRangeUsizeToAeneas (r : ops.range.Range Aeneas.Std.Usize) :
    Aeneas.Std.core.ops.range.Range Aeneas.Std.Usize :=
  { start := r.start, «end» := r.«end» }

def cmRangeFromUsizeToAeneas {T : Type} (r : ops.range.RangeFrom Aeneas.Std.Usize)
    (s : Aeneas.Std.Slice T) :
    Aeneas.Std.core.ops.range.Range Aeneas.Std.Usize :=
  { start := r.start, «end» := Aeneas.Std.Slice.len s }

@[reducible] def ops.range.RangeUsize.Insts.Core_modelsSliceIndexSliceIndexSliceSlice
  (T : Type) : Aeneas.Std.core.slice.index.SliceIndex
    (ops.range.Range Aeneas.Std.Usize) (Aeneas.Std.Slice T) (Aeneas.Std.Slice T) :=
  { sealedInst := {}
    get := fun r s =>
      Aeneas.Std.core.slice.index.SliceIndexRangeUsizeSlice.get (cmRangeUsizeToAeneas r) s
    get_mut := fun r s =>
      Aeneas.Std.core.slice.index.SliceIndexRangeUsizeSlice.get_mut (cmRangeUsizeToAeneas r) s
    get_unchecked := fun _ _ => Aeneas.Std.Result.fail Aeneas.Std.Error.undef
    get_unchecked_mut := fun _ _ => Aeneas.Std.Result.fail Aeneas.Std.Error.undef
    index := fun r s =>
      Aeneas.Std.core.slice.index.SliceIndexRangeUsizeSlice.index (cmRangeUsizeToAeneas r) s
    index_mut := fun r s =>
      Aeneas.Std.core.slice.index.SliceIndexRangeUsizeSlice.index_mut (cmRangeUsizeToAeneas r) s }

@[reducible] def ops.range.RangeFromUsize.Insts.Core_modelsSliceIndexSliceIndexSliceSlice
  (T : Type) : Aeneas.Std.core.slice.index.SliceIndex
    (ops.range.RangeFrom Aeneas.Std.Usize) (Aeneas.Std.Slice T) (Aeneas.Std.Slice T) :=
  { sealedInst := {}
    get := fun r s =>
      Aeneas.Std.core.slice.index.SliceIndexRangeUsizeSlice.get (cmRangeFromUsizeToAeneas r s) s
    get_mut := fun r s =>
      Aeneas.Std.core.slice.index.SliceIndexRangeUsizeSlice.get_mut (cmRangeFromUsizeToAeneas r s) s
    get_unchecked := fun _ _ => Aeneas.Std.Result.fail Aeneas.Std.Error.undef
    get_unchecked_mut := fun _ _ => Aeneas.Std.Result.fail Aeneas.Std.Error.undef
    index := fun r s =>
      Aeneas.Std.core.slice.index.SliceIndexRangeUsizeSlice.index (cmRangeFromUsizeToAeneas r s) s
    index_mut := fun r s =>
      Aeneas.Std.core.slice.index.SliceIndexRangeUsizeSlice.index_mut (cmRangeFromUsizeToAeneas r s) s }

end core_models

end
