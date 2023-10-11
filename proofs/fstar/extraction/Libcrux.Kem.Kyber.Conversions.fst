module Libcrux.Kem.Kyber.Conversions
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let into_padded_array (#v_LEN: usize) (slice: slice u8) : array u8 v_LEN =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if ~.((Core.Slice.impl__len slice <: usize) <=. v_LEN <: bool)
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: slice.len() <= LEN"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let out:array u8 v_LEN = Rust_primitives.Hax.repeat 0uy v_LEN in
  let out:array u8 v_LEN =
    Rust_primitives.Hax.update_at out
      ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = Core.Slice.impl__len slice <: usize }
      )
      (Core.Slice.impl__copy_from_slice (Core.Ops.Index.IndexMut.index_mut out
              ({
                  Core.Ops.Range.f_start = sz 0;
                  Core.Ops.Range.f_end = Core.Slice.impl__len slice <: usize
                })
            <:
            slice u8)
          slice
        <:
        slice u8)
  in
  out

class t_UpdatingArray (#v_Self: Type) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_509883233:t_UpdatingArray v_Self;
  f_push:v_Self -> slice u8 -> v_Self
}

type t_UpdatableArray (#v_LEN: usize) = {
  f_value:array u8 v_LEN;
  f_pointer:usize
}

let impl__new (#v_LEN: usize) (value: array u8 v_LEN) : t_UpdatableArray v_LEN =
  { f_value = value; f_pointer = sz 0 }

let impl__array (#v_LEN: usize) (self: t_UpdatableArray v_LEN) : array u8 v_LEN = self.f_value

let impl_1 (#v_LEN: usize) : t_UpdatingArray (t_UpdatableArray v_LEN) =
  {
    f_impl_1__push
    =
    fun (#v_LEN: usize) (self: t_UpdatableArray v_LEN) (other: slice u8) ->
      let self:t_UpdatableArray v_LEN =
        {
          self with
          f_value
          =
          Rust_primitives.Hax.update_at (f_value self <: t_UpdatableArray v_LEN)
            ({
                Core.Ops.Range.f_start = self.f_pointer;
                Core.Ops.Range.f_end
                =
                self.f_pointer +! (Core.Slice.impl__len other <: usize) <: usize
              })
            (Core.Slice.impl__copy_from_slice (Core.Ops.Index.IndexMut.index_mut self.f_value
                    ({
                        Core.Ops.Range.f_start = self.f_pointer;
                        Core.Ops.Range.f_end
                        =
                        self.f_pointer +! (Core.Slice.impl__len other <: usize) <: usize
                      })
                  <:
                  slice u8)
                other
              <:
              slice u8)
        }
      in
      let self:t_UpdatableArray v_LEN =
        { self with f_pointer = self.f_pointer +! (Core.Slice.impl__len other <: usize) }
      in
      self
  }

let to_unsigned_representative (fe: i32) : u16 =
  cast (fe +! ((fe >>! 15l <: i32) &. Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32)) <: u16