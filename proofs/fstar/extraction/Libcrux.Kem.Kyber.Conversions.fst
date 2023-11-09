module Libcrux.Kem.Kyber.Conversions
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

type t_UpdatableArray (v_LEN: usize) = {
  f_value:t_Array u8 v_LEN;
  f_pointer:usize
}

let impl__array (v_LEN: usize) (self: t_UpdatableArray v_LEN) : t_Array u8 v_LEN = self.f_value

let impl__new (v_LEN: usize) (value: t_Array u8 v_LEN) : t_UpdatableArray v_LEN =
  { f_value = value; f_pointer = sz 0 }

let into_padded_array (v_LEN: usize) (slice: t_Slice u8) : t_Array u8 v_LEN =
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
  let out:t_Array u8 v_LEN = Rust_primitives.Hax.repeat 0uy v_LEN in
  let out:t_Array u8 v_LEN =
    Rust_primitives.Hax.update_at out
      ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = Core.Slice.impl__len slice <: usize }
      )
      (Core.Slice.impl__copy_from_slice (out.[ {
                Core.Ops.Range.f_start = sz 0;
                Core.Ops.Range.f_end = Core.Slice.impl__len slice <: usize
              } ]
            <:
            t_Slice u8)
          slice
        <:
        t_Slice u8)
  in
  out

class t_UpdatingArray (v_Self: Type) = { f_push:v_Self -> t_Slice u8 -> v_Self }

let impl_1 (v_LEN: usize) : t_UpdatingArray (t_UpdatableArray v_LEN) =
  {
    f_push
    =
    fun (self: t_UpdatableArray v_LEN) (other: t_Slice u8) ->
      let self:t_UpdatableArray v_LEN =
        {
          self with
          f_value
          =
          Rust_primitives.Hax.update_at self.f_value
            ({
                Core.Ops.Range.f_start = self.f_pointer;
                Core.Ops.Range.f_end
                =
                self.f_pointer +! (Core.Slice.impl__len other <: usize) <: usize
              })
            (Core.Slice.impl__copy_from_slice (self.f_value.[ {
                      Core.Ops.Range.f_start = self.f_pointer;
                      Core.Ops.Range.f_end
                      =
                      self.f_pointer +! (Core.Slice.impl__len other <: usize) <: usize
                    } ]
                  <:
                  t_Slice u8)
                other
              <:
              t_Slice u8)
        }
      in
      let self:t_UpdatableArray v_LEN =
        { self with f_pointer = self.f_pointer +! (Core.Slice.impl__len other <: usize) }
      in
      self
  }