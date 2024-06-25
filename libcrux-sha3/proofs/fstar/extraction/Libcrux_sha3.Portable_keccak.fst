module Libcrux_sha3.Portable_keccak
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let v__vbcaxq_u64 (a b c: u64) : u64 = a ^. (b &. (~.c <: u64) <: u64)

let v__veor5q_u64 (a b c d e: u64) : u64 =
  let ab:u64 = a ^. b in
  let cd:u64 = c ^. d in
  let abcd:u64 = ab ^. cd in
  abcd ^. e

let v__veorq_n_u64 (a c: u64) : u64 = a ^. c

let slice_1_ (a: t_Array (t_Slice u8) (sz 1)) (start len: usize) : t_Array (t_Slice u8) (sz 1) =
  let list =
    [
      (a.[ sz 0 ] <: t_Slice u8).[ {
          Core.Ops.Range.f_start = start;
          Core.Ops.Range.f_end = start +! len <: usize
        }
        <:
        Core.Ops.Range.t_Range usize ]
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
  Rust_primitives.Hax.array_of_list 1 list

let load_block
      (v_RATE: usize)
      (s: t_Array (t_Array u64 (sz 5)) (sz 5))
      (blocks: t_Array (t_Slice u8) (sz 1))
    : t_Array (t_Array u64 (sz 5)) (sz 5) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if
          ~.((v_RATE <=. (Core.Slice.impl__len #u8 (blocks.[ sz 0 ] <: t_Slice u8) <: usize) <: bool
            ) &&
            ((v_RATE %! sz 8 <: usize) =. sz 0 <: bool))
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: RATE <= blocks[0].len() && RATE % 8 == 0"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let s, hax_temp_output:t_Array (t_Array u64 (sz 5)) (sz 5) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = v_RATE /! sz 8 <: usize }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      s
      (fun s i ->
          let s:t_Array (t_Array u64 (sz 5)) (sz 5) = s in
          let i:usize = i in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
            (i /! sz 5 <: usize)
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.[ i /! sz 5 <: usize ]
                  <:
                  t_Array u64 (sz 5))
                (i %! sz 5 <: usize)
                (((s.[ i /! sz 5 <: usize ] <: t_Array u64 (sz 5)).[ i %! sz 5 <: usize ] <: u64) ^.
                  (Core.Num.impl__u64__from_le_bytes (Core.Result.impl__unwrap #(t_Array u8 (sz 8))
                          #Core.Array.t_TryFromSliceError
                          (Core.Convert.f_try_into #(t_Slice u8)
                              #(t_Array u8 (sz 8))
                              ((blocks.[ sz 0 ] <: t_Slice u8).[ {
                                    Core.Ops.Range.f_start = sz 8 *! i <: usize;
                                    Core.Ops.Range.f_end = (sz 8 *! i <: usize) +! sz 8 <: usize
                                  }
                                  <:
                                  Core.Ops.Range.t_Range usize ]
                                <:
                                t_Slice u8)
                            <:
                            Core.Result.t_Result (t_Array u8 (sz 8)) Core.Array.t_TryFromSliceError)
                        <:
                        t_Array u8 (sz 8))
                    <:
                    u64)
                  <:
                  u64)
              <:
              t_Array u64 (sz 5))
          <:
          t_Array (t_Array u64 (sz 5)) (sz 5))
  in
  s

let rotate_left (v_LEFT v_RIGHT: i32) (x: u64) : u64 =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if ~.((v_LEFT +! v_RIGHT <: i32) =. 64l <: bool)
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: LEFT + RIGHT == 64"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  (x <<! v_LEFT <: u64) |. (x >>! v_RIGHT <: u64)

let v__vrax1q_u64 (a b: u64) : u64 = a ^. (rotate_left 1l 63l b <: u64)

let v__vxarq_u64 (v_LEFT v_RIGHT: i32) (a b: u64) : u64 =
  let ab:u64 = a ^. b in
  rotate_left v_LEFT v_RIGHT ab

let load_block_full
      (v_RATE: usize)
      (s: t_Array (t_Array u64 (sz 5)) (sz 5))
      (blocks: t_Array (t_Array u8 (sz 200)) (sz 1))
    : t_Array (t_Array u64 (sz 5)) (sz 5) =
  let s:t_Array (t_Array u64 (sz 5)) (sz 5) =
    load_block v_RATE
      s
      (let list = [Rust_primitives.unsize (blocks.[ sz 0 ] <: t_Array u8 (sz 200)) <: t_Slice u8] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
        Rust_primitives.Hax.array_of_list 1 list)
  in
  s

let store_block
      (v_RATE v_SIZE: usize)
      (s: t_Array (t_Array u64 (sz 5)) (sz 5))
      (out: t_Array (t_Array u8 v_SIZE) (sz 1))
      (start: usize)
    : t_Array (t_Array u8 v_SIZE) (sz 1) =
  let out, hax_temp_output:t_Array (t_Array u8 v_SIZE) (sz 1) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = v_RATE /! sz 8 <: usize }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      out
      (fun out i ->
          let out:t_Array (t_Array u8 v_SIZE) (sz 1) = out in
          let i:usize = i in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
            (sz 0)
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_range (out.[ sz 0 ]
                  <:
                  t_Array u8 v_SIZE)
                ({
                    Core.Ops.Range.f_start = start +! (sz 8 *! i <: usize) <: usize;
                    Core.Ops.Range.f_end = (start +! (sz 8 *! i <: usize) <: usize) +! sz 8 <: usize
                  }
                  <:
                  Core.Ops.Range.t_Range usize)
                (Core.Slice.impl__copy_from_slice #u8
                    ((out.[ sz 0 ] <: t_Array u8 v_SIZE).[ {
                          Core.Ops.Range.f_start = start +! (sz 8 *! i <: usize) <: usize;
                          Core.Ops.Range.f_end
                          =
                          (start +! (sz 8 *! i <: usize) <: usize) +! sz 8 <: usize
                        }
                        <:
                        Core.Ops.Range.t_Range usize ]
                      <:
                      t_Slice u8)
                    (Rust_primitives.unsize (Core.Num.impl__u64__to_le_bytes ((s.[ i /! sz 5
                                  <:
                                  usize ]
                                <:
                                t_Array u64 (sz 5)).[ i %! sz 5 <: usize ]
                              <:
                              u64)
                          <:
                          t_Array u8 (sz 8))
                      <:
                      t_Slice u8)
                  <:
                  t_Slice u8)
              <:
              t_Array u8 v_SIZE)
          <:
          t_Array (t_Array u8 v_SIZE) (sz 1))
  in
  out

let store_block_full (v_RATE: usize) (s: t_Array (t_Array u64 (sz 5)) (sz 5))
    : t_Array (t_Array u8 (sz 200)) (sz 1) =
  let out:t_Array (t_Array u8 (sz 200)) (sz 1) =
    let list = [Rust_primitives.Hax.repeat 0uy (sz 200)] in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
    Rust_primitives.Hax.array_of_list 1 list
  in
  let out:t_Array (t_Array u8 (sz 200)) (sz 1) = store_block v_RATE (sz 200) s out (sz 0) in
  out

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Libcrux_sha3.Traits.Internal.t_KeccakItem u64 (sz 1) =
  {
    _super_9442900250278684536 = FStar.Tactics.Typeclasses.solve;
    _super_11581440318597584651 = FStar.Tactics.Typeclasses.solve;
    f_zero_pre = (fun (_: Prims.unit) -> true);
    f_zero_post = (fun (_: Prims.unit) (out: u64) -> true);
    f_zero = (fun (_: Prims.unit) -> 0uL);
    f_xor5_pre = (fun (a: u64) (b: u64) (c: u64) (d: u64) (e: u64) -> true);
    f_xor5_post = (fun (a: u64) (b: u64) (c: u64) (d: u64) (e: u64) (out: u64) -> true);
    f_xor5 = (fun (a: u64) (b: u64) (c: u64) (d: u64) (e: u64) -> v__veor5q_u64 a b c d e);
    f_rotate_left1_and_xor_pre = (fun (a: u64) (b: u64) -> true);
    f_rotate_left1_and_xor_post = (fun (a: u64) (b: u64) (out: u64) -> true);
    f_rotate_left1_and_xor = (fun (a: u64) (b: u64) -> v__vrax1q_u64 a b);
    f_xor_and_rotate_pre = (fun (v_LEFT: i32) (v_RIGHT: i32) (a: u64) (b: u64) -> true);
    f_xor_and_rotate_post = (fun (v_LEFT: i32) (v_RIGHT: i32) (a: u64) (b: u64) (out: u64) -> true);
    f_xor_and_rotate
    =
    (fun (v_LEFT: i32) (v_RIGHT: i32) (a: u64) (b: u64) -> v__vxarq_u64 v_LEFT v_RIGHT a b);
    f_and_not_xor_pre = (fun (a: u64) (b: u64) (c: u64) -> true);
    f_and_not_xor_post = (fun (a: u64) (b: u64) (c: u64) (out: u64) -> true);
    f_and_not_xor = (fun (a: u64) (b: u64) (c: u64) -> v__vbcaxq_u64 a b c);
    f_xor_constant_pre = (fun (a: u64) (c: u64) -> true);
    f_xor_constant_post = (fun (a: u64) (c: u64) (out: u64) -> true);
    f_xor_constant = (fun (a: u64) (c: u64) -> v__veorq_n_u64 a c);
    f_xor_pre = (fun (a: u64) (b: u64) -> true);
    f_xor_post = (fun (a: u64) (b: u64) (out: u64) -> true);
    f_xor = (fun (a: u64) (b: u64) -> a ^. b);
    f_load_block_pre
    =
    (fun
        (v_BLOCKSIZE: usize)
        (a: t_Array (t_Array u64 (sz 5)) (sz 5))
        (b: t_Array (t_Slice u8) (sz 1))
        ->
        true);
    f_load_block_post
    =
    (fun
        (v_BLOCKSIZE: usize)
        (a: t_Array (t_Array u64 (sz 5)) (sz 5))
        (b: t_Array (t_Slice u8) (sz 1))
        (out: t_Array (t_Array u64 (sz 5)) (sz 5))
        ->
        true);
    f_load_block
    =
    (fun
        (v_BLOCKSIZE: usize)
        (a: t_Array (t_Array u64 (sz 5)) (sz 5))
        (b: t_Array (t_Slice u8) (sz 1))
        ->
        let hax_temp_output, a:(Prims.unit & t_Array (t_Array u64 (sz 5)) (sz 5)) =
          (), load_block v_BLOCKSIZE a b <: (Prims.unit & t_Array (t_Array u64 (sz 5)) (sz 5))
        in
        a);
    f_store_block_pre
    =
    (fun
        (v_BLOCKSIZE: usize)
        (v_SIZE: usize)
        (a: t_Array (t_Array u64 (sz 5)) (sz 5))
        (b: t_Array (t_Array u8 v_SIZE) (sz 1))
        (start: usize)
        ->
        true);
    f_store_block_post
    =
    (fun
        (v_BLOCKSIZE: usize)
        (v_SIZE: usize)
        (a: t_Array (t_Array u64 (sz 5)) (sz 5))
        (b: t_Array (t_Array u8 v_SIZE) (sz 1))
        (start: usize)
        (out: t_Array (t_Array u8 v_SIZE) (sz 1))
        ->
        true);
    f_store_block
    =
    (fun
        (v_BLOCKSIZE: usize)
        (v_SIZE: usize)
        (a: t_Array (t_Array u64 (sz 5)) (sz 5))
        (b: t_Array (t_Array u8 v_SIZE) (sz 1))
        (start: usize)
        ->
        let hax_temp_output, b:(Prims.unit & t_Array (t_Array u8 v_SIZE) (sz 1)) =
          (), store_block v_BLOCKSIZE v_SIZE a b start
          <:
          (Prims.unit & t_Array (t_Array u8 v_SIZE) (sz 1))
        in
        b);
    f_load_block_full_pre
    =
    (fun
        (v_BLOCKSIZE: usize)
        (a: t_Array (t_Array u64 (sz 5)) (sz 5))
        (b: t_Array (t_Array u8 (sz 200)) (sz 1))
        ->
        true);
    f_load_block_full_post
    =
    (fun
        (v_BLOCKSIZE: usize)
        (a: t_Array (t_Array u64 (sz 5)) (sz 5))
        (b: t_Array (t_Array u8 (sz 200)) (sz 1))
        (out: t_Array (t_Array u64 (sz 5)) (sz 5))
        ->
        true);
    f_load_block_full
    =
    (fun
        (v_BLOCKSIZE: usize)
        (a: t_Array (t_Array u64 (sz 5)) (sz 5))
        (b: t_Array (t_Array u8 (sz 200)) (sz 1))
        ->
        let hax_temp_output, a:(Prims.unit & t_Array (t_Array u64 (sz 5)) (sz 5)) =
          (), load_block_full v_BLOCKSIZE a b <: (Prims.unit & t_Array (t_Array u64 (sz 5)) (sz 5))
        in
        a);
    f_store_block_full_pre
    =
    (fun (v_BLOCKSIZE: usize) (a: t_Array (t_Array u64 (sz 5)) (sz 5)) -> true);
    f_store_block_full_post
    =
    (fun
        (v_BLOCKSIZE: usize)
        (a: t_Array (t_Array u64 (sz 5)) (sz 5))
        (out: t_Array (t_Array u8 (sz 200)) (sz 1))
        ->
        true);
    f_store_block_full
    =
    (fun (v_BLOCKSIZE: usize) (a: t_Array (t_Array u64 (sz 5)) (sz 5)) ->
        store_block_full v_BLOCKSIZE a);
    f_slice_n_pre = (fun (a: t_Array (t_Slice u8) (sz 1)) (start: usize) (len: usize) -> true);
    f_slice_n_post
    =
    (fun
        (a: t_Array (t_Slice u8) (sz 1))
        (start: usize)
        (len: usize)
        (out: t_Array (t_Slice u8) (sz 1))
        ->
        true);
    f_slice_n
    =
    fun (a: t_Array (t_Slice u8) (sz 1)) (start: usize) (len: usize) -> slice_1_ a start len
  }
