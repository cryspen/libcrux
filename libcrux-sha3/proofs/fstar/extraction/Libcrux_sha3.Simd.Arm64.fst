module Libcrux_sha3.Simd.Arm64
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let v__vbcaxq_u64 (a b c: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t) =
  Libcrux_intrinsics.Arm64.v__veorq_u64 a
    (Libcrux_intrinsics.Arm64.v__vbicq_u64 b c <: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)

let v__veor5q_u64 (a b c d e: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t) =
  let ab:Core.Core_arch.Arm_shared.Neon.t_uint64x2_t = Libcrux_intrinsics.Arm64.v__veorq_u64 a b in
  let cd:Core.Core_arch.Arm_shared.Neon.t_uint64x2_t = Libcrux_intrinsics.Arm64.v__veorq_u64 c d in
  let abcd:Core.Core_arch.Arm_shared.Neon.t_uint64x2_t =
    Libcrux_intrinsics.Arm64.v__veorq_u64 ab cd
  in
  Libcrux_intrinsics.Arm64.v__veorq_u64 abcd e

let v__veorq_n_u64 (a: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t) (c: u64) =
  let c:Core.Core_arch.Arm_shared.Neon.t_uint64x2_t = Libcrux_intrinsics.Arm64.v__vdupq_n_u64 c in
  Libcrux_intrinsics.Arm64.v__veorq_u64 a c

let slice_2_ (a: t_Array (t_Slice u8) (sz 2)) (start len: usize) =
  let list =
    [
      (a.[ sz 0 ] <: t_Slice u8).[ {
          Core.Ops.Range.f_start = start;
          Core.Ops.Range.f_end = start +! len <: usize
        }
        <:
        Core.Ops.Range.t_Range usize ];
      (a.[ sz 1 ] <: t_Slice u8).[ {
          Core.Ops.Range.f_start = start;
          Core.Ops.Range.f_end = start +! len <: usize
        }
        <:
        Core.Ops.Range.t_Range usize ]
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
  Rust_primitives.Hax.array_of_list 2 list

let rotate_left (v_LEFT v_RIGHT: i32) (x: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t) =
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
  Libcrux_intrinsics.Arm64.v__veorq_u64 (Libcrux_intrinsics.Arm64.v__vshlq_n_u64 v_LEFT x
      <:
      Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
    (Libcrux_intrinsics.Arm64.v__vshrq_n_u64 v_RIGHT x
      <:
      Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)

let v__vrax1q_u64 (a b: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t) =
  Libcrux_intrinsics.Arm64.v__veorq_u64 a
    (rotate_left 1l 63l b <: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)

let v__vxarq_u64 (v_LEFT v_RIGHT: i32) (a b: Core.Core_arch.Arm_shared.Neon.t_uint64x2_t) =
  let ab:Core.Core_arch.Arm_shared.Neon.t_uint64x2_t = Libcrux_intrinsics.Arm64.v__veorq_u64 a b in
  rotate_left v_LEFT v_RIGHT ab

let load_block
      (v_RATE: usize)
      (s: t_Array (t_Array Core.Core_arch.Arm_shared.Neon.t_uint64x2_t (sz 5)) (sz 5))
      (blocks: t_Array (t_Slice u8) (sz 2))
     =
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
  let s:t_Array (t_Array Core.Core_arch.Arm_shared.Neon.t_uint64x2_t (sz 5)) (sz 5) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = v_RATE /! sz 16 <: usize }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      s
      (fun s i ->
          let s:t_Array (t_Array Core.Core_arch.Arm_shared.Neon.t_uint64x2_t (sz 5)) (sz 5) = s in
          let i:usize = i in
          let v0:Core.Core_arch.Arm_shared.Neon.t_uint64x2_t =
            Libcrux_intrinsics.Arm64.v__vld1q_bytes_u64 ((blocks.[ sz 0 ] <: t_Slice u8).[ {
                    Core.Ops.Range.f_start = sz 16 *! i <: usize;
                    Core.Ops.Range.f_end = sz 16 *! (i +! sz 1 <: usize) <: usize
                  }
                  <:
                  Core.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
          in
          let v1:Core.Core_arch.Arm_shared.Neon.t_uint64x2_t =
            Libcrux_intrinsics.Arm64.v__vld1q_bytes_u64 ((blocks.[ sz 1 ] <: t_Slice u8).[ {
                    Core.Ops.Range.f_start = sz 16 *! i <: usize;
                    Core.Ops.Range.f_end = sz 16 *! (i +! sz 1 <: usize) <: usize
                  }
                  <:
                  Core.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
          in
          let s:t_Array (t_Array Core.Core_arch.Arm_shared.Neon.t_uint64x2_t (sz 5)) (sz 5) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
              ((sz 2 *! i <: usize) /! sz 5 <: usize)
              (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.[ (sz 2 *! i <: usize) /!
                      sz 5
                      <:
                      usize ]
                    <:
                    t_Array Core.Core_arch.Arm_shared.Neon.t_uint64x2_t (sz 5))
                  ((sz 2 *! i <: usize) %! sz 5 <: usize)
                  (Libcrux_intrinsics.Arm64.v__veorq_u64 ((s.[ (sz 2 *! i <: usize) /! sz 5 <: usize
                          ]
                          <:
                          t_Array Core.Core_arch.Arm_shared.Neon.t_uint64x2_t (sz 5)).[ (sz 2 *! i
                            <:
                            usize) %!
                          sz 5
                          <:
                          usize ]
                        <:
                        Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
                      (Libcrux_intrinsics.Arm64.v__vtrn1q_u64 v0 v1
                        <:
                        Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
                    <:
                    Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
                <:
                t_Array Core.Core_arch.Arm_shared.Neon.t_uint64x2_t (sz 5))
          in
          let s:t_Array (t_Array Core.Core_arch.Arm_shared.Neon.t_uint64x2_t (sz 5)) (sz 5) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
              (((sz 2 *! i <: usize) +! sz 1 <: usize) /! sz 5 <: usize)
              (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.[ ((sz 2 *! i <: usize
                        ) +!
                        sz 1
                        <:
                        usize) /!
                      sz 5
                      <:
                      usize ]
                    <:
                    t_Array Core.Core_arch.Arm_shared.Neon.t_uint64x2_t (sz 5))
                  (((sz 2 *! i <: usize) +! sz 1 <: usize) %! sz 5 <: usize)
                  (Libcrux_intrinsics.Arm64.v__veorq_u64 ((s.[ ((sz 2 *! i <: usize) +! sz 1
                              <:
                              usize) /!
                            sz 5
                            <:
                            usize ]
                          <:
                          t_Array Core.Core_arch.Arm_shared.Neon.t_uint64x2_t (sz 5)).[ ((sz 2 *! i
                              <:
                              usize) +!
                            sz 1
                            <:
                            usize) %!
                          sz 5
                          <:
                          usize ]
                        <:
                        Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
                      (Libcrux_intrinsics.Arm64.v__vtrn2q_u64 v0 v1
                        <:
                        Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
                    <:
                    Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
                <:
                t_Array Core.Core_arch.Arm_shared.Neon.t_uint64x2_t (sz 5))
          in
          s)
  in
  let s, hax_temp_output:(t_Array (t_Array Core.Core_arch.Arm_shared.Neon.t_uint64x2_t (sz 5))
      (sz 5) &
    Prims.unit) =
    if (v_RATE %! sz 16 <: usize) <>. sz 0
    then
      let i:usize = ((v_RATE /! sz 8 <: usize) -! sz 1 <: usize) /! sz 5 in
      let j:usize = ((v_RATE /! sz 8 <: usize) -! sz 1 <: usize) %! sz 5 in
      let u:t_Array u64 (sz 2) = Rust_primitives.Hax.repeat 0uL (sz 2) in
      let u:t_Array u64 (sz 2) =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_usize u
          (sz 0)
          (Core.Num.impl__u64__from_le_bytes (Core.Result.impl__unwrap #(t_Array u8 (sz 8))
                  #Core.Array.t_TryFromSliceError
                  (Core.Convert.f_try_into #(t_Slice u8)
                      #(t_Array u8 (sz 8))
                      ((blocks.[ sz 0 ] <: t_Slice u8).[ {
                            Core.Ops.Range.f_start = v_RATE -! sz 8 <: usize;
                            Core.Ops.Range.f_end = v_RATE
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
      in
      let u:t_Array u64 (sz 2) =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_usize u
          (sz 1)
          (Core.Num.impl__u64__from_le_bytes (Core.Result.impl__unwrap #(t_Array u8 (sz 8))
                  #Core.Array.t_TryFromSliceError
                  (Core.Convert.f_try_into #(t_Slice u8)
                      #(t_Array u8 (sz 8))
                      ((blocks.[ sz 1 ] <: t_Slice u8).[ {
                            Core.Ops.Range.f_start = v_RATE -! sz 8 <: usize;
                            Core.Ops.Range.f_end = v_RATE
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
      in
      let uvec:Core.Core_arch.Arm_shared.Neon.t_uint64x2_t =
        Libcrux_intrinsics.Arm64.v__vld1q_u64 (Rust_primitives.unsize u <: t_Slice u64)
      in
      let s:t_Array (t_Array Core.Core_arch.Arm_shared.Neon.t_uint64x2_t (sz 5)) (sz 5) =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
          i
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.[ i ]
                <:
                t_Array Core.Core_arch.Arm_shared.Neon.t_uint64x2_t (sz 5))
              j
              (Libcrux_intrinsics.Arm64.v__veorq_u64 ((s.[ i ]
                      <:
                      t_Array Core.Core_arch.Arm_shared.Neon.t_uint64x2_t (sz 5)).[ j ]
                    <:
                    Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
                  uvec
                <:
                Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
            <:
            t_Array Core.Core_arch.Arm_shared.Neon.t_uint64x2_t (sz 5))
      in
      s, ()
      <:
      (t_Array (t_Array Core.Core_arch.Arm_shared.Neon.t_uint64x2_t (sz 5)) (sz 5) & Prims.unit)
    else
      s, ()
      <:
      (t_Array (t_Array Core.Core_arch.Arm_shared.Neon.t_uint64x2_t (sz 5)) (sz 5) & Prims.unit)
  in
  s

let load_block_full
      (v_RATE: usize)
      (s: t_Array (t_Array Core.Core_arch.Arm_shared.Neon.t_uint64x2_t (sz 5)) (sz 5))
      (blocks: t_Array (t_Array u8 (sz 200)) (sz 2))
     =
  let s:t_Array (t_Array Core.Core_arch.Arm_shared.Neon.t_uint64x2_t (sz 5)) (sz 5) =
    load_block v_RATE
      s
      (let list =
          [
            Rust_primitives.unsize (blocks.[ sz 0 ] <: t_Array u8 (sz 200)) <: t_Slice u8;
            Rust_primitives.unsize (blocks.[ sz 1 ] <: t_Array u8 (sz 200)) <: t_Slice u8
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
        Rust_primitives.Hax.array_of_list 2 list)
  in
  s

let store_block
      (v_RATE v_SIZE: usize)
      (s: t_Array (t_Array Core.Core_arch.Arm_shared.Neon.t_uint64x2_t (sz 5)) (sz 5))
      (out: t_Array (t_Array u8 v_SIZE) (sz 2))
      (start: usize)
     =
  let out:t_Array (t_Array u8 v_SIZE) (sz 2) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = v_RATE /! sz 16 <: usize }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      out
      (fun out i ->
          let out:t_Array (t_Array u8 v_SIZE) (sz 2) = out in
          let i:usize = i in
          let v0:Core.Core_arch.Arm_shared.Neon.t_uint64x2_t =
            Libcrux_intrinsics.Arm64.v__vtrn1q_u64 ((s.[ (sz 2 *! i <: usize) /! sz 5 <: usize ]
                  <:
                  t_Array Core.Core_arch.Arm_shared.Neon.t_uint64x2_t (sz 5)).[ (sz 2 *! i <: usize) %!
                  sz 5
                  <:
                  usize ]
                <:
                Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
              ((s.[ ((sz 2 *! i <: usize) +! sz 1 <: usize) /! sz 5 <: usize ]
                  <:
                  t_Array Core.Core_arch.Arm_shared.Neon.t_uint64x2_t (sz 5)).[ ((sz 2 *! i <: usize
                    ) +!
                    sz 1
                    <:
                    usize) %!
                  sz 5
                  <:
                  usize ]
                <:
                Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
          in
          let v1:Core.Core_arch.Arm_shared.Neon.t_uint64x2_t =
            Libcrux_intrinsics.Arm64.v__vtrn2q_u64 ((s.[ (sz 2 *! i <: usize) /! sz 5 <: usize ]
                  <:
                  t_Array Core.Core_arch.Arm_shared.Neon.t_uint64x2_t (sz 5)).[ (sz 2 *! i <: usize) %!
                  sz 5
                  <:
                  usize ]
                <:
                Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
              ((s.[ ((sz 2 *! i <: usize) +! sz 1 <: usize) /! sz 5 <: usize ]
                  <:
                  t_Array Core.Core_arch.Arm_shared.Neon.t_uint64x2_t (sz 5)).[ ((sz 2 *! i <: usize
                    ) +!
                    sz 1
                    <:
                    usize) %!
                  sz 5
                  <:
                  usize ]
                <:
                Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
          in
          let out:t_Array (t_Array u8 v_SIZE) (sz 2) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
              (sz 0)
              (Rust_primitives.Hax.Monomorphized_update_at.update_at_range (out.[ sz 0 ]
                    <:
                    t_Array u8 v_SIZE)
                  ({
                      Core.Ops.Range.f_start = start +! (sz 16 *! i <: usize) <: usize;
                      Core.Ops.Range.f_end
                      =
                      start +! (sz 16 *! (i +! sz 1 <: usize) <: usize) <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize)
                  (Libcrux_intrinsics.Arm64.v__vst1q_bytes_u64 ((out.[ sz 0 ] <: t_Array u8 v_SIZE).[
                          {
                            Core.Ops.Range.f_start = start +! (sz 16 *! i <: usize) <: usize;
                            Core.Ops.Range.f_end
                            =
                            start +! (sz 16 *! (i +! sz 1 <: usize) <: usize) <: usize
                          }
                          <:
                          Core.Ops.Range.t_Range usize ]
                        <:
                        t_Slice u8)
                      v0
                    <:
                    t_Slice u8)
                <:
                t_Array u8 v_SIZE)
          in
          let out:t_Array (t_Array u8 v_SIZE) (sz 2) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
              (sz 1)
              (Rust_primitives.Hax.Monomorphized_update_at.update_at_range (out.[ sz 1 ]
                    <:
                    t_Array u8 v_SIZE)
                  ({
                      Core.Ops.Range.f_start = start +! (sz 16 *! i <: usize) <: usize;
                      Core.Ops.Range.f_end
                      =
                      start +! (sz 16 *! (i +! sz 1 <: usize) <: usize) <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize)
                  (Libcrux_intrinsics.Arm64.v__vst1q_bytes_u64 ((out.[ sz 1 ] <: t_Array u8 v_SIZE).[
                          {
                            Core.Ops.Range.f_start = start +! (sz 16 *! i <: usize) <: usize;
                            Core.Ops.Range.f_end
                            =
                            start +! (sz 16 *! (i +! sz 1 <: usize) <: usize) <: usize
                          }
                          <:
                          Core.Ops.Range.t_Range usize ]
                        <:
                        t_Slice u8)
                      v1
                    <:
                    t_Slice u8)
                <:
                t_Array u8 v_SIZE)
          in
          out)
  in
  let out, hax_temp_output:(t_Array (t_Array u8 v_SIZE) (sz 2) & Prims.unit) =
    if (v_RATE %! sz 16 <: usize) <>. sz 0
    then
      let _:Prims.unit =
        if true
        then
          let _:Prims.unit =
            if ~.((v_RATE %! sz 8 <: usize) =. sz 0 <: bool)
            then
              Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: RATE % 8 == 0"

                  <:
                  Rust_primitives.Hax.t_Never)
          in
          ()
      in
      let i:usize = ((v_RATE /! sz 8 <: usize) -! sz 1 <: usize) /! sz 5 in
      let j:usize = ((v_RATE /! sz 8 <: usize) -! sz 1 <: usize) %! sz 5 in
      let u:t_Array u8 (sz 16) = Rust_primitives.Hax.repeat 0uy (sz 16) in
      let u:t_Array u8 (sz 16) =
        Libcrux_intrinsics.Arm64.v__vst1q_bytes_u64 u
          ((s.[ i ] <: t_Array Core.Core_arch.Arm_shared.Neon.t_uint64x2_t (sz 5)).[ j ]
            <:
            Core.Core_arch.Arm_shared.Neon.t_uint64x2_t)
      in
      let out:t_Array (t_Array u8 v_SIZE) (sz 2) =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          (sz 0)
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_range (out.[ sz 0 ]
                <:
                t_Array u8 v_SIZE)
              ({
                  Core.Ops.Range.f_start = (start +! v_RATE <: usize) -! sz 8 <: usize;
                  Core.Ops.Range.f_end = start +! v_RATE <: usize
                }
                <:
                Core.Ops.Range.t_Range usize)
              (Core.Slice.impl__copy_from_slice #u8
                  ((out.[ sz 0 ] <: t_Array u8 v_SIZE).[ {
                        Core.Ops.Range.f_start = (start +! v_RATE <: usize) -! sz 8 <: usize;
                        Core.Ops.Range.f_end = start +! v_RATE <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                  (u.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 8 }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                <:
                t_Slice u8)
            <:
            t_Array u8 v_SIZE)
      in
      let out:t_Array (t_Array u8 v_SIZE) (sz 2) =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          (sz 1)
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_range (out.[ sz 1 ]
                <:
                t_Array u8 v_SIZE)
              ({
                  Core.Ops.Range.f_start = (start +! v_RATE <: usize) -! sz 8 <: usize;
                  Core.Ops.Range.f_end = start +! v_RATE <: usize
                }
                <:
                Core.Ops.Range.t_Range usize)
              (Core.Slice.impl__copy_from_slice #u8
                  ((out.[ sz 1 ] <: t_Array u8 v_SIZE).[ {
                        Core.Ops.Range.f_start = (start +! v_RATE <: usize) -! sz 8 <: usize;
                        Core.Ops.Range.f_end = start +! v_RATE <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                  (u.[ { Core.Ops.Range.f_start = sz 8; Core.Ops.Range.f_end = sz 16 }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                <:
                t_Slice u8)
            <:
            t_Array u8 v_SIZE)
      in
      out, () <: (t_Array (t_Array u8 v_SIZE) (sz 2) & Prims.unit)
    else out, () <: (t_Array (t_Array u8 v_SIZE) (sz 2) & Prims.unit)
  in
  out

let store_block_full
      (v_RATE: usize)
      (s: t_Array (t_Array Core.Core_arch.Arm_shared.Neon.t_uint64x2_t (sz 5)) (sz 5))
     =
  let out:t_Array (t_Array u8 (sz 200)) (sz 2) =
    let list = [Rust_primitives.Hax.repeat 0uy (sz 200); Rust_primitives.Hax.repeat 0uy (sz 200)] in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
    Rust_primitives.Hax.array_of_list 2 list
  in
  let out:t_Array (t_Array u8 (sz 200)) (sz 2) = store_block v_RATE (sz 200) s out (sz 0) in
  out
