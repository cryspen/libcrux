module Libcrux_sha3.Simd.Avx2
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let v__vbcaxq_u64 (a b c: u8) =
  Libcrux_intrinsics.Avx2_extract.mm256_xor_si256 a
    (Libcrux_intrinsics.Avx2_extract.mm256_andnot_si256 c b <: u8)

let v__veor5q_u64 (a b c d e: u8) =
  let ab:u8 = Libcrux_intrinsics.Avx2_extract.mm256_xor_si256 a b in
  let cd:u8 = Libcrux_intrinsics.Avx2_extract.mm256_xor_si256 c d in
  let abcd:u8 = Libcrux_intrinsics.Avx2_extract.mm256_xor_si256 ab cd in
  Libcrux_intrinsics.Avx2_extract.mm256_xor_si256 abcd e

let v__veorq_n_u64 (a: u8) (c: u64) =
  let c:u8 = Libcrux_intrinsics.Avx2_extract.mm256_set1_epi64x (cast (c <: u64) <: i64) in
  Libcrux_intrinsics.Avx2_extract.mm256_xor_si256 a c

let slice_4_ (a: t_Array (t_Slice u8) (sz 4)) (start len: usize) =
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
        Core.Ops.Range.t_Range usize ];
      (a.[ sz 2 ] <: t_Slice u8).[ {
          Core.Ops.Range.f_start = start;
          Core.Ops.Range.f_end = start +! len <: usize
        }
        <:
        Core.Ops.Range.t_Range usize ];
      (a.[ sz 3 ] <: t_Slice u8).[ {
          Core.Ops.Range.f_start = start;
          Core.Ops.Range.f_end = start +! len <: usize
        }
        <:
        Core.Ops.Range.t_Range usize ]
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
  Rust_primitives.Hax.array_of_list 4 list

let rotate_left (v_LEFT v_RIGHT: i32) (x: u8) =
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
  Libcrux_intrinsics.Avx2_extract.mm256_xor_si256 (Libcrux_intrinsics.Avx2_extract.mm256_slli_epi64 v_LEFT
        x
      <:
      u8)
    (Libcrux_intrinsics.Avx2_extract.mm256_srli_epi64 v_RIGHT x <: u8)

let v__vrax1q_u64 (a b: u8) =
  Libcrux_intrinsics.Avx2_extract.mm256_xor_si256 a (rotate_left 1l 63l b <: u8)

let v__vxarq_u64 (v_LEFT v_RIGHT: i32) (a b: u8) =
  let ab:u8 = Libcrux_intrinsics.Avx2_extract.mm256_xor_si256 a b in
  rotate_left v_LEFT v_RIGHT ab

let load_block
      (v_RATE: usize)
      (s: t_Array (t_Array u8 (sz 5)) (sz 5))
      (blocks: t_Array (t_Slice u8) (sz 4))
     =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if
          ~.((v_RATE <=. (Core.Slice.impl__len #u8 (blocks.[ sz 0 ] <: t_Slice u8) <: usize) <: bool
            ) &&
            ((v_RATE %! sz 8 <: usize) =. sz 0 <: bool) &&
            (((v_RATE %! sz 32 <: usize) =. sz 8 <: bool) ||
            ((v_RATE %! sz 32 <: usize) =. sz 16 <: bool)))
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: RATE <= blocks[0].len() && RATE % 8 == 0 &&\\n    (RATE % 32 == 8 || RATE % 32 == 16)"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let s:t_Array (t_Array u8 (sz 5)) (sz 5) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = v_RATE /! sz 32 <: usize }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      s
      (fun s i ->
          let s:t_Array (t_Array u8 (sz 5)) (sz 5) = s in
          let i:usize = i in
          let v0:u8 =
            Libcrux_intrinsics.Avx2_extract.mm256_loadu_si256_u8 ((blocks.[ sz 0 ] <: t_Slice u8).[ {
                    Core.Ops.Range.f_start = sz 32 *! i <: usize;
                    Core.Ops.Range.f_end = sz 32 *! (i +! sz 1 <: usize) <: usize
                  }
                  <:
                  Core.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
          in
          let v1:u8 =
            Libcrux_intrinsics.Avx2_extract.mm256_loadu_si256_u8 ((blocks.[ sz 1 ] <: t_Slice u8).[ {
                    Core.Ops.Range.f_start = sz 32 *! i <: usize;
                    Core.Ops.Range.f_end = sz 32 *! (i +! sz 1 <: usize) <: usize
                  }
                  <:
                  Core.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
          in
          let v2:u8 =
            Libcrux_intrinsics.Avx2_extract.mm256_loadu_si256_u8 ((blocks.[ sz 2 ] <: t_Slice u8).[ {
                    Core.Ops.Range.f_start = sz 32 *! i <: usize;
                    Core.Ops.Range.f_end = sz 32 *! (i +! sz 1 <: usize) <: usize
                  }
                  <:
                  Core.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
          in
          let v3:u8 =
            Libcrux_intrinsics.Avx2_extract.mm256_loadu_si256_u8 ((blocks.[ sz 3 ] <: t_Slice u8).[ {
                    Core.Ops.Range.f_start = sz 32 *! i <: usize;
                    Core.Ops.Range.f_end = sz 32 *! (i +! sz 1 <: usize) <: usize
                  }
                  <:
                  Core.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
          in
          let v0l:u8 = Libcrux_intrinsics.Avx2_extract.mm256_unpacklo_epi64 v0 v1 in
          let v1h:u8 = Libcrux_intrinsics.Avx2_extract.mm256_unpackhi_epi64 v0 v1 in
          let v2l:u8 = Libcrux_intrinsics.Avx2_extract.mm256_unpacklo_epi64 v2 v3 in
          let v3h:u8 = Libcrux_intrinsics.Avx2_extract.mm256_unpackhi_epi64 v2 v3 in
          let v0:u8 = Libcrux_intrinsics.Avx2_extract.mm256_permute2x128_si256 32l v0l v2l in
          let v1:u8 = Libcrux_intrinsics.Avx2_extract.mm256_permute2x128_si256 32l v1h v3h in
          let v2:u8 = Libcrux_intrinsics.Avx2_extract.mm256_permute2x128_si256 49l v0l v2l in
          let v3:u8 = Libcrux_intrinsics.Avx2_extract.mm256_permute2x128_si256 49l v1h v3h in
          let s:t_Array (t_Array u8 (sz 5)) (sz 5) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
              ((sz 4 *! i <: usize) /! sz 5 <: usize)
              (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.[ (sz 4 *! i <: usize) /!
                      sz 5
                      <:
                      usize ]
                    <:
                    t_Array u8 (sz 5))
                  ((sz 4 *! i <: usize) %! sz 5 <: usize)
                  (Libcrux_intrinsics.Avx2_extract.mm256_xor_si256 ((s.[ (sz 4 *! i <: usize) /!
                            sz 5
                            <:
                            usize ]
                          <:
                          t_Array u8 (sz 5)).[ (sz 4 *! i <: usize) %! sz 5 <: usize ]
                        <:
                        u8)
                      v0
                    <:
                    u8)
                <:
                t_Array u8 (sz 5))
          in
          let s:t_Array (t_Array u8 (sz 5)) (sz 5) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
              (((sz 4 *! i <: usize) +! sz 1 <: usize) /! sz 5 <: usize)
              (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.[ ((sz 4 *! i <: usize
                        ) +!
                        sz 1
                        <:
                        usize) /!
                      sz 5
                      <:
                      usize ]
                    <:
                    t_Array u8 (sz 5))
                  (((sz 4 *! i <: usize) +! sz 1 <: usize) %! sz 5 <: usize)
                  (Libcrux_intrinsics.Avx2_extract.mm256_xor_si256 ((s.[ ((sz 4 *! i <: usize) +!
                              sz 1
                              <:
                              usize) /!
                            sz 5
                            <:
                            usize ]
                          <:
                          t_Array u8 (sz 5)).[ ((sz 4 *! i <: usize) +! sz 1 <: usize) %! sz 5
                          <:
                          usize ]
                        <:
                        u8)
                      v1
                    <:
                    u8)
                <:
                t_Array u8 (sz 5))
          in
          let s:t_Array (t_Array u8 (sz 5)) (sz 5) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
              (((sz 4 *! i <: usize) +! sz 2 <: usize) /! sz 5 <: usize)
              (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.[ ((sz 4 *! i <: usize
                        ) +!
                        sz 2
                        <:
                        usize) /!
                      sz 5
                      <:
                      usize ]
                    <:
                    t_Array u8 (sz 5))
                  (((sz 4 *! i <: usize) +! sz 2 <: usize) %! sz 5 <: usize)
                  (Libcrux_intrinsics.Avx2_extract.mm256_xor_si256 ((s.[ ((sz 4 *! i <: usize) +!
                              sz 2
                              <:
                              usize) /!
                            sz 5
                            <:
                            usize ]
                          <:
                          t_Array u8 (sz 5)).[ ((sz 4 *! i <: usize) +! sz 2 <: usize) %! sz 5
                          <:
                          usize ]
                        <:
                        u8)
                      v2
                    <:
                    u8)
                <:
                t_Array u8 (sz 5))
          in
          let s:t_Array (t_Array u8 (sz 5)) (sz 5) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
              (((sz 4 *! i <: usize) +! sz 3 <: usize) /! sz 5 <: usize)
              (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.[ ((sz 4 *! i <: usize
                        ) +!
                        sz 3
                        <:
                        usize) /!
                      sz 5
                      <:
                      usize ]
                    <:
                    t_Array u8 (sz 5))
                  (((sz 4 *! i <: usize) +! sz 3 <: usize) %! sz 5 <: usize)
                  (Libcrux_intrinsics.Avx2_extract.mm256_xor_si256 ((s.[ ((sz 4 *! i <: usize) +!
                              sz 3
                              <:
                              usize) /!
                            sz 5
                            <:
                            usize ]
                          <:
                          t_Array u8 (sz 5)).[ ((sz 4 *! i <: usize) +! sz 3 <: usize) %! sz 5
                          <:
                          usize ]
                        <:
                        u8)
                      v3
                    <:
                    u8)
                <:
                t_Array u8 (sz 5))
          in
          s)
  in
  let rem:usize = v_RATE %! sz 32 in
  let start:usize = sz 32 *! (v_RATE /! sz 32 <: usize) in
  let u8s:t_Array u8 (sz 32) = Rust_primitives.Hax.repeat 0uy (sz 32) in
  let u8s:t_Array u8 (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range u8s
      ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 8 }
        <:
        Core.Ops.Range.t_Range usize)
      (Core.Slice.impl__copy_from_slice #u8
          (u8s.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 8 }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          ((blocks.[ sz 0 ] <: t_Slice u8).[ {
                Core.Ops.Range.f_start = start;
                Core.Ops.Range.f_end = start +! sz 8 <: usize
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
        <:
        t_Slice u8)
  in
  let u8s:t_Array u8 (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range u8s
      ({ Core.Ops.Range.f_start = sz 8; Core.Ops.Range.f_end = sz 16 }
        <:
        Core.Ops.Range.t_Range usize)
      (Core.Slice.impl__copy_from_slice #u8
          (u8s.[ { Core.Ops.Range.f_start = sz 8; Core.Ops.Range.f_end = sz 16 }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          ((blocks.[ sz 1 ] <: t_Slice u8).[ {
                Core.Ops.Range.f_start = start;
                Core.Ops.Range.f_end = start +! sz 8 <: usize
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
        <:
        t_Slice u8)
  in
  let u8s:t_Array u8 (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range u8s
      ({ Core.Ops.Range.f_start = sz 16; Core.Ops.Range.f_end = sz 24 }
        <:
        Core.Ops.Range.t_Range usize)
      (Core.Slice.impl__copy_from_slice #u8
          (u8s.[ { Core.Ops.Range.f_start = sz 16; Core.Ops.Range.f_end = sz 24 }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          ((blocks.[ sz 2 ] <: t_Slice u8).[ {
                Core.Ops.Range.f_start = start;
                Core.Ops.Range.f_end = start +! sz 8 <: usize
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
        <:
        t_Slice u8)
  in
  let u8s:t_Array u8 (sz 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range u8s
      ({ Core.Ops.Range.f_start = sz 24; Core.Ops.Range.f_end = sz 32 }
        <:
        Core.Ops.Range.t_Range usize)
      (Core.Slice.impl__copy_from_slice #u8
          (u8s.[ { Core.Ops.Range.f_start = sz 24; Core.Ops.Range.f_end = sz 32 }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          ((blocks.[ sz 3 ] <: t_Slice u8).[ {
                Core.Ops.Range.f_start = start;
                Core.Ops.Range.f_end = start +! sz 8 <: usize
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
        <:
        t_Slice u8)
  in
  let u:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_loadu_si256_u8 (Core.Array.impl_23__as_slice #u8
          (sz 32)
          u8s
        <:
        t_Slice u8)
  in
  let i:usize = (sz 4 *! (v_RATE /! sz 32 <: usize) <: usize) /! sz 5 in
  let j:usize = (sz 4 *! (v_RATE /! sz 32 <: usize) <: usize) %! sz 5 in
  let s:t_Array (t_Array u8 (sz 5)) (sz 5) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
      i
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.[ i ] <: t_Array u8 (sz 5))
          j
          (Libcrux_intrinsics.Avx2_extract.mm256_xor_si256 ((s.[ i ] <: t_Array u8 (sz 5)).[ j ]
                <:
                u8)
              u
            <:
            u8)
        <:
        t_Array u8 (sz 5))
  in
  let s, hax_temp_output:(t_Array (t_Array u8 (sz 5)) (sz 5) & Prims.unit) =
    if rem =. sz 16
    then
      let u8s:t_Array u8 (sz 32) = Rust_primitives.Hax.repeat 0uy (sz 32) in
      let u8s:t_Array u8 (sz 32) =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_range u8s
          ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 8 }
            <:
            Core.Ops.Range.t_Range usize)
          (Core.Slice.impl__copy_from_slice #u8
              (u8s.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 8 }
                  <:
                  Core.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
              ((blocks.[ sz 0 ] <: t_Slice u8).[ {
                    Core.Ops.Range.f_start = start +! sz 8 <: usize;
                    Core.Ops.Range.f_end = start +! sz 16 <: usize
                  }
                  <:
                  Core.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
            <:
            t_Slice u8)
      in
      let u8s:t_Array u8 (sz 32) =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_range u8s
          ({ Core.Ops.Range.f_start = sz 8; Core.Ops.Range.f_end = sz 16 }
            <:
            Core.Ops.Range.t_Range usize)
          (Core.Slice.impl__copy_from_slice #u8
              (u8s.[ { Core.Ops.Range.f_start = sz 8; Core.Ops.Range.f_end = sz 16 }
                  <:
                  Core.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
              ((blocks.[ sz 1 ] <: t_Slice u8).[ {
                    Core.Ops.Range.f_start = start +! sz 8 <: usize;
                    Core.Ops.Range.f_end = start +! sz 16 <: usize
                  }
                  <:
                  Core.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
            <:
            t_Slice u8)
      in
      let u8s:t_Array u8 (sz 32) =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_range u8s
          ({ Core.Ops.Range.f_start = sz 16; Core.Ops.Range.f_end = sz 24 }
            <:
            Core.Ops.Range.t_Range usize)
          (Core.Slice.impl__copy_from_slice #u8
              (u8s.[ { Core.Ops.Range.f_start = sz 16; Core.Ops.Range.f_end = sz 24 }
                  <:
                  Core.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
              ((blocks.[ sz 2 ] <: t_Slice u8).[ {
                    Core.Ops.Range.f_start = start +! sz 8 <: usize;
                    Core.Ops.Range.f_end = start +! sz 16 <: usize
                  }
                  <:
                  Core.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
            <:
            t_Slice u8)
      in
      let u8s:t_Array u8 (sz 32) =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_range u8s
          ({ Core.Ops.Range.f_start = sz 24; Core.Ops.Range.f_end = sz 32 }
            <:
            Core.Ops.Range.t_Range usize)
          (Core.Slice.impl__copy_from_slice #u8
              (u8s.[ { Core.Ops.Range.f_start = sz 24; Core.Ops.Range.f_end = sz 32 }
                  <:
                  Core.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
              ((blocks.[ sz 3 ] <: t_Slice u8).[ {
                    Core.Ops.Range.f_start = start +! sz 8 <: usize;
                    Core.Ops.Range.f_end = start +! sz 16 <: usize
                  }
                  <:
                  Core.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
            <:
            t_Slice u8)
      in
      let u:u8 =
        Libcrux_intrinsics.Avx2_extract.mm256_loadu_si256_u8 (Core.Array.impl_23__as_slice #u8
              (sz 32)
              u8s
            <:
            t_Slice u8)
      in
      let i:usize = ((sz 4 *! (v_RATE /! sz 32 <: usize) <: usize) +! sz 1 <: usize) /! sz 5 in
      let j:usize = ((sz 4 *! (v_RATE /! sz 32 <: usize) <: usize) +! sz 1 <: usize) %! sz 5 in
      let s:t_Array (t_Array u8 (sz 5)) (sz 5) =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
          i
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.[ i ] <: t_Array u8 (sz 5)
              )
              j
              (Libcrux_intrinsics.Avx2_extract.mm256_xor_si256 ((s.[ i ] <: t_Array u8 (sz 5)).[ j ]
                    <:
                    u8)
                  u
                <:
                u8)
            <:
            t_Array u8 (sz 5))
      in
      s, () <: (t_Array (t_Array u8 (sz 5)) (sz 5) & Prims.unit)
    else s, () <: (t_Array (t_Array u8 (sz 5)) (sz 5) & Prims.unit)
  in
  s

let load_block_full
      (v_RATE: usize)
      (s: t_Array (t_Array u8 (sz 5)) (sz 5))
      (blocks: t_Array (t_Array u8 (sz 200)) (sz 4))
     =
  let s:t_Array (t_Array u8 (sz 5)) (sz 5) =
    load_block v_RATE
      s
      (let list =
          [
            Rust_primitives.unsize (blocks.[ sz 0 ] <: t_Array u8 (sz 200)) <: t_Slice u8;
            Rust_primitives.unsize (blocks.[ sz 1 ] <: t_Array u8 (sz 200)) <: t_Slice u8;
            Rust_primitives.unsize (blocks.[ sz 2 ] <: t_Array u8 (sz 200)) <: t_Slice u8;
            Rust_primitives.unsize (blocks.[ sz 3 ] <: t_Array u8 (sz 200)) <: t_Slice u8
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
        Rust_primitives.Hax.array_of_list 4 list)
  in
  s

let store_block
      (v_RATE v_SIZE: usize)
      (s: t_Array (t_Array u8 (sz 5)) (sz 5))
      (out: t_Array (t_Array u8 v_SIZE) (sz 4))
      (start: usize)
     =
  let out:t_Array (t_Array u8 v_SIZE) (sz 4) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = v_RATE /! sz 32 <: usize }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      out
      (fun out i ->
          let out:t_Array (t_Array u8 v_SIZE) (sz 4) = out in
          let i:usize = i in
          let v0l:u8 =
            Libcrux_intrinsics.Avx2_extract.mm256_permute2x128_si256 32l
              ((s.[ (sz 4 *! i <: usize) /! sz 5 <: usize ] <: t_Array u8 (sz 5)).[ (sz 4 *! i
                    <:
                    usize) %!
                  sz 5
                  <:
                  usize ]
                <:
                u8)
              ((s.[ ((sz 4 *! i <: usize) +! sz 2 <: usize) /! sz 5 <: usize ] <: t_Array u8 (sz 5)).[
                  ((sz 4 *! i <: usize) +! sz 2 <: usize) %! sz 5 <: usize ]
                <:
                u8)
          in
          let v1h:u8 =
            Libcrux_intrinsics.Avx2_extract.mm256_permute2x128_si256 32l
              ((s.[ ((sz 4 *! i <: usize) +! sz 1 <: usize) /! sz 5 <: usize ] <: t_Array u8 (sz 5)).[
                  ((sz 4 *! i <: usize) +! sz 1 <: usize) %! sz 5 <: usize ]
                <:
                u8)
              ((s.[ ((sz 4 *! i <: usize) +! sz 3 <: usize) /! sz 5 <: usize ] <: t_Array u8 (sz 5)).[
                  ((sz 4 *! i <: usize) +! sz 3 <: usize) %! sz 5 <: usize ]
                <:
                u8)
          in
          let v2l:u8 =
            Libcrux_intrinsics.Avx2_extract.mm256_permute2x128_si256 49l
              ((s.[ (sz 4 *! i <: usize) /! sz 5 <: usize ] <: t_Array u8 (sz 5)).[ (sz 4 *! i
                    <:
                    usize) %!
                  sz 5
                  <:
                  usize ]
                <:
                u8)
              ((s.[ ((sz 4 *! i <: usize) +! sz 2 <: usize) /! sz 5 <: usize ] <: t_Array u8 (sz 5)).[
                  ((sz 4 *! i <: usize) +! sz 2 <: usize) %! sz 5 <: usize ]
                <:
                u8)
          in
          let v3h:u8 =
            Libcrux_intrinsics.Avx2_extract.mm256_permute2x128_si256 49l
              ((s.[ ((sz 4 *! i <: usize) +! sz 1 <: usize) /! sz 5 <: usize ] <: t_Array u8 (sz 5)).[
                  ((sz 4 *! i <: usize) +! sz 1 <: usize) %! sz 5 <: usize ]
                <:
                u8)
              ((s.[ ((sz 4 *! i <: usize) +! sz 3 <: usize) /! sz 5 <: usize ] <: t_Array u8 (sz 5)).[
                  ((sz 4 *! i <: usize) +! sz 3 <: usize) %! sz 5 <: usize ]
                <:
                u8)
          in
          let v0:u8 = Libcrux_intrinsics.Avx2_extract.mm256_unpacklo_epi64 v0l v1h in
          let v1:u8 = Libcrux_intrinsics.Avx2_extract.mm256_unpackhi_epi64 v0l v1h in
          let v2:u8 = Libcrux_intrinsics.Avx2_extract.mm256_unpacklo_epi64 v2l v3h in
          let v3:u8 = Libcrux_intrinsics.Avx2_extract.mm256_unpackhi_epi64 v2l v3h in
          let out:t_Array (t_Array u8 v_SIZE) (sz 4) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
              (sz 0)
              (Rust_primitives.Hax.Monomorphized_update_at.update_at_range (out.[ sz 0 ]
                    <:
                    t_Array u8 v_SIZE)
                  ({
                      Core.Ops.Range.f_start = start +! (sz 32 *! i <: usize) <: usize;
                      Core.Ops.Range.f_end
                      =
                      start +! (sz 32 *! (i +! sz 1 <: usize) <: usize) <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize)
                  (Libcrux_intrinsics.Avx2_extract.mm256_storeu_si256_u8 ((out.[ sz 0 ]
                          <:
                          t_Array u8 v_SIZE).[ {
                            Core.Ops.Range.f_start = start +! (sz 32 *! i <: usize) <: usize;
                            Core.Ops.Range.f_end
                            =
                            start +! (sz 32 *! (i +! sz 1 <: usize) <: usize) <: usize
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
          let out:t_Array (t_Array u8 v_SIZE) (sz 4) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
              (sz 1)
              (Rust_primitives.Hax.Monomorphized_update_at.update_at_range (out.[ sz 1 ]
                    <:
                    t_Array u8 v_SIZE)
                  ({
                      Core.Ops.Range.f_start = start +! (sz 32 *! i <: usize) <: usize;
                      Core.Ops.Range.f_end
                      =
                      start +! (sz 32 *! (i +! sz 1 <: usize) <: usize) <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize)
                  (Libcrux_intrinsics.Avx2_extract.mm256_storeu_si256_u8 ((out.[ sz 1 ]
                          <:
                          t_Array u8 v_SIZE).[ {
                            Core.Ops.Range.f_start = start +! (sz 32 *! i <: usize) <: usize;
                            Core.Ops.Range.f_end
                            =
                            start +! (sz 32 *! (i +! sz 1 <: usize) <: usize) <: usize
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
          let out:t_Array (t_Array u8 v_SIZE) (sz 4) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
              (sz 2)
              (Rust_primitives.Hax.Monomorphized_update_at.update_at_range (out.[ sz 2 ]
                    <:
                    t_Array u8 v_SIZE)
                  ({
                      Core.Ops.Range.f_start = start +! (sz 32 *! i <: usize) <: usize;
                      Core.Ops.Range.f_end
                      =
                      start +! (sz 32 *! (i +! sz 1 <: usize) <: usize) <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize)
                  (Libcrux_intrinsics.Avx2_extract.mm256_storeu_si256_u8 ((out.[ sz 2 ]
                          <:
                          t_Array u8 v_SIZE).[ {
                            Core.Ops.Range.f_start = start +! (sz 32 *! i <: usize) <: usize;
                            Core.Ops.Range.f_end
                            =
                            start +! (sz 32 *! (i +! sz 1 <: usize) <: usize) <: usize
                          }
                          <:
                          Core.Ops.Range.t_Range usize ]
                        <:
                        t_Slice u8)
                      v2
                    <:
                    t_Slice u8)
                <:
                t_Array u8 v_SIZE)
          in
          let out:t_Array (t_Array u8 v_SIZE) (sz 4) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
              (sz 3)
              (Rust_primitives.Hax.Monomorphized_update_at.update_at_range (out.[ sz 3 ]
                    <:
                    t_Array u8 v_SIZE)
                  ({
                      Core.Ops.Range.f_start = start +! (sz 32 *! i <: usize) <: usize;
                      Core.Ops.Range.f_end
                      =
                      start +! (sz 32 *! (i +! sz 1 <: usize) <: usize) <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize)
                  (Libcrux_intrinsics.Avx2_extract.mm256_storeu_si256_u8 ((out.[ sz 3 ]
                          <:
                          t_Array u8 v_SIZE).[ {
                            Core.Ops.Range.f_start = start +! (sz 32 *! i <: usize) <: usize;
                            Core.Ops.Range.f_end
                            =
                            start +! (sz 32 *! (i +! sz 1 <: usize) <: usize) <: usize
                          }
                          <:
                          Core.Ops.Range.t_Range usize ]
                        <:
                        t_Slice u8)
                      v3
                    <:
                    t_Slice u8)
                <:
                t_Array u8 v_SIZE)
          in
          out)
  in
  let rem:usize = v_RATE %! sz 32 in
  let st:usize = start +! (sz 32 *! (v_RATE /! sz 32 <: usize) <: usize) in
  let u8s:t_Array u8 (sz 32) = Rust_primitives.Hax.repeat 0uy (sz 32) in
  let i:usize = (sz 4 *! (v_RATE /! sz 32 <: usize) <: usize) /! sz 5 in
  let j:usize = (sz 4 *! (v_RATE /! sz 32 <: usize) <: usize) %! sz 5 in
  let u8s:t_Array u8 (sz 32) =
    Libcrux_intrinsics.Avx2_extract.mm256_storeu_si256_u8 u8s
      ((s.[ i ] <: t_Array u8 (sz 5)).[ j ] <: u8)
  in
  let out:t_Array (t_Array u8 v_SIZE) (sz 4) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
      (sz 0)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_range (out.[ sz 0 ]
            <:
            t_Array u8 v_SIZE)
          ({ Core.Ops.Range.f_start = st; Core.Ops.Range.f_end = st +! sz 8 <: usize }
            <:
            Core.Ops.Range.t_Range usize)
          (Core.Slice.impl__copy_from_slice #u8
              ((out.[ sz 0 ] <: t_Array u8 v_SIZE).[ {
                    Core.Ops.Range.f_start = st;
                    Core.Ops.Range.f_end = st +! sz 8 <: usize
                  }
                  <:
                  Core.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
              (u8s.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 8 }
                  <:
                  Core.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
            <:
            t_Slice u8)
        <:
        t_Array u8 v_SIZE)
  in
  let out:t_Array (t_Array u8 v_SIZE) (sz 4) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
      (sz 1)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_range (out.[ sz 1 ]
            <:
            t_Array u8 v_SIZE)
          ({ Core.Ops.Range.f_start = st; Core.Ops.Range.f_end = st +! sz 8 <: usize }
            <:
            Core.Ops.Range.t_Range usize)
          (Core.Slice.impl__copy_from_slice #u8
              ((out.[ sz 1 ] <: t_Array u8 v_SIZE).[ {
                    Core.Ops.Range.f_start = st;
                    Core.Ops.Range.f_end = st +! sz 8 <: usize
                  }
                  <:
                  Core.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
              (u8s.[ { Core.Ops.Range.f_start = sz 8; Core.Ops.Range.f_end = sz 16 }
                  <:
                  Core.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
            <:
            t_Slice u8)
        <:
        t_Array u8 v_SIZE)
  in
  let out:t_Array (t_Array u8 v_SIZE) (sz 4) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
      (sz 2)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_range (out.[ sz 2 ]
            <:
            t_Array u8 v_SIZE)
          ({ Core.Ops.Range.f_start = st; Core.Ops.Range.f_end = st +! sz 8 <: usize }
            <:
            Core.Ops.Range.t_Range usize)
          (Core.Slice.impl__copy_from_slice #u8
              ((out.[ sz 2 ] <: t_Array u8 v_SIZE).[ {
                    Core.Ops.Range.f_start = st;
                    Core.Ops.Range.f_end = st +! sz 8 <: usize
                  }
                  <:
                  Core.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
              (u8s.[ { Core.Ops.Range.f_start = sz 16; Core.Ops.Range.f_end = sz 24 }
                  <:
                  Core.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
            <:
            t_Slice u8)
        <:
        t_Array u8 v_SIZE)
  in
  let out:t_Array (t_Array u8 v_SIZE) (sz 4) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
      (sz 3)
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_range (out.[ sz 3 ]
            <:
            t_Array u8 v_SIZE)
          ({ Core.Ops.Range.f_start = st; Core.Ops.Range.f_end = st +! sz 8 <: usize }
            <:
            Core.Ops.Range.t_Range usize)
          (Core.Slice.impl__copy_from_slice #u8
              ((out.[ sz 3 ] <: t_Array u8 v_SIZE).[ {
                    Core.Ops.Range.f_start = st;
                    Core.Ops.Range.f_end = st +! sz 8 <: usize
                  }
                  <:
                  Core.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
              (u8s.[ { Core.Ops.Range.f_start = sz 24; Core.Ops.Range.f_end = sz 32 }
                  <:
                  Core.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
            <:
            t_Slice u8)
        <:
        t_Array u8 v_SIZE)
  in
  let out, hax_temp_output:(t_Array (t_Array u8 v_SIZE) (sz 4) & Prims.unit) =
    if rem =. sz 16
    then
      let u8s:t_Array u8 (sz 32) = Rust_primitives.Hax.repeat 0uy (sz 32) in
      let i:usize = ((sz 4 *! (v_RATE /! sz 32 <: usize) <: usize) +! sz 1 <: usize) /! sz 5 in
      let j:usize = ((sz 4 *! (v_RATE /! sz 32 <: usize) <: usize) +! sz 1 <: usize) %! sz 5 in
      let u8s:t_Array u8 (sz 32) =
        Libcrux_intrinsics.Avx2_extract.mm256_storeu_si256_u8 u8s
          ((s.[ i ] <: t_Array u8 (sz 5)).[ j ] <: u8)
      in
      let out:t_Array (t_Array u8 v_SIZE) (sz 4) =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          (sz 0)
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_range (out.[ sz 0 ]
                <:
                t_Array u8 v_SIZE)
              ({
                  Core.Ops.Range.f_start = st +! sz 8 <: usize;
                  Core.Ops.Range.f_end = st +! sz 16 <: usize
                }
                <:
                Core.Ops.Range.t_Range usize)
              (Core.Slice.impl__copy_from_slice #u8
                  ((out.[ sz 0 ] <: t_Array u8 v_SIZE).[ {
                        Core.Ops.Range.f_start = st +! sz 8 <: usize;
                        Core.Ops.Range.f_end = st +! sz 16 <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                  (u8s.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 8 }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                <:
                t_Slice u8)
            <:
            t_Array u8 v_SIZE)
      in
      let out:t_Array (t_Array u8 v_SIZE) (sz 4) =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          (sz 1)
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_range (out.[ sz 1 ]
                <:
                t_Array u8 v_SIZE)
              ({
                  Core.Ops.Range.f_start = st +! sz 8 <: usize;
                  Core.Ops.Range.f_end = st +! sz 16 <: usize
                }
                <:
                Core.Ops.Range.t_Range usize)
              (Core.Slice.impl__copy_from_slice #u8
                  ((out.[ sz 1 ] <: t_Array u8 v_SIZE).[ {
                        Core.Ops.Range.f_start = st +! sz 8 <: usize;
                        Core.Ops.Range.f_end = st +! sz 16 <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                  (u8s.[ { Core.Ops.Range.f_start = sz 8; Core.Ops.Range.f_end = sz 16 }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                <:
                t_Slice u8)
            <:
            t_Array u8 v_SIZE)
      in
      let out:t_Array (t_Array u8 v_SIZE) (sz 4) =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          (sz 2)
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_range (out.[ sz 2 ]
                <:
                t_Array u8 v_SIZE)
              ({
                  Core.Ops.Range.f_start = st +! sz 8 <: usize;
                  Core.Ops.Range.f_end = st +! sz 16 <: usize
                }
                <:
                Core.Ops.Range.t_Range usize)
              (Core.Slice.impl__copy_from_slice #u8
                  ((out.[ sz 2 ] <: t_Array u8 v_SIZE).[ {
                        Core.Ops.Range.f_start = st +! sz 8 <: usize;
                        Core.Ops.Range.f_end = st +! sz 16 <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                  (u8s.[ { Core.Ops.Range.f_start = sz 16; Core.Ops.Range.f_end = sz 24 }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                <:
                t_Slice u8)
            <:
            t_Array u8 v_SIZE)
      in
      let out:t_Array (t_Array u8 v_SIZE) (sz 4) =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          (sz 3)
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_range (out.[ sz 3 ]
                <:
                t_Array u8 v_SIZE)
              ({
                  Core.Ops.Range.f_start = st +! sz 8 <: usize;
                  Core.Ops.Range.f_end = st +! sz 16 <: usize
                }
                <:
                Core.Ops.Range.t_Range usize)
              (Core.Slice.impl__copy_from_slice #u8
                  ((out.[ sz 3 ] <: t_Array u8 v_SIZE).[ {
                        Core.Ops.Range.f_start = st +! sz 8 <: usize;
                        Core.Ops.Range.f_end = st +! sz 16 <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                  (u8s.[ { Core.Ops.Range.f_start = sz 24; Core.Ops.Range.f_end = sz 32 }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                <:
                t_Slice u8)
            <:
            t_Array u8 v_SIZE)
      in
      out, () <: (t_Array (t_Array u8 v_SIZE) (sz 4) & Prims.unit)
    else out, () <: (t_Array (t_Array u8 v_SIZE) (sz 4) & Prims.unit)
  in
  out

let store_block_full (v_RATE: usize) (s: t_Array (t_Array u8 (sz 5)) (sz 5)) =
  let out:t_Array (t_Array u8 (sz 200)) (sz 4) =
    Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat 0uy (sz 200) <: t_Array u8 (sz 200))
      (sz 4)
  in
  let out:t_Array (t_Array u8 (sz 200)) (sz 4) = store_block v_RATE (sz 200) s out (sz 0) in
  out
