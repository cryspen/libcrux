module Hacspec_ml_dsa.Encoding
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

#push-options "--z3rlimit 300"

/// SimpleBitPack(w, b) — Algorithm 16.
/// Packs polynomial w (coefficients in [0, b]) into BYTES bytes.
let simple_bit_pack (v_BYTES: usize) (w: t_Array i32 (mk_usize 256)) (b: usize)
    : Prims.Pure (t_Array u8 v_BYTES)
      (requires
        v_BYTES =. (mk_usize 32 *! (Hacspec_ml_dsa.Parameters.bitlen b <: usize) <: usize) &&
        (Hacspec_ml_dsa.Parameters.bitlen b <: usize) <=. mk_usize 23)
      (fun _ -> Prims.l_True) =
  let bits:usize = Hacspec_ml_dsa.Parameters.bitlen b in
  let out:t_Array u8 v_BYTES = Rust_primitives.Hax.repeat (mk_u8 0) v_BYTES in
  let out:t_Array u8 v_BYTES =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (mk_usize 256)
      (fun out i ->
          let out:t_Array u8 v_BYTES = out in
          let i:usize = i in
          i <=. mk_usize 256 <: bool)
      out
      (fun out i ->
          let out:t_Array u8 v_BYTES = out in
          let i:usize = i in
          let v_val:u32 = cast (w.[ i ] <: i32) <: u32 in
          Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
            bits
            (fun out bit ->
                let out:t_Array u8 v_BYTES = out in
                let bit:usize = bit in
                bit <=. bits <: bool)
            out
            (fun out bit ->
                let out:t_Array u8 v_BYTES = out in
                let bit:usize = bit in
                let pos:usize = (i *! bits <: usize) +! bit in
                if ((v_val >>! bit <: u32) &. mk_u32 1 <: u32) =. mk_u32 1
                then
                  let out:t_Array u8 v_BYTES =
                    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
                      (pos /! mk_usize 8 <: usize)
                      ((out.[ pos /! mk_usize 8 <: usize ] <: u8) |.
                        (mk_u8 1 <<! (pos %! mk_usize 8 <: usize) <: u8)
                        <:
                        u8)
                  in
                  out
                else out))
  in
  out

#pop-options

#push-options "--z3rlimit 300"

/// BitPack(w, a, b) — Algorithm 17.
/// Packs polynomial w (coefficients in [-a, b]) into BYTES bytes.
/// Stores b - w_i for each coefficient.
let bit_pack (v_BYTES: usize) (w: t_Array i32 (mk_usize 256)) (a b: usize)
    : Prims.Pure (t_Array u8 v_BYTES)
      (requires
        ((Rust_primitives.Hax.Int.from_machine a <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine b <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine (mk_usize 16777216) <: Hax_lib.Int.t_Int) &&
        v_BYTES =.
        (mk_usize 32 *! (Hacspec_ml_dsa.Parameters.bitlen (a +! b <: usize) <: usize) <: usize) &&
        (Hacspec_ml_dsa.Parameters.bitlen (a +! b <: usize) <: usize) <=. mk_usize 23)
      (fun _ -> Prims.l_True) =
  let bits:usize = Hacspec_ml_dsa.Parameters.bitlen (a +! b <: usize) in
  let out:t_Array u8 v_BYTES = Rust_primitives.Hax.repeat (mk_u8 0) v_BYTES in
  let out:t_Array u8 v_BYTES =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (mk_usize 256)
      (fun out i ->
          let out:t_Array u8 v_BYTES = out in
          let i:usize = i in
          i <=. mk_usize 256 <: bool)
      out
      (fun out i ->
          let out:t_Array u8 v_BYTES = out in
          let i:usize = i in
          let v_val:u32 =
            cast ((cast (b <: usize) <: i64) -! (cast (w.[ i ] <: i32) <: i64) <: i64) <: u32
          in
          Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
            bits
            (fun out bit ->
                let out:t_Array u8 v_BYTES = out in
                let bit:usize = bit in
                bit <=. bits <: bool)
            out
            (fun out bit ->
                let out:t_Array u8 v_BYTES = out in
                let bit:usize = bit in
                let pos:usize = (i *! bits <: usize) +! bit in
                if ((v_val >>! bit <: u32) &. mk_u32 1 <: u32) =. mk_u32 1
                then
                  let out:t_Array u8 v_BYTES =
                    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
                      (pos /! mk_usize 8 <: usize)
                      ((out.[ pos /! mk_usize 8 <: usize ] <: u8) |.
                        (mk_u8 1 <<! (pos %! mk_usize 8 <: usize) <: u8)
                        <:
                        u8)
                  in
                  out
                else out))
  in
  out

#pop-options

#push-options "--z3rlimit 300"

/// SimpleBitUnpack(v, b) — Algorithm 18.
/// Unpacks bytes into a polynomial with coefficients in [0, 2^c - 1] where c = bitlen(b).
let simple_bit_unpack (v: t_Slice u8) (b: usize) : t_Array i32 (mk_usize 256) =
  let bits:usize = Hacspec_ml_dsa.Parameters.bitlen b in
  let w:t_Array i32 (mk_usize 256) = Hacspec_ml_dsa.Parameters.v_ZERO_POLY in
  let w:t_Array i32 (mk_usize 256) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (mk_usize 256)
      (fun w i ->
          let w:t_Array i32 (mk_usize 256) = w in
          let i:usize = i in
          i <=. mk_usize 256 <: bool)
      w
      (fun w i ->
          let w:t_Array i32 (mk_usize 256) = w in
          let i:usize = i in
          let v_val:u32 = mk_u32 0 in
          let v_val:u32 =
            Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
              (mk_usize 24)
              (fun v_val bit ->
                  let v_val:u32 = v_val in
                  let bit:usize = bit in
                  bit <=. mk_usize 24 <: bool)
              v_val
              (fun v_val bit ->
                  let v_val:u32 = v_val in
                  let bit:usize = bit in
                  if bit <. bits <: bool
                  then
                    let pos:usize = (i *! bits <: usize) +! bit in
                    if
                      (pos /! mk_usize 8 <: usize) <. (Core_models.Slice.impl__len #u8 v <: usize) &&
                      (((v.[ pos /! mk_usize 8 <: usize ] <: u8) >>! (pos %! mk_usize 8 <: usize)
                          <:
                          u8) &.
                        mk_u8 1
                        <:
                        u8) =.
                      mk_u8 1
                    then
                      let v_val:u32 = v_val |. (mk_u32 1 <<! bit <: u32) in
                      v_val
                    else v_val
                  else v_val)
          in
          let w:t_Array i32 (mk_usize 256) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize w
              i
              (cast (v_val <: u32) <: i32)
          in
          w)
  in
  w

#pop-options

#push-options "--z3rlimit 300"

/// BitUnpack(v, a, b) — Algorithm 19.
/// Unpacks bytes into a polynomial with coefficients in [b - 2^c + 1, b]
/// where c = bitlen(a + b). When a + b + 1 is a power of 2, coefficients are in [-a, b].
let bit_unpack (v: t_Slice u8) (a b: usize)
    : Prims.Pure (t_Array i32 (mk_usize 256))
      (requires
        ((Rust_primitives.Hax.Int.from_machine a <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine b <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine (mk_usize 16777216) <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let bits:usize = Hacspec_ml_dsa.Parameters.bitlen (a +! b <: usize) in
  let w:t_Array i32 (mk_usize 256) = Hacspec_ml_dsa.Parameters.v_ZERO_POLY in
  let w:t_Array i32 (mk_usize 256) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (mk_usize 256)
      (fun w i ->
          let w:t_Array i32 (mk_usize 256) = w in
          let i:usize = i in
          i <=. mk_usize 256 <: bool)
      w
      (fun w i ->
          let w:t_Array i32 (mk_usize 256) = w in
          let i:usize = i in
          let v_val:u32 = mk_u32 0 in
          let v_val:u32 =
            Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
              (mk_usize 24)
              (fun v_val bit ->
                  let v_val:u32 = v_val in
                  let bit:usize = bit in
                  bit <=. mk_usize 24 <: bool)
              v_val
              (fun v_val bit ->
                  let v_val:u32 = v_val in
                  let bit:usize = bit in
                  if bit <. bits <: bool
                  then
                    let pos:usize = (i *! bits <: usize) +! bit in
                    if
                      (pos /! mk_usize 8 <: usize) <. (Core_models.Slice.impl__len #u8 v <: usize) &&
                      (((v.[ pos /! mk_usize 8 <: usize ] <: u8) >>! (pos %! mk_usize 8 <: usize)
                          <:
                          u8) &.
                        mk_u8 1
                        <:
                        u8) =.
                      mk_u8 1
                    then
                      let v_val:u32 = v_val |. (mk_u32 1 <<! bit <: u32) in
                      v_val
                    else v_val
                  else v_val)
          in
          let w:t_Array i32 (mk_usize 256) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize w
              i
              (cast ((cast (b <: usize) <: i64) -! (cast (v_val <: u32) <: i64) <: i64) <: i32)
          in
          w)
  in
  w

#pop-options

#push-options "--z3rlimit 300"

/// HintBitPack(h) — Algorithm 20.
/// Encodes hint vector h (k polynomials with binary coefficients,
/// collectively at most ω nonzero) into ω + k bytes.
let hint_bit_pack
      (v_K v_HINT_BYTES: usize)
      (h: t_Array (t_Array bool (mk_usize 256)) v_K)
      (omega: usize)
    : Prims.Pure (t_Array u8 v_HINT_BYTES)
      (requires
        v_K <=. mk_usize 8 && omega <=. mk_usize 256 && (omega +! v_K <: usize) =. v_HINT_BYTES)
      (fun _ -> Prims.l_True) =
  let y:t_Array u8 v_HINT_BYTES = Rust_primitives.Hax.repeat (mk_u8 0) v_HINT_BYTES in
  let index:usize = mk_usize 0 in
  let (index: usize), (y: t_Array u8 v_HINT_BYTES) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      v_K
      (fun temp_0_ temp_1_ ->
          let (index: usize), (y: t_Array u8 v_HINT_BYTES) = temp_0_ in
          let _:usize = temp_1_ in
          true)
      (index, y <: (usize & t_Array u8 v_HINT_BYTES))
      (fun temp_0_ i ->
          let (index: usize), (y: t_Array u8 v_HINT_BYTES) = temp_0_ in
          let i:usize = i in
          let (index: usize), (y: t_Array u8 v_HINT_BYTES) =
            Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
              (mk_usize 256)
              (fun temp_0_ temp_1_ ->
                  let (index: usize), (y: t_Array u8 v_HINT_BYTES) = temp_0_ in
                  let _:usize = temp_1_ in
                  true)
              (index, y <: (usize & t_Array u8 v_HINT_BYTES))
              (fun temp_0_ j ->
                  let (index: usize), (y: t_Array u8 v_HINT_BYTES) = temp_0_ in
                  let j:usize = j in
                  if
                    ((h.[ i ] <: t_Array bool (mk_usize 256)).[ j ] <: bool) &&
                    (index <. omega <: bool)
                  then
                    let y:t_Array u8 v_HINT_BYTES =
                      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize y
                        index
                        (cast (j <: usize) <: u8)
                    in
                    let index:usize = index +! mk_usize 1 in
                    index, y <: (usize & t_Array u8 v_HINT_BYTES)
                  else index, y <: (usize & t_Array u8 v_HINT_BYTES))
          in
          let y:t_Array u8 v_HINT_BYTES =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize y
              (omega +! i <: usize)
              (cast (index <: usize) <: u8)
          in
          index, y <: (usize & t_Array u8 v_HINT_BYTES))
  in
  y

#pop-options

#push-options "--z3rlimit 300"

/// HintBitUnpack(y, omega) — Algorithm 21.
/// Decodes hint vector from ω + k bytes. Returns None if malformed.
let hint_bit_unpack (v_K: usize) (y: t_Slice u8) (omega: usize)
    : Prims.Pure (Core_models.Option.t_Option (t_Array (t_Array bool (mk_usize 256)) v_K))
      (requires
        v_K <=. mk_usize 8 && omega <=. mk_usize 256 &&
        (omega +! v_K <: usize) <=. (Core_models.Slice.impl__len #u8 y <: usize))
      (fun _ -> Prims.l_True) =
  let h:t_Array (t_Array bool (mk_usize 256)) v_K =
    Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat false (mk_usize 256)
        <:
        t_Array bool (mk_usize 256))
      v_K
  in
  let index:usize = mk_usize 0 in
  let valid:bool = true in
  let (h: t_Array (t_Array bool (mk_usize 256)) v_K), (index: usize), (valid: bool) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      v_K
      (fun temp_0_ temp_1_ ->
          let (h: t_Array (t_Array bool (mk_usize 256)) v_K), (index: usize), (valid: bool) =
            temp_0_
          in
          let _:usize = temp_1_ in
          true)
      (h, index, valid <: (t_Array (t_Array bool (mk_usize 256)) v_K & usize & bool))
      (fun temp_0_ i ->
          let (h: t_Array (t_Array bool (mk_usize 256)) v_K), (index: usize), (valid: bool) =
            temp_0_
          in
          let i:usize = i in
          if valid
          then
            let v_end:usize = cast (y.[ omega +! i <: usize ] <: u8) <: usize in
            if v_end <. index || v_end >. omega
            then
              let valid:bool = false in
              h, index, valid <: (t_Array (t_Array bool (mk_usize 256)) v_K & usize & bool)
            else
              let first:usize = index in
              Rust_primitives.Hax.Folds.fold_range (mk_i32 0)
                (mk_i32 256)
                (fun temp_0_ temp_1_ ->
                    let
                    (h: t_Array (t_Array bool (mk_usize 256)) v_K), (index: usize), (valid: bool) =
                      temp_0_
                    in
                    let _:i32 = temp_1_ in
                    true)
                (h, index, valid <: (t_Array (t_Array bool (mk_usize 256)) v_K & usize & bool))
                (fun temp_0_ e_scan ->
                    let
                    (h: t_Array (t_Array bool (mk_usize 256)) v_K), (index: usize), (valid: bool) =
                      temp_0_
                    in
                    let e_scan:i32 = e_scan in
                    if valid && (index <. v_end <: bool)
                    then
                      if
                        (index >. first <: bool) &&
                        ((y.[ index -! mk_usize 1 <: usize ] <: u8) >=. (y.[ index ] <: u8) <: bool)
                      then
                        let valid:bool = false in
                        h, index, valid
                        <:
                        (t_Array (t_Array bool (mk_usize 256)) v_K & usize & bool)
                      else
                        let h:t_Array (t_Array bool (mk_usize 256)) v_K =
                          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize h
                            i
                            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (h.[ i ]
                                  <:
                                  t_Array bool (mk_usize 256))
                                (cast (y.[ index ] <: u8) <: usize)
                                true
                              <:
                              t_Array bool (mk_usize 256))
                        in
                        let index:usize = index +! mk_usize 1 in
                        h, index, valid
                        <:
                        (t_Array (t_Array bool (mk_usize 256)) v_K & usize & bool)
                    else
                      h, index, valid <: (t_Array (t_Array bool (mk_usize 256)) v_K & usize & bool))
          else h, index, valid <: (t_Array (t_Array bool (mk_usize 256)) v_K & usize & bool))
  in
  let valid:bool =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (mk_usize 256)
      (fun valid temp_1_ ->
          let valid:bool = valid in
          let _:usize = temp_1_ in
          true)
      valid
      (fun valid i ->
          let valid:bool = valid in
          let i:usize = i in
          if valid && (i >=. index <: bool) && (i <. omega <: bool)
          then
            if (y.[ i ] <: u8) <>. mk_u8 0 <: bool
            then
              let valid:bool = false in
              valid
            else valid
          else valid)
  in
  if valid
  then
    Core_models.Option.Option_Some h
    <:
    Core_models.Option.t_Option (t_Array (t_Array bool (mk_usize 256)) v_K)
  else
    Core_models.Option.Option_None
    <:
    Core_models.Option.t_Option (t_Array (t_Array bool (mk_usize 256)) v_K)

#pop-options

#push-options "--z3rlimit 300"

/// pkEncode(ρ, t1) — Algorithm 22.
let pk_encode
      (v_K v_PK_SIZE: usize)
      (rho: t_Array u8 (mk_usize 32))
      (t1: t_Array (t_Array i32 (mk_usize 256)) v_K)
    : Prims.Pure (t_Array u8 v_PK_SIZE)
      (requires
        v_K <=. mk_usize 8 && v_PK_SIZE =. (mk_usize 32 +! (mk_usize 320 *! v_K <: usize) <: usize))
      (fun _ -> Prims.l_True) =
  let pk:t_Array u8 v_PK_SIZE = Rust_primitives.Hax.repeat (mk_u8 0) v_PK_SIZE in
  let pk:t_Array u8 v_PK_SIZE =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_to pk
      ({ Core_models.Ops.Range.f_end = mk_usize 32 } <: Core_models.Ops.Range.t_RangeTo usize)
      (Core_models.Slice.impl__copy_from_slice #u8
          (pk.[ { Core_models.Ops.Range.f_end = mk_usize 32 }
              <:
              Core_models.Ops.Range.t_RangeTo usize ]
            <:
            t_Slice u8)
          (rho <: t_Slice u8)
        <:
        t_Slice u8)
  in
  let pk:t_Array u8 v_PK_SIZE =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      v_K
      (fun pk temp_1_ ->
          let pk:t_Array u8 v_PK_SIZE = pk in
          let _:usize = temp_1_ in
          true)
      pk
      (fun pk i ->
          let pk:t_Array u8 v_PK_SIZE = pk in
          let i:usize = i in
          let _:Prims.unit = assert_norm (Hacspec_ml_dsa.Parameters.bitlen (sz 1023) == sz 10) in
          let (encoded: t_Array u8 (mk_usize 320)):t_Array u8 (mk_usize 320) =
            simple_bit_pack (mk_usize 320) (t1.[ i ] <: t_Array i32 (mk_usize 256)) (mk_usize 1023)
          in
          let pk:t_Array u8 v_PK_SIZE =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_range pk
              ({
                  Core_models.Ops.Range.f_start
                  =
                  mk_usize 32 +! (i *! mk_usize 320 <: usize) <: usize;
                  Core_models.Ops.Range.f_end
                  =
                  mk_usize 32 +! ((i +! mk_usize 1 <: usize) *! mk_usize 320 <: usize) <: usize
                }
                <:
                Core_models.Ops.Range.t_Range usize)
              (Core_models.Slice.impl__copy_from_slice #u8
                  (pk.[ {
                        Core_models.Ops.Range.f_start
                        =
                        mk_usize 32 +! (i *! mk_usize 320 <: usize) <: usize;
                        Core_models.Ops.Range.f_end
                        =
                        mk_usize 32 +! ((i +! mk_usize 1 <: usize) *! mk_usize 320 <: usize)
                        <:
                        usize
                      }
                      <:
                      Core_models.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                  (encoded <: t_Slice u8)
                <:
                t_Slice u8)
          in
          pk)
  in
  pk

#pop-options

#push-options "--z3rlimit 300"

/// pkDecode(pk) — Algorithm 23.
let pk_decode (v_K: usize) (pk: t_Slice u8)
    : Prims.Pure (t_Array u8 (mk_usize 32) & t_Array (t_Array i32 (mk_usize 256)) v_K)
      (requires
        v_K <=. mk_usize 8 &&
        (Core_models.Slice.impl__len #u8 pk <: usize) >=.
        (mk_usize 32 +! (mk_usize 320 *! v_K <: usize) <: usize))
      (fun _ -> Prims.l_True) =
  let rho:t_Array u8 (mk_usize 32) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 32) in
  let rho:t_Array u8 (mk_usize 32) =
    Core_models.Slice.impl__copy_from_slice #u8
      rho
      (pk.[ { Core_models.Ops.Range.f_end = mk_usize 32 } <: Core_models.Ops.Range.t_RangeTo usize ]
        <:
        t_Slice u8)
  in
  let (t1: t_Array (t_Array i32 (mk_usize 256)) v_K):t_Array (t_Array i32 (mk_usize 256)) v_K =
    Hacspec_ml_dsa.createi #(t_Array i32 (mk_usize 256))
      v_K
      #(usize -> t_Array i32 (mk_usize 256))
      (fun i ->
          let i:usize = i in
          let start:usize = mk_usize 32 +! (i *! mk_usize 320 <: usize) in
          simple_bit_unpack (pk.[ {
                  Core_models.Ops.Range.f_start = start;
                  Core_models.Ops.Range.f_end = start +! mk_usize 320 <: usize
                }
                <:
                Core_models.Ops.Range.t_Range usize ]
              <:
              t_Slice u8)
            (mk_usize 1023))
  in
  rho, t1 <: (t_Array u8 (mk_usize 32) & t_Array (t_Array i32 (mk_usize 256)) v_K)

#pop-options

#push-options "--z3rlimit 300"

/// skEncode(ρ, K, tr, s1, s2, t0) — Algorithm 24.
let sk_encode
      (v_K v_L v_SK_SIZE: usize)
      (rho key: t_Array u8 (mk_usize 32))
      (tr: t_Array u8 (mk_usize 64))
      (s1: t_Array (t_Array i32 (mk_usize 256)) v_L)
      (s2 t0: t_Array (t_Array i32 (mk_usize 256)) v_K)
      (params: Hacspec_ml_dsa.Parameters.t_MlDsaParams)
    : Prims.Pure (t_Array u8 v_SK_SIZE)
      (requires
        v_K <=. mk_usize 8 && v_L <=. mk_usize 8 &&
        (params.Hacspec_ml_dsa.Parameters.f_eta =. mk_usize 2 ||
        params.Hacspec_ml_dsa.Parameters.f_eta =. mk_usize 4) &&
        v_SK_SIZE >=.
        ((mk_usize 128 +! ((v_L +! v_K <: usize) *! mk_usize 128 <: usize) <: usize) +!
          (v_K *! mk_usize 416 <: usize)
          <:
          usize))
      (fun _ -> Prims.l_True) =
  let eta:usize = params.Hacspec_ml_dsa.Parameters.f_eta in
  let sk:t_Array u8 v_SK_SIZE = Rust_primitives.Hax.repeat (mk_u8 0) v_SK_SIZE in
  let sk:t_Array u8 v_SK_SIZE =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_to sk
      ({ Core_models.Ops.Range.f_end = mk_usize 32 } <: Core_models.Ops.Range.t_RangeTo usize)
      (Core_models.Slice.impl__copy_from_slice #u8
          (sk.[ { Core_models.Ops.Range.f_end = mk_usize 32 }
              <:
              Core_models.Ops.Range.t_RangeTo usize ]
            <:
            t_Slice u8)
          (rho <: t_Slice u8)
        <:
        t_Slice u8)
  in
  let sk:t_Array u8 v_SK_SIZE =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range sk
      ({ Core_models.Ops.Range.f_start = mk_usize 32; Core_models.Ops.Range.f_end = mk_usize 64 }
        <:
        Core_models.Ops.Range.t_Range usize)
      (Core_models.Slice.impl__copy_from_slice #u8
          (sk.[ {
                Core_models.Ops.Range.f_start = mk_usize 32;
                Core_models.Ops.Range.f_end = mk_usize 64
              }
              <:
              Core_models.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          (key <: t_Slice u8)
        <:
        t_Slice u8)
  in
  let sk:t_Array u8 v_SK_SIZE =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range sk
      ({ Core_models.Ops.Range.f_start = mk_usize 64; Core_models.Ops.Range.f_end = mk_usize 128 }
        <:
        Core_models.Ops.Range.t_Range usize)
      (Core_models.Slice.impl__copy_from_slice #u8
          (sk.[ {
                Core_models.Ops.Range.f_start = mk_usize 64;
                Core_models.Ops.Range.f_end = mk_usize 128
              }
              <:
              Core_models.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          (tr <: t_Slice u8)
        <:
        t_Slice u8)
  in
  let offset:usize = mk_usize 128 in
  let _:Prims.unit = assert_norm (Hacspec_ml_dsa.Parameters.bitlen (sz 4) == sz 3) in
  let _:Prims.unit = assert_norm (Hacspec_ml_dsa.Parameters.bitlen (sz 8) == sz 4) in
  let (offset: usize), (sk: t_Array u8 v_SK_SIZE) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      v_L
      (fun temp_0_ i ->
          let (offset: usize), (sk: t_Array u8 v_SK_SIZE) = temp_0_ in
          let i:usize = i in
          offset =.
          (mk_usize 128 +!
            (i *!
              ((Hacspec_ml_dsa.Parameters.bitlen (mk_usize 2 *! eta <: usize) <: usize) *!
                mk_usize 32
                <:
                usize)
              <:
              usize)
            <:
            usize)
          <:
          bool)
      (offset, sk <: (usize & t_Array u8 v_SK_SIZE))
      (fun temp_0_ i ->
          let (offset: usize), (sk: t_Array u8 v_SK_SIZE) = temp_0_ in
          let i:usize = i in
          if eta =. mk_usize 2 <: bool
          then
            let (encoded: t_Array u8 (mk_usize 96)):t_Array u8 (mk_usize 96) =
              bit_pack (mk_usize 96) (s1.[ i ] <: t_Array i32 (mk_usize 256)) eta eta
            in
            let sk:t_Array u8 v_SK_SIZE =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_range sk
                ({
                    Core_models.Ops.Range.f_start = offset;
                    Core_models.Ops.Range.f_end = offset +! mk_usize 96 <: usize
                  }
                  <:
                  Core_models.Ops.Range.t_Range usize)
                (Core_models.Slice.impl__copy_from_slice #u8
                    (sk.[ {
                          Core_models.Ops.Range.f_start = offset;
                          Core_models.Ops.Range.f_end = offset +! mk_usize 96 <: usize
                        }
                        <:
                        Core_models.Ops.Range.t_Range usize ]
                      <:
                      t_Slice u8)
                    (encoded <: t_Slice u8)
                  <:
                  t_Slice u8)
            in
            let offset:usize = offset +! mk_usize 96 in
            offset, sk <: (usize & t_Array u8 v_SK_SIZE)
          else
            let (encoded: t_Array u8 (mk_usize 128)):t_Array u8 (mk_usize 128) =
              bit_pack (mk_usize 128) (s1.[ i ] <: t_Array i32 (mk_usize 256)) eta eta
            in
            let sk:t_Array u8 v_SK_SIZE =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_range sk
                ({
                    Core_models.Ops.Range.f_start = offset;
                    Core_models.Ops.Range.f_end = offset +! mk_usize 128 <: usize
                  }
                  <:
                  Core_models.Ops.Range.t_Range usize)
                (Core_models.Slice.impl__copy_from_slice #u8
                    (sk.[ {
                          Core_models.Ops.Range.f_start = offset;
                          Core_models.Ops.Range.f_end = offset +! mk_usize 128 <: usize
                        }
                        <:
                        Core_models.Ops.Range.t_Range usize ]
                      <:
                      t_Slice u8)
                    (encoded <: t_Slice u8)
                  <:
                  t_Slice u8)
            in
            let offset:usize = offset +! mk_usize 128 in
            offset, sk <: (usize & t_Array u8 v_SK_SIZE))
  in
  let (offset: usize), (sk: t_Array u8 v_SK_SIZE) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      v_K
      (fun temp_0_ i ->
          let (offset: usize), (sk: t_Array u8 v_SK_SIZE) = temp_0_ in
          let i:usize = i in
          offset =.
          ((mk_usize 128 +!
              (v_L *!
                ((Hacspec_ml_dsa.Parameters.bitlen (mk_usize 2 *! eta <: usize) <: usize) *!
                  mk_usize 32
                  <:
                  usize)
                <:
                usize)
              <:
              usize) +!
            (i *!
              ((Hacspec_ml_dsa.Parameters.bitlen (mk_usize 2 *! eta <: usize) <: usize) *!
                mk_usize 32
                <:
                usize)
              <:
              usize)
            <:
            usize)
          <:
          bool)
      (offset, sk <: (usize & t_Array u8 v_SK_SIZE))
      (fun temp_0_ i ->
          let (offset: usize), (sk: t_Array u8 v_SK_SIZE) = temp_0_ in
          let i:usize = i in
          if eta =. mk_usize 2 <: bool
          then
            let (encoded: t_Array u8 (mk_usize 96)):t_Array u8 (mk_usize 96) =
              bit_pack (mk_usize 96) (s2.[ i ] <: t_Array i32 (mk_usize 256)) eta eta
            in
            let sk:t_Array u8 v_SK_SIZE =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_range sk
                ({
                    Core_models.Ops.Range.f_start = offset;
                    Core_models.Ops.Range.f_end = offset +! mk_usize 96 <: usize
                  }
                  <:
                  Core_models.Ops.Range.t_Range usize)
                (Core_models.Slice.impl__copy_from_slice #u8
                    (sk.[ {
                          Core_models.Ops.Range.f_start = offset;
                          Core_models.Ops.Range.f_end = offset +! mk_usize 96 <: usize
                        }
                        <:
                        Core_models.Ops.Range.t_Range usize ]
                      <:
                      t_Slice u8)
                    (encoded <: t_Slice u8)
                  <:
                  t_Slice u8)
            in
            let offset:usize = offset +! mk_usize 96 in
            offset, sk <: (usize & t_Array u8 v_SK_SIZE)
          else
            let (encoded: t_Array u8 (mk_usize 128)):t_Array u8 (mk_usize 128) =
              bit_pack (mk_usize 128) (s2.[ i ] <: t_Array i32 (mk_usize 256)) eta eta
            in
            let sk:t_Array u8 v_SK_SIZE =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_range sk
                ({
                    Core_models.Ops.Range.f_start = offset;
                    Core_models.Ops.Range.f_end = offset +! mk_usize 128 <: usize
                  }
                  <:
                  Core_models.Ops.Range.t_Range usize)
                (Core_models.Slice.impl__copy_from_slice #u8
                    (sk.[ {
                          Core_models.Ops.Range.f_start = offset;
                          Core_models.Ops.Range.f_end = offset +! mk_usize 128 <: usize
                        }
                        <:
                        Core_models.Ops.Range.t_Range usize ]
                      <:
                      t_Slice u8)
                    (encoded <: t_Slice u8)
                  <:
                  t_Slice u8)
            in
            let offset:usize = offset +! mk_usize 128 in
            offset, sk <: (usize & t_Array u8 v_SK_SIZE))
  in
  let _:Prims.unit = assert_norm (Hacspec_ml_dsa.Parameters.bitlen (sz (4095 + 4096)) == sz 13) in
  let (offset: usize), (sk: t_Array u8 v_SK_SIZE) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      v_K
      (fun temp_0_ i ->
          let (offset: usize), (sk: t_Array u8 v_SK_SIZE) = temp_0_ in
          let i:usize = i in
          offset =.
          ((mk_usize 128 +!
              ((v_L +! v_K <: usize) *!
                ((Hacspec_ml_dsa.Parameters.bitlen (mk_usize 2 *! eta <: usize) <: usize) *!
                  mk_usize 32
                  <:
                  usize)
                <:
                usize)
              <:
              usize) +!
            (i *! mk_usize 416 <: usize)
            <:
            usize)
          <:
          bool)
      (offset, sk <: (usize & t_Array u8 v_SK_SIZE))
      (fun temp_0_ i ->
          let (offset: usize), (sk: t_Array u8 v_SK_SIZE) = temp_0_ in
          let i:usize = i in
          let (encoded: t_Array u8 (mk_usize 416)):t_Array u8 (mk_usize 416) =
            bit_pack (mk_usize 416)
              (t0.[ i ] <: t_Array i32 (mk_usize 256))
              ((mk_usize 1 <<! (Hacspec_ml_dsa.Parameters.v_D -! mk_usize 1 <: usize) <: usize) -!
                mk_usize 1
                <:
                usize)
              (mk_usize 1 <<! (Hacspec_ml_dsa.Parameters.v_D -! mk_usize 1 <: usize) <: usize)
          in
          let sk:t_Array u8 v_SK_SIZE =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_range sk
              ({
                  Core_models.Ops.Range.f_start = offset;
                  Core_models.Ops.Range.f_end = offset +! mk_usize 416 <: usize
                }
                <:
                Core_models.Ops.Range.t_Range usize)
              (Core_models.Slice.impl__copy_from_slice #u8
                  (sk.[ {
                        Core_models.Ops.Range.f_start = offset;
                        Core_models.Ops.Range.f_end = offset +! mk_usize 416 <: usize
                      }
                      <:
                      Core_models.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                  (encoded <: t_Slice u8)
                <:
                t_Slice u8)
          in
          let offset:usize = offset +! mk_usize 416 in
          offset, sk <: (usize & t_Array u8 v_SK_SIZE))
  in
  sk

#pop-options

#push-options "--z3rlimit 300"

/// skDecode(sk) — Algorithm 25.
let sk_decode (v_K v_L: usize) (sk: t_Slice u8) (params: Hacspec_ml_dsa.Parameters.t_MlDsaParams)
    : Prims.Pure
      (t_Array u8 (mk_usize 32) & t_Array u8 (mk_usize 32) & t_Array u8 (mk_usize 64) &
        t_Array (t_Array i32 (mk_usize 256)) v_L &
        t_Array (t_Array i32 (mk_usize 256)) v_K &
        t_Array (t_Array i32 (mk_usize 256)) v_K)
      (requires
        v_K <=. mk_usize 8 && v_L <=. mk_usize 8 &&
        (params.Hacspec_ml_dsa.Parameters.f_eta =. mk_usize 2 ||
        params.Hacspec_ml_dsa.Parameters.f_eta =. mk_usize 4) &&
        (Core_models.Slice.impl__len #u8 sk <: usize) >=.
        ((mk_usize 128 +! ((v_L +! v_K <: usize) *! mk_usize 128 <: usize) <: usize) +!
          (v_K *! mk_usize 416 <: usize)
          <:
          usize))
      (fun _ -> Prims.l_True) =
  let eta:usize = params.Hacspec_ml_dsa.Parameters.f_eta in
  let _:Prims.unit = assert_norm (Hacspec_ml_dsa.Parameters.bitlen (sz 4) == sz 3) in
  let _:Prims.unit = assert_norm (Hacspec_ml_dsa.Parameters.bitlen (sz 8) == sz 4) in
  let eta_bytes:usize =
    mk_usize 32 *! (Hacspec_ml_dsa.Parameters.bitlen (mk_usize 2 *! eta <: usize) <: usize)
  in
  let rho:t_Array u8 (mk_usize 32) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 32) in
  let rho:t_Array u8 (mk_usize 32) =
    Core_models.Slice.impl__copy_from_slice #u8
      rho
      (sk.[ { Core_models.Ops.Range.f_end = mk_usize 32 } <: Core_models.Ops.Range.t_RangeTo usize ]
        <:
        t_Slice u8)
  in
  let key:t_Array u8 (mk_usize 32) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 32) in
  let key:t_Array u8 (mk_usize 32) =
    Core_models.Slice.impl__copy_from_slice #u8
      key
      (sk.[ {
            Core_models.Ops.Range.f_start = mk_usize 32;
            Core_models.Ops.Range.f_end = mk_usize 64
          }
          <:
          Core_models.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let tr:t_Array u8 (mk_usize 64) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 64) in
  let tr:t_Array u8 (mk_usize 64) =
    Core_models.Slice.impl__copy_from_slice #u8
      tr
      (sk.[ {
            Core_models.Ops.Range.f_start = mk_usize 64;
            Core_models.Ops.Range.f_end = mk_usize 128
          }
          <:
          Core_models.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let (s1: t_Array (t_Array i32 (mk_usize 256)) v_L):t_Array (t_Array i32 (mk_usize 256)) v_L =
    Hacspec_ml_dsa.createi #(t_Array i32 (mk_usize 256))
      v_L
      #(usize -> t_Array i32 (mk_usize 256))
      (fun i ->
          let i:usize = i in
          let offset:usize = mk_usize 128 +! (i *! eta_bytes <: usize) in
          bit_unpack (sk.[ {
                  Core_models.Ops.Range.f_start = offset;
                  Core_models.Ops.Range.f_end = offset +! eta_bytes <: usize
                }
                <:
                Core_models.Ops.Range.t_Range usize ]
              <:
              t_Slice u8)
            eta
            eta)
  in
  let (s2: t_Array (t_Array i32 (mk_usize 256)) v_K):t_Array (t_Array i32 (mk_usize 256)) v_K =
    Hacspec_ml_dsa.createi #(t_Array i32 (mk_usize 256))
      v_K
      #(usize -> t_Array i32 (mk_usize 256))
      (fun i ->
          let i:usize = i in
          let offset:usize =
            (mk_usize 128 +! (v_L *! eta_bytes <: usize) <: usize) +! (i *! eta_bytes <: usize)
          in
          bit_unpack (sk.[ {
                  Core_models.Ops.Range.f_start = offset;
                  Core_models.Ops.Range.f_end = offset +! eta_bytes <: usize
                }
                <:
                Core_models.Ops.Range.t_Range usize ]
              <:
              t_Slice u8)
            eta
            eta)
  in
  let d_minus_1_:usize = Hacspec_ml_dsa.Parameters.v_D -! mk_usize 1 in
  let _:Prims.unit =
    assert_norm (Hacspec_ml_dsa.Parameters.bitlen (sz (pow2 12 - 1 + pow2 12)) == sz 13)
  in
  let t0_bytes:usize =
    mk_usize 32 *!
    (Hacspec_ml_dsa.Parameters.bitlen (((mk_usize 1 <<! d_minus_1_ <: usize) -! mk_usize 1 <: usize) +!
          (mk_usize 1 <<! d_minus_1_ <: usize)
          <:
          usize)
      <:
      usize)
  in
  let (t0: t_Array (t_Array i32 (mk_usize 256)) v_K):t_Array (t_Array i32 (mk_usize 256)) v_K =
    Hacspec_ml_dsa.createi #(t_Array i32 (mk_usize 256))
      v_K
      #(usize -> t_Array i32 (mk_usize 256))
      (fun i ->
          let i:usize = i in
          let offset:usize =
            (mk_usize 128 +! ((v_L +! v_K <: usize) *! eta_bytes <: usize) <: usize) +!
            (i *! t0_bytes <: usize)
          in
          bit_unpack (sk.[ {
                  Core_models.Ops.Range.f_start = offset;
                  Core_models.Ops.Range.f_end = offset +! t0_bytes <: usize
                }
                <:
                Core_models.Ops.Range.t_Range usize ]
              <:
              t_Slice u8)
            ((mk_usize 1 <<! d_minus_1_ <: usize) -! mk_usize 1 <: usize)
            (mk_usize 1 <<! d_minus_1_ <: usize))
  in
  rho, key, tr, s1, s2, t0
  <:
  (t_Array u8 (mk_usize 32) & t_Array u8 (mk_usize 32) & t_Array u8 (mk_usize 64) &
    t_Array (t_Array i32 (mk_usize 256)) v_L &
    t_Array (t_Array i32 (mk_usize 256)) v_K &
    t_Array (t_Array i32 (mk_usize 256)) v_K)

#pop-options

#push-options "--z3rlimit 300"

#push-options "--admit_smt_queries true"

/// sigEncode(c\u{303}, z, h) — Algorithm 26.
let sig_encode
      (v_K v_L v_SIG_SIZE: usize)
      (c_tilde: t_Slice u8)
      (z: t_Array (t_Array i32 (mk_usize 256)) v_L)
      (h: t_Array (t_Array bool (mk_usize 256)) v_K)
      (params: Hacspec_ml_dsa.Parameters.t_MlDsaParams)
    : Prims.Pure (t_Array u8 v_SIG_SIZE)
      (requires
        v_K <=. mk_usize 8 && v_L <=. mk_usize 8 &&
        params.Hacspec_ml_dsa.Parameters.f_omega <=. mk_usize 256 &&
        params.Hacspec_ml_dsa.Parameters.f_lambda <=. mk_usize 256 &&
        (params.Hacspec_ml_dsa.Parameters.f_gamma1 =. (mk_i32 1 <<! mk_i32 17 <: i32) ||
        params.Hacspec_ml_dsa.Parameters.f_gamma1 =. (mk_i32 1 <<! mk_i32 19 <: i32)) &&
        (Core_models.Slice.impl__len #u8 c_tilde <: usize) >=.
        (params.Hacspec_ml_dsa.Parameters.f_lambda /! mk_usize 4 <: usize) &&
        v_SIG_SIZE >=.
        ((((params.Hacspec_ml_dsa.Parameters.f_lambda /! mk_usize 4 <: usize) +!
              (v_L *! mk_usize 640 <: usize)
              <:
              usize) +!
            params.Hacspec_ml_dsa.Parameters.f_omega
            <:
            usize) +!
          v_K
          <:
          usize))
      (fun _ -> Prims.l_True) =
  let gamma1:usize = cast (params.Hacspec_ml_dsa.Parameters.f_gamma1 <: i32) <: usize in
  let c_tilde_len:usize = params.Hacspec_ml_dsa.Parameters.f_lambda /! mk_usize 4 in
  let sigma:t_Array u8 v_SIG_SIZE = Rust_primitives.Hax.repeat (mk_u8 0) v_SIG_SIZE in
  let sigma:t_Array u8 v_SIG_SIZE =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_to sigma
      ({ Core_models.Ops.Range.f_end = c_tilde_len } <: Core_models.Ops.Range.t_RangeTo usize)
      (Core_models.Slice.impl__copy_from_slice #u8
          (sigma.[ { Core_models.Ops.Range.f_end = c_tilde_len }
              <:
              Core_models.Ops.Range.t_RangeTo usize ]
            <:
            t_Slice u8)
          (c_tilde.[ { Core_models.Ops.Range.f_end = c_tilde_len }
              <:
              Core_models.Ops.Range.t_RangeTo usize ]
            <:
            t_Slice u8)
        <:
        t_Slice u8)
  in
  let offset:usize = c_tilde_len in
  let _:Prims.unit =
    assert_norm (Hacspec_ml_dsa.Parameters.bitlen (sz (pow2 17 - 1 + pow2 17)) == sz 18)
  in
  let _:Prims.unit =
    assert_norm (Hacspec_ml_dsa.Parameters.bitlen (sz (pow2 19 - 1 + pow2 19)) == sz 20)
  in
  let (offset: usize), (sigma: t_Array u8 v_SIG_SIZE) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      v_L
      (fun temp_0_ i ->
          let (offset: usize), (sigma: t_Array u8 v_SIG_SIZE) = temp_0_ in
          let i:usize = i in
          offset =.
          (c_tilde_len +!
            (i *!
              ((Hacspec_ml_dsa.Parameters.bitlen ((gamma1 -! mk_usize 1 <: usize) +! gamma1 <: usize
                    )
                  <:
                  usize) *!
                mk_usize 32
                <:
                usize)
              <:
              usize)
            <:
            usize)
          <:
          bool)
      (offset, sigma <: (usize & t_Array u8 v_SIG_SIZE))
      (fun temp_0_ i ->
          let (offset: usize), (sigma: t_Array u8 v_SIG_SIZE) = temp_0_ in
          let i:usize = i in
          if gamma1 =. (mk_usize 1 <<! mk_i32 17 <: usize) <: bool
          then
            let (encoded: t_Array u8 (mk_usize 576)):t_Array u8 (mk_usize 576) =
              bit_pack (mk_usize 576)
                (z.[ i ] <: t_Array i32 (mk_usize 256))
                (gamma1 -! mk_usize 1 <: usize)
                gamma1
            in
            let sigma:t_Array u8 v_SIG_SIZE =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_range sigma
                ({
                    Core_models.Ops.Range.f_start = offset;
                    Core_models.Ops.Range.f_end = offset +! mk_usize 576 <: usize
                  }
                  <:
                  Core_models.Ops.Range.t_Range usize)
                (Core_models.Slice.impl__copy_from_slice #u8
                    (sigma.[ {
                          Core_models.Ops.Range.f_start = offset;
                          Core_models.Ops.Range.f_end = offset +! mk_usize 576 <: usize
                        }
                        <:
                        Core_models.Ops.Range.t_Range usize ]
                      <:
                      t_Slice u8)
                    (encoded <: t_Slice u8)
                  <:
                  t_Slice u8)
            in
            let offset:usize = offset +! mk_usize 576 in
            offset, sigma <: (usize & t_Array u8 v_SIG_SIZE)
          else
            let (encoded: t_Array u8 (mk_usize 640)):t_Array u8 (mk_usize 640) =
              bit_pack (mk_usize 640)
                (z.[ i ] <: t_Array i32 (mk_usize 256))
                (gamma1 -! mk_usize 1 <: usize)
                gamma1
            in
            let sigma:t_Array u8 v_SIG_SIZE =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_range sigma
                ({
                    Core_models.Ops.Range.f_start = offset;
                    Core_models.Ops.Range.f_end = offset +! mk_usize 640 <: usize
                  }
                  <:
                  Core_models.Ops.Range.t_Range usize)
                (Core_models.Slice.impl__copy_from_slice #u8
                    (sigma.[ {
                          Core_models.Ops.Range.f_start = offset;
                          Core_models.Ops.Range.f_end = offset +! mk_usize 640 <: usize
                        }
                        <:
                        Core_models.Ops.Range.t_Range usize ]
                      <:
                      t_Slice u8)
                    (encoded <: t_Slice u8)
                  <:
                  t_Slice u8)
            in
            let offset:usize = offset +! mk_usize 640 in
            offset, sigma <: (usize & t_Array u8 v_SIG_SIZE))
  in
  let hint_bytes:usize = params.Hacspec_ml_dsa.Parameters.f_omega +! v_K in
  let sigma:t_Array u8 v_SIG_SIZE =
    if gamma1 =. (mk_usize 1 <<! mk_i32 17 <: usize)
    then
      let (hint_enc: t_Array u8 (mk_usize 84)):t_Array u8 (mk_usize 84) =
        hint_bit_pack v_K (mk_usize 84) h params.Hacspec_ml_dsa.Parameters.f_omega
      in
      let sigma:t_Array u8 v_SIG_SIZE =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_range sigma
          ({
              Core_models.Ops.Range.f_start = offset;
              Core_models.Ops.Range.f_end = offset +! hint_bytes <: usize
            }
            <:
            Core_models.Ops.Range.t_Range usize)
          (Core_models.Slice.impl__copy_from_slice #u8
              (sigma.[ {
                    Core_models.Ops.Range.f_start = offset;
                    Core_models.Ops.Range.f_end = offset +! hint_bytes <: usize
                  }
                  <:
                  Core_models.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
              (hint_enc.[ { Core_models.Ops.Range.f_end = hint_bytes }
                  <:
                  Core_models.Ops.Range.t_RangeTo usize ]
                <:
                t_Slice u8)
            <:
            t_Slice u8)
      in
      sigma
    else
      if params.Hacspec_ml_dsa.Parameters.f_omega =. mk_usize 55
      then
        let (hint_enc: t_Array u8 (mk_usize 61)):t_Array u8 (mk_usize 61) =
          hint_bit_pack v_K (mk_usize 61) h params.Hacspec_ml_dsa.Parameters.f_omega
        in
        let sigma:t_Array u8 v_SIG_SIZE =
          Rust_primitives.Hax.Monomorphized_update_at.update_at_range sigma
            ({
                Core_models.Ops.Range.f_start = offset;
                Core_models.Ops.Range.f_end = offset +! hint_bytes <: usize
              }
              <:
              Core_models.Ops.Range.t_Range usize)
            (Core_models.Slice.impl__copy_from_slice #u8
                (sigma.[ {
                      Core_models.Ops.Range.f_start = offset;
                      Core_models.Ops.Range.f_end = offset +! hint_bytes <: usize
                    }
                    <:
                    Core_models.Ops.Range.t_Range usize ]
                  <:
                  t_Slice u8)
                (hint_enc.[ { Core_models.Ops.Range.f_end = hint_bytes }
                    <:
                    Core_models.Ops.Range.t_RangeTo usize ]
                  <:
                  t_Slice u8)
              <:
              t_Slice u8)
        in
        sigma
      else
        let (hint_enc: t_Array u8 (mk_usize 83)):t_Array u8 (mk_usize 83) =
          hint_bit_pack v_K (mk_usize 83) h params.Hacspec_ml_dsa.Parameters.f_omega
        in
        let sigma:t_Array u8 v_SIG_SIZE =
          Rust_primitives.Hax.Monomorphized_update_at.update_at_range sigma
            ({
                Core_models.Ops.Range.f_start = offset;
                Core_models.Ops.Range.f_end = offset +! hint_bytes <: usize
              }
              <:
              Core_models.Ops.Range.t_Range usize)
            (Core_models.Slice.impl__copy_from_slice #u8
                (sigma.[ {
                      Core_models.Ops.Range.f_start = offset;
                      Core_models.Ops.Range.f_end = offset +! hint_bytes <: usize
                    }
                    <:
                    Core_models.Ops.Range.t_Range usize ]
                  <:
                  t_Slice u8)
                (hint_enc.[ { Core_models.Ops.Range.f_end = hint_bytes }
                    <:
                    Core_models.Ops.Range.t_RangeTo usize ]
                  <:
                  t_Slice u8)
              <:
              t_Slice u8)
        in
        sigma
  in
  sigma

#pop-options

#pop-options

#push-options "--z3rlimit 300"

/// sigDecode(σ) — Algorithm 27.
/// Returns (c\u{303}, z, h) or None if the hint is malformed.
let sig_decode
      (v_K v_L v_CC_TILDE_LEN: usize)
      (sigma: t_Slice u8)
      (params: Hacspec_ml_dsa.Parameters.t_MlDsaParams)
    : Prims.Pure
      (Core_models.Option.t_Option
        (t_Array u8 v_CC_TILDE_LEN & t_Array (t_Array i32 (mk_usize 256)) v_L &
          t_Array (t_Array bool (mk_usize 256)) v_K))
      (requires
        v_K <=. mk_usize 8 && v_L <=. mk_usize 8 &&
        params.Hacspec_ml_dsa.Parameters.f_omega <=. mk_usize 256 &&
        v_CC_TILDE_LEN <=. mk_usize 64 &&
        (params.Hacspec_ml_dsa.Parameters.f_gamma1 =. (mk_i32 1 <<! mk_i32 17 <: i32) ||
        params.Hacspec_ml_dsa.Parameters.f_gamma1 =. (mk_i32 1 <<! mk_i32 19 <: i32)) &&
        (Core_models.Slice.impl__len #u8 sigma <: usize) >=.
        (((v_CC_TILDE_LEN +! (v_L *! mk_usize 640 <: usize) <: usize) +!
            params.Hacspec_ml_dsa.Parameters.f_omega
            <:
            usize) +!
          v_K
          <:
          usize))
      (fun _ -> Prims.l_True) =
  let gamma1:usize = cast (params.Hacspec_ml_dsa.Parameters.f_gamma1 <: i32) <: usize in
  let _:Prims.unit =
    assert_norm (Hacspec_ml_dsa.Parameters.bitlen (sz (pow2 17 - 1 + pow2 17)) == sz 18)
  in
  let _:Prims.unit =
    assert_norm (Hacspec_ml_dsa.Parameters.bitlen (sz (pow2 19 - 1 + pow2 19)) == sz 20)
  in
  let z_bytes:usize =
    mk_usize 32 *!
    (Hacspec_ml_dsa.Parameters.bitlen ((gamma1 -! mk_usize 1 <: usize) +! gamma1 <: usize) <: usize)
  in
  let c_tilde:t_Array u8 v_CC_TILDE_LEN = Rust_primitives.Hax.repeat (mk_u8 0) v_CC_TILDE_LEN in
  let c_tilde:t_Array u8 v_CC_TILDE_LEN =
    Core_models.Slice.impl__copy_from_slice #u8
      c_tilde
      (sigma.[ { Core_models.Ops.Range.f_end = v_CC_TILDE_LEN }
          <:
          Core_models.Ops.Range.t_RangeTo usize ]
        <:
        t_Slice u8)
  in
  let (z: t_Array (t_Array i32 (mk_usize 256)) v_L):t_Array (t_Array i32 (mk_usize 256)) v_L =
    Hacspec_ml_dsa.createi #(t_Array i32 (mk_usize 256))
      v_L
      #(usize -> t_Array i32 (mk_usize 256))
      (fun i ->
          let i:usize = i in
          let offset:usize = v_CC_TILDE_LEN +! (i *! z_bytes <: usize) in
          bit_unpack (sigma.[ {
                  Core_models.Ops.Range.f_start = offset;
                  Core_models.Ops.Range.f_end = offset +! z_bytes <: usize
                }
                <:
                Core_models.Ops.Range.t_Range usize ]
              <:
              t_Slice u8)
            (gamma1 -! mk_usize 1 <: usize)
            gamma1)
  in
  let hint_offset:usize = v_CC_TILDE_LEN +! (v_L *! z_bytes <: usize) in
  match
    hint_bit_unpack v_K
      (sigma.[ { Core_models.Ops.Range.f_start = hint_offset }
          <:
          Core_models.Ops.Range.t_RangeFrom usize ]
        <:
        t_Slice u8)
      params.Hacspec_ml_dsa.Parameters.f_omega
    <:
    Core_models.Option.t_Option (t_Array (t_Array bool (mk_usize 256)) v_K)
  with
  | Core_models.Option.Option_Some h ->
    Core_models.Option.Option_Some
    (c_tilde, z, h
      <:
      (t_Array u8 v_CC_TILDE_LEN & t_Array (t_Array i32 (mk_usize 256)) v_L &
        t_Array (t_Array bool (mk_usize 256)) v_K))
    <:
    Core_models.Option.t_Option
    (t_Array u8 v_CC_TILDE_LEN & t_Array (t_Array i32 (mk_usize 256)) v_L &
      t_Array (t_Array bool (mk_usize 256)) v_K)
  | Core_models.Option.Option_None  ->
    Core_models.Option.Option_None
    <:
    Core_models.Option.t_Option
    (t_Array u8 v_CC_TILDE_LEN & t_Array (t_Array i32 (mk_usize 256)) v_L &
      t_Array (t_Array bool (mk_usize 256)) v_K)

#pop-options

#push-options "--z3rlimit 300"

/// w1Encode(w1) — Algorithm 28.
/// Encodes the high-bits vector w1 into bytes for hashing.
let w1_encode
      (v_K v_W1_BYTES: usize)
      (w1: t_Array (t_Array i32 (mk_usize 256)) v_K)
      (params: Hacspec_ml_dsa.Parameters.t_MlDsaParams)
    : Prims.Pure (t_Array u8 v_W1_BYTES)
      (requires
        v_K <=. mk_usize 8 &&
        (params.Hacspec_ml_dsa.Parameters.f_gamma2 =.
        ((Hacspec_ml_dsa.Parameters.v_Q -! mk_i32 1 <: i32) /! mk_i32 88 <: i32) ||
        params.Hacspec_ml_dsa.Parameters.f_gamma2 =.
        ((Hacspec_ml_dsa.Parameters.v_Q -! mk_i32 1 <: i32) /! mk_i32 32 <: i32)) &&
        v_W1_BYTES >=. (v_K *! mk_usize 192 <: usize))
      (fun _ -> Prims.l_True) =
  let encoded:t_Array u8 v_W1_BYTES = Rust_primitives.Hax.repeat (mk_u8 0) v_W1_BYTES in
  let _:Prims.unit = assert_norm (Hacspec_ml_dsa.Parameters.bitlen (sz 43) == sz 6) in
  let _:Prims.unit = assert_norm (Hacspec_ml_dsa.Parameters.bitlen (sz 15) == sz 4) in
  let w1_max:usize =
    cast (((Hacspec_ml_dsa.Parameters.v_Q -! mk_i32 1 <: i32) /!
          (mk_i32 2 *! params.Hacspec_ml_dsa.Parameters.f_gamma2 <: i32)
          <:
          i32) -!
        mk_i32 1
        <:
        i32)
    <:
    usize
  in
  let bytes_per_poly:usize = mk_usize 32 *! (Hacspec_ml_dsa.Parameters.bitlen w1_max <: usize) in
  let encoded:t_Array u8 v_W1_BYTES =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      v_K
      (fun encoded i ->
          let encoded:t_Array u8 v_W1_BYTES = encoded in
          let i:usize = i in
          i <=. v_K <: bool)
      encoded
      (fun encoded i ->
          let encoded:t_Array u8 v_W1_BYTES = encoded in
          let i:usize = i in
          if
            params.Hacspec_ml_dsa.Parameters.f_gamma2 =.
            ((Hacspec_ml_dsa.Parameters.v_Q -! mk_i32 1 <: i32) /! mk_i32 88 <: i32)
            <:
            bool
          then
            let (packed: t_Array u8 (mk_usize 192)):t_Array u8 (mk_usize 192) =
              simple_bit_pack (mk_usize 192) (w1.[ i ] <: t_Array i32 (mk_usize 256)) w1_max
            in
            let encoded:t_Array u8 v_W1_BYTES =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_range encoded
                ({
                    Core_models.Ops.Range.f_start = i *! bytes_per_poly <: usize;
                    Core_models.Ops.Range.f_end
                    =
                    (i +! mk_usize 1 <: usize) *! bytes_per_poly <: usize
                  }
                  <:
                  Core_models.Ops.Range.t_Range usize)
                (Core_models.Slice.impl__copy_from_slice #u8
                    (encoded.[ {
                          Core_models.Ops.Range.f_start = i *! bytes_per_poly <: usize;
                          Core_models.Ops.Range.f_end
                          =
                          (i +! mk_usize 1 <: usize) *! bytes_per_poly <: usize
                        }
                        <:
                        Core_models.Ops.Range.t_Range usize ]
                      <:
                      t_Slice u8)
                    (packed <: t_Slice u8)
                  <:
                  t_Slice u8)
            in
            encoded
          else
            let (packed: t_Array u8 (mk_usize 128)):t_Array u8 (mk_usize 128) =
              simple_bit_pack (mk_usize 128) (w1.[ i ] <: t_Array i32 (mk_usize 256)) w1_max
            in
            let encoded:t_Array u8 v_W1_BYTES =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_range encoded
                ({
                    Core_models.Ops.Range.f_start = i *! bytes_per_poly <: usize;
                    Core_models.Ops.Range.f_end
                    =
                    (i +! mk_usize 1 <: usize) *! bytes_per_poly <: usize
                  }
                  <:
                  Core_models.Ops.Range.t_Range usize)
                (Core_models.Slice.impl__copy_from_slice #u8
                    (encoded.[ {
                          Core_models.Ops.Range.f_start = i *! bytes_per_poly <: usize;
                          Core_models.Ops.Range.f_end
                          =
                          (i +! mk_usize 1 <: usize) *! bytes_per_poly <: usize
                        }
                        <:
                        Core_models.Ops.Range.t_Range usize ]
                      <:
                      t_Slice u8)
                    (packed <: t_Slice u8)
                  <:
                  t_Slice u8)
            in
            encoded)
  in
  encoded

#pop-options

/// CoeffFromThreeBytes(b0, b1, b2) — Algorithm 14.
/// Returns an element of {0, 1, ..., q-1} or None (rejection).
let coeff_from_three_bytes (b0 b1 b2: u8) : Core_models.Option.t_Option i32 =
  let b2p:u8 = if b2 >. mk_u8 127 then b2 -! mk_u8 128 else b2 in
  let z:i32 =
    (((cast (b2p <: u8) <: i32) <<! mk_i32 16 <: i32) |.
      ((cast (b1 <: u8) <: i32) <<! mk_i32 8 <: i32)
      <:
      i32) |.
    (cast (b0 <: u8) <: i32)
  in
  if z <. Hacspec_ml_dsa.Parameters.v_Q
  then Core_models.Option.Option_Some z <: Core_models.Option.t_Option i32
  else Core_models.Option.Option_None <: Core_models.Option.t_Option i32

/// CoeffFromHalfByte(b, η) — Algorithm 15.
/// Returns an element of {-η, ..., η} or None (rejection).
let coeff_from_half_byte (b: u8) (eta: usize) : Core_models.Option.t_Option i32 =
  if eta =. mk_usize 2 && (cast (b <: u8) <: usize) <. mk_usize 15
  then
    Core_models.Option.Option_Some (mk_i32 2 -! (cast (b %! mk_u8 5 <: u8) <: i32))
    <:
    Core_models.Option.t_Option i32
  else
    if eta =. mk_usize 4 && (cast (b <: u8) <: usize) <. mk_usize 9
    then
      Core_models.Option.Option_Some (mk_i32 4 -! (cast (b <: u8) <: i32))
      <:
      Core_models.Option.t_Option i32
    else Core_models.Option.Option_None <: Core_models.Option.t_Option i32
