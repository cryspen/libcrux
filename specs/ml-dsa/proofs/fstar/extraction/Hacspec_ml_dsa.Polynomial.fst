module Hacspec_ml_dsa.Polynomial
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

/// Coefficient-wise addition of two polynomials.
let poly_add (a b: t_Array i32 (mk_usize 256)) : t_Array i32 (mk_usize 256) =
  Hacspec_ml_dsa.createi #i32
    (mk_usize 256)
    #(usize -> i32)
    (fun i ->
        let i:usize = i in
        Hacspec_ml_dsa.Arithmetic.mod_q ((cast (a.[ i ] <: i32) <: i64) +!
            (cast (b.[ i ] <: i32) <: i64)
            <:
            i64)
        <:
        i32)

/// Coefficient-wise subtraction of two polynomials.
let poly_sub (a b: t_Array i32 (mk_usize 256)) : t_Array i32 (mk_usize 256) =
  Hacspec_ml_dsa.createi #i32
    (mk_usize 256)
    #(usize -> i32)
    (fun i ->
        let i:usize = i in
        Hacspec_ml_dsa.Arithmetic.mod_q ((cast (a.[ i ] <: i32) <: i64) -!
            (cast (b.[ i ] <: i32) <: i64)
            <:
            i64)
        <:
        i32)

/// Coefficient-wise multiplication in NTT domain (Hadamard product).
let poly_pointwise_mul (a b: t_Array i32 (mk_usize 256)) : t_Array i32 (mk_usize 256) =
  Hacspec_ml_dsa.createi #i32
    (mk_usize 256)
    #(usize -> i32)
    (fun i ->
        let i:usize = i in
        Hacspec_ml_dsa.Arithmetic.mod_q ((cast (a.[ i ] <: i32) <: i64) *!
            (cast (b.[ i ] <: i32) <: i64)
            <:
            i64)
        <:
        i32)

/// Apply NTT to each polynomial in a vector.
let vector_ntt (v_N: usize) (v: t_Array (t_Array i32 (mk_usize 256)) v_N)
    : t_Array (t_Array i32 (mk_usize 256)) v_N =
  Hacspec_ml_dsa.createi #(t_Array i32 (mk_usize 256))
    v_N
    #(usize -> t_Array i32 (mk_usize 256))
    (fun i ->
        let i:usize = i in
        Hacspec_ml_dsa.Ntt.ntt (v.[ i ] <: t_Array i32 (mk_usize 256)) <: t_Array i32 (mk_usize 256)
    )

/// Apply INTT to each polynomial in a vector.
let vector_intt (v_N: usize) (v: t_Array (t_Array i32 (mk_usize 256)) v_N)
    : t_Array (t_Array i32 (mk_usize 256)) v_N =
  Hacspec_ml_dsa.createi #(t_Array i32 (mk_usize 256))
    v_N
    #(usize -> t_Array i32 (mk_usize 256))
    (fun i ->
        let i:usize = i in
        Hacspec_ml_dsa.Ntt.intt (v.[ i ] <: t_Array i32 (mk_usize 256))
        <:
        t_Array i32 (mk_usize 256))

/// Coefficient-wise addition of two vectors.
let vector_add (v_N: usize) (a b: t_Array (t_Array i32 (mk_usize 256)) v_N)
    : t_Array (t_Array i32 (mk_usize 256)) v_N =
  Hacspec_ml_dsa.createi #(t_Array i32 (mk_usize 256))
    v_N
    #(usize -> t_Array i32 (mk_usize 256))
    (fun i ->
        let i:usize = i in
        poly_add (a.[ i ] <: t_Array i32 (mk_usize 256)) (b.[ i ] <: t_Array i32 (mk_usize 256))
        <:
        t_Array i32 (mk_usize 256))

/// Coefficient-wise subtraction of two vectors.
let vector_sub (v_N: usize) (a b: t_Array (t_Array i32 (mk_usize 256)) v_N)
    : t_Array (t_Array i32 (mk_usize 256)) v_N =
  Hacspec_ml_dsa.createi #(t_Array i32 (mk_usize 256))
    v_N
    #(usize -> t_Array i32 (mk_usize 256))
    (fun i ->
        let i:usize = i in
        poly_sub (a.[ i ] <: t_Array i32 (mk_usize 256)) (b.[ i ] <: t_Array i32 (mk_usize 256))
        <:
        t_Array i32 (mk_usize 256))

/// Multiply a polynomial (in NTT domain) with each element of a vector (in NTT domain).
let scalar_vector_ntt
      (v_N: usize)
      (c: t_Array i32 (mk_usize 256))
      (v: t_Array (t_Array i32 (mk_usize 256)) v_N)
    : t_Array (t_Array i32 (mk_usize 256)) v_N =
  Hacspec_ml_dsa.createi #(t_Array i32 (mk_usize 256))
    v_N
    #(usize -> t_Array i32 (mk_usize 256))
    (fun i ->
        let i:usize = i in
        poly_pointwise_mul c (v.[ i ] <: t_Array i32 (mk_usize 256)) <: t_Array i32 (mk_usize 256))

/// Infinity norm of a polynomial: max |coeff| where coefficients are centered mod q.
let poly_infinity_norm (p: t_Array i32 (mk_usize 256)) : i32 =
  let max:i32 = mk_i32 0 in
  let max:i32 =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (mk_usize 256)
      (fun max temp_1_ ->
          let max:i32 = max in
          let _:usize = temp_1_ in
          true)
      max
      (fun max i ->
          let max:i32 = max in
          let i:usize = i in
          let c:i32 = Hacspec_ml_dsa.Arithmetic.coeff_norm (p.[ i ] <: i32) in
          if c >. max
          then
            let max:i32 = c in
            max
          else max)
  in
  max

/// Infinity norm of a vector: max over all polynomials.
let vector_infinity_norm (v_N: usize) (v: t_Array (t_Array i32 (mk_usize 256)) v_N) : i32 =
  let max:i32 = mk_i32 0 in
  let max:i32 =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      v_N
      (fun max temp_1_ ->
          let max:i32 = max in
          let _:usize = temp_1_ in
          true)
      max
      (fun max i ->
          let max:i32 = max in
          let i:usize = i in
          let n:i32 = poly_infinity_norm (v.[ i ] <: t_Array i32 (mk_usize 256)) in
          if n >. max
          then
            let max:i32 = n in
            max
          else max)
  in
  max

/// Apply Power2Round componentwise to a vector, returning (v1, v0).
let vector_power2round (v_N: usize) (v: t_Array (t_Array i32 (mk_usize 256)) v_N)
    : Prims.Pure
      (t_Array (t_Array i32 (mk_usize 256)) v_N & t_Array (t_Array i32 (mk_usize 256)) v_N)
      (requires
        forall i.
          i < Seq.length v ==>
          (forall j.
              j < 256 ==>
              Rust_primitives.Integers.v (Seq.index (Seq.index v i) j) >= 0 /\
              Rust_primitives.Integers.v (Seq.index (Seq.index v i) j) <
              Rust_primitives.Integers.v Hacspec_ml_dsa.Parameters.v_Q))
      (fun _ -> Prims.l_True) =
  let (v1: t_Array (t_Array i32 (mk_usize 256)) v_N):t_Array (t_Array i32 (mk_usize 256)) v_N =
    Hacspec_ml_dsa.createi #(t_Array i32 (mk_usize 256))
      v_N
      #(usize -> t_Array i32 (mk_usize 256))
      (fun i ->
          let i:usize = i in
          Hacspec_ml_dsa.createi #i32
            (mk_usize 256)
            #(usize -> i32)
            (fun j ->
                let j:usize = j in
                let (r1: i32), (_: i32) =
                  Hacspec_ml_dsa.Arithmetic.power2round ((v.[ i ] <: t_Array i32 (mk_usize 256)).[ j
                      ]
                      <:
                      i32)
                in
                r1)
          <:
          t_Array i32 (mk_usize 256))
  in
  let (v0: t_Array (t_Array i32 (mk_usize 256)) v_N):t_Array (t_Array i32 (mk_usize 256)) v_N =
    Hacspec_ml_dsa.createi #(t_Array i32 (mk_usize 256))
      v_N
      #(usize -> t_Array i32 (mk_usize 256))
      (fun i ->
          let i:usize = i in
          Hacspec_ml_dsa.createi #i32
            (mk_usize 256)
            #(usize -> i32)
            (fun j ->
                let j:usize = j in
                let (_: i32), (r0: i32) =
                  Hacspec_ml_dsa.Arithmetic.power2round ((v.[ i ] <: t_Array i32 (mk_usize 256)).[ j
                      ]
                      <:
                      i32)
                in
                r0)
          <:
          t_Array i32 (mk_usize 256))
  in
  v1, v0 <: (t_Array (t_Array i32 (mk_usize 256)) v_N & t_Array (t_Array i32 (mk_usize 256)) v_N)

/// Apply HighBits componentwise to a vector.
let vector_high_bits (v_N: usize) (v: t_Array (t_Array i32 (mk_usize 256)) v_N) (gamma2: i32)
    : Prims.Pure (t_Array (t_Array i32 (mk_usize 256)) v_N)
      (requires
        gamma2 >. mk_i32 0 /\ gamma2 <. (Hacspec_ml_dsa.Parameters.v_Q /! mk_i32 2) /\
        (forall i.
            i < Seq.length v ==>
            (forall j.
                j < 256 ==>
                Rust_primitives.Integers.v (Seq.index (Seq.index v i) j) >= 0 /\
                Rust_primitives.Integers.v (Seq.index (Seq.index v i) j) <
                Rust_primitives.Integers.v Hacspec_ml_dsa.Parameters.v_Q)))
      (fun _ -> Prims.l_True) =
  Hacspec_ml_dsa.createi #(t_Array i32 (mk_usize 256))
    v_N
    #(usize -> t_Array i32 (mk_usize 256))
    (fun i ->
        let i:usize = i in
        Hacspec_ml_dsa.createi #i32
          (mk_usize 256)
          #(usize -> i32)
          (fun j ->
              let j:usize = j in
              Hacspec_ml_dsa.Arithmetic.high_bits ((v.[ i ] <: t_Array i32 (mk_usize 256)).[ j ]
                  <:
                  i32)
                gamma2
              <:
              i32)
        <:
        t_Array i32 (mk_usize 256))

/// Apply LowBits componentwise to a vector.
let vector_low_bits (v_N: usize) (v: t_Array (t_Array i32 (mk_usize 256)) v_N) (gamma2: i32)
    : Prims.Pure (t_Array (t_Array i32 (mk_usize 256)) v_N)
      (requires
        gamma2 >. mk_i32 0 /\ gamma2 <. (Hacspec_ml_dsa.Parameters.v_Q /! mk_i32 2) /\
        (forall i.
            i < Seq.length v ==>
            (forall j.
                j < 256 ==>
                Rust_primitives.Integers.v (Seq.index (Seq.index v i) j) >= 0 /\
                Rust_primitives.Integers.v (Seq.index (Seq.index v i) j) <
                Rust_primitives.Integers.v Hacspec_ml_dsa.Parameters.v_Q)))
      (fun _ -> Prims.l_True) =
  Hacspec_ml_dsa.createi #(t_Array i32 (mk_usize 256))
    v_N
    #(usize -> t_Array i32 (mk_usize 256))
    (fun i ->
        let i:usize = i in
        Hacspec_ml_dsa.createi #i32
          (mk_usize 256)
          #(usize -> i32)
          (fun j ->
              let j:usize = j in
              Hacspec_ml_dsa.Arithmetic.low_bits ((v.[ i ] <: t_Array i32 (mk_usize 256)).[ j ]
                  <:
                  i32)
                gamma2
              <:
              i32)
        <:
        t_Array i32 (mk_usize 256))

#push-options "--z3rlimit 300"

/// Count the number of `true` entries in a hint vector.
let count_hints (v_N: usize) (h: t_Array (t_Array bool (mk_usize 256)) v_N)
    : Prims.Pure usize (requires Rust_primitives.Integers.v v_N <= 8) (fun _ -> Prims.l_True) =
  let v_total:usize = mk_usize 0 in
  let v_total:usize =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      v_N
      (fun v_total i ->
          let v_total:usize = v_total in
          let i:usize = i in
          v_total <=. (i *! mk_usize 256 <: usize) <: bool)
      v_total
      (fun v_total i ->
          let v_total:usize = v_total in
          let i:usize = i in
          Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
            (mk_usize 256)
            (fun v_total j ->
                let v_total:usize = v_total in
                let j:usize = j in
                v_total <=. ((i *! mk_usize 256 <: usize) +! j <: usize) <: bool)
            v_total
            (fun v_total j ->
                let v_total:usize = v_total in
                let j:usize = j in
                if (h.[ i ] <: t_Array bool (mk_usize 256)).[ j ] <: bool
                then
                  let v_total:usize = v_total +! mk_usize 1 in
                  v_total
                else v_total)
          <:
          usize)
  in
  v_total

#pop-options

/// Apply MakeHint componentwise to two vectors, returning hint vector and count of ones.
let vector_make_hint (v_N: usize) (z r: t_Array (t_Array i32 (mk_usize 256)) v_N) (gamma2: i32)
    : Prims.Pure (t_Array (t_Array bool (mk_usize 256)) v_N & usize)
      (requires
        Rust_primitives.Integers.v v_N <= 8 /\ gamma2 >. mk_i32 0 /\
        gamma2 <. (Hacspec_ml_dsa.Parameters.v_Q /! mk_i32 2) /\
        (forall i.
            i < Seq.length r ==>
            (forall j.
                j < 256 ==>
                Rust_primitives.Integers.v (Seq.index (Seq.index r i) j) >= 0 /\
                Rust_primitives.Integers.v (Seq.index (Seq.index r i) j) <
                Rust_primitives.Integers.v Hacspec_ml_dsa.Parameters.v_Q)))
      (fun _ -> Prims.l_True) =
  let (h: t_Array (t_Array bool (mk_usize 256)) v_N):t_Array (t_Array bool (mk_usize 256)) v_N =
    Hacspec_ml_dsa.createi #(t_Array bool (mk_usize 256))
      v_N
      #(usize -> t_Array bool (mk_usize 256))
      (fun i ->
          let i:usize = i in
          Hacspec_ml_dsa.createi #bool
            (mk_usize 256)
            #(usize -> bool)
            (fun j ->
                let j:usize = j in
                Hacspec_ml_dsa.Arithmetic.make_hint ((z.[ i ] <: t_Array i32 (mk_usize 256)).[ j ]
                    <:
                    i32)
                  ((r.[ i ] <: t_Array i32 (mk_usize 256)).[ j ] <: i32)
                  gamma2
                <:
                bool)
          <:
          t_Array bool (mk_usize 256))
  in
  let count:usize = count_hints v_N h in
  h, count <: (t_Array (t_Array bool (mk_usize 256)) v_N & usize)

/// Apply UseHint componentwise to a hint vector and a polynomial vector.
let vector_use_hint
      (v_N: usize)
      (h: t_Array (t_Array bool (mk_usize 256)) v_N)
      (r: t_Array (t_Array i32 (mk_usize 256)) v_N)
      (gamma2: i32)
    : Prims.Pure (t_Array (t_Array i32 (mk_usize 256)) v_N)
      (requires
        gamma2 >. mk_i32 0 /\ gamma2 <. (Hacspec_ml_dsa.Parameters.v_Q /! mk_i32 2) /\
        (forall i.
            i < Seq.length r ==>
            (forall j.
                j < 256 ==>
                Rust_primitives.Integers.v (Seq.index (Seq.index r i) j) >= 0 /\
                Rust_primitives.Integers.v (Seq.index (Seq.index r i) j) <
                Rust_primitives.Integers.v Hacspec_ml_dsa.Parameters.v_Q)))
      (fun _ -> Prims.l_True) =
  Hacspec_ml_dsa.createi #(t_Array i32 (mk_usize 256))
    v_N
    #(usize -> t_Array i32 (mk_usize 256))
    (fun i ->
        let i:usize = i in
        Hacspec_ml_dsa.createi #i32
          (mk_usize 256)
          #(usize -> i32)
          (fun j ->
              let j:usize = j in
              Hacspec_ml_dsa.Arithmetic.uuse_hint ((h.[ i ] <: t_Array bool (mk_usize 256)).[ j ]
                  <:
                  bool)
                ((r.[ i ] <: t_Array i32 (mk_usize 256)).[ j ] <: i32)
                gamma2
              <:
              i32)
        <:
        t_Array i32 (mk_usize 256))

#push-options "--z3rlimit 150"

/// Reduce each coefficient modulo q to [0, q-1].
let poly_reduce (p: t_Array i32 (mk_usize 256)) : t_Array i32 (mk_usize 256) =
  Hacspec_ml_dsa.createi #i32
    (mk_usize 256)
    #(usize -> i32)
    (fun i ->
        let i:usize = i in
        let r:i64 =
          (((cast (p.[ i ] <: i32) <: i64) %! (cast (Hacspec_ml_dsa.Parameters.v_Q <: i32) <: i64)
              <:
              i64) +!
            (cast (Hacspec_ml_dsa.Parameters.v_Q <: i32) <: i64)
            <:
            i64) %!
          (cast (Hacspec_ml_dsa.Parameters.v_Q <: i32) <: i64)
        in
        cast (r <: i64) <: i32)

#pop-options

#push-options "--z3rlimit 150"

/// Reduce each coefficient to centered representative in [-(q-1)/2, (q-1)/2].
let poly_mod_pm (p: t_Array i32 (mk_usize 256)) : t_Array i32 (mk_usize 256) =
  Hacspec_ml_dsa.createi #i32
    (mk_usize 256)
    #(usize -> i32)
    (fun i ->
        let i:usize = i in
        let r:i64 =
          (((cast (p.[ i ] <: i32) <: i64) %! (cast (Hacspec_ml_dsa.Parameters.v_Q <: i32) <: i64)
              <:
              i64) +!
            (cast (Hacspec_ml_dsa.Parameters.v_Q <: i32) <: i64)
            <:
            i64) %!
          (cast (Hacspec_ml_dsa.Parameters.v_Q <: i32) <: i64)
        in
        let r:i32 = cast (r <: i64) <: i32 in
        if r >. (Hacspec_ml_dsa.Parameters.v_Q /! mk_i32 2 <: i32)
        then r -! Hacspec_ml_dsa.Parameters.v_Q
        else r)

#pop-options
