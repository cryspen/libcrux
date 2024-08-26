module Tactics.MachineInts

open FStar.Tactics.V2
open FStar.Tactics.V2.SyntaxHelpers
open FStar.Class.Printable
open FStar.Option

open Tactics.Utils
module RI = Rust_primitives.Integers

/// The size of a machine int.
type size = 
  | PtrSize
  | Size of n:nat {match n with | 8 | 16 | 32 | 64 | 128 -> true | _ -> false}
type signedness = | Signed | Unsigned

type machine_int_op = | MkInt | V

noeq type machine_int_term =
  | Op { op: machine_int_op; native: bool; size: size; signedness: signedness; contents: machine_int_term }
  | Lit of int
  | Term of term

let x = `%FStar.UInt8.uint_to_t

/// Expect `n` to be a definition in a machine int namespace
let expect_native_machine_int_ns (n: string): (option (signedness & size & string))
  = match explode_qn n with
  | "FStar"::int_module::[def_name] ->
    let? (sign, size) = match int_module with
    | "Int8"  -> Some (Signed, Size 8)
    | "Int16" -> Some (Signed, Size 16)
    | "Int32" -> Some (Signed, Size 32)
    | "Int64" -> Some (Signed, Size 64)
    | "Int128" -> Some (Signed, Size 128)
    | "UInt8"  -> Some (Unsigned, Size 8)
    | "UInt16" -> Some (Unsigned, Size 16)
    | "UInt32" -> Some (Unsigned, Size 32)
    | "UInt64" -> Some (Unsigned, Size 64)
    | "UInt18" -> Some (Unsigned, Size 128)
    | _ -> None
    in Some (sign, size, def_name)
  | _ -> None

let mk_native_machine_int_ns (sign: signedness) (size: size): option (list string)
  = let sign = match sign with | Signed -> "" | Unsigned -> "U" in
    let? size = match size with | PtrSize -> None | Size n -> Some (string_of_int n) in
    Some ["FStar"; sign ^ "Int" ^ size]

let expect_inttype t: Tac (option (signedness & size))
  = let t = norm_term [iota; reify_; delta_namespace ["Rust_primitives.Integers"; "Lib.IntTypes"]; primops; unmeta] t in
    let?# t = expect_fvar t in
    match t with
    | `%RI.i8_inttype   | `%Lib.IntTypes.S8   -> Some (  Signed, Size 8)
    | `%RI.i16_inttype  | `%Lib.IntTypes.S16  -> Some (  Signed, Size 16)
    | `%RI.i32_inttype  | `%Lib.IntTypes.S32  -> Some (  Signed, Size 32)
    | `%RI.i64_inttype  | `%Lib.IntTypes.S64  -> Some (  Signed, Size 64)
    | `%RI.i128_inttype | `%Lib.IntTypes.S128 -> Some (  Signed, Size 128)
    | `%RI.u8_inttype   | `%Lib.IntTypes.U8   -> Some (Unsigned, Size 8)
    | `%RI.u16_inttype  | `%Lib.IntTypes.U16  -> Some (Unsigned, Size 16)
    | `%RI.u32_inttype  | `%Lib.IntTypes.U32  -> Some (Unsigned, Size 32)
    | `%RI.u64_inttype  | `%Lib.IntTypes.U64  -> Some (Unsigned, Size 64)
    | `%RI.u128_inttype | `%Lib.IntTypes.U128 -> Some (Unsigned, Size 128)
    | `%RI.isize_inttype -> Some (Signed, PtrSize)
    | `%RI.usize_inttype -> Some (Unsigned, PtrSize)
    | _ -> None

let mk_inttype_name (sign: signedness) (size: size): name =
  let sign = match sign with | Signed -> "i" | Unsigned -> "u" in
  let size = match size with | PtrSize -> "size" | Size n -> string_of_int n in
  ["Rust_primitives"; "Integers"; sign ^ size ^ "_inttype"]

let mk_inttype (sign: signedness) (size: size): Tac term =
  pack (Tv_FVar (pack_fv (mk_inttype_name sign size)))

let rec term_to_machine_int_term'' (t: term): Tac (option machine_int_term) =
  let t = norm_term [delta_only [(`%RI.sz); (`%RI.isz)]] t in
  match t with
  | Tv_Const (C_Int n) -> Some (Lit n)
  | _ ->
    let?# (hd, args) = collect_app_hd t in
    match expect_native_machine_int_ns hd, args with
    | (Some (signedness, size, def_name), [arg, _]) -> begin
      let native = true in
      let contents = term_to_machine_int_term' arg in
      let?# op = match def_name with
      | "__uint_to_t" | "__int_to_t" | "uint_to_t" | "int_to_t" -> Some MkInt
      | "v" -> Some V | _   -> None in
      Some (Op {op; native; size; signedness; contents})
      end
    | (None, [inttype, _; contents, _]) -> begin
      let?# (signedness, size) = expect_inttype inttype in
      let contents = term_to_machine_int_term' contents in
      let?# op = match hd with | `%RI.mk_int -> Some MkInt
                               | `%RI.v      -> Some V
                               | _ -> None in
      Some (Op {op; native = false; size; signedness; contents})
      end
    | _ -> None

and term_to_machine_int_term' (t: term): Tac machine_int_term =
  match term_to_machine_int_term'' t with | Some t -> t | None -> Term t

let term_to_machine_int_term (t: term): Tac (option (t: machine_int_term {~(Term? t)}))
  = match term_to_machine_int_term' t with
  | Term _ -> None | t -> Some t

let rec machine_int_term_to_term (t: machine_int_term): Tac (option term) =
  match t with
  | Term t -> Some t
  | Op {native = false; op; size; signedness; contents} -> 
    let inttype = mk_inttype signedness size in
    let?# contents = machine_int_term_to_term contents in
    let op = match op with | V -> `RI.v
                           | MkInt -> `RI.mk_int in
    Some (`((`#op) #(`#inttype) (`#contents)))
  | Op {native = true; op; size; signedness; contents} -> 
    let?# ns = mk_native_machine_int_ns signedness size in
    let f = FStar.List.Tot.append ns [
      match op with
      | MkInt -> (match signedness with | Signed -> "" | Unsigned -> "u") ^ "int_to_t"
      | V     -> "v"
    ] in
    let f = pack (Tv_FVar (pack_fv f)) in
    let?# contents = machine_int_term_to_term contents in
    Some (mk_e_app f [contents])
  | Lit n -> Some (pack (Tv_Const (C_Int n)))

type operation = machine_int_term -> option machine_int_term

/// Removes `mk_int (v ...)` or `v (mk_int ...)` when it's the same type
let rec flatten_machine_int_term: operation = function
  | Op x -> begin match x.contents with
           | Op y -> if x.op <> y.op && x.size = y.size && x.signedness = y.signedness 
                    then Some (match flatten_machine_int_term y.contents with
                       | Some result -> result
                       | None        -> y.contents)
                    else let? y = flatten_machine_int_term (Op y) in
                         Some (Op {x with contents = y})
           | _ -> None
           end
  | _ -> None

let rec change_native_machine_int_term (native: bool): operation = function
  | Op x -> let contents = change_native_machine_int_term native x.contents in
           if x.native = native
           then None
           else Some (Op { x with native
                                ; contents = match contents with
                                           | Some contents ->   contents
                                           | None          -> x.contents})
  | _ -> None

let combine: operation -> operation -> operation =
  fun f g t -> match f t with 
          | Some t -> (match g t with | Some t -> Some t | None -> Some t)
          | None   -> g t

/// We call `x` a normal machine integer if `x` has no `mk_int (v
/// ...)` or `v (mk_int ...)` sequence and if all `mk_int` and `v` are
/// native (aka `FStar.[U]Int*.*`, not
/// `Rust_primitives.Integer.*`). Note `usize` is an exception,
/// `mk_int` and `v` alone one usizes (and isizes) cannot be reduced
/// further.
let norm_machine_int_term = combine flatten_machine_int_term (change_native_machine_int_term true)

/// We call `x` a normal generic machine integer if `x` has no
/// `FStar.[U]Int*.[u]int_to_t/v`, and no `mk_int (v ...)` or `v
/// (mk_int ...)`.
let norm_generic_machine_int_term = combine flatten_machine_int_term (change_native_machine_int_term false)

let rw_v_mk_int_usize x
  : Lemma (eq2 (RI.v #RI.usize_inttype (RI.mk_int #RI.usize_inttype x)) x) = ()
let rw_mk_int_v_usize x
  : Lemma (eq2 (RI.mk_int #RI.usize_inttype (RI.v #RI.usize_inttype x)) x) = ()

/// Unfolds `mk_int` using `mk_int_equiv_lemma`
let norm_mk_int () =
  let?# (lhs, _) = expect_lhs_eq_uvar () in
  let lhs' = term_to_machine_int_term lhs in
  match?# lhs' with
  | Op {op = MkInt; native = false; size; signedness; contents} -> 
     let inttype = mk_inttype signedness size in
     let lemma = `(RI.mk_int_equiv_lemma #(`#inttype)) in
     let lemma = norm_term [primops; iota; delta; zeta] lemma in
     focus (fun _ -> 
       apply_lemma_rw lemma
       // iterAllSMT (fun () -> smt_sync `or_else` (fun _ -> dump "norm_mk_int: Could not solve SMT here"))
     );
     Some ()
  | _ -> None

/// Rewrites `goal_lhs` into `machine_int`. This function expects the
/// goal to be of the shape `<goal_lhs> == (?...)`, where `<goal_lhs>`
/// is a machine int. Do not call this function directly.
let _rewrite_to (goal_lhs: term) (eq_type: typ) (machine_int: machine_int_term): Tac (option unit)
  = let?# t_term = machine_int_term_to_term machine_int in
    Some (focus (fun _ ->
      let rw = tcut (`squash (eq2 #(`#eq_type) (`#goal_lhs) (`#t_term))) in
      // This tcut will generate simple verification conditions, we
      // discharge them right away
      // iterAllSMT (fun () -> smt_sync `or_else` (fun _ -> dump "norm_mk_int: Could not solve SMT here"));
      flip ();
      pointwise' (fun () -> match norm_mk_int () with 
                      | Some _ -> ()
                      | None   -> // special case for usize
                        (fun () ->           (fun () -> apply_lemma_rw (`rw_v_mk_int_usize))
                                `or_else` (fun () -> apply_lemma_rw (`rw_mk_int_v_usize)))
                        `or_else` trefl
                );
      compute ();
      trefl ();
      apply_lemma_rw rw
    ))

let transform (f: machine_int_term -> option machine_int_term): Tac unit
  = pointwise' (fun _ ->
      match revert_if_none (fun _ -> 
              let?# (lhs, eq_type) = expect_lhs_eq_uvar () in
              let?# machine_int = term_to_machine_int_term lhs in
              let?# machine_int' = f machine_int in
              let?# _ = _rewrite_to lhs eq_type machine_int' in
              Some ()
            )
      with
      | None -> trefl ()
      | _ -> ()
    )

open Rust_primitives.Integers
let _ = fun x -> assert (v (mk_int #usize_inttype x) == x) 
                by (transform norm_machine_int_term; trefl ())
let _ =       assert (mk_int #u8_inttype 3 == 3uy) 
                by (transform norm_machine_int_term; trefl ())
let _ = fun x -> assert (mk_int #u8_inttype x == FStar.UInt8.uint_to_t x)
                by (transform norm_machine_int_term)
let _ = assert (v (mk_int #usize_inttype 3) == 3) 
                by (transform norm_machine_int_term; trefl ())
let _ = fun x -> assert (v (mk_int #usize_inttype x) == x) 
                by (transform norm_machine_int_term; trefl ())
let _ =       assert (mk_int #u8_inttype 3 == 3uy)
                by (transform norm_generic_machine_int_term; trefl ())
let _ = fun x -> assert (mk_int #u8_inttype x == FStar.UInt8.uint_to_t x)
                by (transform norm_generic_machine_int_term; trefl ())
