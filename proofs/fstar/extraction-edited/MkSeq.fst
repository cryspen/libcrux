module MkSeq
open Core

open FStar.Tactics.V2

private let init (len: nat) (f: (i:nat{i < len}) -> Tac 'a): Tac (list 'a)
  = let rec h (i: nat {i <= len}): Tac (list 'a)
     = if i = len then [] else f i :: h (i + 1)
    in h 0

private let tuple_proj (n: nat) (i: nat): Tac term
  = if n = 1 then `(id) else
    let name = "__proj__Mktuple" ^ string_of_int n ^ "__item___" ^ string_of_int (i + 1) in
    Tv_FVar (pack_fv ["FStar";"Pervasives";"Native";name])

private let tuple_type (n: nat): Tac term
  = if n = 1 then `(id) else
    let name = "tuple" ^ string_of_int n in
    Tv_FVar (pack_fv ["FStar";"Pervasives";"Native";name])

open Rust_primitives.Integers
open Libcrux.Kem.Kyber.Arithmetic

// let create4 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10: 'a)
//   : Pure 
//     (t_Array 'a (sz 11))
//     (requires True)
//     (ensures fun (r: t_Array 'a (sz 11)) -> 
//       r.[sz 0] == x0 /\
//       r.[sz 1] == x1 /\
//       r.[sz 2] == x2 /\
//       r.[sz 3] == x3 /\
//       r.[sz 4] == x4 /\
//       r.[sz 5] == x5 /\
//       r.[sz 6] == x6 /\
//       r.[sz 7] == x7 /\
//       True
//       )
//   = Libcrux.Kem.Kyber.Arithmetic.createi
//     (sz 11) 
//     (fun x -> match v x with
//       | 0 -> x0
//       | 1 -> x1
//       | 2 -> x2
//       | 3 -> x3
//       | 4 -> x4
//       | 5 -> x5
//       | 6 -> x6
//       | 7 -> x7
//       | 8 -> x8
//       | 9 -> x9
//       | 10 -> x10
//       )

private let create_gen_tac (n: nat): Tac sigelt
  = let typ_bd = {fresh_binder_named "t" (`Type0) with qual = FStar.Reflection.V2.Q_Implicit} in
    let typ = binder_to_term typ_bd in
    let input_typ = mk_e_app (tuple_type n) (init n (fun _ -> typ)) in
    let input_bd = fresh_binder_named "tup" input_typ in
    let output_type = `t_Array (`#typ) (sz (`@n)) in
    let nth i = `((`#(tuple_proj n i)) (`#input_bd)) in
    let mk_and: term -> term -> Tac term = fun t u -> `(`#t /\ `#u) in
    let post =
      let mk_inv s i = `(Seq.index (`#s) (`@i) == (`#(tuple_proj n i)) (`#input_bd)) in
      let invs s = Tactics.fold_left mk_and (`(Seq.length (`#s) == (`@n))) (init n (mk_inv s)) in
      let bd = fresh_binder_named "s" output_type in
      mk_abs [bd] (invs bd)
    in
    let comp = C_Eff [] ["Prims"; "Pure"]
      (`t_Array (`#typ) (sz (`@n)))
      [ (`(requires True), Q_Explicit); (post, Q_Explicit)] []
    in
    let args = [typ_bd; input_bd] in
    let l = Tactics.fold_right (fun hd tl -> `((`#hd)::(`#tl))) (init n nth) (`[]) in
    let indexes =
      let f i = `((`#(nth i)) == List.Tot.index (`#l) (`@i)) in
      Tactics.fold_left mk_and (`True) (init n f)
    in
    let lb_def = mk_abs args (`(
      let l = `#l in
      let s = Seq.createL l <: t_Array (`#typ) (sz (`@n)) in
      FStar.Classical.forall_intro (Seq.lemma_index_is_nth s);
      assert (`#indexes) by (Tactics.norm [primops; iota; delta; zeta]);
      s
    )) in
    let lb_typ = mk_arr args (pack_comp comp) in
    let open FStar.List.Tot in
    let lb_fv = pack_fv (cur_module () @ ["create" ^ string_of_int n]) in
    Sg_Let { isrec = false; lbs = [{ lb_fv; lb_us = []; lb_typ; lb_def }] }

%splice[] (init 13 (fun i -> create_gen_tac (i + 1)))
