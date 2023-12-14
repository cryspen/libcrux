module MkSeq
open Core
let mk_seq1 (v0: 'a): Pure (t_Array 'a (sz 1)) (requires True) 
  (ensures fun s -> Seq.length s == 1 /\ Seq.index s 0 == v0)
  = let l = [v0] in
    let s = Seq.createL l in
    assert (Seq.seq_to_list s == l ==> (
                 Seq.length s == 1 /\ Seq.index s 0 == v0
           )) by (Tactics.norm [primops; iota; delta; zeta]);
    s
    
unfold let mk_seq_tup1 (v0) = mk_seq1 v0

let mk_seq2 (v0 v1: 'a): Pure (t_Array 'a (sz 2)) (requires True) 
  (ensures fun s -> Seq.length s == 2 /\ Seq.index s 0 == v0/\Seq.index s 1 == v1)
  = let l = [v0;v1] in
    let s = Seq.createL l in
    assert (Seq.seq_to_list s == l ==> (
                 Seq.length s == 2 /\ Seq.index s 0 == v0/\Seq.index s 1 == v1
           )) by (Tactics.norm [primops; iota; delta; zeta]);
    s
    
unfold let mk_seq_tup2 (v0, v1) = mk_seq2 v0 v1

let mk_seq3 (v0 v1 v2: 'a): Pure (t_Array 'a (sz 3)) (requires True) 
  (ensures fun s -> Seq.length s == 3 /\ Seq.index s 0 == v0/\Seq.index s 1 == v1/\Seq.index s 2 == v2)
  = let l = [v0;v1;v2] in
    let s = Seq.createL l in
    assert (Seq.seq_to_list s == l ==> (
                 Seq.length s == 3 /\ Seq.index s 0 == v0/\Seq.index s 1 == v1/\Seq.index s 2 == v2
           )) by (Tactics.norm [primops; iota; delta; zeta]);
    s
    
unfold let mk_seq_tup3 (v0, v1, v2) = mk_seq3 v0 v1 v2

let mk_seq4 (v0 v1 v2 v3: 'a): Pure (t_Array 'a (sz 4)) (requires True) 
  (ensures fun s -> Seq.length s == 4 /\ Seq.index s 0 == v0/\Seq.index s 1 == v1/\Seq.index s 2 == v2/\Seq.index s 3 == v3)
  = let l = [v0;v1;v2;v3] in
    let s = Seq.createL l in
    assert (Seq.seq_to_list s == l ==> (
                 Seq.length s == 4 /\ Seq.index s 0 == v0/\Seq.index s 1 == v1/\Seq.index s 2 == v2/\Seq.index s 3 == v3
           )) by (Tactics.norm [primops; iota; delta; zeta]);
    s
    
unfold let mk_seq_tup4 (v0, v1, v2, v3) = mk_seq4 v0 v1 v2 v3

let mk_seq5 (v0 v1 v2 v3 v4: 'a): Pure (t_Array 'a (sz 5)) (requires True) 
  (ensures fun s -> Seq.length s == 5 /\ Seq.index s 0 == v0/\Seq.index s 1 == v1/\Seq.index s 2 == v2/\Seq.index s 3 == v3/\Seq.index s 4 == v4)
  = let l = [v0;v1;v2;v3;v4] in
    let s = Seq.createL l in
    assert (Seq.seq_to_list s == l ==> (
                 Seq.length s == 5 /\ Seq.index s 0 == v0/\Seq.index s 1 == v1/\Seq.index s 2 == v2/\Seq.index s 3 == v3/\Seq.index s 4 == v4
           )) by (Tactics.norm [primops; iota; delta; zeta]);
    s
    
unfold let mk_seq_tup5 (v0, v1, v2, v3, v4) = mk_seq5 v0 v1 v2 v3 v4

let mk_seq6 (v0 v1 v2 v3 v4 v5: 'a): Pure (t_Array 'a (sz 6)) (requires True) 
  (ensures fun s -> Seq.length s == 6 /\ Seq.index s 0 == v0/\Seq.index s 1 == v1/\Seq.index s 2 == v2/\Seq.index s 3 == v3/\Seq.index s 4 == v4/\Seq.index s 5 == v5)
  = let l = [v0;v1;v2;v3;v4;v5] in
    let s = Seq.createL l in
    assert (Seq.seq_to_list s == l ==> (
                 Seq.length s == 6 /\ Seq.index s 0 == v0/\Seq.index s 1 == v1/\Seq.index s 2 == v2/\Seq.index s 3 == v3/\Seq.index s 4 == v4/\Seq.index s 5 == v5
           )) by (Tactics.norm [primops; iota; delta; zeta]);
    s
    
unfold let mk_seq_tup6 (v0, v1, v2, v3, v4, v5) = mk_seq6 v0 v1 v2 v3 v4 v5

let mk_seq7 (v0 v1 v2 v3 v4 v5 v6: 'a): Pure (t_Array 'a (sz 7)) (requires True) 
  (ensures fun s -> Seq.length s == 7 /\ Seq.index s 0 == v0/\Seq.index s 1 == v1/\Seq.index s 2 == v2/\Seq.index s 3 == v3/\Seq.index s 4 == v4/\Seq.index s 5 == v5/\Seq.index s 6 == v6)
  = let l = [v0;v1;v2;v3;v4;v5;v6] in
    let s = Seq.createL l in
    assert (Seq.seq_to_list s == l ==> (
                 Seq.length s == 7 /\ Seq.index s 0 == v0/\Seq.index s 1 == v1/\Seq.index s 2 == v2/\Seq.index s 3 == v3/\Seq.index s 4 == v4/\Seq.index s 5 == v5/\Seq.index s 6 == v6
           )) by (Tactics.norm [primops; iota; delta; zeta]);
    s
    
unfold let mk_seq_tup7 (v0, v1, v2, v3, v4, v5, v6) = mk_seq7 v0 v1 v2 v3 v4 v5 v6

let mk_seq8 (v0 v1 v2 v3 v4 v5 v6 v7: 'a): Pure (t_Array 'a (sz 8)) (requires True) 
  (ensures fun s -> Seq.length s == 8 /\ Seq.index s 0 == v0/\Seq.index s 1 == v1/\Seq.index s 2 == v2/\Seq.index s 3 == v3/\Seq.index s 4 == v4/\Seq.index s 5 == v5/\Seq.index s 6 == v6/\Seq.index s 7 == v7)
  = let l = [v0;v1;v2;v3;v4;v5;v6;v7] in
    let s = Seq.createL l in
    assert (Seq.seq_to_list s == l ==> (
                 Seq.length s == 8 /\ Seq.index s 0 == v0/\Seq.index s 1 == v1/\Seq.index s 2 == v2/\Seq.index s 3 == v3/\Seq.index s 4 == v4/\Seq.index s 5 == v5/\Seq.index s 6 == v6/\Seq.index s 7 == v7
           )) by (Tactics.norm [primops; iota; delta; zeta]);
    s
    
unfold let mk_seq_tup8 (v0, v1, v2, v3, v4, v5, v6, v7) = mk_seq8 v0 v1 v2 v3 v4 v5 v6 v7

let mk_seq9 (v0 v1 v2 v3 v4 v5 v6 v7 v8: 'a): Pure (t_Array 'a (sz 9)) (requires True) 
  (ensures fun s -> Seq.length s == 9 /\ Seq.index s 0 == v0/\Seq.index s 1 == v1/\Seq.index s 2 == v2/\Seq.index s 3 == v3/\Seq.index s 4 == v4/\Seq.index s 5 == v5/\Seq.index s 6 == v6/\Seq.index s 7 == v7/\Seq.index s 8 == v8)
  = let l = [v0;v1;v2;v3;v4;v5;v6;v7;v8] in
    let s = Seq.createL l in
    assert (Seq.seq_to_list s == l ==> (
                 Seq.length s == 9 /\ Seq.index s 0 == v0/\Seq.index s 1 == v1/\Seq.index s 2 == v2/\Seq.index s 3 == v3/\Seq.index s 4 == v4/\Seq.index s 5 == v5/\Seq.index s 6 == v6/\Seq.index s 7 == v7/\Seq.index s 8 == v8
           )) by (Tactics.norm [primops; iota; delta; zeta]);
    s
    
unfold let mk_seq_tup9 (v0, v1, v2, v3, v4, v5, v6, v7, v8) = mk_seq9 v0 v1 v2 v3 v4 v5 v6 v7 v8

let mk_seq10 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9: 'a): Pure (t_Array 'a (sz 10)) (requires True) 
  (ensures fun s -> Seq.length s == 10 /\ Seq.index s 0 == v0/\Seq.index s 1 == v1/\Seq.index s 2 == v2/\Seq.index s 3 == v3/\Seq.index s 4 == v4/\Seq.index s 5 == v5/\Seq.index s 6 == v6/\Seq.index s 7 == v7/\Seq.index s 8 == v8/\Seq.index s 9 == v9)
  = let l = [v0;v1;v2;v3;v4;v5;v6;v7;v8;v9] in
    let s = Seq.createL l in
    assert (Seq.seq_to_list s == l ==> (
                 Seq.length s == 10 /\ Seq.index s 0 == v0/\Seq.index s 1 == v1/\Seq.index s 2 == v2/\Seq.index s 3 == v3/\Seq.index s 4 == v4/\Seq.index s 5 == v5/\Seq.index s 6 == v6/\Seq.index s 7 == v7/\Seq.index s 8 == v8/\Seq.index s 9 == v9
           )) by (Tactics.norm [primops; iota; delta; zeta]);
    s
    
unfold let mk_seq_tup10 (v0, v1, v2, v3, v4, v5, v6, v7, v8, v9) = mk_seq10 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9

let mk_seq11 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10: 'a): Pure (t_Array 'a (sz 11)) (requires True) 
  (ensures fun s -> Seq.length s == 11 /\ Seq.index s 0 == v0/\Seq.index s 1 == v1/\Seq.index s 2 == v2/\Seq.index s 3 == v3/\Seq.index s 4 == v4/\Seq.index s 5 == v5/\Seq.index s 6 == v6/\Seq.index s 7 == v7/\Seq.index s 8 == v8/\Seq.index s 9 == v9/\Seq.index s 10 == v10)
  = let l = [v0;v1;v2;v3;v4;v5;v6;v7;v8;v9;v10] in
    let s = Seq.createL l in
    assert (Seq.seq_to_list s == l ==> (
                 Seq.length s == 11 /\ Seq.index s 0 == v0/\Seq.index s 1 == v1/\Seq.index s 2 == v2/\Seq.index s 3 == v3/\Seq.index s 4 == v4/\Seq.index s 5 == v5/\Seq.index s 6 == v6/\Seq.index s 7 == v7/\Seq.index s 8 == v8/\Seq.index s 9 == v9/\Seq.index s 10 == v10
           )) by (Tactics.norm [primops; iota; delta; zeta]);
    s
    
unfold let mk_seq_tup11 (v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10) = mk_seq11 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10

let mk_seq12 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11: 'a): Pure (t_Array 'a (sz 12)) (requires True) 
  (ensures fun s -> Seq.length s == 12 /\ Seq.index s 0 == v0/\Seq.index s 1 == v1/\Seq.index s 2 == v2/\Seq.index s 3 == v3/\Seq.index s 4 == v4/\Seq.index s 5 == v5/\Seq.index s 6 == v6/\Seq.index s 7 == v7/\Seq.index s 8 == v8/\Seq.index s 9 == v9/\Seq.index s 10 == v10/\Seq.index s 11 == v11)
  = let l = [v0;v1;v2;v3;v4;v5;v6;v7;v8;v9;v10;v11] in
    let s = Seq.createL l in
    assert (Seq.seq_to_list s == l ==> (
                 Seq.length s == 12 /\ Seq.index s 0 == v0/\Seq.index s 1 == v1/\Seq.index s 2 == v2/\Seq.index s 3 == v3/\Seq.index s 4 == v4/\Seq.index s 5 == v5/\Seq.index s 6 == v6/\Seq.index s 7 == v7/\Seq.index s 8 == v8/\Seq.index s 9 == v9/\Seq.index s 10 == v10/\Seq.index s 11 == v11
           )) by (Tactics.norm [primops; iota; delta; zeta]);
    s
    
unfold let mk_seq_tup12 (v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11) = mk_seq12 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11

let mk_seq13 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12: 'a): Pure (t_Array 'a (sz 13)) (requires True) 
  (ensures fun s -> Seq.length s == 13 /\ Seq.index s 0 == v0/\Seq.index s 1 == v1/\Seq.index s 2 == v2/\Seq.index s 3 == v3/\Seq.index s 4 == v4/\Seq.index s 5 == v5/\Seq.index s 6 == v6/\Seq.index s 7 == v7/\Seq.index s 8 == v8/\Seq.index s 9 == v9/\Seq.index s 10 == v10/\Seq.index s 11 == v11/\Seq.index s 12 == v12)
  = let l = [v0;v1;v2;v3;v4;v5;v6;v7;v8;v9;v10;v11;v12] in
    let s = Seq.createL l in
    assert (Seq.seq_to_list s == l ==> (
                 Seq.length s == 13 /\ Seq.index s 0 == v0/\Seq.index s 1 == v1/\Seq.index s 2 == v2/\Seq.index s 3 == v3/\Seq.index s 4 == v4/\Seq.index s 5 == v5/\Seq.index s 6 == v6/\Seq.index s 7 == v7/\Seq.index s 8 == v8/\Seq.index s 9 == v9/\Seq.index s 10 == v10/\Seq.index s 11 == v11/\Seq.index s 12 == v12
           )) by (Tactics.norm [primops; iota; delta; zeta]);
    s
    
unfold let mk_seq_tup13 (v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12) = mk_seq13 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12

let mk_seq14 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13: 'a): Pure (t_Array 'a (sz 14)) (requires True) 
  (ensures fun s -> Seq.length s == 14 /\ Seq.index s 0 == v0/\Seq.index s 1 == v1/\Seq.index s 2 == v2/\Seq.index s 3 == v3/\Seq.index s 4 == v4/\Seq.index s 5 == v5/\Seq.index s 6 == v6/\Seq.index s 7 == v7/\Seq.index s 8 == v8/\Seq.index s 9 == v9/\Seq.index s 10 == v10/\Seq.index s 11 == v11/\Seq.index s 12 == v12/\Seq.index s 13 == v13)
  = let l = [v0;v1;v2;v3;v4;v5;v6;v7;v8;v9;v10;v11;v12;v13] in
    let s = Seq.createL l in
    assert (Seq.seq_to_list s == l ==> (
                 Seq.length s == 14 /\ Seq.index s 0 == v0/\Seq.index s 1 == v1/\Seq.index s 2 == v2/\Seq.index s 3 == v3/\Seq.index s 4 == v4/\Seq.index s 5 == v5/\Seq.index s 6 == v6/\Seq.index s 7 == v7/\Seq.index s 8 == v8/\Seq.index s 9 == v9/\Seq.index s 10 == v10/\Seq.index s 11 == v11/\Seq.index s 12 == v12/\Seq.index s 13 == v13
           )) by (Tactics.norm [primops; iota; delta; zeta]);
    s
    
unfold let mk_seq_tup14 (v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13) = mk_seq14 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13

let mk_seq15 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14: 'a): Pure (t_Array 'a (sz 15)) (requires True) 
  (ensures fun s -> Seq.length s == 15 /\ Seq.index s 0 == v0/\Seq.index s 1 == v1/\Seq.index s 2 == v2/\Seq.index s 3 == v3/\Seq.index s 4 == v4/\Seq.index s 5 == v5/\Seq.index s 6 == v6/\Seq.index s 7 == v7/\Seq.index s 8 == v8/\Seq.index s 9 == v9/\Seq.index s 10 == v10/\Seq.index s 11 == v11/\Seq.index s 12 == v12/\Seq.index s 13 == v13/\Seq.index s 14 == v14)
  = let l = [v0;v1;v2;v3;v4;v5;v6;v7;v8;v9;v10;v11;v12;v13;v14] in
    let s = Seq.createL l in
    assert (Seq.seq_to_list s == l ==> (
                 Seq.length s == 15 /\ Seq.index s 0 == v0/\Seq.index s 1 == v1/\Seq.index s 2 == v2/\Seq.index s 3 == v3/\Seq.index s 4 == v4/\Seq.index s 5 == v5/\Seq.index s 6 == v6/\Seq.index s 7 == v7/\Seq.index s 8 == v8/\Seq.index s 9 == v9/\Seq.index s 10 == v10/\Seq.index s 11 == v11/\Seq.index s 12 == v12/\Seq.index s 13 == v13/\Seq.index s 14 == v14
           )) by (Tactics.norm [primops; iota; delta; zeta]);
    s
    
// unfold let mk_seq_tup15 (v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14) = mk_seq15 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14

// let mk_seq16 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15: 'a): Pure (t_Array 'a (sz 16)) (requires True) 
//   (ensures fun s -> Seq.length s == 16 /\ Seq.index s 0 == v0/\Seq.index s 1 == v1/\Seq.index s 2 == v2/\Seq.index s 3 == v3/\Seq.index s 4 == v4/\Seq.index s 5 == v5/\Seq.index s 6 == v6/\Seq.index s 7 == v7/\Seq.index s 8 == v8/\Seq.index s 9 == v9/\Seq.index s 10 == v10/\Seq.index s 11 == v11/\Seq.index s 12 == v12/\Seq.index s 13 == v13/\Seq.index s 14 == v14/\Seq.index s 15 == v15)
//   = let l = [v0;v1;v2;v3;v4;v5;v6;v7;v8;v9;v10;v11;v12;v13;v14;v15] in
//     let s = Seq.createL l in
//     assert (Seq.seq_to_list s == l ==> (
//                  Seq.length s == 16 /\ Seq.index s 0 == v0/\Seq.index s 1 == v1/\Seq.index s 2 == v2/\Seq.index s 3 == v3/\Seq.index s 4 == v4/\Seq.index s 5 == v5/\Seq.index s 6 == v6/\Seq.index s 7 == v7/\Seq.index s 8 == v8/\Seq.index s 9 == v9/\Seq.index s 10 == v10/\Seq.index s 11 == v11/\Seq.index s 12 == v12/\Seq.index s 13 == v13/\Seq.index s 14 == v14/\Seq.index s 15 == v15
//            )) by (Tactics.norm [primops; iota; delta; zeta]);
//     s
    
// unfold let mk_seq_tup16 (v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15) = mk_seq16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15

// let mk_seq17 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16: 'a): Pure (t_Array 'a (sz 17)) (requires True) 
//   (ensures fun s -> Seq.length s == 17 /\ Seq.index s 0 == v0/\Seq.index s 1 == v1/\Seq.index s 2 == v2/\Seq.index s 3 == v3/\Seq.index s 4 == v4/\Seq.index s 5 == v5/\Seq.index s 6 == v6/\Seq.index s 7 == v7/\Seq.index s 8 == v8/\Seq.index s 9 == v9/\Seq.index s 10 == v10/\Seq.index s 11 == v11/\Seq.index s 12 == v12/\Seq.index s 13 == v13/\Seq.index s 14 == v14/\Seq.index s 15 == v15/\Seq.index s 16 == v16)
//   = let l = [v0;v1;v2;v3;v4;v5;v6;v7;v8;v9;v10;v11;v12;v13;v14;v15;v16] in
//     let s = Seq.createL l in
//     assert (Seq.seq_to_list s == l ==> (
//                  Seq.length s == 17 /\ Seq.index s 0 == v0/\Seq.index s 1 == v1/\Seq.index s 2 == v2/\Seq.index s 3 == v3/\Seq.index s 4 == v4/\Seq.index s 5 == v5/\Seq.index s 6 == v6/\Seq.index s 7 == v7/\Seq.index s 8 == v8/\Seq.index s 9 == v9/\Seq.index s 10 == v10/\Seq.index s 11 == v11/\Seq.index s 12 == v12/\Seq.index s 13 == v13/\Seq.index s 14 == v14/\Seq.index s 15 == v15/\Seq.index s 16 == v16
//            )) by (Tactics.norm [primops; iota; delta; zeta]);
//     s
    
// unfold let mk_seq_tup17 (v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16) = mk_seq17 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16

// let mk_seq18 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17: 'a): Pure (t_Array 'a (sz 18)) (requires True) 
//   (ensures fun s -> Seq.length s == 18 /\ Seq.index s 0 == v0/\Seq.index s 1 == v1/\Seq.index s 2 == v2/\Seq.index s 3 == v3/\Seq.index s 4 == v4/\Seq.index s 5 == v5/\Seq.index s 6 == v6/\Seq.index s 7 == v7/\Seq.index s 8 == v8/\Seq.index s 9 == v9/\Seq.index s 10 == v10/\Seq.index s 11 == v11/\Seq.index s 12 == v12/\Seq.index s 13 == v13/\Seq.index s 14 == v14/\Seq.index s 15 == v15/\Seq.index s 16 == v16/\Seq.index s 17 == v17)
//   = let l = [v0;v1;v2;v3;v4;v5;v6;v7;v8;v9;v10;v11;v12;v13;v14;v15;v16;v17] in
//     let s = Seq.createL l in
//     assert (Seq.seq_to_list s == l ==> (
//                  Seq.length s == 18 /\ Seq.index s 0 == v0/\Seq.index s 1 == v1/\Seq.index s 2 == v2/\Seq.index s 3 == v3/\Seq.index s 4 == v4/\Seq.index s 5 == v5/\Seq.index s 6 == v6/\Seq.index s 7 == v7/\Seq.index s 8 == v8/\Seq.index s 9 == v9/\Seq.index s 10 == v10/\Seq.index s 11 == v11/\Seq.index s 12 == v12/\Seq.index s 13 == v13/\Seq.index s 14 == v14/\Seq.index s 15 == v15/\Seq.index s 16 == v16/\Seq.index s 17 == v17
//            )) by (Tactics.norm [primops; iota; delta; zeta]);
//     s
    
// unfold let mk_seq_tup18 (v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17) = mk_seq18 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17

// let mk_seq19 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18: 'a): Pure (t_Array 'a (sz 19)) (requires True) 
//   (ensures fun s -> Seq.length s == 19 /\ Seq.index s 0 == v0/\Seq.index s 1 == v1/\Seq.index s 2 == v2/\Seq.index s 3 == v3/\Seq.index s 4 == v4/\Seq.index s 5 == v5/\Seq.index s 6 == v6/\Seq.index s 7 == v7/\Seq.index s 8 == v8/\Seq.index s 9 == v9/\Seq.index s 10 == v10/\Seq.index s 11 == v11/\Seq.index s 12 == v12/\Seq.index s 13 == v13/\Seq.index s 14 == v14/\Seq.index s 15 == v15/\Seq.index s 16 == v16/\Seq.index s 17 == v17/\Seq.index s 18 == v18)
//   = let l = [v0;v1;v2;v3;v4;v5;v6;v7;v8;v9;v10;v11;v12;v13;v14;v15;v16;v17;v18] in
//     let s = Seq.createL l in
//     assert (Seq.seq_to_list s == l ==> (
//                  Seq.length s == 19 /\ Seq.index s 0 == v0/\Seq.index s 1 == v1/\Seq.index s 2 == v2/\Seq.index s 3 == v3/\Seq.index s 4 == v4/\Seq.index s 5 == v5/\Seq.index s 6 == v6/\Seq.index s 7 == v7/\Seq.index s 8 == v8/\Seq.index s 9 == v9/\Seq.index s 10 == v10/\Seq.index s 11 == v11/\Seq.index s 12 == v12/\Seq.index s 13 == v13/\Seq.index s 14 == v14/\Seq.index s 15 == v15/\Seq.index s 16 == v16/\Seq.index s 17 == v17/\Seq.index s 18 == v18
//            )) by (Tactics.norm [primops; iota; delta; zeta]);
//     s
    
// unfold let mk_seq_tup19 (v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18) = mk_seq19 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18

// let mk_seq20 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19: 'a): Pure (t_Array 'a (sz 20)) (requires True) 
//   (ensures fun s -> Seq.length s == 20 /\ Seq.index s 0 == v0/\Seq.index s 1 == v1/\Seq.index s 2 == v2/\Seq.index s 3 == v3/\Seq.index s 4 == v4/\Seq.index s 5 == v5/\Seq.index s 6 == v6/\Seq.index s 7 == v7/\Seq.index s 8 == v8/\Seq.index s 9 == v9/\Seq.index s 10 == v10/\Seq.index s 11 == v11/\Seq.index s 12 == v12/\Seq.index s 13 == v13/\Seq.index s 14 == v14/\Seq.index s 15 == v15/\Seq.index s 16 == v16/\Seq.index s 17 == v17/\Seq.index s 18 == v18/\Seq.index s 19 == v19)
//   = let l = [v0;v1;v2;v3;v4;v5;v6;v7;v8;v9;v10;v11;v12;v13;v14;v15;v16;v17;v18;v19] in
//     let s = Seq.createL l in
//     assert (Seq.seq_to_list s == l ==> (
//                  Seq.length s == 20 /\ Seq.index s 0 == v0/\Seq.index s 1 == v1/\Seq.index s 2 == v2/\Seq.index s 3 == v3/\Seq.index s 4 == v4/\Seq.index s 5 == v5/\Seq.index s 6 == v6/\Seq.index s 7 == v7/\Seq.index s 8 == v8/\Seq.index s 9 == v9/\Seq.index s 10 == v10/\Seq.index s 11 == v11/\Seq.index s 12 == v12/\Seq.index s 13 == v13/\Seq.index s 14 == v14/\Seq.index s 15 == v15/\Seq.index s 16 == v16/\Seq.index s 17 == v17/\Seq.index s 18 == v18/\Seq.index s 19 == v19
//            )) by (Tactics.norm [primops; iota; delta; zeta]);
//     s
    
// unfold let mk_seq_tup20 (v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19) = mk_seq20 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19
// (*
// let s = n => {
//     let vars = (new Array(n)).fill(0).map((_, i) => 'v'+i);
//     let clause = 'Seq.length s == ' + n + ' /\\ ' + vars.map((v, i) => `Seq.index s ${i} == ${v}`).join('/\\');
//     return `let mk_seq${n} (${vars.join(' ')}: 'a): Pure (t_Array 'a ${n}) (requires True) 
//   (ensures fun s -> ${clause})
//   = let l = [${vars.join(';')}] in
//     let s = Seq.createL l in
//     assert (Seq.seq_to_list s == l ==> (
//                  ${clause}
//            )) by (Tactics.norm [primops; iota; delta; zeta]);
//     s
    
// unfold let mk_seq_tup${n} (${vars.join(', ')}) = mk_seq${n} ${vars.join(' ')}`};
// 'module MkSeq\nopen Core\n' + (new Array(20)).fill(0).map((_, i) => s(1+i)).join('\n\n')
// *)

