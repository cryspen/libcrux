module Libcrux_platform.Macos_arm
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

val cstr (src: t_Slice i8) : Prims.Pure string Prims.l_True (fun _ -> Prims.l_True)

/// Check that we're actually on an ARM mac.
/// When this returns false, no other function in here must be called.
val actually_arm: Prims.unit -> Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

val check (feature: t_Slice i8) : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

val sysctl: Prims.unit -> Prims.Pure Prims.unit Prims.l_True (fun _ -> Prims.l_True)

let sysctl__v_ADV_SIMD_STR: t_Array i8 (mk_usize 20) =
  let list =
    [
      mk_i8 104; mk_i8 119; mk_i8 46; mk_i8 111; mk_i8 112; mk_i8 116; mk_i8 105; mk_i8 111;
      mk_i8 110; mk_i8 97; mk_i8 108; mk_i8 46; mk_i8 65; mk_i8 100; mk_i8 118; mk_i8 83; mk_i8 73;
      mk_i8 77; mk_i8 68; mk_i8 0
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 20);
  Rust_primitives.Hax.array_of_list 20 list

let sysctl__v_FEAT_AES_STR: t_Array i8 (mk_usize 25) =
  let list =
    [
      mk_i8 104; mk_i8 119; mk_i8 46; mk_i8 111; mk_i8 112; mk_i8 116; mk_i8 105; mk_i8 111;
      mk_i8 110; mk_i8 97; mk_i8 108; mk_i8 46; mk_i8 97; mk_i8 114; mk_i8 109; mk_i8 46; mk_i8 70;
      mk_i8 69; mk_i8 65; mk_i8 84; mk_i8 95; mk_i8 65; mk_i8 69; mk_i8 83; mk_i8 0
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 25);
  Rust_primitives.Hax.array_of_list 25 list

let sysctl__v_FEAT_PMULL_STR: t_Array i8 (mk_usize 27) =
  let list =
    [
      mk_i8 104; mk_i8 119; mk_i8 46; mk_i8 111; mk_i8 112; mk_i8 116; mk_i8 105; mk_i8 111;
      mk_i8 110; mk_i8 97; mk_i8 108; mk_i8 46; mk_i8 97; mk_i8 114; mk_i8 109; mk_i8 46; mk_i8 70;
      mk_i8 69; mk_i8 65; mk_i8 84; mk_i8 95; mk_i8 80; mk_i8 77; mk_i8 85; mk_i8 76; mk_i8 76;
      mk_i8 0
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 27);
  Rust_primitives.Hax.array_of_list 27 list

let sysctl__v_FEAT_SHA256_STR: t_Array i8 (mk_usize 28) =
  let list =
    [
      mk_i8 104; mk_i8 119; mk_i8 46; mk_i8 111; mk_i8 112; mk_i8 116; mk_i8 105; mk_i8 111;
      mk_i8 110; mk_i8 97; mk_i8 108; mk_i8 46; mk_i8 97; mk_i8 114; mk_i8 109; mk_i8 46; mk_i8 70;
      mk_i8 69; mk_i8 65; mk_i8 84; mk_i8 95; mk_i8 83; mk_i8 72; mk_i8 65; mk_i8 50; mk_i8 53;
      mk_i8 54; mk_i8 0
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 28);
  Rust_primitives.Hax.array_of_list 28 list

(* item error backend: (AST import) something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/1343.
Please upvote or comment this issue if you see this error message.
Mutable static items are not supported.

Last AST:
/** print_rust: pitem: not implemented  (item: { Concrete_ident.T.def_id =
  { Explicit_def_id.T.is_constructor = false;
    def_id =
    { Types.index = (0, 0); is_local = true;
      kind =
      Types.Static {mutability = true; nested = false; safety = Types.Safe};
      krate = "libcrux_platform";
      parent =
      (Some { Types.contents =
              { Types.id = 0;
                value =
                { Types.index = (0, 0); is_local = true; kind = Types.Mod;
                  krate = "libcrux_platform";
                  parent =
                  (Some { Types.contents =
                          { Types.id = 0;
                            value =
                            { Types.index = (0, 0); is_local = true;
                              kind = Types.Mod; krate = "libcrux_platform";
                              parent = None; path = [] }
                            }
                          });
                  path =
                  [{ Types.data = (Types.TypeNs "macos_arm");
                     disambiguator = 0 }
                    ]
                  }
                }
              });
      path =
      [{ Types.data = (Types.TypeNs "macos_arm"); disambiguator = 0 };
        { Types.data = (Types.ValueNs "ADV_SIMD"); disambiguator = 0 }]
      }
    };
  moved = None; suffix = None }) */
const _: () = ();
 *)

(* item error backend: (AST import) something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/1343.
Please upvote or comment this issue if you see this error message.
Mutable static items are not supported.

Last AST:
/** print_rust: pitem: not implemented  (item: { Concrete_ident.T.def_id =
  { Explicit_def_id.T.is_constructor = false;
    def_id =
    { Types.index = (0, 0); is_local = true;
      kind =
      Types.Static {mutability = true; nested = false; safety = Types.Safe};
      krate = "libcrux_platform";
      parent =
      (Some { Types.contents =
              { Types.id = 0;
                value =
                { Types.index = (0, 0); is_local = true; kind = Types.Mod;
                  krate = "libcrux_platform";
                  parent =
                  (Some { Types.contents =
                          { Types.id = 0;
                            value =
                            { Types.index = (0, 0); is_local = true;
                              kind = Types.Mod; krate = "libcrux_platform";
                              parent = None; path = [] }
                            }
                          });
                  path =
                  [{ Types.data = (Types.TypeNs "macos_arm");
                     disambiguator = 0 }
                    ]
                  }
                }
              });
      path =
      [{ Types.data = (Types.TypeNs "macos_arm"); disambiguator = 0 };
        { Types.data = (Types.ValueNs "AES"); disambiguator = 0 }]
      }
    };
  moved = None; suffix = None }) */
const _: () = ();
 *)

(* item error backend: (AST import) something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/1343.
Please upvote or comment this issue if you see this error message.
Mutable static items are not supported.

Last AST:
/** print_rust: pitem: not implemented  (item: { Concrete_ident.T.def_id =
  { Explicit_def_id.T.is_constructor = false;
    def_id =
    { Types.index = (0, 0); is_local = true;
      kind =
      Types.Static {mutability = true; nested = false; safety = Types.Safe};
      krate = "libcrux_platform";
      parent =
      (Some { Types.contents =
              { Types.id = 0;
                value =
                { Types.index = (0, 0); is_local = true; kind = Types.Mod;
                  krate = "libcrux_platform";
                  parent =
                  (Some { Types.contents =
                          { Types.id = 0;
                            value =
                            { Types.index = (0, 0); is_local = true;
                              kind = Types.Mod; krate = "libcrux_platform";
                              parent = None; path = [] }
                            }
                          });
                  path =
                  [{ Types.data = (Types.TypeNs "macos_arm");
                     disambiguator = 0 }
                    ]
                  }
                }
              });
      path =
      [{ Types.data = (Types.TypeNs "macos_arm"); disambiguator = 0 };
        { Types.data = (Types.ValueNs "PMULL"); disambiguator = 0 }]
      }
    };
  moved = None; suffix = None }) */
const _: () = ();
 *)

(* item error backend: (AST import) something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/1343.
Please upvote or comment this issue if you see this error message.
Mutable static items are not supported.

Last AST:
/** print_rust: pitem: not implemented  (item: { Concrete_ident.T.def_id =
  { Explicit_def_id.T.is_constructor = false;
    def_id =
    { Types.index = (0, 0); is_local = true;
      kind =
      Types.Static {mutability = true; nested = false; safety = Types.Safe};
      krate = "libcrux_platform";
      parent =
      (Some { Types.contents =
              { Types.id = 0;
                value =
                { Types.index = (0, 0); is_local = true; kind = Types.Mod;
                  krate = "libcrux_platform";
                  parent =
                  (Some { Types.contents =
                          { Types.id = 0;
                            value =
                            { Types.index = (0, 0); is_local = true;
                              kind = Types.Mod; krate = "libcrux_platform";
                              parent = None; path = [] }
                            }
                          });
                  path =
                  [{ Types.data = (Types.TypeNs "macos_arm");
                     disambiguator = 0 }
                    ]
                  }
                }
              });
      path =
      [{ Types.data = (Types.TypeNs "macos_arm"); disambiguator = 0 };
        { Types.data = (Types.ValueNs "SHA256"); disambiguator = 0 }]
      }
    };
  moved = None; suffix = None }) */
const _: () = ();
 *)

val aes: Prims.unit -> Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

val adv_simd: Prims.unit -> Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

val pmull: Prims.unit -> Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

val sha256: Prims.unit -> Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

(* item error backend: (AST import) something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/1343.
Please upvote or comment this issue if you see this error message.
Mutable static items are not supported.

Last AST:
/** print_rust: pitem: not implemented  (item: { Concrete_ident.T.def_id =
  { Explicit_def_id.T.is_constructor = false;
    def_id =
    { Types.index = (0, 0); is_local = true;
      kind =
      Types.Static {mutability = true; nested = false; safety = Types.Safe};
      krate = "libcrux_platform";
      parent =
      (Some { Types.contents =
              { Types.id = 0;
                value =
                { Types.index = (0, 0); is_local = true; kind = Types.Mod;
                  krate = "libcrux_platform";
                  parent =
                  (Some { Types.contents =
                          { Types.id = 0;
                            value =
                            { Types.index = (0, 0); is_local = true;
                              kind = Types.Mod; krate = "libcrux_platform";
                              parent = None; path = [] }
                            }
                          });
                  path =
                  [{ Types.data = (Types.TypeNs "macos_arm");
                     disambiguator = 0 }
                    ]
                  }
                }
              });
      path =
      [{ Types.data = (Types.TypeNs "macos_arm"); disambiguator = 0 };
        { Types.data = (Types.ValueNs "INITIALIZED"); disambiguator = 0 }]
      }
    };
  moved = None; suffix = None }) */
const _: () = ();
 *)

/// Initialize CPU detection.
val init: Prims.unit -> Prims.Pure Prims.unit Prims.l_True (fun _ -> Prims.l_True)
