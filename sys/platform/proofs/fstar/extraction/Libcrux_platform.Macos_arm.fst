module Libcrux_platform.Macos_arm
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

assume
val cstr': src: t_Slice i8 -> Prims.Pure string Prims.l_True (fun _ -> Prims.l_True)

let cstr = cstr'

assume
val actually_arm': Prims.unit -> Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

let actually_arm = actually_arm'

assume
val check': feature: t_Slice i8 -> Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

let check = check'

assume
val sysctl': Prims.unit -> Prims.Pure Prims.unit Prims.l_True (fun _ -> Prims.l_True)

let sysctl = sysctl'

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

assume
val aes': Prims.unit -> Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

let aes = aes'

assume
val adv_simd': Prims.unit -> Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

let adv_simd = adv_simd'

assume
val pmull': Prims.unit -> Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

let pmull = pmull'

assume
val sha256': Prims.unit -> Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

let sha256 = sha256'

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

assume
val init': Prims.unit -> Prims.Pure Prims.unit Prims.l_True (fun _ -> Prims.l_True)

let init = init'
