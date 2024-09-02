module Libcrux_ml_kem.Vector.Portable
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Vector.Portable.Vector_type in
  ()

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Libcrux_ml_kem.Vector.Traits.t_Repr
Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
  {
    _super_11581440318597584651 = FStar.Tactics.Typeclasses.solve;
    _super_9442900250278684536 = FStar.Tactics.Typeclasses.solve;
    f_repr_pre = (fun (x: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) -> true);
    f_repr_post
    =
    (fun
        (x: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
        (out: t_Array i16 (sz 16))
        ->
        true);
    f_repr
    =
    fun (x: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) ->
      Libcrux_ml_kem.Vector.Portable.Vector_type.to_i16_array x
  }

(* item error backend: (TraitsSpecs) something is not implemented yet.
associated_expr_rebinding: zip two lists of different lengths (original_vars and target_vars)

 - original_vars: [{ Local_ident.T.name = "a"; id = (Local_ident.T.Expr, 2) };
  { Local_ident.T.name = "output"; id = (Local_ident.T.Expr, 4) };
  { Local_ident.T.name = "output_future"; id = (Local_ident.T.Expr, 6) };
  { Local_ident.T.name = "result"; id = (Local_ident.T.Expr, 7) }]
 - target_vars: [{ Local_ident.T.name = "a"; id = (Local_ident.T.Expr, 2) };
  { Local_ident.T.name = "output"; id = (Local_ident.T.Expr, 4) };
  { Local_ident.T.name = "out1"; id = (Local_ident.T.Expr, -1) }]

 - original_params: [{ Ast.Make.p =
   Ast.Make.PBinding {mut = Ast.Immutable; mode = Ast.Make.ByValue;
     var = { Local_ident.T.name = "a"; id = (Local_ident.T.Expr, 2) };
     typ =
     Ast.Make.TSlice {witness = Features.On.Slice.Slice;
       ty = (Ast.Make.TInt { Ast.size = Ast.S8; signedness = Ast.Unsigned })};
     subpat = None};
   span =
   { Span.id = 180853;
     data =
     [{ Span.Imported.filename =
        (Span.Imported.Real
           (Span.Imported.LocalPath "libcrux-ml-kem/src/vector/portable.rs"));
        hi = { Span.Imported.col = 19; line = 186 };
        lo = { Span.Imported.col = 18; line = 186 } }
       ]
     };
   typ =
   Ast.Make.TSlice {witness = Features.On.Slice.Slice;
     ty = (Ast.Make.TInt { Ast.size = Ast.S8; signedness = Ast.Unsigned })}
   };
  { Ast.Make.p =
    Ast.Make.PBinding {mut = Ast.Immutable; mode = Ast.Make.ByValue;
      var = { Local_ident.T.name = "output"; id = (Local_ident.T.Expr, 4) };
      typ =
      Ast.Make.TSlice {witness = Features.On.Slice.Slice;
        ty = (Ast.Make.TInt { Ast.size = Ast.S16; signedness = Ast.Signed })};
      subpat = None};
    span =
    { Span.id = 180855;
      data =
      [{ Span.Imported.filename =
         (Span.Imported.Real
            (Span.Imported.LocalPath "libcrux-ml-kem/src/vector/portable.rs"));
         hi = { Span.Imported.col = 34; line = 186 };
         lo = { Span.Imported.col = 28; line = 186 } }
        ]
      };
    typ =
    Ast.Make.TSlice {witness = Features.On.Slice.Slice;
      ty = (Ast.Make.TInt { Ast.size = Ast.S16; signedness = Ast.Signed })}
    };
  { Ast.Make.p =
    Ast.Make.PConstruct {name = `TupleCons (2);
      args =
      [{ Ast.Make.field = `TupleField ((0, 2));
         pat =
         { Ast.Make.p =
           Ast.Make.PBinding {mut = Ast.Immutable; mode = Ast.Make.ByValue;
             var =
             { Local_ident.T.name = "output_future";
               id = (Local_ident.T.Expr, 6) };
             typ =
             Ast.Make.TSlice {witness = Features.On.Slice.Slice;
               ty =
               (Ast.Make.TInt { Ast.size = Ast.S16; signedness = Ast.Signed })};
             subpat = None};
           span =
           { Span.id = 180857;
             data =
             [{ Span.Imported.filename =
                (Span.Imported.Real
                   (Span.Imported.LocalPath
                      "libcrux-ml-kem/src/vector/portable.rs"));
                hi = { Span.Imported.col = 80; line = 185 };
                lo = { Span.Imported.col = 4; line = 185 } }
               ]
             };
           typ =
           Ast.Make.TSlice {witness = Features.On.Slice.Slice;
             ty =
             (Ast.Make.TInt { Ast.size = Ast.S16; signedness = Ast.Signed })}
           }
         };
        { Ast.Make.field = `TupleField ((1, 2));
          pat =
          { Ast.Make.p =
            Ast.Make.PBinding {mut = Ast.Immutable; mode = Ast.Make.ByValue;
              var =
              { Local_ident.T.name = "result"; id = (Local_ident.T.Expr, 7) };
              typ =
              (Ast.Make.TInt
                 { Ast.size = Ast.SSize; signedness = Ast.Unsigned });
              subpat = None};
            span =
            { Span.id = 180858;
              data =
              [{ Span.Imported.filename =
                 (Span.Imported.Real
                    (Span.Imported.LocalPath
                       "libcrux-ml-kem/src/vector/portable.rs"));
                 hi = { Span.Imported.col = 21; line = 185 };
                 lo = { Span.Imported.col = 15; line = 185 } }
                ]
              };
            typ =
            (Ast.Make.TInt
               { Ast.size = Ast.SSize; signedness = Ast.Unsigned })
            }
          }
        ];
      is_record = false; is_struct = true};
    span =
    { Span.id = 180856;
      data =
      [{ Span.Imported.filename =
         (Span.Imported.Real
            (Span.Imported.LocalPath "libcrux-ml-kem/src/vector/portable.rs"));
         hi = { Span.Imported.col = 80; line = 185 };
         lo = { Span.Imported.col = 4; line = 185 } }
        ]
      };
    typ =
    Ast.Make.TApp {ident = `TupleType (2);
      args =
      [(Ast.Make.GType
          Ast.Make.TSlice {witness = Features.On.Slice.Slice;
            ty =
            (Ast.Make.TInt { Ast.size = Ast.S16; signedness = Ast.Signed })});
        (Ast.Make.GType
           (Ast.Make.TInt { Ast.size = Ast.SSize; signedness = Ast.Unsigned }))
        ]}
    }
  ]
 - params: [{ Ast.Make.p =
   Ast.Make.PBinding {mut = Ast.Immutable; mode = Ast.Make.ByValue;
     var = { Local_ident.T.name = "a"; id = (Local_ident.T.Expr, 2) };
     typ =
     Ast.Make.TSlice {witness = Features.On.Slice.Slice;
       ty = (Ast.Make.TInt { Ast.size = Ast.S8; signedness = Ast.Unsigned })};
     subpat = None};
   span =
   { Span.id = 173961;
     data =
     [{ Span.Imported.filename =
        (Span.Imported.Real
           (Span.Imported.LocalPath "libcrux-ml-kem/src/vector/portable.rs"));
        hi = { Span.Imported.col = 19; line = 186 };
        lo = { Span.Imported.col = 18; line = 186 } }
       ]
     };
   typ =
   Ast.Make.TSlice {witness = Features.On.Slice.Slice;
     ty = (Ast.Make.TInt { Ast.size = Ast.S8; signedness = Ast.Unsigned })}
   };
  { Ast.Make.p =
    Ast.Make.PBinding {mut = Ast.Immutable; mode = Ast.Make.ByValue;
      var = { Local_ident.T.name = "output"; id = (Local_ident.T.Expr, 4) };
      typ =
      Ast.Make.TSlice {witness = Features.On.Slice.Slice;
        ty = (Ast.Make.TInt { Ast.size = Ast.S16; signedness = Ast.Signed })};
      subpat = None};
    span =
    { Span.id = 173963;
      data =
      [{ Span.Imported.filename =
         (Span.Imported.Real
            (Span.Imported.LocalPath "libcrux-ml-kem/src/vector/portable.rs"));
         hi = { Span.Imported.col = 34; line = 186 };
         lo = { Span.Imported.col = 28; line = 186 } }
        ]
      };
    typ =
    Ast.Make.TSlice {witness = Features.On.Slice.Slice;
      ty = (Ast.Make.TInt { Ast.size = Ast.S16; signedness = Ast.Signed })}
    };
  { Ast.Make.p =
    Ast.Make.PBinding {mut = Ast.Immutable; mode = Ast.Make.ByValue;
      var = { Local_ident.T.name = "out1"; id = (Local_ident.T.Expr, -1) };
      typ =
      Ast.Make.TApp {ident = `TupleType (2);
        args =
        [(Ast.Make.GType
            Ast.Make.TSlice {witness = Features.On.Slice.Slice;
              ty =
              (Ast.Make.TInt { Ast.size = Ast.S16; signedness = Ast.Signed })});
          (Ast.Make.GType
             (Ast.Make.TInt
                { Ast.size = Ast.SSize; signedness = Ast.Unsigned }))
          ]};
      subpat = None};
    span =
    { Span.id = 173964;
      data =
      [{ Span.Imported.filename =
         (Span.Imported.Real
            (Span.Imported.LocalPath "libcrux-ml-kem/src/vector/portable.rs"));
         hi = { Span.Imported.col = 5; line = 188 };
         lo = { Span.Imported.col = 57; line = 186 } }
        ]
      };
    typ =
    Ast.Make.TApp {ident = `TupleType (2);
      args =
      [(Ast.Make.GType
          Ast.Make.TSlice {witness = Features.On.Slice.Slice;
            ty =
            (Ast.Make.TInt { Ast.size = Ast.S16; signedness = Ast.Signed })});
        (Ast.Make.GType
           (Ast.Make.TInt { Ast.size = Ast.SSize; signedness = Ast.Unsigned }))
        ]}
    }
  ]

Last AST:
/** print_rust: pitem: not implemented  (item: { Concrete_ident.T.def_id =
  { Concrete_ident.Imported.krate = "libcrux_ml_kem";
    path =
    [{ Concrete_ident.Imported.data =
       (Concrete_ident.Imported.TypeNs "vector"); disambiguator = 0 };
      { Concrete_ident.Imported.data =
        (Concrete_ident.Imported.TypeNs "portable"); disambiguator = 0 };
      { Concrete_ident.Imported.data = Concrete_ident.Imported.Impl;
        disambiguator = 1 }
      ]
    };
  kind = Concrete_ident.Kind.Value }) */
const _: () = ();
 *)
