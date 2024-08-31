module Libcrux_intrinsics.Avx2_extract
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

(* item error backend: (TransformHaxLibInline) Fatal error: something we considered as impossible occurred! [1mPlease report this by submitting an issue on GitHub![0m
Details: Malformed `Quote` item: `quote_of_expr` failed. Expression was:
{ Ast.Make.e =
  Ast.Make.App {
    f =
    { Ast.Make.e =
      (Ast.Make.GlobalVar
         `Concrete ({ Concrete_ident.T.def_id =
  { Concrete_ident.Imported.krate = "rust_primitives";
    path =
    [{ Concrete_ident.Imported.data = (Concrete_ident.Imported.TypeNs "hax");
       disambiguator = 0 };
      { Concrete_ident.Imported.data =
        (Concrete_ident.Imported.ValueNs "failure"); disambiguator = 0 }
      ]
    };
  kind = Concrete_ident.Kind.Value }));
      span =
      { Span.id = 1879;
        data =
        [{ Span.Imported.filename =
           (Span.Imported.Real
              (Span.Imported.LocalPath
                 "libcrux-intrinsics/src/avx2_extract.rs"));
           hi = { Span.Imported.col = 2; line = 240 };
           lo = { Span.Imported.col = 0; line = 237 } }
          ]
        };
      typ =
      (Ast.Make.TArrow ([Ast.Make.TStr; Ast.Make.TStr],
         Ast.Make.TApp {
           ident =
           `Concrete ({ Concrete_ident.T.def_id =
  { Concrete_ident.Imported.krate = "rust_primitives";
    path =
    [{ Concrete_ident.Imported.data = (Concrete_ident.Imported.TypeNs "hax");
       disambiguator = 0 };
      { Concrete_ident.Imported.data =
        (Concrete_ident.Imported.TypeNs "Never"); disambiguator = 0 }
      ]
    };
  kind = Concrete_ident.Kind.Type });
           args = []}
         ))
      };
    args =
    [{ Ast.Make.e =
       (Ast.Make.Literal
          (Ast.String
             "(AST import) Fatal error: something we considered as impossible occurred! \027[1mPlease report this by submitting an issue on GitHub!\027[0m\nDetails: [import_thir:literal] got an error literal: this means the Rust compiler or Hax's frontend probably reported errors above."));
       span =
       { Span.id = 1879;
         data =
         [{ Span.Imported.filename =
            (Span.Imported.Real
               (Span.Imported.LocalPath
                  "libcrux-intrinsics/src/avx2_extract.rs"));
            hi = { Span.Imported.col = 2; line = 240 };
            lo = { Span.Imported.col = 0; line = 237 } }
           ]
         };
       typ = Ast.Make.TStr };
      { Ast.Make.e =
        (Ast.Make.Literal
           (Ast.String
              "{ Types.attributes = [];\n  contents =\n  Types.Literal {\n    lit =\n    { Types.node =\n      (Types.Err Types.ErrorGuaranteed {todo = \"ErrorGuaranteed(())\"});\n      span =\n      { Types.filename =\n        (Types.Real (Types.LocalPath \"libcrux-intrinsics/src/lib.rs\"));\n        hi = { Types.col = \"0\"; line = \"1\" };\n        lo = { Types.col = \"0\"; line = \"1\" } }\n      };\n    neg = false};\n  hir_id = None;\n  span =\n  { Types.filename =\n    (Types.Real (Types.LocalPath \"libcrux-intrinsics/src/avx2_extract.rs\"));\n    hi = { Types.col = \"2\"; line = \"240\" };\n    lo = { Types.col = \"0\"; line = \"237\" } };\n  ty = Types.Never }"));
        span =
        { Span.id = 1879;
          data =
          [{ Span.Imported.filename =
             (Span.Imported.Real
                (Span.Imported.LocalPath
                   "libcrux-intrinsics/src/avx2_extract.rs"));
             hi = { Span.Imported.col = 2; line = 240 };
             lo = { Span.Imported.col = 0; line = 237 } }
            ]
          };
        typ = Ast.Make.TStr }
      ];
    generic_args = []; bounds_impls = []; trait = None};
  span =
  { Span.id = 1879;
    data =
    [{ Span.Imported.filename =
       (Span.Imported.Real
          (Span.Imported.LocalPath "libcrux-intrinsics/src/avx2_extract.rs"));
       hi = { Span.Imported.col = 2; line = 240 };
       lo = { Span.Imported.col = 0; line = 237 } }
      ]
    };
  typ =
  Ast.Make.TApp {
    ident =
    `Concrete ({ Concrete_ident.T.def_id =
  { Concrete_ident.Imported.krate = "rust_primitives";
    path =
    [{ Concrete_ident.Imported.data = (Concrete_ident.Imported.TypeNs "hax");
       disambiguator = 0 };
      { Concrete_ident.Imported.data =
        (Concrete_ident.Imported.TypeNs "Never"); disambiguator = 0 }
      ]
    };
  kind = Concrete_ident.Kind.Type });
    args = []}
  }

Last AST:
/** print_rust: pitem: not implemented  (item: { Concrete_ident.T.def_id =
  { Concrete_ident.Imported.krate = "libcrux_intrinsics";
    path =
    [{ Concrete_ident.Imported.data =
       (Concrete_ident.Imported.TypeNs "avx2_extract"); disambiguator = 0 };
      { Concrete_ident.Imported.data =
        (Concrete_ident.Imported.ValueNs "mm256_srli_epi16");
        disambiguator = 0 }
      ]
    };
  kind = Concrete_ident.Kind.Value }) */
const _: () = ();
 *)
