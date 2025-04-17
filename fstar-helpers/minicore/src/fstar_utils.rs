pub mod manual_norm {
    /// An F* stuck term that blocks normalization.
    #[hax_lib::fstar::before("irreducible")]
    pub const MANUAL_NORM: () = ();

    /// A lemma that normalizes `MANUAL_NORM` away.
    #[hax_lib::lemma]
    pub fn manual_norm_lemma(_: ()) -> Proof<{ hax_lib::eq(MANUAL_NORM, ()) }> {}

    /// Makes an expression opaque to the F* normalizer.
    #[macro_export]
    macro_rules! opaque {
        (|$($x:ident : $ty:ty),*| -> $out:ty {$body:expr}) => {{
            #[hax_lib::fstar::before("[@@strict_on_arguments [0]]")]
            fn leaf(_: (), $($x:$ty,)*) -> $out {
                $body
            }
            (|$($x:$ty,)*| leaf(MANUAL_NORM, $($x)*))
        }};
    }
    pub use opaque;
}
pub use manual_norm::*;
