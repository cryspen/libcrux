//! This is a collection of libcrux internal proc macros.

use proc_macro::{Delimiter, TokenStream, TokenTree};
use quote::{format_ident, quote};
use syn::{parse::Parser, parse_macro_input, ItemMod, LitInt, Token};

fn skip_comma<T: Iterator<Item = TokenTree>>(ts: &mut T) {
    match ts.next() {
        Some(TokenTree::Punct(p)) => assert_eq!(p.as_char(), ','),
        _ => panic!("Expected comma"),
    }
}

fn accept_token<T: Iterator<Item = TokenTree>>(ts: &mut T) -> TokenTree {
    match ts.next() {
        Some(t) => t,
        _ => panic!("early end"),
    }
}

fn brace(ts: TokenStream) -> TokenTree {
    TokenTree::Group(proc_macro::Group::new(Delimiter::Brace, ts))
}

#[proc_macro]
pub fn unroll_for(ts: TokenStream) -> TokenStream {
    let mut i = ts.into_iter();
    let n_loops = accept_token(&mut i).to_string().parse::<u32>().unwrap();
    skip_comma(&mut i);
    let var = accept_token(&mut i).to_string();
    let var = &var[1..var.len() - 1];
    skip_comma(&mut i);
    let start = accept_token(&mut i).to_string();
    skip_comma(&mut i);
    let increment = accept_token(&mut i).to_string();
    skip_comma(&mut i);
    let grouped_body = brace(TokenStream::from_iter(i));
    let chunks = (0..n_loops).map(|i| {
        let chunks = [
            format!("const {}: u32 = {} + {} * {};", var, start, i, increment)
                .parse()
                .unwrap(),
            TokenStream::from(grouped_body.clone()),
            ";".parse().unwrap(),
        ];
        TokenStream::from(brace(TokenStream::from_iter(chunks)))
    });
    TokenStream::from(brace(TokenStream::from_iter(chunks.into_iter().flatten())))
    // "{ let i = 0; println!(\"FROM MACRO{}\", i); }".parse().unwrap()
}

/// Annotation for a generic ML-DSA implementation, which pulls in
/// parameter-set specific constants.
///
/// Given a list of parameter set identifiers, i.e. `44,65,87`, for
/// each identifier $id a feature-gated module `ml_dsa_$id` is generated, which
/// pulls in the parameter specific constants, assumed to be specified
/// in `crate::constants::ml_dsa_$id`. Further, type aliases for for
/// signing, and verification keys, whole keypairs and signatures are
/// created.
#[proc_macro_attribute]
pub fn ml_dsa_parameter_sets(args: TokenStream, item: TokenStream) -> TokenStream {
    let ItemMod {
        attrs,
        vis,
        content,
        semi,
        ..
    } = parse_macro_input!(item as ItemMod);

    let variants_vec = syn::punctuated::Punctuated::<LitInt, Token![,]>::parse_terminated
        .parse(args)
        .unwrap();
    let mut expanded = quote! {};

    for parameter_set in variants_vec {
        let parameter_set_string = quote! {#parameter_set}.to_string();
        let feature_name = format!("mldsa{}", parameter_set_string);
        let modpath = format_ident!("ml_dsa_{}", parameter_set_string);

        let sk_ident = format_ident!("MLDSA{}SigningKey", parameter_set_string);
        let vk_ident = format_ident!("MLDSA{}VerificationKey", parameter_set_string);
        let keypair_ident = format_ident!("MLDSA{}KeyPair", parameter_set_string);
        let sig_ident = format_ident!("MLDSA{}Signature", parameter_set_string);

        // add the variant at the end of the function name
        if let Some((_, ref content)) = content {
            let this_content = content.clone();
            let fun = quote! {
                #(#attrs)*
                #[cfg(feature = #feature_name)]
                #vis mod #modpath {
                    use crate::constants::#modpath::*;

                    pub type #sk_ident = MLDSASigningKey<SIGNING_KEY_SIZE>;
                    pub type #vk_ident = MLDSAVerificationKey<VERIFICATION_KEY_SIZE>;
                    pub type #keypair_ident = MLDSAKeyPair<VERIFICATION_KEY_SIZE, SIGNING_KEY_SIZE>;
                    pub type #sig_ident = MLDSASignature<SIGNATURE_SIZE>;

                    #(#this_content)*
                } #semi
            };
            expanded.extend(fun);
        }
    }
    expanded.into()
}
