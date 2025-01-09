//! This is a collection of libcrux internal proc macros.

use std::collections::HashMap;

use proc_macro::{Delimiter, TokenStream, TokenTree};
use quote::{format_ident, quote};
use syn::{
    parenthesized, parse::Parser, parse_macro_input, punctuated::Punctuated, Attribute, Ident,
    ItemMod, LitInt, Meta, MetaList, Path, Token,
};

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

    let variants_vec = Punctuated::<LitInt, Token![,]>::parse_terminated
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

#[proc_macro_attribute]
pub fn ml_kem_variants(args: TokenStream, item: TokenStream) -> TokenStream {
    let ItemMod {
        attrs,
        vis,
        content,
        semi,
        ..
    } = parse_macro_input!(item as ItemMod);

    // #[ml_kem_variants(keys(512, 768, 1024), platforms(portable, avx2, neon))]
    let nested = Punctuated::<Meta, Token![,]>::parse_terminated
        .parse(args)
        .unwrap();

    let mut keys = Punctuated::default();
    let mut platforms = Vec::new();

    // Read the nested meta data
    for meta in nested {
        match meta {
            Meta::List(list) if list.path.is_ident("keys") => {
                keys = Punctuated::<LitInt, Token![,]>::parse_terminated
                    .parse(list.tokens.into())
                    .unwrap();
            }
            Meta::List(list) if list.path.is_ident("platforms") => {
                let nested_platforms = Punctuated::<Meta, Token![,]>::parse_terminated
                    .parse(list.tokens.into())
                    .unwrap();
                // eprintln!(
                //     "nested_platforms: {:?}",
                //     quote! {#nested_platforms}.to_string()
                // );
                for meta in nested_platforms {
                    match meta {
                        Meta::List(list) => {
                            let paths = Punctuated::<Path, Token![,]>::parse_terminated
                                .parse(list.tokens.into())
                                .unwrap();
                            platforms.push((list.path, paths));
                        }
                        _ => panic!("Expected a list for platforms with paths"),
                    }
                }
            }
            _ => panic!("Expected a list for keys and platforms"),
        }
    }

    let mut expanded = quote! {};

    eprintln!("keys: {:?}", quote! {#keys}.to_string());
    for (k, v) in platforms.iter() {
        eprintln!(
            "platforms: {:?} | {:?}",
            quote! {#k}.to_string(),
            quote! {#v}.to_string()
        );
    }
    for parameter_set in keys {
        for (platform, paths) in platforms.clone() {
            let params = quote! {#parameter_set}.to_string();
            let parameter_set_string = format!("{}_{}", params, quote! {#platform}.to_string());
            let feature_name = format!("mlkem{}", params);
            let platform_string = quote! {#platform}.to_string();
            let feature_platform = match platform_string.as_str() {
                "portable" => quote! {},
                "avx2" => quote! {#[cfg(feature = "simd256")]},
                "neon" => quote! {#[cfg(feature = "simd128")]},
                _ => panic!("Unexpected platform {}", platform_string),
            };
            let const_mod = format_ident!("mlkem{}_constants", params);
            let modpath = format_ident!("ml_kem_{}", parameter_set_string);

            // Build platform dependent types
            let mut platform_types = quote! {};
            let vec_type = paths.first().unwrap();
            platform_types.extend(quote! {
                type Vector = #vec_type;
            });
            let hash_type = paths.get(1).unwrap();
            platform_types.extend(quote! {
                type Hash = #hash_type;
            });

            let mod_comment = format!("ML-KEM {} {}", params, platform_string);

            // add the variant at the end of the function name
            if let Some((_, ref content)) = content {
                let this_content = content.clone();
                let fun = quote! {
                    #[doc = #mod_comment]
                    #(#attrs)*
                    #[cfg(feature = #feature_name)]
                    #feature_platform
                    #vis mod #modpath {
                        use super::#const_mod::*;
                        #platform_types

                        #(#this_content)*
                    } #semi
                };
                expanded.extend(fun);
            }
        }
    }
    expanded.into()
}
