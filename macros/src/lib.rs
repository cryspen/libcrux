//! This is a collection of libcrux internal proc macros.

use std::collections::HashMap;

use proc_macro::{Delimiter, TokenStream, TokenTree};
use quote::{format_ident, quote};
use syn::{
    parenthesized,
    parse::Parser,
    parse_macro_input, parse_quote,
    punctuated::Punctuated,
    token::{Comma, Dot, Unsafe},
    Attribute, ExprMethodCall, FnArg, Ident, ItemFn, ItemMod, LitInt, Meta, MetaList, Pat, Path,
    Stmt, Token,
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

/// Instantiate ML-KEM variants.
///
/// This instantiates key sizes and platform versions.
#[proc_macro_attribute]
pub fn ml_kem_instantiations(args: TokenStream, item: TokenStream) -> TokenStream {
    let ItemMod {
        attrs,
        vis,
        content,
        semi,
        ..
    } = parse_macro_input!(item as ItemMod);

    // #[ml_kem_variants(keys(512, 768, 1024), platforms(portable(..), avx2(..), neon(..)))]
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

                for meta in nested_platforms {
                    match meta {
                        Meta::List(list) => {
                            let paths = Punctuated::<Path, Token![,]>::parse_terminated
                                .parse(list.tokens.into())
                                .unwrap();
                            platforms.push((list.path.get_ident().unwrap().clone(), paths));
                        }
                        _ => panic!("Expected a list for platforms with paths"),
                    }
                }
            }
            _ => panic!("Expected a list for keys and platforms"),
        }
    }

    let mut expanded = quote! {};

    // Write the modules for each key and platform combination
    for parameter_set in keys {
        for (platform, paths) in platforms.clone() {
            let MlkemNamesResult {
                params,
                feature_name,
                const_mod,
                ..
            } = mlkem_names(&parameter_set);
            let (platform_string, feature_platform, modpath) =
                mlkem_platform_names(&platform, &params);

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
                let mut this_content = content.clone();

                if platform_string == "avx2" {
                    // For AVX2 we add an inner unsafe function that we annotate
                    // with the avx2 target feature.
                    make_avx2(&mut this_content);
                }

                let module = quote! {
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
                expanded.extend(module);
            }
        }
    }
    expanded.into()
}

struct MlkemNamesResult {
    params: String,
    feature_name: String,
    const_mod: Ident,
    multiplex_mod: Ident,
}

fn mlkem_names(parameter_set: &LitInt) -> MlkemNamesResult {
    let params = quote! {#parameter_set}.to_string();
    let feature_name = format!("mlkem{}", params);
    let const_mod = format_ident!("mlkem{}_constants", params);
    let multiplex_mod = format_ident!("mlkem{}", params);

    MlkemNamesResult {
        params,
        feature_name,
        const_mod,
        multiplex_mod,
    }
}

type PlatformNames = (String, proc_macro2::TokenStream, Ident);

fn mlkem_platform_names(platform: &Ident, params: &String) -> PlatformNames {
    let parameter_set_string = format!("{}_{}", params, quote! {#platform}.to_string());
    let platform_string = quote! {#platform}.to_string();
    let feature_platform = match platform_string.as_str() {
        "portable" => quote! {},
        "avx2" => quote! {#[cfg(feature = "simd256")]},
        "neon" => quote! {#[cfg(feature = "simd128")]},
        _ => panic!("Unexpected platform {}", platform_string),
    }
    .into();
    let modpath = format_ident!("mlkem{}", parameter_set_string);
    (platform_string, feature_platform, modpath)
}

/// Annotate avx2 function with the target attribute
fn make_avx2(items: &mut Vec<syn::Item>) {
    for item in items {
        if let syn::Item::Fn(ref mut fun) = item {
            fun.attrs.push(parse_quote! {
                #[allow(unsafe_code)]
            });
            let ItemFn {
                attrs: _,
                vis: _,
                sig,
                block,
            } = fun;
            let mut inner_sig = sig.clone();
            inner_sig.ident = Ident::new(
                &format!("_inner_{}", inner_sig.ident),
                inner_sig.ident.span(),
            );
            inner_sig.unsafety = Some(Unsafe::default());
            let inner: ItemFn = parse_quote! {
                #[allow(unsafe_code)]
                #[cfg_attr(not(hax), target_feature(enable = "avx2"))]
                #inner_sig
                #block
            };

            let inner_name = inner_sig.ident;
            let generic_params = &sig.generics;

            // Extract the idents from the function arguments.
            let inner_args: Punctuated<syn::Ident, Comma> = sig
                .inputs
                .iter()
                .filter_map(|a| match a {
                    FnArg::Typed(arg) => match arg.pat.as_ref() {
                        Pat::Ident(i) => Some(i.ident.clone()),
                        _ => None,
                    },
                    _ => None,
                })
                .collect();

            // Build the function with the inner and the call to it.
            block.stmts = Vec::new();
            block.stmts.push(parse_quote! {
                #inner
            });
            block
                .stmts
                .push(parse_quote! {unsafe {#inner_name #generic_params (#inner_args)}});
        }
        if let syn::Item::Mod(ref mut module) = item {
            if let Some((_, mod_items)) = &mut module.content {
                make_avx2(mod_items);
            }
        }
    }
}

#[proc_macro_attribute]
pub fn ml_kem_multiplexing(args: TokenStream, item: TokenStream) -> TokenStream {
    let ItemMod {
        attrs,
        vis,
        content,
        semi,
        ..
    } = parse_macro_input!(item as ItemMod);

    let nested = Punctuated::<Meta, Token![,]>::parse_terminated
        .parse(args)
        .unwrap();

    let mut keys = Punctuated::default();
    let mut platforms = Punctuated::default();

    // Read the nested meta data
    for meta in nested {
        match meta {
            Meta::List(list) if list.path.is_ident("keys") => {
                keys = Punctuated::<LitInt, Token![,]>::parse_terminated
                    .parse(list.tokens.into())
                    .unwrap();
            }
            Meta::List(list) if list.path.is_ident("platforms") => {
                platforms = Punctuated::<Ident, Token![,]>::parse_terminated
                    .parse(list.tokens.into())
                    .unwrap();
            }
            _ => panic!("Expected a list for keys and platforms"),
        }
    }

    let mut expanded = quote! {};

    for parameter_set in keys {
        let MlkemNamesResult {
            params,
            feature_name,
            const_mod,
            multiplex_mod,
        } = mlkem_names(&parameter_set);

        let mut inst = quote! {};
        for platform in platforms.clone() {
            // Get all platform modules for the parameter set.
            let (platform_string, feature_platform, modpath) =
                mlkem_platform_names(&platform, &params);
            let platform_string = format_ident!("{}_instantiation", platform_string);
            inst.extend(quote! {
                #feature_platform
                use super::#modpath as #platform_string;
            });
        }

        // add the variant at the end of the function name
        if let Some((_, ref content)) = content {
            let this_content = content.clone();
            let fun = quote! {
                #(#attrs)*
                #[cfg(feature = #feature_name)]
                #vis mod #multiplex_mod {
                    #inst
                    use super::#const_mod::*;

                    #(#this_content)*
                } #semi
            };
            expanded.extend(fun);
        }
    }

    expanded.into()
}
