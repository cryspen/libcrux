//! This is a collection of libcrux internal proc macros.

use proc_macro::{Delimiter, TokenStream, TokenTree};
use quote::quote;
use std::collections::HashMap;
use syn::{parse_macro_input, Attribute, Ident, ItemFn, Stmt};

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

#[proc_macro_attribute]
pub fn consts(args: TokenStream, item: TokenStream) -> TokenStream {
    let ItemFn {
        attrs,
        vis,
        sig,
        block,
        ..
    } = parse_macro_input!(item as ItemFn);

    let mut variants_map: HashMap<String, _> = HashMap::new();
    let mut derived_const_vec = Vec::new();

    // Parse an attribute list of the type
    // #[my_consts(
    //   v4x4{const X: usize = 4; const Y: usize = 4;},
    //   v6x5{const X: usize = 5; const Y: usize = 6;},
    //   derived { // optional - shold be in function
    //      const Z: usize = X + Y;
    //   }
    // )]
    let parser = syn::meta::parser(|meta| {
        let ident = meta.path.clone();

        if ident.get_ident().unwrap().to_string() == "derived" {
            let content;
            syn::braced!(content in meta.input);

            while !content.is_empty() {
                derived_const_vec.push(content.parse::<Stmt>().unwrap());
            }

            return Ok(());
        }

        let content;
        syn::braced!(content in meta.input);

        let mut const_vec = Vec::new();
        let mut attributes: Option<Vec<Attribute>> = None;
        while !content.is_empty() {
            // There may be a config flag here.
            if let Ok(new_attributes) = Attribute::parse_outer(&content) {
                if let Some(attributes) = &mut attributes {
                    attributes.extend(new_attributes);
                } else {
                    attributes = Some(new_attributes);
                }
            }

            const_vec.push(content.parse::<Stmt>().unwrap());
        }

        variants_map.insert(quote! {#ident}.to_string(), (attributes, const_vec));
        Ok(())
    });
    parse_macro_input!(args with parser);

    let mut expanded = quote! {};

    for (variant, (attributes, consts)) in variants_map.iter() {
        // add the variant at the end of the function name
        let mut this_sig = sig.clone();
        this_sig.ident = Ident::new(
            &format!("{}_{}", this_sig.ident, variant),
            this_sig.ident.span(),
        );

        let mut attribute_tokens = quote! {};
        if let Some(av) = attributes {
            for a in av {
                attribute_tokens.extend(quote! {
                    #a
                });
            }
        }

        let fun = quote! {
                #attribute_tokens
                #(#attrs)*
                #vis #this_sig {
                    #(
                        #attribute_tokens
                        #consts
                    )*
                    #(#derived_const_vec)*

                    #block
                }
        };
        expanded.extend(fun);
    }

    expanded.into()
}
