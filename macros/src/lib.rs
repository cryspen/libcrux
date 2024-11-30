use proc_macro::{Delimiter, TokenStream, TokenTree};
use quote::quote;
use std::collections::HashMap;
use syn::{parse_macro_input, parse_str, ItemFn, ReturnType, Token};

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
pub fn generic_types(attributes: TokenStream, item: TokenStream) -> TokenStream {
    let ItemFn {
        attrs,
        vis,
        sig,
        block,
        ..
    } = parse_macro_input!(item as ItemFn);

    // Inject types into the function signature.
    fn generic_types(ty: &mut syn::Type, old: &syn::Path, new: &syn::Path) {
        match ty {
            syn::Type::Path(type_path) => {
                // for segment in &mut type_path.path.segments {
                //     if let syn::PathArguments::AngleBracketed(angle_bracketed_args) =
                //         &mut segment.arguments
                //     {
                //         for arg in &mut angle_bracketed_args.args {
                //             match arg {
                //                 syn::GenericArgument::Type(t) => {
                //                     // Recurse again. We could end here,
                //                     // but we need to do the same for Path
                //                     eprintln!("Found generic arg {}", quote!{#t}.to_string());
                //                     generic_types(t, old, new);
                //                 }
                //                 _ => {}
                //             }
                //         }
                //     }
                // }
                // eprintln!("Got a type_path {}", quote! {#type_path}.to_string());

                let tp = &mut type_path.path;
                let ts = quote! {#tp}.to_string();
                // eprintln!("Found type arg {ts}");
                // eprintln!("Found generic type: {:?}", ts);
                // eprintln!("  Looking to replace {old} with {new}.");
                // XXX: use the path instead of going to strings.
                let ts = ts.replace(&(quote! {#old}.to_string()), &(quote! {#new}.to_string()));
                *tp = parse_str::<syn::Path>(&ts).expect("  Unable to replace type");
                // eprintln!("  new generic type: {:?}", quote! {#t}.to_string());
            }
            syn::Type::Array(a) => {
                // eprintln!(" --- found array: {:?}", quote! {#a}.to_string());
                generic_types(a.elem.as_mut(), old, new);
            }
            syn::Type::Tuple(t) => {
                for new_t in t.elems.iter_mut() {
                    generic_types(new_t, old, new);
                }
            }
            _ => {
                // eprintln!("We don't care about {}", quote! {#ty}.to_string())
            }
        }
    }

    let mut types_map = HashMap::new();
    let mut types_map_gen = HashMap::new();
    let mut variants = Vec::new();

    // Parse an attribute list of the type
    // #[generic_types(
    //   portable(T: MyTypePortable, U, OtherTypePortable),
    //   avx2(T: MyTypeAvx2, U, OtherTypeAvx2),
    // )]
    let parser = syn::meta::parser(|meta| {
        // eprintln!("Found attribute {:?}", meta);
        let name_postfix = meta.path.clone();
        // eprintln!("name: {:?}", quote! {#name_postfix}.to_string());
        variants.push(name_postfix.clone());
        let mut types_vec = Vec::new();
        let mut types_vec_gen = Vec::new();
        meta.parse_nested_meta(|meta| {
            // Alias: Type
            let key = meta.path.clone();
            // eprintln!("  type: {:?}", quote! {#key}.to_string());
            let _token: Token![:] = meta.input.parse()?;
            let value: syn::Path = meta.input.parse()?;
            // eprintln!("  value: {:?}", quote! {#value}.to_string());

            let alias = quote! {type #key = #value;};
            types_vec.push(alias);
            types_vec_gen.push((key, value));

            Ok(())
        })?;
        types_map.insert(quote! {#name_postfix}.to_string(), types_vec);
        types_map_gen.insert(quote! {#name_postfix}.to_string(), types_vec_gen);
        Ok(())
    });
    parse_macro_input!(attributes with parser);

    // eprintln!(" >>>>>> Done parsing");

    // We generate functions for each generic type name
    let mut expanded = quote! {};
    for variant in variants.iter() {
        let variant_string = quote! {#variant}.to_string();
        let new_types = types_map.get(&variant_string).unwrap();
        // eprintln!(" > {} gets", variant_string);
        // eprintln!(
        //     " >> {:?}",
        //     new_types
        //         .iter()
        //         .map(|t| quote! {#t}.to_string())
        //         .collect::<Vec<_>>()
        // );

        // // add the variant at the end of the function name
        let mut this_sig = sig.clone();

        // Replace all occurences of key in the return type with the value for
        // each variant.
        let mut platform_struct = variant.clone();
        for (key, value) in types_map_gen.get(&variant_string).unwrap().iter() {
            if let ReturnType::Type(_, ty) = &mut this_sig.output {
                // eprintln!(
                //     "Update function signature for {}",
                //     key.get_ident().unwrap().to_string()
                // );
                generic_types(ty.as_mut(), key, value);
            }
            if key.get_ident().unwrap().to_string() == "Platform" {
                platform_struct = value.clone();
            }
        }

        // Make this an inherent function of the Platform struct. This allows
        // calling monomorphised functions without knowing the platform.
        // XXX: don't hardcode "Platform"

        let fun = quote! {
            impl #platform_struct {
                #(#attrs)*
                #vis #this_sig {
                    #(#new_types)*
                    #block
                }
            }
        };
        expanded.extend(fun);
    }

    expanded.into()
}

#[proc_macro_attribute]
pub fn inherit(_attributes: TokenStream, item: TokenStream) -> TokenStream {
    item
}
