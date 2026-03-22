extern crate proc_macro;

use std::collections::HashMap;

use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::{format_ident, quote};
use syn::{parse_macro_input, Attribute, Fields, Ident, Item, ItemMod, ItemStruct};

struct ActionDef {
    ident: Ident,
    real_return: TokenStream2,
    model_return: TokenStream2,
    bridge: TokenStream2,
    uses: Vec<Ident>,
    fields: Fields,
    other_attrs: Vec<Attribute>,
}

fn parse_module_attr(attr: TokenStream) -> Ident {
    let attr_str = attr.to_string();
    let parts: Vec<&str> = attr_str.split('=').collect();
    if parts.len() != 2 || parts[0].trim() != "state" {
        panic!("Expected #[lockstep_actions(state = YourStateType)]");
    }
    Ident::new(parts[1].trim(), proc_macro2::Span::call_site())
}

fn parse_type_str(s: &str) -> TokenStream2 {
    let ty: syn::Type = syn::parse_str(s)
        .unwrap_or_else(|e| panic!("Failed to parse type `{s}`: {e}"));
    quote!(#ty)
}

fn parse_action_attrs(item: &ItemStruct) -> ActionDef {
    let mut real_return = None;
    let mut model_return = None;
    let mut bridge = None;
    let mut opaque_types = None;
    let mut uses = Vec::new();
    let mut other_attrs = Vec::new();

    for attr in &item.attrs {
        if attr.path().is_ident("action") {
            let meta_list = attr.meta.require_list().expect("Expected #[action(...)]");
            let tokens = meta_list.tokens.to_string();

            let mut remaining = tokens.as_str();
            while !remaining.is_empty() {
                remaining = remaining.trim_start_matches([',', ' ', '\n', '\t']);
                if remaining.is_empty() {
                    break;
                }

                if remaining.starts_with("real_return") {
                    let (val, rest) = extract_string_value(remaining, "real_return");
                    real_return = Some(val);
                    remaining = rest;
                } else if remaining.starts_with("model_return") {
                    let (val, rest) = extract_string_value(remaining, "model_return");
                    model_return = Some(val);
                    remaining = rest;
                } else if remaining.starts_with("bridge") {
                    let (val, rest) = extract_string_value(remaining, "bridge");
                    bridge = Some(parse_type_str(&val));
                    remaining = rest;
                } else if remaining.starts_with("opaque_types") {
                    let (val, rest) = extract_brace_value(remaining, "opaque_types");
                    opaque_types = Some(parse_opaque_types(&val));
                    remaining = rest;
                } else if remaining.starts_with("uses") {
                    let (val, rest) = extract_bracket_value(remaining, "uses");
                    uses = val
                        .split(',')
                        .map(|s| s.trim())
                        .filter(|s| !s.is_empty())
                        .map(|s| Ident::new(s, proc_macro2::Span::call_site()))
                        .collect();
                    remaining = rest;
                } else {
                    let unknown = remaining.split([',', '=']).next().unwrap_or(remaining).trim();
                    panic!(
                        "Unknown key `{}` in #[action] for `{}`. \
                         Expected: real_return, model_return, bridge, opaque_types, uses",
                        unknown, item.ident
                    );
                }
            }
        } else {
            other_attrs.push(attr.clone());
        }
    }

    let real_return_str = real_return.expect(&format!(
        "Missing `real_return` in #[action] for `{}`",
        item.ident
    ));
    let real_ret = parse_type_str(&real_return_str);

    // model_return defaults to real_return when omitted
    let model_return_str = model_return.unwrap_or_else(|| real_return_str.clone());
    let model_ret = parse_type_str(&model_return_str);

    // Derive bridge if not explicitly provided
    let bridge = bridge.unwrap_or_else(|| {
        let opaques = opaque_types.unwrap_or_default();
        let real_ty: syn::Type = syn::parse_str(&real_return_str)
            .unwrap_or_else(|e| panic!("Failed to parse real_return `{real_return_str}`: {e}"));
        let model_ty: syn::Type = syn::parse_str(&model_return_str)
            .unwrap_or_else(|e| panic!("Failed to parse model_return `{model_return_str}`: {e}"));
        derive_bridge(&real_ty, &model_ty, &opaques, &item.ident.to_string())
    });

    ActionDef {
        ident: item.ident.clone(),
        real_return: real_ret,
        model_return: model_ret,
        bridge,
        uses,
        fields: item.fields.clone(),
        other_attrs,
    }
}

fn extract_string_value<'a>(input: &'a str, key: &str) -> (String, &'a str) {
    let rest = &input[key.len()..];
    let rest = rest.trim_start();
    let rest = rest.strip_prefix('=').expect("Expected '=' after key");
    let rest = rest.trim_start();
    let rest = rest.strip_prefix('"').expect("Expected '\"' after '='");
    let mut depth = 0;
    let mut end = 0;
    for (i, c) in rest.char_indices() {
        match c {
            '"' if depth == 0 => {
                end = i;
                break;
            }
            '<' => depth += 1,
            '>' => depth -= 1,
            _ => {}
        }
    }
    let value = rest[..end].to_string();
    let remaining = &rest[end + 1..];
    (value, remaining)
}

fn extract_bracket_value<'a>(input: &'a str, key: &str) -> (String, &'a str) {
    let rest = &input[key.len()..];
    let rest = rest.trim_start();
    let rest = rest.strip_prefix('=').expect("Expected '=' after key");
    let rest = rest.trim_start();
    let rest = rest.strip_prefix('[').expect("Expected '[' after '='");
    if let Some(end) = rest.find(']') {
        let value = rest[..end].to_string();
        let remaining = &rest[end + 1..];
        (value, remaining)
    } else {
        panic!("Unclosed bracket in {key}");
    }
}

fn extract_brace_value<'a>(input: &'a str, key: &str) -> (String, &'a str) {
    let rest = &input[key.len()..];
    let rest = rest.trim_start();
    let rest = rest.strip_prefix('=').expect("Expected '=' after key");
    let rest = rest.trim_start();
    let rest = rest.strip_prefix('{').expect("Expected '{' after '='");
    let mut depth = 1;
    let mut end = 0;
    for (i, c) in rest.char_indices() {
        match c {
            '{' => depth += 1,
            '}' => {
                depth -= 1;
                if depth == 0 {
                    end = i;
                    break;
                }
            }
            _ => {}
        }
    }
    let value = rest[..end].to_string();
    let remaining = &rest[end + 1..];
    (value, remaining)
}

fn parse_opaque_types(s: &str) -> HashMap<String, String> {
    let mut map = HashMap::new();
    for pair in s.split(',') {
        let pair = pair.trim();
        if pair.is_empty() {
            continue;
        }
        let parts: Vec<&str> = pair.split("=>").collect();
        if parts.len() != 2 {
            panic!(
                "Invalid opaque_types entry `{pair}`. Expected `RealType => ModelType`"
            );
        }
        map.insert(parts[0].trim().to_string(), parts[1].trim().to_string());
    }
    map
}

// ===========================================================================
// Polynomial bridge derivation
// ===========================================================================

/// Derive the bridge type from `real_return` and `model_return` types,
/// walking both type ASTs in lockstep. This is the polynomial functor
/// decomposition: each algebraic data type's bridge is derived
/// mechanically from its structure.
fn derive_bridge(
    real: &syn::Type,
    model: &syn::Type,
    opaques: &HashMap<String, String>,
    action_name: &str,
) -> TokenStream2 {
    let real_str = normalize_type(real);
    let model_str = normalize_type(model);

    // Types identical → Transparent
    if real_str == model_str {
        return if real_str == "()" {
            quote!(UnitBridge)
        } else {
            quote!(Transparent<#real>)
        };
    }

    // Check opaque types mapping
    if let Some(expected_model) = opaques.get(&real_str) {
        if *expected_model == model_str {
            return quote!(Opaque<#real, #model>);
        }
    }

    // Try to decompose structurally
    match (real, model) {
        // Result<A, B> / Result<A', B'>
        (syn::Type::Path(rp), syn::Type::Path(mp))
            if path_ident(rp) == "Result" && path_ident(mp) == "Result" =>
        {
            let r_args = path_generic_args(rp);
            let m_args = path_generic_args(mp);
            if r_args.len() == 2 && m_args.len() == 2 {
                let ok_bridge = derive_bridge(&r_args[0], &m_args[0], opaques, action_name);
                let err_bridge = derive_bridge(&r_args[1], &m_args[1], opaques, action_name);
                return quote!(ResultBridge<#ok_bridge, #err_bridge>);
            }
        }
        // Option<A> / Option<A'>
        (syn::Type::Path(rp), syn::Type::Path(mp))
            if path_ident(rp) == "Option" && path_ident(mp) == "Option" =>
        {
            let r_args = path_generic_args(rp);
            let m_args = path_generic_args(mp);
            if r_args.len() == 1 && m_args.len() == 1 {
                let inner = derive_bridge(&r_args[0], &m_args[0], opaques, action_name);
                return quote!(OptionBridge<#inner>);
            }
        }
        // Vec<A> / Vec<A'>
        (syn::Type::Path(rp), syn::Type::Path(mp))
            if path_ident(rp) == "Vec" && path_ident(mp) == "Vec" =>
        {
            let r_args = path_generic_args(rp);
            let m_args = path_generic_args(mp);
            if r_args.len() == 1 && m_args.len() == 1 {
                let inner = derive_bridge(&r_args[0], &m_args[0], opaques, action_name);
                return quote!(VecBridge<#inner>);
            }
        }
        // (A, B) / (A', B') — tuples
        (syn::Type::Tuple(rt), syn::Type::Tuple(mt))
            if rt.elems.len() == mt.elems.len() =>
        {
            let n = rt.elems.len();
            if n == 0 {
                return quote!(UnitBridge);
            }
            let bridges: Vec<_> = rt.elems.iter().zip(mt.elems.iter())
                .map(|(r, m)| derive_bridge(r, m, opaques, action_name))
                .collect();
            if n == 2 {
                let (a, b) = (&bridges[0], &bridges[1]);
                return quote!(TupleBridge<#a, #b>);
            } else if n == 3 {
                let (a, b, c) = (&bridges[0], &bridges[1], &bridges[2]);
                return quote!(Tuple3Bridge<#a, #b, #c>);
            }
            // For other arities, fall through to error
        }
        _ => {}
    }

    panic!(
        "Cannot derive bridge for action `{action_name}`: \
         real type `{real_str}` and model type `{model_str}` differ \
         but no matching entry in `opaque_types`. \
         Add `opaque_types = {{ {real_str} => {model_str} }}` or \
         specify `bridge` explicitly."
    );
}

/// Normalize a type to a canonical string for comparison.
fn normalize_type(ty: &syn::Type) -> String {
    quote!(#ty).to_string().replace(' ', "")
}

/// Extract the last segment identifier from a type path (e.g., "Result" from "std::result::Result").
fn path_ident(tp: &syn::TypePath) -> String {
    tp.path
        .segments
        .last()
        .map(|s| s.ident.to_string())
        .unwrap_or_default()
}

/// Extract generic type arguments from a type path.
fn path_generic_args(tp: &syn::TypePath) -> Vec<syn::Type> {
    tp.path
        .segments
        .last()
        .and_then(|seg| {
            if let syn::PathArguments::AngleBracketed(ref args) = seg.arguments {
                Some(
                    args.args
                        .iter()
                        .filter_map(|arg| {
                            if let syn::GenericArgument::Type(ty) = arg {
                                Some(ty.clone())
                            } else {
                                None
                            }
                        })
                        .collect(),
                )
            } else {
                None
            }
        })
        .unwrap_or_default()
}

// ===========================================================================
// Main proc macro
// ===========================================================================

#[proc_macro_attribute]
pub fn lockstep_actions(attr: TokenStream, item: TokenStream) -> TokenStream {
    // Parsed for API documentation purposes — tells readers which state
    // type these actions target. Not used in codegen (yet).
    let _state_type = parse_module_attr(attr);
    let input = parse_macro_input!(item as ItemMod);

    let mod_vis = &input.vis;
    let mod_ident = &input.ident;
    let mod_attrs = &input.attrs;

    let (_, items) = input
        .content
        .expect("Expected a module with inline content (not `mod foo;`)");

    let mut actions: Vec<ActionDef> = Vec::new();
    let mut other_items: Vec<Item> = Vec::new();

    for item in items {
        match item {
            Item::Struct(ref s) if has_action_attr(s) => {
                actions.push(parse_action_attrs(s));
            }
            _ => {
                other_items.push(item);
            }
        }
    }

    if actions.is_empty() {
        panic!("No #[action] structs found in module `{mod_ident}`");
    }

    let pascal = to_pascal_case(&mod_ident.to_string());
    let gadt_name = format_ident!("{}Gadt", pascal);
    let visitor_name = format_ident!("{}Visitor", pascal);
    let any_action_name = format_ident!("Any{}Action", pascal);
    let model_interp_name = format_ident!("{}ModelInterp", pascal);
    let sut_interp_name = format_ident!("{}SutInterp", pascal);

    // -- struct defs --
    let struct_defs = gen_struct_defs(&actions);

    // -- GADT enum --
    let gadt_enum = gen_gadt_enum(&gadt_name, &actions);

    // -- visitor --
    let visitor_trait = gen_visitor_trait(&visitor_name, &actions);
    let accept_impl = gen_accept_impl(&gadt_name, &visitor_name, &actions);

    // -- constructors (typed + boxed) --
    let constructors = gen_constructors(&gadt_name, &any_action_name, &actions);

    // -- used_vars --
    let used_vars_impl = gen_used_vars(&gadt_name, &actions);

    // -- typed run_model/run_sut on GADT (the blog-post pattern with proof.cast) --
    let gadt_run_impls = gen_gadt_run_methods(
        &gadt_name,
        &model_interp_name,
        &sut_interp_name,
        &actions,
    );

    // -- AnyAction enum with real bridge/store dispatch --
    let any_action_impl = gen_any_action(
        &gadt_name,
        &any_action_name,
        &actions,
    );

    // -- interpreter traits --
    let model_interp_trait = gen_model_interp_trait(&model_interp_name, &actions);
    let sut_interp_trait = gen_sut_interp_trait(&sut_interp_name, &actions);

    // -- dispatch helpers --
    let dispatch_fns = gen_dispatch_fns(
        &gadt_name,
        &any_action_name,
        &model_interp_name,
        &sut_interp_name,
        &actions,
    );

    let output = quote! {
        #(#mod_attrs)*
        #mod_vis mod #mod_ident {
            // Auto-import prelude so bridge types can use short names
            #[allow(unused_imports)]
            use proptest_lockstep::prelude::*;
            #[allow(unused_imports)]
            use super::*;

            #(#other_items)*

            #(#struct_defs)*

            #gadt_enum

            #constructors

            #used_vars_impl

            #visitor_trait
            #accept_impl

            #gadt_run_impls

            #any_action_impl

            #model_interp_trait
            #sut_interp_trait

            #dispatch_fns
        }
    };

    output.into()
}

// ===========================================================================
// Code generators
// ===========================================================================

fn gen_struct_defs(actions: &[ActionDef]) -> Vec<TokenStream2> {
    actions
        .iter()
        .map(|a| {
            let ident = &a.ident;
            let fields = &a.fields;
            let attrs = &a.other_attrs;
            match fields {
                Fields::Named(_) => quote! {
                    #(#attrs)*
                    #[derive(Debug, Clone)]
                    pub struct #ident #fields
                },
                Fields::Unnamed(_) => quote! {
                    #(#attrs)*
                    #[derive(Debug, Clone)]
                    pub struct #ident #fields;
                },
                Fields::Unit => quote! {
                    #(#attrs)*
                    #[derive(Debug, Clone)]
                    pub struct #ident;
                },
            }
        })
        .collect()
}

fn gen_gadt_enum(gadt_name: &Ident, actions: &[ActionDef]) -> TokenStream2 {
    let variants = actions.iter().map(|a| {
        let ident = &a.ident;
        let real_ret = &a.real_return;
        quote! { #ident(Is<#real_ret, R>, #ident) }
    });

    quote! {
        #[derive(Debug, Clone)]
        pub enum #gadt_name<R> {
            #(#variants),*
        }
    }
}

fn gen_visitor_trait(visitor_name: &Ident, actions: &[ActionDef]) -> TokenStream2 {
    let methods = actions.iter().map(|a| {
        let ident = &a.ident;
        let method = format_ident!("visit_{}", to_snake_case(&ident.to_string()));
        quote! { fn #method(&mut self, action: &#ident) -> Self::Output; }
    });

    quote! {
        pub trait #visitor_name {
            type Output;
            #(#methods)*
        }
    }
}

fn gen_accept_impl(
    gadt_name: &Ident,
    visitor_name: &Ident,
    actions: &[ActionDef],
) -> TokenStream2 {
    let arms = actions.iter().map(|a| {
        let ident = &a.ident;
        let method = format_ident!("visit_{}", to_snake_case(&ident.to_string()));
        quote! { #gadt_name::#ident(_, ref action) => visitor.#method(action) }
    });

    quote! {
        impl<R> #gadt_name<R> {
            pub fn accept<V: #visitor_name>(&self, visitor: &mut V) -> V::Output {
                match self { #(#arms),* }
            }
        }
    }
}

fn gen_constructors(
    gadt_name: &Ident,
    any_name: &Ident,
    actions: &[ActionDef],
) -> TokenStream2 {
    let typed_ctors = actions.iter().map(|a| {
        let ident = &a.ident;
        let real_ret = &a.real_return;
        let fn_name = format_ident!("new_{}", to_snake_case(&ident.to_string()));
        quote! {
            /// Construct a typed GADT variant.
            pub fn #fn_name(action: #ident) -> #gadt_name<#real_ret> {
                #gadt_name::#ident(Is::refl(), action)
            }
        }
    });

    // Boxed constructors: action -> Box<dyn AnyAction> in one call
    let boxed_ctors = actions.iter().map(|a| {
        let ident = &a.ident;
        let fn_name = format_ident!("{}", to_snake_case(&ident.to_string()));
        let new_fn = format_ident!("new_{}", to_snake_case(&ident.to_string()));
        quote! {
            /// Construct a boxed action ready for use in strategies.
            pub fn #fn_name(action: #ident) -> Box<dyn proptest_lockstep::action::AnyAction> {
                Box::new(#any_name::#ident(#new_fn(action)))
            }
        }
    });

    quote! {
        #(#typed_ctors)*
        #(#boxed_ctors)*
    }
}

fn gen_used_vars(gadt_name: &Ident, actions: &[ActionDef]) -> TokenStream2 {
    let arms = actions.iter().map(|a| {
        let ident = &a.ident;
        let uses = &a.uses;
        if uses.is_empty() {
            quote! { #gadt_name::#ident(_, _) => vec![] }
        } else {
            let ids = uses.iter().map(|u| quote! { action.#u.var_id() });
            quote! { #gadt_name::#ident(_, ref action) => vec![#(#ids),*] }
        }
    });

    quote! {
        impl<R> #gadt_name<R> {
            pub fn used_vars(&self) -> Vec<usize> {
                match self { #(#arms),* }
            }
        }
    }
}

/// Generate typed `run_sut` on the GADT using the `Is<>` witness.
///
/// Each match arm uses `proof.cast()` to safely convert the SUT's typed
/// result to the generic `R`:
/// ```ignore
/// FsActionGadt::Open(proof, action) => proof.cast(I::open(sut, action, env))
/// ```
///
/// `run_model` is NOT generated on the GADT because the GADT is
/// parameterized by `real_return`, and the model interpreter may return
/// `model_return` (a different type for opaque handles). Model dispatch
/// goes through `dispatch_model` which uses `Box<dyn Any>`.
fn gen_gadt_run_methods(
    gadt_name: &Ident,
    _model_interp: &Ident,
    sut_interp: &Ident,
    actions: &[ActionDef],
) -> TokenStream2 {
    let sut_arms = actions.iter().map(|a| {
        let ident = &a.ident;
        let method = format_ident!("{}", to_snake_case(&ident.to_string()));
        quote! {
            #gadt_name::#ident(ref proof, ref action) => proof.cast(I::#method(sut, action, env))
        }
    });

    quote! {
        impl<R> #gadt_name<R> {
            /// Execute the SUT interpreter, using the `Is<>` witness to
            /// cast the typed result to the generic `R`.
            pub fn run_sut<I: #sut_interp>(&self, sut: &mut I::Sut, env: &TypedEnv) -> R {
                match self { #(#sut_arms),* }
            }
        }
    }
}

fn gen_any_action(
    gadt_name: &Ident,
    any_name: &Ident,
    actions: &[ActionDef],
) -> TokenStream2 {
    let variants = actions.iter().map(|a| {
        let ident = &a.ident;
        let real_ret = &a.real_return;
        quote! { #ident(#gadt_name<#real_ret>) }
    });

    let debug_arms = actions.iter().map(|a| {
        let ident = &a.ident;
        quote! { #any_name::#ident(ref inner) => std::fmt::Debug::fmt(inner, f) }
    });

    let used_vars_arms = actions.iter().map(|a| {
        let ident = &a.ident;
        let uses = &a.uses;
        if uses.is_empty() {
            quote! { #any_name::#ident(_) => vec![] }
        } else {
            let ids = uses.iter().map(|u| quote! { action.#u.var_id() });
            quote! {
                #any_name::#ident(#gadt_name::#ident(_, ref action)) => vec![#(#ids),*],
                #[allow(unreachable_patterns)]
                #any_name::#ident(_) => vec![]
            }
        }
    });

    let check_bridge_arms = actions.iter().map(|a| {
        let ident = &a.ident;
        let real_ret = &a.real_return;
        let model_ret = &a.model_return;
        let bridge = &a.bridge;
        quote! {
            #any_name::#ident(_) => {
                let m = model_result.downcast_ref::<#model_ret>()
                    .unwrap_or_else(|| panic!(
                        "check_bridge({}): model downcast to {} failed",
                        stringify!(#ident), stringify!(#model_ret)
                    ));
                let s = sut_result.downcast_ref::<#real_ret>()
                    .unwrap_or_else(|| panic!(
                        "check_bridge({}): SUT downcast to {} failed",
                        stringify!(#ident), stringify!(#real_ret)
                    ));
                <#bridge as LockstepBridge>::check(s, m)
            }
        }
    });

    let store_model_arms = actions.iter().map(|a| {
        let ident = &a.ident;
        let model_ret = &a.model_return;
        quote! {
            #any_name::#ident(_) => {
                let v = result.downcast_ref::<#model_ret>()
                    .unwrap_or_else(|| panic!(
                        "store_model_var({}): downcast to {} failed",
                        stringify!(#ident), stringify!(#model_ret)
                    ));
                env.insert(var_id, v.clone());
            }
        }
    });

    let store_sut_arms = actions.iter().map(|a| {
        let ident = &a.ident;
        let real_ret = &a.real_return;
        quote! {
            #any_name::#ident(_) => {
                let v = result.downcast_ref::<#real_ret>()
                    .unwrap_or_else(|| panic!(
                        "store_sut_var({}): downcast to {} failed",
                        stringify!(#ident), stringify!(#real_ret)
                    ));
                env.insert(var_id, v.clone());
            }
        }
    });

    quote! {
        /// Type-erased action wrapper. This is the existential boundary —
        /// the only dynamic dispatch point in the system.
        #[derive(Clone)]
        pub enum #any_name {
            #(#variants),*
        }

        impl std::fmt::Debug for #any_name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                match self { #(#debug_arms),* }
            }
        }

        impl proptest_lockstep::action::AnyAction for #any_name {
            fn as_any(&self) -> &dyn std::any::Any { self }

            fn used_vars(&self) -> Vec<usize> {
                match self { #(#used_vars_arms),* }
            }

            fn check_bridge(
                &self,
                model_result: &dyn std::any::Any,
                sut_result: &dyn std::any::Any,
            ) -> Result<(), String> {
                match self { #(#check_bridge_arms),* }
            }

            fn store_model_var(
                &self, var_id: usize, result: &dyn std::any::Any, env: &mut TypedEnv,
            ) {
                match self { #(#store_model_arms),* }
            }

            fn store_sut_var(
                &self, var_id: usize, result: &dyn std::any::Any, env: &mut TypedEnv,
            ) {
                match self { #(#store_sut_arms),* }
            }
        }
    }
}

fn gen_model_interp_trait(name: &Ident, actions: &[ActionDef]) -> TokenStream2 {
    let methods = actions.iter().map(|a| {
        let ident = &a.ident;
        let model_ret = &a.model_return;
        let method = format_ident!("{}", to_snake_case(&ident.to_string()));
        quote! {
            fn #method(state: &mut Self::State, action: &#ident, env: &TypedEnv) -> #model_ret;
        }
    });

    quote! {
        /// Typed model interpreter — one method per action, fully typed.
        pub trait #name {
            type State;
            #(#methods)*
        }
    }
}

fn gen_sut_interp_trait(name: &Ident, actions: &[ActionDef]) -> TokenStream2 {
    let methods = actions.iter().map(|a| {
        let ident = &a.ident;
        let real_ret = &a.real_return;
        let method = format_ident!("{}", to_snake_case(&ident.to_string()));
        quote! {
            fn #method(sut: &mut Self::Sut, action: &#ident, env: &TypedEnv) -> #real_ret;
        }
    });

    quote! {
        /// Typed SUT interpreter — one method per action, fully typed.
        pub trait #name {
            type Sut;
            #(#methods)*
        }
    }
}

fn gen_dispatch_fns(
    gadt_name: &Ident,
    any_name: &Ident,
    model_interp: &Ident,
    sut_interp: &Ident,
    actions: &[ActionDef],
) -> TokenStream2 {
    let model_arms = actions.iter().map(|a| {
        let ident = &a.ident;
        let method = format_ident!("{}", to_snake_case(&ident.to_string()));
        quote! {
            #any_name::#ident(#gadt_name::#ident(_, ref action)) =>
                Box::new(I::#method(state, action, env))
        }
    });

    let sut_arms: Vec<_> = actions.iter().map(|a| {
        let ident = &a.ident;
        let method = format_ident!("{}", to_snake_case(&ident.to_string()));
        quote! {
            #any_name::#ident(#gadt_name::#ident(_, ref action)) =>
                Box::new(I::#method(sut, action, env))
        }
    }).collect();

    let sut_arms_send = sut_arms.clone();

    quote! {
        /// Dispatch to the typed model interpreter. Use as the body of
        /// `LockstepModel::step_model`.
        pub fn dispatch_model<I: #model_interp>(
            state: &mut I::State,
            action: &dyn proptest_lockstep::action::AnyAction,
            env: &TypedEnv,
        ) -> Box<dyn std::any::Any> {
            let a = action.as_any().downcast_ref::<#any_name>()
                .expect(concat!("dispatch_model: expected ", stringify!(#any_name)));
            match a {
                #(#model_arms,)*
                #[allow(unreachable_patterns)]
                _ => unreachable!()
            }
        }

        /// Dispatch to the typed SUT interpreter. Use as the body of
        /// `LockstepModel::step_sut`.
        pub fn dispatch_sut<I: #sut_interp>(
            sut: &mut I::Sut,
            action: &dyn proptest_lockstep::action::AnyAction,
            env: &TypedEnv,
        ) -> Box<dyn std::any::Any> {
            let a = action.as_any().downcast_ref::<#any_name>()
                .expect(concat!("dispatch_sut: expected ", stringify!(#any_name)));
            match a {
                #(#sut_arms,)*
                #[allow(unreachable_patterns)]
                _ => unreachable!()
            }
        }

        /// Dispatch to the typed SUT interpreter, returning a `Send`-able result.
        /// Use as the body of `ConcurrentLockstepModel::step_sut_send`.
        ///
        /// This is identical to `dispatch_sut` but returns `Box<dyn Any + Send>`.
        /// Requires all SUT return types to be `Send`.
        pub fn dispatch_sut_send<I: #sut_interp>(
            sut: &mut I::Sut,
            action: &dyn proptest_lockstep::action::AnyAction,
            env: &TypedEnv,
        ) -> Box<dyn std::any::Any + Send> {
            let a = action.as_any().downcast_ref::<#any_name>()
                .expect(concat!("dispatch_sut_send: expected ", stringify!(#any_name)));
            match a {
                #(#sut_arms_send,)*
                #[allow(unreachable_patterns)]
                _ => unreachable!()
            }
        }
    }
}

fn has_action_attr(s: &ItemStruct) -> bool {
    s.attrs.iter().any(|a| a.path().is_ident("action"))
}

fn to_pascal_case(s: &str) -> String {
    s.split('_')
        .map(|word| {
            let mut c = word.chars();
            match c.next() {
                None => String::new(),
                Some(f) => f.to_uppercase().collect::<String>() + c.as_str(),
            }
        })
        .collect()
}

fn to_snake_case(s: &str) -> String {
    let mut result = String::new();
    let chars: Vec<char> = s.chars().collect();
    for (i, &c) in chars.iter().enumerate() {
        if c.is_uppercase() {
            // Insert underscore before uppercase if:
            // - not at the start, AND
            // - previous char was lowercase, OR next char is lowercase
            //   (handles acronyms: "HTTPSHandler" → "https_handler")
            if i > 0 {
                let prev_lower = chars[i - 1].is_lowercase();
                let next_lower = chars.get(i + 1).map_or(false, |c| c.is_lowercase());
                if prev_lower || next_lower {
                    result.push('_');
                }
            }
            result.push(c.to_lowercase().next().unwrap());
        } else {
            result.push(c);
        }
    }
    result
}
