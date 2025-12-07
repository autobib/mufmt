use proc_macro::TokenStream;
use quote::quote;
use syn::{DeriveInput, parse_macro_input};

/// Derive macro for implementing the `Ast` trait.
///
/// This macro implements the `Ast` trait for types that implement `FromStr`.
///
/// # Example
///
/// ```
/// # use mufmt_derive::Ast;
/// use mufmt::Ast;
///
/// #[derive(Ast)]
/// struct MyType {
///     value: String,
/// }
/// # impl std::str::FromStr for MyType {
/// #     type Err = std::convert::Infallible;
/// #     fn from_str(s: &str) -> Result<Self, Self::Err> {
/// #         Ok(Self {
/// #             value: s.into(),
/// #         })
/// #     }
/// # }
/// ```
/// This generates:
/// ```
/// # use mufmt::Ast;
/// # impl std::str::FromStr for MyType {
/// #     type Err = std::convert::Infallible;
/// #     fn from_str(s: &str) -> Result<Self, Self::Err> {
/// #         Ok(Self {
/// #             value: s.into(),
/// #         })
/// #     }
/// # }
/// impl Ast<'_> for MyType {
///     type Error = <MyType as std::str::FromStr>::Err;
///
///     fn from_expr(s: &str) -> Result<Self, Self::Error> {
///         std::str::FromStr::from_str(s)
///     }
/// }
/// ```
#[proc_macro_derive(Ast)]
pub fn derive_ast(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;

    // use an absolute path to mufmt
    let expanded = quote! {
        impl ::mufmt::Ast<'_> for #name {
            type Error = <#name as ::std::str::FromStr>::Err;

            fn from_expr(s: &str) -> ::std::result::Result<Self, Self::Error> {
                ::std::str::FromStr::from_str(s)
            }
        }
    };

    TokenStream::from(expanded)
}
