//! # `Ast` and `Manifest` implementations
//!
//! This module provides custom [`Ast`](crate::Ast) and [`Manifest`](crate::Manifest)
//! implementations. It also provides documentation and examples for the implementations on
//! standard library types.
//!
//! Jump to:
//! - [`Ast` implementations](#ast-implementations)
//! - [`Ast` examples](#ast-examples)
//! - [`Manifest` implementations](#manifest-implementations)
//!
//! ## [`Ast`](crate::Ast) implementations
//! The following table summarizes the implementations on standard library types.
//!
//! Types | Parse rules | Syntax Error
//! ------|-------------|------
//! `String`, `&'fmt str`, `PathBuf`, `&'fmt Path` | Captures the literal contents of the expression | [`Infallible`][I]
//! `bool` | literal `true` or `false` | [`ParseBoolError`](std::str::ParseBoolError)
//! `u*`, `i*`, and `NonZero<..>` variants | The number, from a decimal | [`ParseIntError`]
//! `f32`, `f64` |  The float, using the rules in [`FromStr`][F2] | [`ParseFloatError`](std::num::ParseFloatError)
//! `()` | Only an empty expression | [`NotEmpty`]
//! [`Infallible`][I] | Always fails to parse | `()`
//! [`Option<T>`] where `T: Ast` | `None` if the expression is empty, else `Some(T)` | The error type of `T`
//! [`Box<T>`], [`Arc<T>`][A], [`Rc<T>`][R] where `T: Ast` | Uses parse rules of `T` | The error type of `T`
//! `Result<T, T::Error>` where `T: Ast` | Uses parse rules of `T`, capturing error | [`Infallible`][I]
//!
//! The following additional types are parsed using their [`FromStr`][F] implementations:
//! - [`IpAddr`](std::net::IpAddr), [`Ipv4Addr`](std::net::Ipv4Addr), [`Ipv6Addr`](std::net::Ipv6Addr), [`SocketAddr`](std::net::SocketAddr), [`SocketAddrV4`](std::net::SocketAddrV4), [`SocketAddrV6`](std::net::SocketAddrV6)
//!
//! You can implement [`Ast`](crate::Ast) on your own types which implement [`FromStr`][F] using the [`Ast`](../derive.Ast.html) derive macro.
//!
//! The following table summarizes the implementations on types defined in this module.
//!
//! Types | Parse rules | Syntax Error
//! ------|-------------|-------------
//! [`BoundedInt<N>`] | A decimal in the range `0..N` | [`ParseBoundedIntError`]
//! [`IgnoredAny`] | Accepts any expression without capturing | [`Infallible`][I]
//!
//! ### `Ast` examples
//! Parse a float in many different formats.
//! ```
//! # use mufmt::Ast;
//! assert_eq!(f64::from_expr("4e2"), Ok(4e2));
//! assert_eq!(f64::from_expr("+infinity"), Ok(f64::INFINITY));
//! ```
//! Parse an `Option<T>`.
//! ```
//! # use mufmt::Ast;
//! assert_eq!(Option::<u8>::from_expr(""), Ok(None));
//! assert_eq!(Option::<u8>::from_expr("3"), Ok(Some(3)));
//!
//! // the `Option` has precedence over the internal type
//! assert_eq!(Option::<String>::from_expr(""), Ok(None));
//! assert_eq!(String::from_expr(""), Ok(String::new()));
//! ```
//! Parse a `Result<T, T::Error>`.
//! ```
//! # use mufmt::Ast;
//! // always returns Ok(_) since the err variant is captured
//! assert!(matches!(Result::<u8, <u8 as Ast>::Error>::from_expr(""), Ok(Err(_))));
//! assert!(matches!(Result::<u16, <u16 as Ast>::Error>::from_expr("12"), Ok(Ok(_))));
//! ```
//!
//! ## [`Manifest`](crate::Manifest) implementations.
//!
//! Types | Accepted `Ast` | Displays | Render Error
//! ------|-----|----------|------
//! [`HashMap<K, V>`][H], [`BTreeMap<K, V>`][B] | Any borrowed format of `K` | Value `V` corresponding to the key | [`KeyMissing`] if the key does not exist
//! [`Vec<T>`], [`VecDeque<T>`][V], `&[T]`, `&mut T`, [`[T]`](std::slice), [`[T; N]`](std::array) | `usize` | Value `T` at the index | [`IndexOutOfRange`] if the index is too large
//! [`[T; N]`](std::array) | [`BoundedInt<N>`] | Value `T` at the index | [`Infallible`][I]
//! `Fn(&A) -> Result<T, E>` | `A` | `T` | `E`
//! [`Placeholder<T>`] | Any | Value `T` | [`Infalible`][I]
//!
//! [A]: std::sync::Arc
//! [R]: std::rc::Rc
//! [I]: std::convert::Infallible
//! [F]: std::str::FromStr
//! [F2]: f64#method.from_str
//! [H]: std::collections::HashMap
//! [B]: std::collections::BTreeMap
//! [V]: std::collections::VecDeque

mod ast;
mod manifest;

use std::num::{IntErrorKind, ParseIntError};

pub use ast::{BoundedInt, IgnoredAny};
pub use manifest::Placeholder;

/// An index is out of range.
///
/// This is the error type for the [`Manifest`](crate::Manifest) implementation of container types
/// like [`Vec`] or slices and array types.
/// ```
/// use mufmt::{Template, types::IndexOutOfRange};
///
/// let template = Template::<&str, usize>::compile("User {3}").unwrap();
/// let mut mfst = vec!["Jon", "Thomas"];
///
/// // index `3` is out of range
/// assert_eq!(template.render(&mfst), Err(IndexOutOfRange(3)));
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct IndexOutOfRange(pub usize);

/// A key is missing.
///
/// This is the error type for the [`Manifest`](crate::Manifest) implementation of container types
/// like [`HashMap`](std::collections::HashMap) and [`BTreeMap`](std::collections::HashMap) when
/// the template contains a key which does not exist in the database.
/// ```
/// use std::collections::HashMap;
/// use mufmt::{Template, types::KeyMissing};
///
/// let template = Template::<&str, &str>::compile("Hello {name}!").unwrap();
/// let mut mfst: HashMap<&'static str, &'static str> = HashMap::new();
/// mfst.insert("age", "37");
///
/// // the key `name` is missing
/// assert_eq!(template.render(&mfst), Err(KeyMissing));
/// ```
/// The missing key is not reported since it cannot be moved out of the template. If your key
/// type is `Clone` or `Copy`, you can implement this feature as follows.
/// ```
/// use std::{borrow::Borrow, collections::HashMap, hash::Hash, fmt::Display};
/// use mufmt::{Manifest, Template};
///
/// struct Wrapper<K, V> {
///    inner: HashMap<K, V>
/// }
///
/// #[derive(Debug, PartialEq)]
/// struct KeyMissing<K>(K);
///
/// impl<Q, K, V> Manifest<Q> for Wrapper<K, V>
/// where
///     K: Borrow<Q> + Eq + Hash,
///     Q: Eq + Hash + Clone, // we need `Clone` to move out of the template
///     V: Display,
///{
///    type Error = KeyMissing<Q>;
///
///    fn manifest(&self, ast: &Q) -> Result<impl Display, Self::Error> {
///        self.inner.get(ast).ok_or_else(|| KeyMissing(ast.clone()))
///    }
///}
///
/// let template = Template::<&str, &str>::compile("Hello {name}!").unwrap();
/// let mut mfst: Wrapper<&'static str, &'static str> = Wrapper {
///     inner: HashMap::new(),
/// };
/// mfst.inner.insert("age", "37");
///
/// // the key `name` is missing
/// assert_eq!(template.render(&mfst), Err(KeyMissing("name")));
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct KeyMissing;

/// An expression was expected to be empty.
///
/// This is the error type for the [`Ast`](crate::Ast) implementation of the unit type
/// `()` which is returned when an expression contains contents.
/// ```
/// use mufmt::{Template, SyntaxErrorKind, types::NotEmpty};
///
/// assert!(Template::<&str, ()>::compile("User {}").is_ok());
///
/// assert_eq!(
///     Template::<&str, ()>::compile("User {a}").unwrap_err().kind,
///     SyntaxErrorKind::InvalidExpr(NotEmpty),
/// );
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NotEmpty;

/// An error which may occur while parsing a [`BoundedInt`] from a string.
pub enum ParseBoundedIntError {
    /// Parsed a valid `usize`, which is out of range.
    OutOfRange(usize),
    /// The string is not a valid `usize`
    ParseError(ParseIntError),
}

impl From<ParseIntError> for ParseBoundedIntError {
    fn from(v: ParseIntError) -> Self {
        Self::ParseError(v)
    }
}

impl ParseBoundedIntError {
    /// Outputs the detailed cause of failed parsing.
    pub const fn kind(&self) -> IntErrorKind {
        match self {
            Self::OutOfRange(_) => IntErrorKind::PosOverflow,
            Self::ParseError(err) => *err.kind(),
        }
    }
}
