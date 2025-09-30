//! # μfmt
//!
//! μfmt (`mufmt`) is a minimal and extensible runtime formatting library.
//!
//! μfmt allows arbitrary types to define a formatting syntax and compiled template
//! format. μfmt also provides a number of built-in formats, backed by data stored in
//! collection types like [`HashMap`](std::collections::HashMap) or [`Vec`].
//!
//! The main API entrypoints are [`Ast`], [`Manifest`], and [`Template`].
//! In short:
//!
//! - The [`Ast`] describes how to parse a template expression into a strongly typed format.
//! - The [`Manifest`] describes how to display an `Ast`.
//! - The [`Template`] uses the `Ast` to compile templates and the `Manifest` to render them.
//!
//! For more information, go to:
//!
//! - [Introduction](#introduction): for a quick introduction and basic usage
//! - [Syntax](#syntax): to understand the global syntax rules
//! - [`Ast` and `Manifest` overview](#api-overview): for a general overview of the core `Ast` and
//!   `Manifest` traits
//! - [`Template` overview](#template-overview): for an overview of the [`Template`] struct, and
//!   its cousins [`Oneshot`] and [`TemplateSpans`].
//! - The [`types`] module: for custom [`Ast`] and [`Manifest`] implementations and a documentation
//!   of the implementations for the standard library.
//!
//! ## Introduction
//! μfmt templates are similar to Rust format strings:
//! ```
//! "Hello {name}!";
//! ```
//! Parts outside brackets are referred to as *text* and parts inside brackets are referred to as
//! *expressions*. See [syntax](#syntax) for a full description of the syntax.
//!
//! However, μfmt does not interpret the contents of expression. Instead, the expression syntax is
//! defined by an [`Ast`] implementation.
//! ```
//! use mufmt::BorrowedTemplate;
//! use std::collections::HashMap;
//!
//! // The `Ast` is &str
//! let template = BorrowedTemplate::<&str>::compile("Hello {name}!").unwrap();
//! // The `Manifest` is `HashMap<str, str>`
//! let mfst = HashMap::from([("name", "John")]);
//!
//! assert_eq!(template.render(&mfst).unwrap(), "Hello John!");
//! ```
//! In this example, the `{name}` expression is parsed as a string: `"name"`. The parsing rules are
//! defined by the [`Manifest`] implementation of the `HashMap`, which expects raw strings which
//! correspond to map keys. In general, the type is the associated [`Ast`] implementation.
//!
//! Suppose we instead provide a [`Vec`] as the context. Then the keys are parsed as `usize`.
//! In this example, we also see that same template can be re-used with a new context without
//! requiring recompilation of the template.
//! ```
//! # use mufmt::BorrowedTemplate;
//! // we don't need a type annotation here since `Vec` only accepts `usize` as the key
//! let template = BorrowedTemplate::compile("Letter: {1}").unwrap();
//! let mfst = vec!["α", "β", "γ"];
//!
//! let mut buf = String::new();
//! template.render_fmt(&mfst, &mut buf).unwrap();
//! assert_eq!(buf, "Letter: β");
//!
//! // we define a new context: but now, a `Vec<char>` instead of `Vec<&'static string>`
//! let new_mfst = vec!['a', 'b', 'c'];
//!
//! // this works since (for `Vec`) the key type does not depend on the type in the container
//! buf.clear();
//! template.render_fmt(&new_mfst, &mut buf).unwrap();
//! assert_eq!(buf, "Letter: b");
//!
//! // the intermediate syntax type is a `usize`, which is used to index into the vec
//! // if the user provides an invalid type, compilation will fail
//! assert!(BorrowedTemplate::<usize>::compile("{-100}").is_err()); // SyntaxError::Ast(ParseIntError, ...)
//! assert!(BorrowedTemplate::<i8>::compile("{-100}").is_ok());
//! ```
//! Passing a template with the incorrect expression type will result in a compilation error.
//! ```compile_fail
//! # use mufmt::BorrowedTemplate;
//! # use std::collections::HashMap;
//! let mfst = HashMap::from([("123", "456")]);
//! // this `HashMap` has `&str` keys, which cannot be retrieved with a `usize`
//! let template = BorrowedTemplate::<usize>::compile("Number: {123}").unwrap();
//! template.render(&mfst);
//! ```
//! Modifying the key type fixes this error.
//! ```
//! # use mufmt::BorrowedTemplate;
//! # use std::collections::HashMap;
//! let mfst = HashMap::from([(123, "456")]); // usize keys are compatible
//! let template = BorrowedTemplate::<usize>::compile("Number: {123}").unwrap();
//! template.render(&mfst);
//! ```
//!
//! ## Syntax
//! A μfmt template is a UTF-8 string where bracket-delimited expressions `{...}` are replaced with values
//! when the string is rendered.
//!
//! 1. The template not inside an expression are referred to as *text*,  and the parts inside an expression are
//!    referred to as *expressions*.
//! 2. Expressions are whitespace trimmed according to the rules of [`trim`](str::trim).
//! 3. To include brackets inside *text*, doubled brackets (like `{{` and `}}`) result in text
//!    consisting of a single bracket.
//! 4. To include brackets inside *expressions*, you can use *extended expression delimiters*: the initial
//!    `{` of an expression may be followed by any number of `#` characters. Then, the expression can only be
//!    closed by an equal number of `#` characters, followed by `}`.
//!
//! Otherwise, the interpretation of contents of the expressions are defined by the specific implementation.
//!
//! Here are examples for each of the above points.
//!
//! 1. `"Hello {name}!"` is text `Hello `, then an expression `name`, then text `!`.
//! 2. `"Hello { name  }!"` is equivalent to the above example.
//! 3. `"{{{contents}"` is text `{{`, then an expression `contents`.
//! 4. `"{## #}##}"` is an expression `#}`.
//!
//! ## API overview
//! Broadly speaking, template rendering is split into two independent phases.
//!
//! 1. A template string `"Hello {name}"` is compiled by the μfmt [syntax](#syntax) and the expression
//!    parsing rules defined by the [`Ast`] implementation. The compiled representation is a
//!    [`Template`] and an error during this phase is a [`SyntaxError`].
//! 2. The compiled template is combined with additional data via a [`Manifest`]
//!    implementation to obtain a type which can be displayed. An error during this phase
//!    is the associated error type [`Manifest::Error`].
//!
//! The precise dividing line between where the `Ast` parsing ends and template rendering begins is
//! intentionally unspecified and depends on the use-case. However, a good rule of thumb
//! (especially if you are reusing templates) is to do as much as possible when parsing into the
//! `Ast` and to minimize errors during rendering.
//!
//! ### The [`Ast`] trait
//! An [`Ast`] implementation is responsible for parsing the contents of a `{expression}`.
//! ```
//! pub trait Ast<'fmt>: Sized {
//!     type Error;
//!
//!     fn from_expr(expr: &'fmt str) -> Result<Self, Self::Error>;
//! }
//! ```
//! The [`Ast::from_expr`] method is called by [`Template::compile`] on each expression in the template
//! string.
//!
//! The associated `'fmt` lifetime corresponds to the lifetime of the original template string and
//! can be used if the [`Ast`] benefits from borrowing from the text of the expression itself.
//!
//! The simplest [`Ast`] implementation is the one for `&'fmt str` which is exactly as follows:
//! ```
//! # pub trait Ast<'fmt>: Sized {
//! #     type Error;
//! #     fn from_expr(expr: &'fmt str) -> Result<Self, Self::Error>;
//! # }
//! impl<'fmt> Ast<'fmt> for &'fmt str {
//!     // Always succeeds
//!     type Error = std::convert::Infallible;
//!
//!     fn from_expr(expr: &'fmt str) -> Result<Self, Self::Error> {
//!         Ok(expr)
//!     }
//! }
//! ```
//!
//! ### The [`Manifest`] trait
//! The [`Manifest`] trait describes how to display the [`Ast`] corresponding to each expression
//! produced by an [`Ast`] implementation.
//! ```
//! use std::fmt::Display;
//!
//! pub trait Manifest<A> {
//!     type Error;
//!
//!     fn manifest(&self, ast: &A) -> Result<impl Display, Self::Error>;
//! }
//! ```
//! A `Manifest` implementation is one which knows how to display any `Ast` of type `A`. A single
//! type can implement `Manifest` multiple times, depending on the keys which it accepts.
//!
//! A [`Vec`] implemenets [`Manifest`] by converting an index to the corresponding item at that
//! index:
//! ```
//! # use std::fmt::Display;
//! # pub trait Manifest<A> {
//! #     type Error;
//! #     fn manifest(&self, ast: &A) -> Result<impl Display, Self::Error>;
//! # }
//! use mufmt::types::IndexOutOfRange;
//!
//! impl<T: Display> Manifest<usize> for Vec<T> {
//!     type Error = IndexOutOfRange;
//!
//!     fn manifest(&self, n: &usize) -> Result<impl Display, Self::Error> {
//!         self.get(*n).ok_or(IndexOutOfRange(*n))
//!     }
//! }
//! ```
//! The returned `Display` implementation is ephemeral. It may borrow from `self` and
//! also from the `ast`.
//!
//! ## Template overview
//! When you want to work with a template string, you have essentially three options:
//!
//! - [`Template`], [`Oneshot`], and [`TemplateSpans`].
//!
//!
//! ### [`Template`] struct
//! By default, you should use the [`Template`] struct. This contains a compiled representation of
//! a template string, with expressions compiled according to the rules of the associated [`Ast`] typed.
//!
//! You can construct a [`Template`] from a template string using [`Template::compile`], which will
//! immediately report syntax errors. Then, the [`Template`] struct can be rendered using three methods:
//!
//! - [`Template::render`], for convenient rendering directly into a [`String`].
//! - [`Template::render_io`], when you have a [`io::Write`] buffer and want to avoid an
//!   allocation.
//! - [`Template::render_fmt`], when you have a [`fmt::Write`] buffer and want to avoid an
//!   allocation.
//!
//! These methods do not consume the template which allows repeated rendering of the same template.
//! Moreover, since compilation is separate from rendering, you can report errors
//! early, before rendering the template.
//!
//! Since a [`Template`] is generic over the text type, some aliases are provided which may be more
//! convenient:
//!
//! - [`BorrowedTemplate`] and [`OwnedTemplate`].
//!
//! ### [`Oneshot`] struct
//! If you know you will only render a template exactly once, you can use the [`Oneshot`] struct.
//! It has similar same rendering methods as a [`Template`]:
//!
//! - [`Oneshot::render`], [`Oneshot::render_io`], and [`Oneshot::render_fmt`]
//!
//! The main gain is that we skip the intermediate compiled representation. This can result in
//! reduced memory usage if the template is extremely large.
//!
//! The main downside is that the error types are more general (returns a global [`Error`], rather
//! than an error type specialized to the method) and the template cannot be reused.
//!
//! It also exposes validation methods to check syntax without rendering the template:
//!
//! - [`Oneshot::validate`] and [`Oneshot::validate_any`]
//!
//! ### [`TemplateSpans`] iterator
//! Finally, if you actually want to work with the template directly and are not interested in
//! rendering, you can use the [`TemplateSpans`] iterator.
//!
//! This is an iterator over `Result<Span, SyntaxError>`, where a [`Span`] represents a contiguous
//! substring of the template string. The key additional feature is [error
//! recovery](TemplateSpans#error-recovery): this iterator can recover from non-fatal parsing
//! errors, such as expressions which are invalid for the provided `Ast`.
//!
//! A [`TemplateSpans`] struct can also be obtained with [`Oneshot::spans`].
//!
//! If you already have a [`Template`], you might be interested [`Template::spans`], which just
//! contains the [`Span`]s without the possible syntax errors.

#![deny(missing_docs)]

mod error;
#[cfg(test)]
mod tests;
pub mod types;

pub use error::{Error, FmtRenderError, IORenderError, SyntaxError, SyntaxErrorKind};

use memchr::{memchr, memchr2, memmem};
use std::{convert::Infallible, fmt, io, marker::PhantomData, str::from_utf8_unchecked};

/// A typed representation of an expression which does not interpret the contents.
///
/// Often, you can use a [provided implementation](types#ast-implementations).
///
/// The role of an `Ast` is to perform as much validation as possible, without any knowledge of the
/// [`Manifest`] which may later use it. The correct balance here depends, of course, on the
/// particular use-case.
///
/// ### Example
/// A [`HashMap`](std::collections::HashMap) uses `&str` as its `Ast` implementation.
/// An `&str` is not aware at all of the contents of an expression, except that it should interpret it as
/// a string. In contrast, if we are aware that the keys must come from a specific list, we can
/// check that this is the case when the template is compiled.
/// ```
/// use mufmt::{Ast, BorrowedTemplate};
///
/// /// The permitted colours
/// enum Color {
///     Red,
///     Green,
///     Blue,
/// }
///
/// struct InvalidColor(pub String);
///
/// /// An `Ast` implementation which requires a string matching one of the colors.
/// impl Ast<'_> for Color {
///     type Error = InvalidColor;
///
///     fn from_expr(expr: &str) -> Result<Self, Self::Error> {
///         // expressions are whitespace trimmed, so we don't need to handle this here
///         match expr {
///             "red" => Ok(Self::Red),
///             "green" => Ok(Self::Green),
///             "blue" => Ok(Self::Blue),
///             s => Err(InvalidColor(s.to_owned())),
///         }
///     }
/// }
///
/// assert!(BorrowedTemplate::<Color>::compile("My favourite colors are {blue} and { green }!").is_ok());
/// assert!(BorrowedTemplate::<Color>::compile("The sky is very {orange}!").is_err());
/// ```
pub trait Ast<'fmt>: Sized {
    /// An error which may occur while parsing an expression.
    type Error;

    /// Parse the `Ast` from the expression.
    fn from_expr(expr: &'fmt str) -> Result<Self, Self::Error>;
}

/// A manifest knows how to display an [`Ast`].
///
/// Often, you can use a [provided implementation](types#manifest-implementations).
///
/// Manifest implementations typically contain state which determine how the string is
/// displayed.
///
/// ## No mutable self reference
/// A `Manifest` implementation is not provided a mutable self-reference. There are two reasons
/// for this:
///
/// 1. To encourage predictable template rendering.
/// 2. To simplify the use-case of rendering from multiple threads simultaneously.
///
/// If you must, you can work around this API restriction with [interior
/// mutability](https://doc.rust-lang.org/reference/interior-mutability.html).
pub trait Manifest<A> {
    /// An error produced when manifesting.
    type Error;

    /// Convert the `Ast` to a type which can be displayed.
    ///
    /// Note that the returned [`Display`](fmt::Display) implementation is ephemeral and can borrow
    /// from `&self` or the `ast`.
    fn manifest(&self, ast: &A) -> Result<impl fmt::Display, Self::Error>;

    /// Write the `Ast` into a [`fmt::Write`] implementation.
    fn write_fmt<W: fmt::Write>(
        &self,
        ast: &A,
        mut writer: W,
    ) -> Result<(), FmtRenderError<Self::Error>> {
        Ok(write!(
            writer,
            "{}",
            self.manifest(ast).map_err(FmtRenderError::Render)?
        )?)
    }

    /// Write the `Ast` into a [`io::Write`] implementation.
    fn write_io<W: io::Write>(
        &self,
        ast: &A,
        mut writer: W,
    ) -> Result<(), IORenderError<Self::Error>> {
        Ok(write!(
            writer,
            "{}",
            self.manifest(ast).map_err(IORenderError::Render)?
        )?)
    }
}

/// A component of a template, either text or an expression.
///
/// Internally, a [`Template`] is a [`Vec`] of [`Span`]s, which correspond to subsequent
/// expressions.
/// The spans can be accessed using the [`Template::spans`] method.
#[derive(Debug, PartialEq, Clone)]
pub enum Span<T, A> {
    /// Text, with brackets correctly escaped.
    Text(T),
    /// An interpreted expression.
    Expr(A),
}

impl<T, A> Span<T, A> {
    /// Returns if this is a [`Text`](Span::Text).
    pub fn is_text(&self) -> bool {
        matches!(self, Self::Text(_))
    }

    /// Returns if this is a [`Expr`](Span::Expr).
    pub fn is_expr(&self) -> bool {
        matches!(self, Self::Expr(_))
    }

    /// Apply a closure to the text, converting it to a new type.
    pub fn map_text<F, U>(self, f: F) -> Span<U, A>
    where
        F: FnOnce(T) -> U,
    {
        match self {
            Self::Text(t) => Span::Text(f(t)),
            Self::Expr(e) => Span::Expr(e),
        }
    }

    /// Apply a closure to the expression, converting it to a new type.
    pub fn map_expr<F, B>(self, f: F) -> Span<T, B>
    where
        F: FnOnce(A) -> B,
    {
        match self {
            Self::Text(t) => Span::Text(t),
            Self::Expr(e) => Span::Expr(f(e)),
        }
    }
}

/// A `Span` augumented with the index in the original template string at which the span starts.
#[derive(Debug, PartialEq)]
struct IndexedSpan<'fmt, T> {
    span: Span<T, &'fmt str>,
    offset: usize,
}

impl<'fmt, T, A: Ast<'fmt>> TryFrom<IndexedSpan<'fmt, T>> for Span<T, A> {
    type Error = SyntaxError<A::Error>;

    fn try_from(spanned: IndexedSpan<'fmt, T>) -> Result<Self, Self::Error> {
        Ok(match spanned.span {
            Span::Text(s) => Self::Text(s),
            Span::Expr(s) => Self::Expr(A::from_expr(s.trim()).map_err(|e| SyntaxError {
                kind: SyntaxErrorKind::InvalidExpr(e),
                span: spanned.offset..spanned.offset + s.len(),
            })?),
        })
    }
}

/// A dynamically parsed iterator of the [spans](Span) of a template string.
///
/// The main way to use a [`TemplateSpans`] is as an iterator of `Result<Span, SyntaxError>`. Construct a
/// [`TemplateSpans`] from a template string using [`TemplateSpans::new`], or from a [`Oneshot`]
/// using [`Oneshot::spans`].
///
/// Span iteration is deterministic and fully defined by the following rules. Go to:
///
/// - [Error recovery](#error-recovery)
/// - [Text span breaking](#text-span-breaking)
/// - [Fused and bounded length](#fused-and-bounded-length)
///
/// ## Error recovery
/// If the template string contains a syntax error, an `Err(_)` will be returned. Iteration will
/// continue past the error location if the error type is locally recoverable. This occurs in the
/// following cases:
///
/// 1. In the presence of an extra closing bracket.
/// 2. If the [`Ast`] implementation fails to parse an expression.
///
/// Here is an example illustrating this behaviour.
/// ```
/// # use mufmt::{Span, SyntaxErrorKind, TemplateSpans};
/// let mut spans_iter = TemplateSpans::<usize>::new("{12} }and {invalid}");
///
/// assert_eq!(spans_iter.next(), Some(Ok(Span::Expr(12))));
/// assert_eq!(spans_iter.next(), Some(Ok(Span::Text(" "))));
/// assert_eq!(
///     spans_iter.next().unwrap().unwrap_err().kind,
///     SyntaxErrorKind::ExtraBracket,
/// );
/// assert_eq!(spans_iter.next(), Some(Ok(Span::Text("and "))));
/// assert!(matches!(
///     spans_iter.next().unwrap().unwrap_err().kind,
///     SyntaxErrorKind::InvalidExpr(_),
/// ));
/// ```
/// Unclosed expressions cannot be recovered.
/// ```
/// # use mufmt::{Span, SyntaxErrorKind, TemplateSpans};
/// let mut spans_iter = TemplateSpans::<&str>::new("{unclosed");
///
/// assert_eq!(
///     spans_iter.next().unwrap().unwrap_err().kind,
///     SyntaxErrorKind::UnclosedExpr,
/// );
/// // the entire template string was consumed trying to find the closing bracket
/// assert!(spans_iter.next().is_none());
/// ```
///
/// ## Text span breaking
/// Approximately speaking, spans are produced to be as large as possible. However, since each span
/// must refer to a contiguous substring of the original template string (to avoid allocating), a text
/// span can be broken by an escaped bracket (either `{{` or `}}`).
///
/// ### Lazy escape breaking
/// Spans are broken *lazily*: the second char of an escaped bracket is included in the next
/// span. In particular, a text span does not contain `{` or `}` except possibly as the first
/// character of the span.
///
/// Here is an example illustrating this behaviour.
/// ```
/// # use mufmt::{Span, TemplateSpans};
/// let mut spans_iter = TemplateSpans::<usize>::new("Escaped {{bracket}}");
///
/// assert_eq!(spans_iter.next(), Some(Ok(Span::Text("Escaped "))));
/// assert_eq!(spans_iter.next(), Some(Ok(Span::Text("{bracket"))));
/// assert_eq!(spans_iter.next(), Some(Ok(Span::Text("}"))));
/// assert_eq!(spans_iter.next(), None);
/// ```
/// In particular, lazy span production rules mean that the representation may not be
/// absolutely minimal: the above example has an equivalent representation in which the second span
/// is `Span::Text("{bracket}")`. This representation will never be produced.
///
/// ### No spurious text spans
/// Text spans are guaranteed to be non-empty.
///
/// Here is an example illustrating this behaviour.
/// ```
/// # use mufmt::{Span, TemplateSpans};
/// let mut spans_iter = TemplateSpans::<usize>::new("{0}{1} {2}");
/// assert_eq!(spans_iter.next(), Some(Ok(Span::Expr(0))));
/// assert_eq!(spans_iter.next(), Some(Ok(Span::Expr(1))));
/// assert_eq!(spans_iter.next(), Some(Ok(Span::Text(" "))));
/// assert_eq!(spans_iter.next(), Some(Ok(Span::Expr(2))));
/// ```
///
/// ## Fused and bounded length
/// Each call to `.next()` is guaranteed to increment the parser position within the template
/// string, unless there are no characters remaining. In particular, [`TemplateSpans`] implements [`FusedIterator`](std::iter::FusedIterator).
///
/// Since the parser position increments, the number of steps in the iteration is at most
/// `self.remainder().len()`. This is reported by the `size_hint` implementation.
/// ```
/// # use mufmt::TemplateSpans;
/// let mut spans_iter = TemplateSpans::<&str>::new("Hello {name}!");
///
/// assert_eq!(spans_iter.remainder(), "Hello {name}!");
/// assert_eq!(spans_iter.size_hint(), (1, Some(spans_iter.remainder().len())));
///
/// let _ = spans_iter.next();
/// assert_eq!(spans_iter.remainder(), "{name}!");
/// assert_eq!(spans_iter.size_hint(), (1, Some(spans_iter.remainder().len())));
///
/// let _ = spans_iter.next();
/// assert_eq!(spans_iter.remainder(), "!");
/// assert_eq!(spans_iter.size_hint(), (1, Some(spans_iter.remainder().len())));
///
/// let _ = spans_iter.next();
/// assert_eq!(spans_iter.size_hint(), (0, Some(0)));
/// assert_eq!(spans_iter.remainder(), "");
/// assert!(spans_iter.next().is_none());
/// ```
/// The extremal conditions for `size_hint` are realized in the following cases.
/// ```
/// # use mufmt::TemplateSpans;
/// // A single text block
/// let mut spans_iter = TemplateSpans::<&str>::new("Only text");
/// assert_eq!(spans_iter.size_hint().0, spans_iter.count());
///
/// // An alternating sequence of text blocks and extra closing brackets (resulting in errors)
/// // attains the size hint limit
/// let mut spans_iter = TemplateSpans::<&str>::new("0}0}");
/// assert_eq!(spans_iter.size_hint().1, Some(spans_iter.count()));
/// ```
pub struct TemplateSpans<'fmt, A> {
    inner: Oneshot<'fmt>,
    _marker: PhantomData<A>,
}

impl<'fmt, A> TemplateSpans<'fmt, A>
where
    A: Ast<'fmt>,
{
    /// Initialize from a template string.
    pub fn new(s: &'fmt str) -> Self {
        Self {
            inner: Oneshot::new(s),
            _marker: PhantomData,
        }
    }

    /// Returns the part of the template string which has not yet been parsed.
    ///
    /// ## Example
    /// ```
    /// use mufmt::TemplateSpans;
    ///
    /// let spans_iter = TemplateSpans::<&str>::new("A template {expr}");
    /// ```
    pub fn remainder(&self) -> &'fmt str {
        self.inner.remainder()
    }
}

impl<'fmt, A> Iterator for TemplateSpans<'fmt, A>
where
    A: Ast<'fmt>,
{
    type Item = Result<Span<&'fmt str, A>, SyntaxError<A::Error>>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        Some(
            self.inner
                .next_span::<&str, A::Error>()
                .transpose()?
                .and_then(TryInto::try_into),
        )
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.remaining_parts_count()
    }
}

impl<'fmt, A: Ast<'fmt>> std::iter::FusedIterator for TemplateSpans<'fmt, A> {}

/// A template which can be rendered at most once.
///
/// In many cases, you want to use [`Template`] since the additional cost of preparing a
/// `Template` is relatively minimal (a single [`Vec`] allocation).
///
/// A [`Oneshot`] template provides the same render methods as a [`Template`]: [`Oneshot::render`],
/// [`Oneshot::render_io`], and [`Oneshot::render_fmt`]. The main difference is that these methods
/// accept `self` and return a more general [`Error`] type since parsing and rendering occur at the
/// same time.
///
/// ## Examples
/// Check syntax using [`Oneshot::validate`]:
/// ```
/// use mufmt::{Ast, Oneshot, types::IgnoredAny};
///
/// fn is_valid<'fmt, A: Ast<'fmt>>(s: &'fmt str) -> bool {
///     Oneshot::new(s).validate::<A>().is_ok()
/// }
///
/// // `IgnoredAny` is a special type which can be parsed from any expression
/// // and ignores the contents
/// assert!(is_valid::<IgnoredAny>("No errors {{ {expr}"));
/// assert!(!is_valid::<IgnoredAny>("Invalid: {{expr}"));
/// // validate expressions as `usize`
/// assert!(!is_valid::<usize>("Not a usize: {-100}"));
/// ```
pub struct Oneshot<'fmt> {
    // SAFETY: Must be bytes from valid str
    template: &'fmt [u8],
    // SAFETY: Must be <= template.len(), and correspond to a valid char offset (i.e.
    // self.template[self.cursor..] must return a valid string
    cursor: usize,
}

impl<'fmt> Oneshot<'fmt> {
    /// Initialize from a template string.
    pub fn new(s: &'fmt str) -> Self {
        Self {
            template: s.as_bytes(),
            cursor: 0,
        }
    }

    /// Consume this template, checking if the syntax is valid for the provided [`Ast`].
    ///
    /// This method only reports the first error encountered. If you want to report as many errors as
    /// possible, use a [`TemplateSpans`] iterator instead which supports [error
    /// recovery](TemplateSpans#error-recovery).
    ///
    /// ## Examples
    /// Validate template syntax.
    /// ```
    /// use mufmt::Oneshot;
    ///
    /// let oneshot = Oneshot::new("Valid {template}");
    /// assert!(oneshot.validate::<&str>().is_ok());
    ///
    /// let oneshot = Oneshot::new("{unclosed");
    /// assert!(oneshot.validate::<&str>().is_err());
    /// ```
    /// The provided `Ast` determines the expression validation rules.
    /// ```
    /// # use mufmt::Oneshot;
    /// let s = "Not a number: {template}";
    /// assert!(Oneshot::new(s).validate::<usize>().is_err());
    /// assert!(Oneshot::new(s).validate::<&str>().is_ok());
    /// ```
    /// Check that a template contains no expression blocks using [`Infallible`]:
    /// ```
    /// # use mufmt::Oneshot;
    /// use std::convert::Infallible;
    /// assert!(Oneshot::new("Contains an expr: {}").validate::<Infallible>().is_err());
    /// assert!(Oneshot::new("Only text!").validate::<Infallible>().is_ok());
    /// ```
    pub fn validate<A>(self) -> Result<(), SyntaxError<A::Error>>
    where
        A: Ast<'fmt>,
    {
        self.spans::<A>().try_for_each(|r| r.map(|_| ()))
    }

    /// Consumes this template, checking if the syntax is valid according to the global syntax
    /// rules (i.e., without checking the expressions).
    ///
    /// This is a shorthand for calling [`Oneshot::validate`] with `Ast` type
    /// [`IgnoredAny`](types::IgnoredAny).
    pub fn validate_any(self) -> Result<(), SyntaxError<Infallible>> {
        self.validate::<types::IgnoredAny>()
    }

    /// Returns an iterator over the spans corresponding to the underlying template string.
    ///
    /// See the [`TemplateSpans`] docs for more detail.
    pub fn spans<A>(self) -> TemplateSpans<'fmt, A>
    where
        A: Ast<'fmt>,
    {
        TemplateSpans {
            inner: self,
            _marker: PhantomData,
        }
    }

    /// A convenience function to render directly into a newly allocated `String`.
    ///
    /// This is equivalent to allocating a new `String` yourself and writing into it with
    /// [`render_fmt`](Self::render_fmt).
    pub fn render<A, M>(mut self, mfst: &M) -> Result<String, Error<A::Error, M::Error>>
    where
        A: Ast<'fmt>,
        M: Manifest<A>,
    {
        use std::fmt::Write as _;
        let mut buf = String::new();
        while let Some(spanned) = self.next_span()? {
            match TryInto::<Span<&'fmt str, A>>::try_into(spanned)? {
                Span::Text(s) => buf.push_str(s),
                Span::Expr(ast) => {
                    let _ = write!(&mut buf, "{}", mfst.manifest(&ast).map_err(Error::Render)?);
                }
            }
        }

        Ok(buf)
    }

    /// Write the template into the provided [`io::Write`] implementation.
    ///
    /// The writer is not flushed unless the [`Manifest`] implementation overrides the default
    /// [`Manifest::write_io`] implementation to manually flush the writer.
    pub fn render_io<A, M, W>(
        mut self,
        mfst: &M,
        mut writer: W,
    ) -> Result<(), Error<A::Error, M::Error>>
    where
        A: Ast<'fmt>,
        M: Manifest<A>,
        W: io::Write,
    {
        while let Some(spanned) = self.next_span()? {
            match TryInto::<Span<&'fmt str, A>>::try_into(spanned)? {
                Span::Text(s) => writer.write_all(s.as_bytes())?,
                Span::Expr(ast) => {
                    mfst.write_io(&ast, &mut writer)?;
                }
            }
        }

        Ok(())
    }

    /// Write the template into the provided [`fmt::Write`] implementation.
    pub fn render_fmt<A, M, W>(
        mut self,
        mfst: &M,
        mut writer: W,
    ) -> Result<(), Error<A::Error, M::Error>>
    where
        A: Ast<'fmt>,
        M: Manifest<A>,
        W: fmt::Write,
    {
        while let Some(spanned) = self.next_span()? {
            match TryInto::<Span<&'fmt str, A>>::try_into(spanned)? {
                Span::Text(s) => writer.write_str(s)?,
                Span::Expr(ast) => {
                    mfst.write_fmt(&ast, &mut writer)?;
                }
            }
        }

        Ok(())
    }

    /// The trailing characters which have not yet been parsed.
    fn remainder(&self) -> &'fmt str {
        // SAFETY: self.cursor is guaranteed to be a valid char index for the original string which
        // produced self.template
        unsafe { from_utf8_unchecked(self.template.get_unchecked(self.cursor..)) }
    }

    /// The size hint implementation.
    fn remaining_parts_count(&self) -> (usize, Option<usize>) {
        if self.cursor == self.template.len() {
            (0, Some(0))
        } else {
            (
                1,
                // SAFETY: self.cursor <= self.template.len() is the invariant
                Some(unsafe { self.template.len().unchecked_sub(self.cursor) }),
            )
        }
    }

    /// Extract the text corresponding to the provided range, along with the index at which the
    /// text starts.
    ///
    /// # Safety
    /// The provided range must be a valid start and end index for the original string from which
    /// self.template was constructed.
    unsafe fn get_unchecked(&self, range: std::ops::Range<usize>) -> &'fmt str {
        unsafe { from_utf8_unchecked(self.template.get_unchecked(range)) }
    }

    /// The core parsing logic.
    ///
    /// This method behaves like a fallible iterator of [`IndexedSpan`], each corresponding to a
    /// [`Span`], with some extra information about the offset within the input string.
    fn next_span<T, E>(&mut self) -> Result<Option<IndexedSpan<'fmt, T>>, SyntaxError<E>>
    where
        T: From<&'fmt str>,
    {
        unsafe {
            // SAFETY: self.cursor is guaranteed to be a valid index for the provided bytes
            let tail = self.template.get_unchecked(self.cursor..);
            match tail {
                [] => Ok(None),
                [b'{', b'{', ..] | [b'}', b'}', ..] => {
                    // single escaped bracket

                    // we opportunistically try to read as many characters as possible,
                    // as long as they are not more brackets

                    // SAFETY: we just checked that there is another byte which is an ASCII char
                    let text_start = self.cursor.unchecked_add(1);

                    // SAFETY: we just checked that there are two initial bytes which are ASCII
                    // char
                    let after_bracket_start = self.cursor.unchecked_add(2);

                    if let Some(offset) = memchr2(
                        b'{',
                        b'}',
                        // SAFETY: the two bytes we just read are ASCII char
                        self.template.get_unchecked(after_bracket_start..),
                    ) {
                        // SAFETY: offset returned is smaller than the length of the tail
                        let text_end = after_bracket_start.unchecked_add(offset);

                        // INVARIANT: text_start and text_end are both valid char offsets inside
                        // the buffer, since text_end is an index adjacent to one of the ASCII char
                        // '{' or '}'

                        // SAFETY: text_start and text_end are valid char offsets
                        let s = self.get_unchecked(text_start..text_end);
                        // SAFETY: text_end is a valid char offset
                        self.cursor = text_end;
                        Ok(Some(IndexedSpan {
                            span: Span::Text(s.into()),
                            offset: text_start,
                        }))
                    } else {
                        let res = Ok(Some(IndexedSpan {
                            span: Span::Text(
                                // SAFETY: text_start is a valid char offset
                                from_utf8_unchecked(&self.template.get_unchecked(text_start..))
                                    .into(),
                            ),
                            offset: text_start,
                        }));
                        self.cursor = self.template.len();
                        res
                    }
                }
                [b'}', ..] => {
                    // unexpected closing bracket which is not escaped
                    let err_start = self.cursor;
                    // SAFETY: we just checked that there is a valid ASCII byte
                    self.cursor = self.cursor.unchecked_add(1);
                    Err(SyntaxError {
                        span: err_start..self.cursor,
                        kind: SyntaxErrorKind::ExtraBracket,
                    })
                }
                [b'{', b'#', ..] => {
                    // extended expression

                    // we first count how many leading `#` characters there are
                    // SAFETY: we just checked that there are two a valid ASCII bytes
                    let hash_count = self
                        .template
                        .get_unchecked(self.cursor.unchecked_add(2)..)
                        .iter()
                        .take_while(|b| **b == b'#')
                        .count()
                        // SAFETY: we skipped two byte, so the maximum remaining bytes must be at
                        // most usize::MAX - 2, so this is valid
                        .unchecked_add(1);

                    // SAFETY: we count for the `{` and 1 for each hash `#`
                    let expr_start = self.cursor.unchecked_add(1).unchecked_add(hash_count);

                    // INVARIANT: expr_start is a valid char index and > self.cursor + 1

                    // SAFETY: the byte immediately after self.cursor is '{', and we have the
                    // expr_start invariant
                    let hash_patt = &self
                        .template
                        .get_unchecked(self.cursor.unchecked_add(1)..expr_start);

                    // SAFETY: expr_start is a valid char index
                    let tail = &self.template.get_unchecked(expr_start..);
                    for idx in memmem::find_iter(tail, hash_patt) {
                        // candidate end: check if the next byte is a closing bracket
                        // SAFETY: memmem only returns valid byte indices, and since `hash_patt`
                        // consists only of ASCII chars, the index is also a valid char index
                        let expr_end = expr_start.unchecked_add(idx);
                        // SAFETY: we know there are `hash_count` many bytes following, since this
                        // is the search pattern
                        if let Some(b'}') = self.template.get(expr_end.unchecked_add(hash_count)) {
                            let s = self.get_unchecked(expr_start..expr_end);
                            // SAFETY: expr_end is immediately followed by `hash_count` # and 1
                            // `}`, since we just checked this with `self.template.get`.
                            self.cursor = expr_end.unchecked_add(hash_count).unchecked_add(1);
                            return Ok(Some(IndexedSpan {
                                span: Span::Expr(s),
                                offset: expr_start,
                            }));
                        }
                    }
                    let err_start = self.cursor;
                    self.cursor = self.template.len();
                    Err(SyntaxError {
                        span: err_start..self.cursor,
                        kind: SyntaxErrorKind::UnclosedExpr,
                    })
                }
                [b'{', ..] => {
                    // normal expression

                    // SAFETY: the first byte is '{'
                    let expr_start = self.cursor.unchecked_add(1);
                    // SAFETY: the first byte is '{'
                    let tail = &self.template.get_unchecked(expr_start..);
                    match memchr(b'}', tail) {
                        Some(idx) => {
                            // SAFETY: the returned index is valid in `tail` which starts at
                            // position `expr_start` in the original slice
                            let expr_end = expr_start.unchecked_add(idx);
                            // SAFETY: they are both valid indices since they are adjacent to `{`
                            // and `}` bytes respectively
                            let s = self.get_unchecked(expr_start..expr_end);
                            // SAFETY: we found a `}`, so the next index is still valid
                            self.cursor = expr_end.unchecked_add(1);
                            Ok(Some(IndexedSpan {
                                span: Span::Expr(s),
                                offset: expr_start,
                            }))
                        }
                        None => {
                            // the expression is unclosed, so there is nothing else we can do
                            let err_start = self.cursor;
                            self.cursor = self.template.len();
                            Err(SyntaxError {
                                span: err_start..self.cursor,
                                kind: SyntaxErrorKind::UnclosedExpr,
                            })
                        }
                    }
                }
                _ => {
                    // text

                    // SAFETY: self.cursor is valid index
                    let tail = self.template.get_unchecked(self.cursor..);
                    if let Some(offset) = memchr2(b'{', b'}', tail) {
                        let text_start = self.cursor;
                        // SAFETY: we just found a '{' or '}'
                        let text_end = self.cursor.unchecked_add(offset);
                        self.cursor += offset;
                        // SAFETY: these are valid indices which are adjacent to ascii char bytes,
                        // so slicing is valid
                        let s = self.get_unchecked(text_start..text_end);
                        Ok(Some(IndexedSpan {
                            span: Span::Text(s.into()),
                            offset: text_start,
                        }))
                    } else {
                        let res = Ok(Some(IndexedSpan {
                            // SAFETY: self.cursor is valid index, and was used to produce 'tail'
                            span: Span::Text(from_utf8_unchecked(tail).into()),
                            offset: self.cursor,
                        }));
                        self.cursor = self.template.len();
                        res
                    }
                }
            }
        }
    }
}

/// A compiled representation of a template string with expression syntax defined by an [`Ast`].
///
/// Compile a template by providing a template string and an [`Ast`] using [`Template::compile`].
/// Once you have a template, render it using an appropriate [`Manifest`]:
///
/// - [`Template::render`] returns a [`String`].
/// - [`Template::render_io`] writes to an [`io::Write`] implementation, such as a
///   [`File`](std::fs::File) or [`stdout`](std::io::stdout)).
/// - [`Template::render_fmt`] writes to a [`fmt::Write`] implementation, such as a [`&mut String`](String) buffer.
///
/// Templates are immutable, but you can deconstruct and reconstruct a template using its
/// [`IntoIterator`] and [`FromIterator`] implementations.
///
/// ## Type parameters
/// A `Template` is generic over two type parameters:
///
/// - `T`: the template text type. For example, `T = &str` or `T = Box<str>`. These
///   cases are aliased in [`BorrowedTemplate`] and [`OwnedTemplate`]. `T` can
///   be any type which is `From<&'fmt str>` (when compiling) and `AsRef<str>` (when rendering).
/// - `A`: the compiled format of the expression. When compiling from a template string, this must
///   implement [`Ast`].
///
/// For example, if you want ownership:
/// ```
/// use mufmt::Template;
/// let template_str = "A {0}".to_owned();
///
/// // A template which owns all of its own data:
/// // - text stored as `String`
/// // - expressions compiled as `usize`
/// let template = Template::<String, usize>::compile(&template_str).unwrap();
///
/// // we can safely drop the original data
/// drop(template_str);
///
/// // and still use the template
/// let mfst = vec!["cat"];
/// assert_eq!(template.render(&mfst).unwrap(), "A cat");
/// ```
/// Or if you want to borrow:
/// ```
/// # use std::collections::HashMap;
/// # use mufmt::Template;
/// let template_str = "A {key}".to_owned();
///
/// // A template which borrows all of its data from the template string
/// let template = Template::<&str, &str>::compile(&template_str).unwrap();
///
/// // drop(template_str); // uncomment for compile error
///
/// let mfst = HashMap::from([("key", "cat")]);
/// assert_eq!(template.render(&mfst).unwrap(), "A cat");
/// ```
///
/// ## Template spans
/// A template is internally a [`Vec`] of [`Span`]s with additional metadata.
///
/// Access the spans with [`Template::spans`].
/// ```
/// # use mufmt::{Span, Template};
/// let template = Template::<&str, usize>::compile("Items {1} and {12}").unwrap();
/// // the implementation of `len` and `nth` efficient
/// assert_eq!(template.spans().len(), 4);
/// assert_eq!(template.spans().get(3), Some(&Span::Expr(12)));
/// ```
/// Then, modify the template by decomposing it into spans and then reconstructing it.
/// ```
/// # use mufmt::{Span, Template};
/// # let template = Template::<&str, usize>::compile("Items {1} and {12}").unwrap();
/// let mapped_template: Template<&str, usize> = template
///     // a template can be converted into an iterator of `Span`s.
///     .into_iter()
///     .map(|span| match span {
///         Span::Text(t) => Span::Text(t),
///         Span::Expr(b) => Span::Expr(b.max(4)),
///     })
///     // a template can be constructed from an iterator of `Span`s.
///     .collect();
/// assert_eq!(mapped_template.spans().get(1), Some(&Span::Expr(4)));
/// ```
/// Manually construct a template from an iterator of [`Span`]s.
/// ```
/// # use mufmt::{Span, Template};
/// let template: Template<&'static str, usize> =
///     [Span::Text("Hello "), Span::Expr(2), Span::Text("!")]
///         .into_iter()
///         .collect();
///
/// let mfst = ["Eero", "Aino", "Maija"];
///
/// assert_eq!(template.render(&mfst).unwrap(), "Hello Maija!");
/// ```
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct Template<T, A> {
    /// The text and expression spans of this template.
    inner: Vec<Span<T, A>>,
}

/// A type alias for a template which borrows from the template string.
pub type BorrowedTemplate<'fmt, A> = Template<&'fmt str, A>;

/// A type alias for a template which owns its own data.
pub type OwnedTemplate<A> = Template<Box<str>, A>;

impl<T, A> FromIterator<Span<T, A>> for Template<T, A> {
    fn from_iter<I: IntoIterator<Item = Span<T, A>>>(iter: I) -> Self {
        Self {
            inner: Vec::from_iter(iter),
        }
    }
}

impl<T, A> IntoIterator for Template<T, A> {
    type Item = Span<T, A>;

    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.inner.into_iter()
    }
}

impl<T, A> Template<T, A> {
    /// Compile the provided template string, interpreting the expressions using the `Ast`.
    #[inline]
    pub fn compile<'fmt>(s: &'fmt str) -> Result<Self, SyntaxError<A::Error>>
    where
        A: Ast<'fmt>,
        T: From<&'fmt str>,
    {
        TemplateSpans::new(s)
            .map(|r| r.map(|s| s.map_text(Into::into)))
            .collect()
    }

    /// A convenience function to render directly into a newly allocated `String`.
    ///
    /// This is equivalent to allocating a new `String` yourself and writing into it with
    /// [`render_fmt`](Self::render_fmt).
    pub fn render<M>(&self, mfst: &M) -> Result<String, M::Error>
    where
        T: AsRef<str>,
        M: Manifest<A>,
    {
        use std::fmt::Write;
        let mut buf = String::new();
        for span in self.spans() {
            match span {
                Span::Text(s) => {
                    buf.push_str(s.as_ref());
                }
                Span::Expr(ast) => {
                    let _ = write!(&mut buf, "{}", mfst.manifest(ast)?);
                }
            }
        }

        Ok(buf)
    }

    /// Write the compiled template into the provided [`io::Write`] implementation.
    ///
    /// The writer is not flushed unless the [`Manifest`] implementation overrides the default
    /// [`Manifest::write_io`] implementation to manually flush the writer.
    pub fn render_io<M, W>(&self, mfst: &M, mut writer: W) -> Result<(), IORenderError<M::Error>>
    where
        T: AsRef<[u8]>,
        M: Manifest<A>,
        W: io::Write,
    {
        for span in self.spans() {
            match span {
                Span::Text(s) => {
                    writer.write_all(s.as_ref())?;
                }
                Span::Expr(ast) => {
                    mfst.write_io(ast, &mut writer)?;
                }
            }
        }

        Ok(())
    }

    /// Write the compiled template into the provided [`fmt::Write`] implementation.
    pub fn render_fmt<M, W>(&self, mfst: &M, mut writer: W) -> Result<(), FmtRenderError<M::Error>>
    where
        T: AsRef<str>,
        M: Manifest<A>,
        W: fmt::Write,
    {
        for span in self.spans() {
            match span {
                Span::Text(s) => {
                    writer.write_str(s.as_ref())?;
                }
                Span::Expr(ast) => {
                    mfst.write_fmt(ast, &mut writer)?;
                }
            }
        }

        Ok(())
    }

    /// Returns a slice of the template spans.
    ///
    /// If this template was compiled using [`Template::compile`], the spans will satisfy
    /// [precise text breaking rules](TemplateSpans#text-span-breaking).
    #[inline]
    pub fn spans(&self) -> &[Span<T, A>] {
        &self.inner
    }
}
