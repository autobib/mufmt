//! # μfmt
//!
//! μfmt (`mufmt`) is a minimal and extensible runtime formatting library.
//!
//! μfmt allows arbitrary types to define a formatting syntax and compiled template
//! format. μfmt also provides a number of built-in formats, backed by data stored in
//! collection types like [`HashMap`](std::collections::HashMap) or [`Vec`].
//!
//! The main API entrypoints are [`Template`], [`Ast`], and [`Manifest`].
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
//! let ctx = HashMap::from([("name", "John")]);
//!
//! assert_eq!(template.render(&ctx).unwrap(), "Hello John!");
//! ```
//! In this example, the `{name}` expression is parsed as a string: `"name"`. The parsing rules are
//! defined by the [`Manifest`] implementation of the `HashMap`, which expects raw strings which
//! correspond to map keys. In general, the type is the associated [`Ast`] implementation.
//!
//! Suppose we instead provide a [`Vec`] as the context. Then the keys are instead parsed as `usize`.
//! In this example, we also see that same template can be re-used with a new context without
//! requiring recompilation of the template.
//! ```
//! # use mufmt::BorrowedTemplate;
//! // we don't need a type annotation here since `Vec` only accepts `usize` as the key
//! let template = BorrowedTemplate::compile("Letter: {1}").unwrap();
//! let ctx = vec!["α", "β", "γ"];
//!
//! let mut buf = String::new();
//! template.render_fmt(&ctx, &mut buf).unwrap();
//! assert_eq!(buf, "Letter: β");
//!
//! // we define a new context: but now, a `Vec<char>` instead of `Vec<&'static string>`
//! let new_ctx = vec!['a', 'b', 'c'];
//!
//! // this works since (for `Vec`) the key type does not depend on the type in the container
//! buf.clear();
//! template.render_fmt(&new_ctx, &mut buf).unwrap();
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
//! let ctx = HashMap::from([("123", "456")]);
//! // a `HashMap` expects an `&str`, not a `usize`
//! let template = BorrowedTemplate::<usize>::compile("Number: {123}").unwrap();
//! template.render(&ctx);
//! ```
//!
//! ## Syntax
//! A μfmt template is just a rust `str` where bracket-delimited expressions `{...}` are replaced with values
//! when the string is rendered.
//!
//! 1. The template not inside an expression are referred to as *text*,  and the parts inside an expression are
//!    referred to as *expressions*.
//! 2. expressions are whitespace trimmed according to the rules of [`trim`](str::trim).
//! 3. To include brackets inside *text*, repeating the bracket (like `{{`) results in text
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
//! 1. A template string `"Hello {name}"` is compiled by the μfmt parsing rules and the expression
//!    parsing rules defined by the [`Ast`] implementation. The compiled representation is a
//!    [`Template`] and an error during this phase is a [`SyntaxError`].
//! 2. The compiled template is combined with additional data via a [`Manifest`]
//!    implementation to obtain a type which can be displayed. An error during this phase
//!    is a [`RenderError`].
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

#![deny(missing_docs)]

mod error;
#[cfg(test)]
mod tests;
pub mod types;

pub use error::{Error, RenderError, SyntaxError};

use memchr::{memchr, memchr2, memmem};
use std::{fmt, io, str::from_utf8_unchecked};

/// A typed representation of an expression which does not interpret the contents.
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

/// Manifest provided to render the `Ast` to a new string.
pub trait Manifest<A> {
    /// An error which is produced when rendering.
    type Error;

    /// Convert the `Ast` to a type which can be displayed.
    ///
    /// The rendered format is ephemeral.
    fn manifest(&self, ast: &A) -> Result<impl fmt::Display, Self::Error>;
}

/// A component of a template.
///
/// Internally, a [`Template`] is a [`Vec`] of [`Span`]s, which correspond to subsequent
/// expressions.
/// The spans can be accessed
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
}

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
            Span::Expr(s) => Self::Expr(
                A::from_expr(s.trim())
                    .map_err(|e| SyntaxError::Ast(e, spanned.offset..spanned.offset + s.len()))?,
            ),
        })
    }
}

/// A template which can be rendered at most once.
///
/// In most cases, you want to use [`Template`] since the additional cost of preparing a
/// `Template` is relatively minimal (a single [`Vec`] allocation).
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
    // SAFETY: Must correspond to a valid str index in the string from which `template` was
    // produced.
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
    pub fn validate<A>(mut self) -> Result<(), SyntaxError<A::Error>>
    where
        A: Ast<'fmt>,
    {
        while let Some(spanned) = self.next_span()? {
            let _ = TryInto::<Span<&'fmt str, A>>::try_into(spanned)?;
        }
        Ok(())
    }

    /// A convenience function to render directly into a newly allocated `String`.
    ///
    /// This is equivalent to allocating a new `String` yourself and writing into it with
    /// [`render_fmt`](Self::render_fmt).
    pub fn render<A, C>(mut self, ctx: &C) -> Result<String, Error<A::Error, C::Error>>
    where
        A: Ast<'fmt>,
        C: Manifest<A>,
    {
        use std::fmt::Write;
        let mut buf = String::new();
        while let Some(spanned) = self.next_span()? {
            match TryInto::<Span<&'fmt str, A>>::try_into(spanned)? {
                Span::Text(s) => buf.push_str(s),
                Span::Expr(ast) => {
                    let _ = write!(
                        &mut buf,
                        "{}",
                        ctx.manifest(&ast).map_err(RenderError::Render)?
                    );
                }
            }
        }

        Ok(buf)
    }

    /// Write the template into the provided [`io::Write`] implementation.
    pub fn render_io<A, C, W>(
        mut self,
        ctx: &C,
        mut writer: W,
    ) -> Result<(), Error<A::Error, C::Error>>
    where
        A: Ast<'fmt>,
        C: Manifest<A>,
        W: io::Write,
    {
        while let Some(spanned) = self.next_span()? {
            match TryInto::<Span<&'fmt str, A>>::try_into(spanned)? {
                Span::Text(s) => writer.write_all(s.as_bytes())?,
                Span::Expr(ast) => {
                    let _ = write!(
                        writer,
                        "{}",
                        ctx.manifest(&ast).map_err(RenderError::Render)?
                    );
                }
            }
        }

        Ok(())
    }

    /// Write the template into the provided [`fmt::Write`] implementation.
    pub fn render_fmt<A, C, W>(
        mut self,
        ctx: &C,
        mut writer: W,
    ) -> Result<(), Error<A::Error, C::Error>>
    where
        A: Ast<'fmt>,
        C: Manifest<A>,
        W: fmt::Write,
    {
        while let Some(spanned) = self.next_span()? {
            match TryInto::<Span<&'fmt str, A>>::try_into(spanned)? {
                Span::Text(s) => writer.write_str(s)?,
                Span::Expr(ast) => {
                    let _ = write!(
                        writer,
                        "{}",
                        ctx.manifest(&ast).map_err(RenderError::Render)?
                    );
                }
            }
        }

        Ok(())
    }

    /// Extract the text corresponding to the provided range, along with the index at which the
    /// text starts.
    unsafe fn get_unchecked(&self, range: std::ops::Range<usize>) -> &'fmt str {
        unsafe { from_utf8_unchecked(self.template.get_unchecked(range)) }
    }

    /// The core parsing logic.
    fn next_span<T, E>(&mut self) -> Result<Option<IndexedSpan<'fmt, T>>, SyntaxError<E>>
    where
        T: From<&'fmt str>,
    {
        // check what we are parsing
        let tail = unsafe { self.template.get_unchecked(self.cursor..) };
        match tail {
            [] => Ok(None),
            [b'{', b'{', ..] | [b'}', b'}', ..] => {
                // single escaped bracket

                // we opportunistically try to read as many characters as possible,
                // as long as they are not more brackets
                let text_start = self.cursor + 1;

                if let Some(offset) = memchr2(b'{', b'}', unsafe {
                    self.template.get_unchecked(self.cursor + 2..)
                }) {
                    let text_end = self.cursor + 2 + offset;
                    let s = unsafe { self.get_unchecked(text_start..text_end) };
                    self.cursor = text_end;
                    Ok(Some(IndexedSpan {
                        span: Span::Text(s.into()),
                        offset: text_start,
                    }))
                } else {
                    let res = Ok(Some(IndexedSpan {
                        span: Span::Text(unsafe {
                            from_utf8_unchecked(&self.template[text_start..]).into()
                        }),
                        offset: text_start,
                    }));
                    self.cursor = self.template.len();
                    res
                }
            }
            [b'}', ..] => {
                // unexpected closing bracket which is not escaped

                Err(SyntaxError::ExtraBracket(self.cursor))
            }
            [b'{', b'#', ..] => {
                // extended expression

                // we first count how many leading `#` characters there are
                let hash_count = self.template[self.cursor + 2..]
                    .iter()
                    .take_while(|b| **b == b'#')
                    .count()
                    + 1;
                let expr_start = self.cursor + 1 + hash_count;
                let hash_patt = &self.template[self.cursor + 1..expr_start];

                let tail = &self.template[expr_start..];
                for idx in memmem::find_iter(tail, hash_patt) {
                    // candidate end: check if the next byte is a closing bracket
                    let expr_end = expr_start + idx;
                    if let Some(b'}') = self.template.get(expr_end + hash_count) {
                        let s = unsafe { self.get_unchecked(expr_start..expr_end) };
                        self.cursor = expr_end + hash_count + 1;
                        return Ok(Some(IndexedSpan {
                            span: Span::Expr(s),
                            offset: expr_start,
                        }));
                    }
                }
                Err(SyntaxError::UnclosedExpr(self.cursor))
            }
            [b'{', ..] => {
                // normal expression

                let expr_start = self.cursor + 1;
                let tail = &self.template[expr_start..];
                match memchr(b'}', tail) {
                    Some(idx) => {
                        let expr_end = expr_start + idx;
                        let s = unsafe { self.get_unchecked(expr_start..expr_end) };
                        self.cursor = expr_end + 1;
                        Ok(Some(IndexedSpan {
                            span: Span::Expr(s),
                            offset: expr_start,
                        }))
                    }
                    None => Err(SyntaxError::UnclosedExpr(self.cursor)),
                }
            }
            _ => {
                // text
                let tail = unsafe { self.template.get_unchecked(self.cursor..) };
                if let Some(offset) = memchr2(b'{', b'}', tail) {
                    let text_start = self.cursor;
                    let text_end = self.cursor + offset;
                    self.cursor += offset;
                    let s = unsafe { self.get_unchecked(text_start..text_end) };
                    Ok(Some(IndexedSpan {
                        span: Span::Text(s.into()),
                        offset: text_start,
                    }))
                } else {
                    let res = Ok(Some(IndexedSpan {
                        span: Span::Text(unsafe { from_utf8_unchecked(tail).into() }),
                        offset: self.cursor,
                    }));
                    self.cursor = self.template.len();
                    res
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
/// ## Type parameters
/// A `Template` is generic over two type parameters:
///
/// - `T`: the template text type. Typically, `T = &str` (when you want to
///   borrow from the template string) or `T = String` (when you want ownership). These
///   cases are aliased in [`BorrowedTemplate`] and [`OwnedTemplate`]. `T` can
///   be any type which is `From<&'fmt str>` (when compiling) and `AsRef<str>` (when rendering).
/// - `A`: the compiled format of the expression. When compiling from a template string, this must
///   implement [`Ast`].
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
/// let ctx = ["Eero", "Aino", "Maija"];
///
/// assert_eq!(template.render(&ctx).unwrap(), "Hello Maija!");
/// ```
///
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct Template<T, A> {
    /// The text and expression spans of this template.
    inner: Vec<Span<T, A>>,
}

/// A type alias for a template which borrows from the template string.
pub type BorrowedTemplate<'fmt, A> = Template<&'fmt str, A>;

/// A type alias for a template which owns its own data.
pub type OwnedTemplate<A> = Template<String, A>;

impl<'fmt, T, A> TryFrom<Oneshot<'fmt>> for Template<T, A>
where
    T: From<&'fmt str>,
    A: Ast<'fmt>,
{
    type Error = SyntaxError<A::Error>;

    fn try_from(mut value: Oneshot<'fmt>) -> Result<Self, Self::Error> {
        let mut inner = Vec::new();
        while let Some(spanned) = value.next_span()? {
            inner.push(spanned.try_into()?);
        }
        Ok(Self { inner })
    }
}

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
        let oneshot = Oneshot::new(s);
        oneshot.try_into()
    }

    /// A convenience function to render directly into a newly allocated `String`.
    ///
    /// This is equivalent to allocating a new `String` yourself and writing into it with
    /// [`render_fmt`](Self::render_fmt).
    pub fn render<C>(&self, ctx: &C) -> Result<String, C::Error>
    where
        T: AsRef<str>,
        C: Manifest<A>,
    {
        use std::fmt::Write;
        let mut buf = String::new();
        for span in self.spans() {
            match span {
                Span::Text(s) => {
                    buf.push_str(s.as_ref());
                }
                Span::Expr(ast) => {
                    let _ = write!(&mut buf, "{}", ctx.manifest(ast)?);
                }
            }
        }

        Ok(buf)
    }

    /// Write the compiled template into the provided [`io::Write`] implementation.
    pub fn render_io<C, W>(&self, ctx: &C, mut writer: W) -> Result<(), RenderError<C::Error>>
    where
        T: AsRef<[u8]>,
        C: Manifest<A>,
        W: io::Write,
    {
        for span in self.spans() {
            match span {
                Span::Text(s) => {
                    writer.write_all(s.as_ref())?;
                }
                Span::Expr(ast) => {
                    write!(
                        writer,
                        "{}",
                        ctx.manifest(ast).map_err(RenderError::Render)?
                    )?;
                }
            }
        }

        Ok(())
    }

    /// Write the compiled template into the provided [`fmt::Write`] implementation.
    pub fn render_fmt<C, W>(&self, ctx: &C, mut writer: W) -> Result<(), RenderError<C::Error>>
    where
        T: AsRef<str>,
        C: Manifest<A>,
        W: fmt::Write,
    {
        for span in self.spans() {
            match span {
                Span::Text(s) => {
                    writer.write_str(s.as_ref())?;
                }
                Span::Expr(ast) => {
                    write!(
                        writer,
                        "{}",
                        ctx.manifest(ast).map_err(RenderError::Render)?
                    )?;
                }
            }
        }

        Ok(())
    }

    /// Returns a slice of the template spans.
    #[inline]
    pub fn spans(&self) -> &[Span<T, A>] {
        &self.inner
    }
}
