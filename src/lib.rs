//! # μfmt
//!
//! μfmt (`mufmt`) is a minimal and extensible runtime formatting library.
//!
//! μfmt defines a runtime formatting interface which allows arbitrary types to define a
//! formatting syntax and compiled format corresponding to a runtime-provided template.
//!
//! The main API entrypoints are [`Template`], [`Ast`], and [`Context`].
//!
//! - [Introduction](#introduction): for a quick introduction and basic usage
//! - [Template Syntax](#syntax): to understand the global syntax rules
//! - [API Introduction](#api-introduction): for a detailed introduction to writing your own
//!   format.
//! - [Built-in implementats](#built-in-implementations): for a summary of the [`Ast`] and
//!   [`Context`] implementations included by default.
//!
//! ## Introduction
//! μfmt templates are similar to Rust format strings:
//! ```
//! "Hello {name}!";
//! ```
//! Parts outside brackets are referred to as *text* and parts inside brackets are referred to as
//! *blocks*. See [syntax](#syntax) for a full description of the syntax.
//!
//! However, μfmt does not interpret the contents of blocks. Instead, the block syntax is
//! *type-driven*: template rendering is defined using the provided rendering context.
//! ```
//! use mufmt::Template;
//! use std::collections::HashMap;
//!
//! let template = Template::compile("Hello {name}!").unwrap();
//! let ctx = HashMap::from([("name", "John")]);
//!
//! assert_eq!(template.render(&ctx).unwrap(), "Hello John!");
//! ```
//! In this example, the `{name}` block is parsed as a string: `"name"`. The parsing rules are
//! defined by the [`Context`] implementation of `HashMap<&'static str, &'static str>`. This
//! context expects raw strings which correspond to map keys.
//!
//! Suppose we instead provide a [`Vec`] as the context. Then the keys are instead parsed as `usize`.
//! In this example, we also see that same template can be re-used with a new context without
//! requiring recompilation of the template.
//! ```
//! # use mufmt::Template;
//! let template = Template::compile("Letter: {1}").unwrap();
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
//! assert!(Template::<usize>::compile("{-100}").is_err()); // SyntaxError::Ast(ParseIntError, ...)
//! assert!(Template::<i8>::compile("{-100}").is_ok());
//! ```
//! Passing a template with the incorrect block type will result in a compilation error.
//! ```compile_fail
//! # use mufmt::Template;
//! let ctx = HashMap::from([("123", "456")]);
//! // a `HashMap` expects an `&str`, not a `usize`
//! let template = Template::<usize>::compile("Number: {123}").unwrap();
//! template.render(&ctx);
//! ```
//!
//! ## Syntax
//! A μfmt template is just a rust `str` where bracket-delimited blocks `{...}` are replaced with values
//! when the string is rendered.
//!
//! 1. The template not inside a block are referred to as *text*,  and the parts inside a block are
//!    referred to as *blocks*.
//! 2. Blocks are whitespace trimmed according to the rules of [`trim`](str::trim).
//! 3. To include brackets inside *text*, repeating the bracket (like `{{`) results in text
//!    consisting of a single bracket.
//! 4. To include brackets inside *blocks*, you can use *extended block delimiters*: the initial
//!    `{` of a block may be followed by any number of `#` characters. Then, the block can only be
//!    closed by an equal number of `#` characters, followed by `}`.
//!
//! Otherwise, the interpretation of contents of the blocks are defined by the specific implementation.
//!
//! Here are examples for each of the above points.
//!
//! 1. `"Hello {name}!"` is text `Hello `, then a block `name`, then text `!`.
//! 2. `"Hello { name  }!"` is equivalent to the above example.
//! 3. `"{{{contents}"` is text `{{`, then a block `contents`.
//! 4. `"{## #}##}"` is a block `#}`.
//!
//! ## API introduction
//! Broadly speaking, template rendering is split into two independent phases.
//!
//! 1. A template string `"Hello {name}"` is compiled by the μfmt parsing rules and the block
//!    parsing rules defined by the [`Ast`] implementation. The compiled representation is a
//!    [`Template`] and an error during this phase is a [`SyntaxError`].
//! 2. The compiled template is combined with additional data via a [`Context`]
//!    implementation to obtain a type which can be displayed. An error during this phase
//!    is a [`RenderError`].
//!
//! The precise dividing line between where the `Ast` parsing ends and template rendering begins
//! depends on the use-case. At one extreme, one could simply use a `&'fmt str` and then perform
//! all parsing within the [`Context`] implementation. In this case, compilation is guaranteed to
//! succeed as long as the template string matches the general syntax.
//!
//! On the other hand, if a single template is rendered a very large number of times, there can
//! be a substantial gain in performance by doing as much work as possible up-front.
//!
//! ### An example template language
//! To understand how these two phases interact, let's define a custom template language. The idea
//! will be as follows:
//! - The user will provide blocks of the form `{<str>:<u8>}`, which is then
//!   formatted to repeat the provided `<str>` `<u8>` times. For example, the
//!   template `"{ AB : 3 }"` renders to `ABABAB`.
//! - Since we don't want the strings to be too long, we will provide an additional
//!   `u8` which will specify a limit for the number of repetitions.
//!
//! First, we must determine our intermediate [`Ast`] type. The natural candidate here is a tuple
//! `(&'fmt, u8)`.
//!
//! Then, we define our [`Context`]. This is a single `u8` which defines the limit of the
//! number of repetitions.
//! ```
//! use std::{fmt, num::ParseIntError};
//! use mufmt::{Ast, Context, Template, error::RenderError};
//!
//! /// The string to be repeated along with the number of repetitions.
//! struct Repeat<'fmt>(&'fmt str, u8);
//!
//! #[derive(Debug)]
//! enum Error {
//!     /// Failed to parse the int
//!     InvalidInt(ParseIntError),
//!     /// Missing the `:` delimeter
//!     MissingDelimeter,
//! }
//!
//! impl<'fmt> Ast<'fmt> for Repeat<'fmt> {
//!     type Error = Error;
//!
//!     /// Parse a block of the form `{<str> : <u8>}`
//!     fn parse(block: &'fmt str) -> Result<Self, Self::Err> {
//!         match block.split_once(':') {
//!             Some((left, right)) => {
//!                 // parse the u8 using `u8::from_str`
//!                 let count = right.trim().parse().map_err(Error::InvalidInt)?;
//!
//!                 Ok(Self(left.trim(), count))
//!             }
//!             None => Err(Error::MissingDelimeter),
//!         }
//!     }
//! }
//!
//! /// Implement `Display` so we can use it as the return type for `Context::render`
//! /// as well.
//! impl<'fmt> fmt::Display for Repeat<'fmt> {
//!     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//!         for _ in 0..self.1 {
//!             f.write_str(self.0)?;
//!         }
//!         Ok(())
//!     }
//! }
//!
//!
//! /// The context information used to render the `Ast`
//! struct Limit(u8);
//!
//! impl Context for Limit {
//!     type Ast<'fmt> = Repeat<'fmt>;
//!
//!     fn render(
//!         &self,
//!         ast: &Self::Ast<'_>,
//!     ) -> Result<impl fmt::Display, RenderError> {
//!         // limit the number of repetitions to the provided value
//!         let reps = ast.1.min(self.0);
//!         Ok(Repeat(ast.0, reps))
//!     }
//! }
//!
//! let template = Template::compile("{%: 7}!").unwrap();
//!
//! assert_eq!(template.render(&Limit(10)).unwrap(), "%%%%%%%!");
//! assert_eq!(template.render(&Limit(3)).unwrap(), "%%%!");
//! ```
//!
//! ## Built-in implementations
//!
//! ### `Ast` implementations
//! 1. An `&'fmt str` implements `Ast` by reading the contents of the block (recalling that the
//!    block automatically whitespace trimmed).
//! 2. The following types implement `Ast` using their [`FromStr`](std::str::FromStr) implementation:
//!    - All `u*` and `i*` numeric types, along with their `NonZero<...>` variants.
//!    - The float types: `f32` and `f64`.
//! 3. A [`BoundedInt`](ast::BoundedInt), which is a wrapper around a `usize` which is guaranteed
//!    to be smaller than a provided const bound.
//!
//! ### `Context` implementations
//! 1. [`HashMap`](std::collections::HashMap) and [`BTreeMap`](std::collections::BTreeMap), with
//!    keys which can be read from `&'fmt str`, and values which implement
//!    [`Display`](fmt::Display). Accepts an `&'fmt str`.
//!    and read the corresponding value (if any). Returns an error if the key is missing.
//! 2. [`Vec`] and [`VecDeque`](std::collections::VecDeque) with values which implement
//!    [`Display`](fmt::Display). Accepts a `usize`. Returns an error if the index is out of range.
//! 3. Slice types `&'a [T]`, `&'a mut [T]`, and `[T]` with values which implement
//!    [`Display`](fmt::Display). Their [`Context`] implementations accept a `usize`. Returns
//!    an error if the index is out of range.
//! 4. [`[T; N]`](std::array) with values which implement [`Display`](fmt::Display). Their
//!    [`Context`] implementations accept a [`BoundedInt`](ast::BoundedInt). In particular, range
//!    bounds are checked at template compile time and this does not produce runtime errors.

#![deny(missing_docs)]

pub mod ast;
pub mod error;
#[cfg(test)]
mod tests;

use error::{RenderError, SyntaxError};

use memchr::{memchr, memchr2, memmem};
use std::{fmt, io, str::from_utf8_unchecked};

/// A typed representation of a block which does not interpret the contents.
///
/// The role of an `Ast` is to perform as much validation as possible, without any knowledge of the
/// [`Context`] which may later use it. The correct balance here depends, of course, on the
/// particular use-case.
///
/// ### Example
/// A [`HashMap`](std::collections::HashMap) uses `&str` as its `Ast` implementation.
/// An `&str` is not aware at all of the contents of a block, except that it should interpret it as
/// a string. In contrast, if we are aware that the keys must come from a specific list, we can
/// check that this is the case when the template is compiled.
/// ```
/// use mufmt::{Ast, Template};
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
///     fn parse(block: &str) -> Result<Self, Self::Err> {
///         // blocks are whitespace trimmed, so we don't need to handle this here
///         match block {
///             "red" => Ok(Self::Red),
///             "green" => Ok(Self::Green),
///             "blue" => Ok(Self::Blue),
///             s => Err(InvalidColor(s.to_owned())),
///         }
///     }
/// }
///
/// assert!(Template::<Color>::compile("My favourite colors are {blue} and { green }!").is_ok());
/// assert!(Template::<Color>::compile("The sky is very {orange}!").is_err());
/// ```
pub trait Ast<'fmt>: Sized {
    /// An error which may occur while parsing a block.
    type Error;

    /// Parse the `Ast` from the block contents.
    fn parse(block: &'fmt str) -> Result<Self, Self::Error>;
}

/// Context provided to render the `Ast` to a new string.
pub trait Context {
    /// The compiled representation accepted by this context.
    type Ast<'fmt>: Ast<'fmt>;

    /// An error which is produced when rendering.
    type Error;

    /// Convert the `Ast` to a type which can be displayed.
    ///
    /// The rendered format is ephemeral.
    fn render(&self, ast: &Self::Ast<'_>) -> Result<impl fmt::Display, Self::Error>;
}

#[derive(Debug, PartialEq)]
enum Part<'fmt, A> {
    Text(&'fmt str),
    Block(A),
}

#[derive(Debug, PartialEq)]
struct SpannedPart<'fmt> {
    part: Part<'fmt, &'fmt str>,
    offset: usize,
}

impl<'fmt, A: Ast<'fmt>> TryFrom<SpannedPart<'fmt>> for Part<'fmt, A> {
    type Error = SyntaxError<A::Error>;

    fn try_from(spanned: SpannedPart<'fmt>) -> Result<Self, Self::Error> {
        Ok(match spanned.part {
            Part::Text(s) => Part::Text(s),
            Part::Block(s) => Part::Block(
                A::parse(s.trim())
                    .map_err(|e| SyntaxError::Ast(e, spanned.offset..spanned.offset + s.len()))?,
            ),
        })
    }
}

/// A template which can be used exactly once.
///
/// In most cases, you just want to use [`Template`] since the additional cost of preparing a
/// `Template` is relatively minimal (a single extra [`Vec`] allocation).
pub struct Oneshot<'fmt> {
    // SAFETY: Must be bytes from valid str
    template: &'fmt [u8],
    // SAFETY: Must correspond to a valid str index in the string from which `template` was
    // produced.
    cursor: usize,
}

impl<'fmt> Oneshot<'fmt> {
    fn new(s: &'fmt str) -> Self {
        Self {
            template: s.as_bytes(),
            cursor: 0,
        }
    }

    /// Extract the text corresponding to the provided range, along with the index at which the
    /// text starts.
    unsafe fn get_unchecked(&self, range: std::ops::Range<usize>) -> &'fmt str {
        unsafe { from_utf8_unchecked(self.template.get_unchecked(range)) }
    }

    fn next_part<E>(&mut self) -> Result<Option<SpannedPart<'fmt>>, SyntaxError<E>> {
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
                    Ok(Some(SpannedPart {
                        part: Part::Text(s),
                        offset: text_start,
                    }))
                } else {
                    let res = Ok(Some(SpannedPart {
                        part: Part::Text(unsafe {
                            from_utf8_unchecked(&self.template[text_start..])
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
                // extended block

                // we first count how many leading `#` characters there are
                let hash_count = self.template[self.cursor + 2..]
                    .iter()
                    .take_while(|b| **b == b'#')
                    .count()
                    + 1;
                let block_start = self.cursor + 1 + hash_count;
                let hash_patt = &self.template[self.cursor + 1..block_start];

                let tail = &self.template[block_start..];
                for idx in memmem::find_iter(tail, hash_patt) {
                    // candidate end: check if the next byte is a closing bracket
                    let block_end = block_start + idx;
                    if let Some(b'}') = self.template.get(block_end + hash_count) {
                        let s = unsafe { self.get_unchecked(block_start..block_end) };
                        self.cursor = block_end + hash_count + 1;
                        return Ok(Some(SpannedPart {
                            part: Part::Block(s),
                            offset: block_start,
                        }));
                    }
                }
                Err(SyntaxError::UnclosedBlock(self.cursor))
            }
            [b'{', ..] => {
                // normal block

                let block_start = self.cursor + 1;
                let tail = &self.template[block_start..];
                match memchr(b'}', tail) {
                    Some(idx) => {
                        let block_end = block_start + idx;
                        let s = unsafe { self.get_unchecked(block_start..block_end) };
                        self.cursor = block_end + 1;
                        Ok(Some(SpannedPart {
                            part: Part::Block(s),
                            offset: block_start,
                        }))
                    }
                    None => Err(SyntaxError::UnclosedBlock(self.cursor)),
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
                    Ok(Some(SpannedPart {
                        part: Part::Text(s),
                        offset: text_start,
                    }))
                } else {
                    let res = Ok(Some(SpannedPart {
                        part: Part::Text(unsafe { from_utf8_unchecked(tail) }),
                        offset: self.cursor,
                    }));
                    self.cursor = self.template.len();
                    res
                }
            }
        }
    }
}

/// A compiled representation of a template string, with block syntax defined by the [`Ast`].
pub struct Template<'fmt, A: Ast<'fmt>> {
    parts: Vec<Part<'fmt, A>>,
}

impl<'fmt, A> TryFrom<Oneshot<'fmt>> for Template<'fmt, A>
where
    A: Ast<'fmt>,
{
    type Error = SyntaxError<A::Error>;

    fn try_from(mut value: Oneshot<'fmt>) -> Result<Self, Self::Error> {
        let mut parts = Vec::new();
        while let Some(pair) = value.next_part()? {
            parts.push(pair.try_into()?);
        }
        Ok(Self { parts })
    }
}

impl<'fmt, A: Ast<'fmt>> Template<'fmt, A> {
    /// Compile the provided template string, interpreting the blocks using the `Ast`.
    pub fn compile(s: &'fmt str) -> Result<Self, SyntaxError<A::Error>> {
        let oneshot = Oneshot::new(s);
        oneshot.try_into()
    }

    /// A convenience function to render directly into a newly allocated `String`.
    ///
    /// This is equivalent to allocating a new `String` yourself and writing into it with
    /// [`render_fmt`](Self::render_fmt).
    pub fn render<C>(&self, ctx: &C) -> Result<String, C::Error>
    where
        C: Context<Ast<'fmt> = A>,
    {
        use std::fmt::Write;

        let mut buf = String::new();
        for part in self.parts.iter() {
            match part {
                Part::Text(s) => {
                    buf.push_str(s);
                }
                Part::Block(ast) => {
                    let _ = write!(&mut buf, "{}", ctx.render(ast)?);
                }
            }
        }

        Ok(buf)
    }

    /// Write the compiled template into the provided [`io::Write`] implementation.
    pub fn render_io<C, W>(&self, ctx: &C, mut writer: W) -> Result<(), RenderError<C::Error>>
    where
        C: Context<Ast<'fmt> = A>,
        W: io::Write,
    {
        for part in self.parts.iter() {
            match part {
                Part::Text(s) => {
                    writer.write_all(s.as_bytes())?;
                }
                Part::Block(ast) => {
                    write!(writer, "{}", ctx.render(ast).map_err(RenderError::Custom)?)?;
                }
            }
        }

        Ok(())
    }

    /// Write the compiled template into the provided [`fmt::Write`] implementation.
    pub fn render_fmt<C, W>(&self, ctx: &C, mut writer: W) -> Result<(), RenderError<C::Error>>
    where
        C: Context<Ast<'fmt> = A>,
        W: fmt::Write,
    {
        for part in self.parts.iter() {
            match part {
                Part::Text(s) => {
                    writer.write_str(s)?;
                }
                Part::Block(ast) => {
                    write!(writer, "{}", ctx.render(ast).map_err(RenderError::Custom)?)?;
                }
            }
        }

        Ok(())
    }
}
