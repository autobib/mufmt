//! # Errors during template compilation and rendering
//!
//! This module contains a variety of error types which can occur while compiling or rendering
//! templates.
//!
//! The [`SyntaxError`], [`IORenderError`], [`FmtRenderError`], and [`Error`] contain generics to propogate errors
//! which may result from a particular [`Ast`](crate::Ast) or [`Manifest`](crate::Manifest) implementation.

use std::{
    convert::Infallible,
    fmt::{self},
    io,
    ops::Range,
};

/// An error while compiling a template string.
///
/// A syntax error also contains range information concerning the location in the template string
/// from which this syntax error was originally parsed. See [`SyntaxError::locate`] for more
/// detail.
#[derive(Debug, PartialEq, Clone)]
pub struct SyntaxError<E> {
    /// The type of syntax error which occured.
    pub kind: SyntaxErrorKind<E>,
    /// The range in the template string at which the error occured.
    pub(crate) span: Range<usize>,
}

/// The type of syntax error which occured.
///
/// The [`SyntaxErrorKind::InvalidExpr`] variant is emitted by the particular [`Ast`](crate::Ast)
/// implementation which is used to parse the template string expressions. It is the associated
/// [`Ast::Error`](crate::Ast::Error) type.
#[derive(Debug, PartialEq, Clone)]
pub enum SyntaxErrorKind<E> {
    /// The format parsing a expression produced an error.
    InvalidExpr(E),
    /// A closing bracket, without a matching opening bracket.
    ExtraBracket,
    /// An expression was started, but not closed.
    UnclosedExpr,
}

impl<E> SyntaxError<E> {
    /// Locate the syntax error inside the original template string.
    ///
    /// The returned range is guaranteed to correspond to a valid slice of the original template string,
    /// and represents the location at which the error was produced.
    ///
    /// # Examples
    /// An expression failed to parse: recover the original expression text.
    /// ```
    /// use mufmt::Template;
    ///
    /// let s = "{ not a usize}";
    /// let err = Template::<&str, usize>::compile(s).unwrap_err();
    /// assert_eq!(&s[err.locate()], " not a usize");
    /// ```
    /// Get the index of an unclosed delimeter.
    /// ```
    /// # use mufmt::Template;
    /// let err = Template::<&str, &str>::compile("extra}").unwrap_err();
    /// assert_eq!(err.locate().start, 5);
    /// ```
    /// Get all of the trailing characters from an unclosed expression.
    /// ```
    /// # use mufmt::Template;
    /// let s = " {# 12 }";
    /// let err = Template::<&str, usize>::compile(s).unwrap_err();
    /// assert_eq!(&s[err.locate()], "{# 12 }");
    /// ```
    ///
    /// # Ranges
    /// The provided ranges depend on the error kind:
    ///
    /// Syntax Error Kind | Range
    /// ------------------|------
    /// [`SyntaxErrorKind::InvalidExpr`] | the contents of the expression before trimming whitespace, but not including the brackets.
    /// [`SyntaxErrorKind::ExtraBracket`] | a range of length 1 containing precisely the extra bracket.
    /// [`SyntaxErrorKind::UnclosedExpr`] | a range starting before the expression bracket and terminating at the end of the template string.
    pub fn locate(&self) -> Range<usize> {
        self.span.clone()
    }
}

/// An error while rendering a compiled template string into an [`io::Write`].
///
/// The [`Render`](IORenderError::Render) variant is emitted by the particular
/// [`Manifest`](crate::Manifest) implementation which is used to parse the template string
/// expressions.
/// It is the associated [`Manifest::Error`](crate::Manifest::Error) type.
///
/// For infallible rendering, there is a is a `From<IORenderError<Infallible>>` implementation for `io::Error`.
#[derive(Debug)]
pub enum IORenderError<R> {
    /// A value in an expression could not be rendered.
    Render(R),
    /// An error occured while writing to an [`io::Write`].
    IO(io::Error),
}

impl<R> From<io::Error> for IORenderError<R> {
    fn from(err: io::Error) -> Self {
        Self::IO(err)
    }
}

impl From<IORenderError<Infallible>> for io::Error {
    fn from(err: IORenderError<Infallible>) -> Self {
        let IORenderError::IO(io) = err;
        io
    }
}

/// An error while rendering a compiled template string into a [`fmt::Write`].
///
/// The [`Render`](FmtRenderError::Render) variant is emitted by the particular
/// [`Manifest`](crate::Manifest) implementation which is used to parse the template string
/// expressions.
/// It is the associated [`Manifest::Error`](crate::Manifest::Error) type.
///
/// For infallible rendering, there is a is a `From<FmtRenderError<Infallible>>` implementation for `fmt::Error`.
#[derive(Debug, PartialEq, Eq)]
pub enum FmtRenderError<R> {
    /// A value in an expression could not be rendered.
    Render(R),
    /// An error occured while writing to a [`fmt::Write`].
    Fmt(fmt::Error),
}

impl<R> From<fmt::Error> for FmtRenderError<R> {
    fn from(err: fmt::Error) -> Self {
        Self::Fmt(err)
    }
}

impl From<FmtRenderError<Infallible>> for fmt::Error {
    fn from(err: FmtRenderError<Infallible>) -> Self {
        let FmtRenderError::Fmt(fmt) = err;
        fmt
    }
}

/// A general error type capturing any error which could occur while compiling or rendering a
/// template string.
///
/// This error type is used by the [`Oneshot`](crate::Oneshot) render methods, though it could also
/// be useful for handling any error which might occur in this crate since it implements `From<T>`
/// for the following types `T`:
///
/// - [`SyntaxError<E>`], [`io::Error`], [`fmt::Error`], [`IORenderError`], [`FmtRenderError`].
#[derive(Debug)]
pub enum Error<E, R> {
    /// An error when compiling the template string.
    Syntax(SyntaxError<E>),
    /// A value in an expression could not be rendered.
    Render(R),
    /// An error occured while writing to an [`io::Write`].
    IO(io::Error),
    /// An error occured while writing to a [`fmt::Write`].
    Fmt(fmt::Error),
}

impl<E, R> From<SyntaxError<E>> for Error<E, R> {
    fn from(err: SyntaxError<E>) -> Self {
        Self::Syntax(err)
    }
}

impl<E, R> From<IORenderError<R>> for Error<E, R> {
    fn from(err: IORenderError<R>) -> Self {
        match err {
            IORenderError::Render(r) => Self::Render(r),
            IORenderError::IO(io_err) => Self::IO(io_err),
        }
    }
}

impl<E, R> From<FmtRenderError<R>> for Error<E, R> {
    fn from(err: FmtRenderError<R>) -> Self {
        match err {
            FmtRenderError::Render(r) => Self::Render(r),
            FmtRenderError::Fmt(fmt_err) => Self::Fmt(fmt_err),
        }
    }
}

impl<E, R> From<io::Error> for Error<E, R> {
    fn from(err: io::Error) -> Self {
        Self::IO(err)
    }
}

impl<E, R> From<fmt::Error> for Error<E, R> {
    fn from(err: fmt::Error) -> Self {
        Self::Fmt(err)
    }
}

mod stderror {
    use super::{Error, FmtRenderError, IORenderError, SyntaxError, SyntaxErrorKind};

    use std::{
        error::Error as StdError,
        fmt::{self, Display},
    };

    impl<E: Display> Display for SyntaxErrorKind<E> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                Self::InvalidExpr(e) => write!(f, "Invalid expression: {e}"),
                Self::ExtraBracket => {
                    f.write_str("Unexpected closing bracket '}' without matching opening bracket")
                }
                Self::UnclosedExpr => f.write_str("Expression not closed"),
            }
        }
    }

    impl<E: Display> Display for SyntaxError<E> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "Template parse error: {}", self.kind)
        }
    }

    const RENDER_ERROR_PREFIX: &str = "Failed to render template expression";
    const FMT_ERROR_PREFIX: &str = "A format error occured while rendering a template";
    const IO_ERROR_PREFIX: &str = "An IO error occured while rendering a template";

    impl<R: Display> Display for FmtRenderError<R> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                Self::Render(e) => write!(f, "{RENDER_ERROR_PREFIX}: {e}"),
                Self::Fmt(e) => write!(f, "{FMT_ERROR_PREFIX}: {e}"),
            }
        }
    }

    impl<R: Display> Display for IORenderError<R> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                Self::Render(e) => write!(f, "{RENDER_ERROR_PREFIX}: {e}"),
                Self::IO(e) => write!(f, "{IO_ERROR_PREFIX}: {e}"),
            }
        }
    }

    impl<E: Display, R: Display> Display for Error<E, R> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                Self::Syntax(syntax_error) => syntax_error.fmt(f),
                Self::Render(e) => write!(f, "{RENDER_ERROR_PREFIX}: {e}"),
                Self::IO(e) => write!(f, "{IO_ERROR_PREFIX}: {e}"),
                Self::Fmt(e) => write!(f, "{FMT_ERROR_PREFIX}: {e}"),
            }
        }
    }

    impl<E: StdError> StdError for SyntaxError<E> {}
    impl<R: StdError> StdError for FmtRenderError<R> {}
    impl<R: StdError> StdError for IORenderError<R> {}
    impl<E: StdError, R: StdError> StdError for Error<E, R> {}
}
