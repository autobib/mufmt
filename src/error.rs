//! # Error types
//!
//! This module contains a variety of error types used in this crate.
//!
//! - The [`SyntaxError`], [`RenderError`], and [`Error`] contain generics to propogate errors
//!   which may result from a particular [`Ast`](crate::Ast) or [`Manifest`](crate::Manifest)
//!   implementation.

use std::{fmt, io, ops};

// TODO: work out a way for the errors to contain span information relative to the original
// template

/// An error while compiling a template string.
///
/// The [`Ast`](SyntaxError::Ast) variant is emitted by the particular [`Ast`](crate::Ast)
/// implementation which is used to parse the template string expressions. It is the associated
/// [`Ast::Error`](crate::Ast::Error) type.
#[derive(Debug, PartialEq)]
pub enum SyntaxError<E> {
    /// The format parsing a expression produced an error.
    Ast(E, ops::Range<usize>),
    /// A closing bracket, without a matching opening bracket.
    ExtraBracket(usize),
    /// An expression was started, but not closed.
    UnclosedExpr(usize),
}

/// An error while rendering a compiled template string into an [`io::Write`].
///
/// The [`Render`](IORenderError::Render) variant is emitted by the particular
/// [`Manifest`](crate::Manifest) implementation which is used to parse the template string
/// expressions.
/// It is the associated [`Manifest::Error`](crate::Manifest::Error) type.
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

/// An error while rendering a compiled template string into a [`fmt::Write`].
///
/// The [`Render`](FmtRenderError::Render) variant is emitted by the particular
/// [`Manifest`](crate::Manifest) implementation which is used to parse the template string
/// expressions.
/// It is the associated [`Manifest::Error`](crate::Manifest::Error) type.
#[derive(Debug)]
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
    /// An error occured while writing to an [`fmt::Write`].
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
