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

/// An error while rendering a compiled template string.
///
/// The [`Render`](RenderError::Render) variant is emitted by the particular
/// [`Manifest`](crate::Manifest) implementation which is used to parse the template string
/// expressions.
/// It is the associated [`Manifest::Error`](crate::Manifest::Error) type.
#[derive(Debug)]
pub enum RenderError<R> {
    /// A value in an expression could not be rendered.
    Render(R),
    /// An error occured while writing to an [`io::Write`].
    IO(io::Error),
    /// An error occured while writing to a [`fmt::Write`].
    Fmt(fmt::Error),
}

/// Any error when compiling or rendering a template string.
#[derive(Debug)]
pub enum Error<E, R> {
    /// An error when compiling the template string.
    Syntax(SyntaxError<E>),
    /// An error when rendering the compiled template string.
    Render(RenderError<R>),
}

impl<R> From<io::Error> for RenderError<R> {
    fn from(err: io::Error) -> Self {
        Self::IO(err)
    }
}

impl<R> From<fmt::Error> for RenderError<R> {
    fn from(err: fmt::Error) -> Self {
        Self::Fmt(err)
    }
}

impl<E, R> From<SyntaxError<E>> for Error<E, R> {
    fn from(err: SyntaxError<E>) -> Self {
        Self::Syntax(err)
    }
}

impl<E, R> From<RenderError<R>> for Error<E, R> {
    fn from(err: RenderError<R>) -> Self {
        Self::Render(err)
    }
}

impl<E, R> From<io::Error> for Error<E, R> {
    fn from(err: io::Error) -> Self {
        Self::Render(RenderError::IO(err))
    }
}

impl<E, R> From<fmt::Error> for Error<E, R> {
    fn from(err: fmt::Error) -> Self {
        Self::Render(RenderError::Fmt(err))
    }
}
