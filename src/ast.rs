//! # `Ast` and `Context` implementations
//!
//! This module defines a few custom [`Ast`] and [`Context`] implementations.
use std::{
    borrow::Borrow,
    collections::{BTreeMap, HashMap, VecDeque},
    convert::Infallible,
    fmt,
    hash::Hash,
    num::{IntErrorKind, NonZero, ParseIntError},
};

use super::{Ast, Context};

macro_rules! ast_as_fromstr {
    ($($type:ty),*) => {
        $(
            impl<'fmt> Ast<'fmt> for $type {
                type Error = <$type as ::std::str::FromStr>::Err;

                fn parse(s: &'fmt str) -> Result<Self, Self::Error> {
                    ::std::str::FromStr::from_str(s)
                }
            }
        )*
    };
}

ast_as_fromstr!(
    usize,
    u8,
    u16,
    u32,
    u64,
    u128,
    isize,
    i8,
    i16,
    i32,
    i64,
    i128,
    NonZero<usize>,
    NonZero<u8>,
    NonZero<u16>,
    NonZero<u32>,
    NonZero<u64>,
    NonZero<u128>,
    NonZero<isize>,
    NonZero<i8>,
    NonZero<i16>,
    NonZero<i32>,
    NonZero<i64>,
    NonZero<i128>,
    f32,
    f64
);

impl<'fmt> Ast<'fmt> for &'fmt str {
    type Error = Infallible;

    fn parse(s: &'fmt str) -> Result<Self, Self::Error> {
        Ok(s)
    }
}

impl<F, D: fmt::Display> Context for F
where
    F: for<'fmt> Fn(&'fmt str) -> D,
{
    type Ast<'fmt> = &'fmt str;

    type Error = Infallible;

    fn render(&self, ast: &Self::Ast<'_>) -> Result<impl fmt::Display, Self::Error> {
        Ok((self)(ast))
    }
}

/// Rendering failed since an index is out of range.
#[derive(Debug, Clone, Copy)]
pub struct IndexOutOfRange;

/// Rendering failed since a key is undefined.
#[derive(Debug, Clone, Copy)]
pub struct UndefinedKey;

macro_rules! impl_context_with_get {
    ($err:tt, $ast:ty) => {
        type Ast<'fmt> = $ast;

        type Error = $err;

        fn render(&self, ast: &Self::Ast<'_>) -> Result<impl fmt::Display, Self::Error> {
            match self.get(*ast) {
                Some(it) => Ok(it),
                None => Err($err),
            }
        }
    };
}

impl<T: fmt::Display> Context for Vec<T> {
    impl_context_with_get!(IndexOutOfRange, usize);
}

impl<T: fmt::Display> Context for [T] {
    impl_context_with_get!(IndexOutOfRange, usize);
}

impl<T: fmt::Display> Context for &[T] {
    impl_context_with_get!(IndexOutOfRange, usize);
}

impl<T: fmt::Display> Context for &mut [T] {
    impl_context_with_get!(IndexOutOfRange, usize);
}

impl<T: fmt::Display> Context for VecDeque<T> {
    impl_context_with_get!(IndexOutOfRange, usize);
}

impl<K, V> Context for HashMap<K, V>
where
    K: Borrow<str> + Eq + Hash,
    V: fmt::Display,
{
    impl_context_with_get!(UndefinedKey, &'fmt str);
}

impl<K, V> Context for BTreeMap<K, V>
where
    K: Borrow<str> + Ord,
    V: fmt::Display,
{
    impl_context_with_get!(UndefinedKey, &'fmt str);
}

/// A `usize` in the range `0..N`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BoundedInt<const N: usize> {
    inner: usize,
}

impl<const N: usize> BoundedInt<N> {
    /// Initialize from a `usize`, checking that it satisfies the required bound.
    pub const fn new(n: usize) -> Option<Self> {
        if n < N { Some(Self { inner: n }) } else { None }
    }
}

impl<const N: usize> From<BoundedInt<N>> for usize {
    fn from(val: BoundedInt<N>) -> Self {
        val.inner
    }
}

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

impl<const N: usize> Ast<'_> for BoundedInt<N> {
    type Error = ParseBoundedIntError;

    fn parse(block: &str) -> Result<Self, Self::Error> {
        let inner = block.parse()?;
        if inner < N {
            Ok(Self { inner })
        } else {
            Err(Self::Error::OutOfRange(inner))
        }
    }
}

impl<const N: usize, T: fmt::Display> Context for [T; N] {
    type Ast<'fmt> = BoundedInt<N>;

    type Error = Infallible;

    fn render(&self, ast: &Self::Ast<'_>) -> Result<impl fmt::Display, Self::Error> {
        Ok(unsafe { self.as_slice().get_unchecked(ast.inner) })
    }
}
