//! # [`Ast`] implementations and custom types

use std::{
    convert::Infallible,
    net::{IpAddr, Ipv4Addr, Ipv6Addr, SocketAddr, SocketAddrV4, SocketAddrV6},
    num::NonZero,
    path::{Path, PathBuf},
    rc::Rc,
    sync::Arc,
};

use super::{IndexOutOfRange, NotEmpty, ParseBoundedIntError};
use crate::Ast;

macro_rules! ast_from_new {
    ($($ast:tt)*) => {
        $(
            impl<'fmt, T: $crate::Ast<'fmt>> $crate::Ast<'fmt> for $ast<T> {
                type Error = T::Error;

                fn from_expr(s: &'fmt str) -> Result<Self, Self::Error> {
                    Ok($ast::new(T::from_expr(s)?))
                }
            }
        )*
    };
}

ast_from_new!(Box Arc Rc);

macro_rules! ast_from_str {
    ($($ast:ty)*) => {
        $(
            impl $crate::Ast<'_> for $ast {
                type Error = <$ast as ::std::str::FromStr>::Err;

                fn from_expr(s: &str) -> Result<Self, Self::Error> {
                    ::std::str::FromStr::from_str(s)
                }
            }
        )*
    };
}

ast_from_str!(
    // str types
    String PathBuf char
    // std::net
    IpAddr Ipv4Addr Ipv6Addr SocketAddr SocketAddrV4 SocketAddrV6
    // bool
    bool
    // numeric types
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
    NonZero<usize> NonZero<u8> NonZero<u16> NonZero<u32> NonZero<u64> NonZero<u128>
    NonZero<isize> NonZero<i8> NonZero<i16> NonZero<i32> NonZero<i64> NonZero<i128>
    f32 f64
);

/// A `usize` in the range `0..N`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BoundedInt<const N: usize> {
    inner: usize,
}

impl<'fmt, T: Ast<'fmt>> Ast<'fmt> for Option<T> {
    type Error = T::Error;

    fn from_expr(expr: &'fmt str) -> Result<Self, Self::Error> {
        if expr.is_empty() {
            Ok(None)
        } else {
            Ok(Some(T::from_expr(expr)?))
        }
    }
}

impl<'fmt, T: Ast<'fmt>> Ast<'fmt> for Result<T, T::Error> {
    type Error = Infallible;

    fn from_expr(expr: &'fmt str) -> Result<Self, Self::Error> {
        Ok(T::from_expr(expr))
    }
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

impl<const N: usize> TryFrom<usize> for BoundedInt<N> {
    type Error = IndexOutOfRange;

    fn try_from(n: usize) -> Result<Self, Self::Error> {
        Self::new(n).ok_or(IndexOutOfRange(n))
    }
}

impl<const N: usize> Ast<'_> for BoundedInt<N> {
    type Error = ParseBoundedIntError;

    fn from_expr(expr: &str) -> Result<Self, Self::Error> {
        let inner = expr.parse()?;
        if inner < N {
            Ok(Self { inner })
        } else {
            Err(Self::Error::OutOfRange(inner))
        }
    }
}

impl<'fmt> Ast<'fmt> for &'fmt str {
    type Error = Infallible;

    fn from_expr(s: &'fmt str) -> Result<Self, Self::Error> {
        Ok(s)
    }
}

impl<'fmt> Ast<'fmt> for &'fmt Path {
    type Error = Infallible;

    fn from_expr(s: &'fmt str) -> Result<Self, Self::Error> {
        Ok(Path::new(s))
    }
}

impl Ast<'_> for () {
    type Error = NotEmpty;

    fn from_expr(s: &'_ str) -> Result<Self, Self::Error> {
        if s.is_empty() { Ok(()) } else { Err(NotEmpty) }
    }
}

impl Ast<'_> for Infallible {
    type Error = ();

    fn from_expr(_: &'_ str) -> Result<Self, Self::Error> {
        Err(())
    }
}

/// A type with an [`Ast`] implementation that never fails and ignores the expression contents.
#[derive(Debug, Copy, Clone, PartialEq)]
pub struct IgnoredAny;

impl Ast<'_> for IgnoredAny {
    type Error = Infallible;

    fn from_expr(_: &str) -> Result<Self, Self::Error> {
        Ok(Self)
    }
}
