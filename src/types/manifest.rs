//! # [`Manifest`] implementations and custom types

use std::{
    borrow::Borrow,
    collections::{BTreeMap, HashMap, VecDeque},
    convert::Infallible,
    fmt::Display,
    hash::Hash,
};

use super::{BoundedInt, IndexOutOfRange, KeyMissing};
use crate::Manifest;

impl<A, F, D: Display, E> Manifest<A> for F
where
    F: Fn(&A) -> Result<D, E>,
{
    type Error = E;

    fn manifest(&self, ast: &A) -> Result<impl Display, Self::Error> {
        (self)(ast)
    }
}

macro_rules! impl_index_context {
    ($($ast:ty),*) => {
        $(
            impl<T: Display> Manifest<usize> for $ast {
                type Error = IndexOutOfRange;

                fn manifest(&self, ast: &usize) -> Result<impl Display, Self::Error> {
                    self.get(*ast).ok_or(IndexOutOfRange(*ast))
                }
            }
        )*
    };
}

impl_index_context!(Vec<T>, [T], &[T], &mut [T], VecDeque<T>);

impl<Q, K, V> Manifest<Q> for HashMap<K, V>
where
    K: Borrow<Q> + Eq + Hash,
    Q: Hash + Eq,
    V: Display,
{
    type Error = KeyMissing;

    fn manifest(&self, ast: &Q) -> Result<impl Display, Self::Error> {
        self.get(ast).ok_or(KeyMissing)
    }
}

impl<Q, K, V> Manifest<Q> for BTreeMap<K, V>
where
    K: Borrow<Q> + Ord,
    Q: Ord,
    V: Display,
{
    type Error = KeyMissing;

    fn manifest(&self, ast: &Q) -> Result<impl Display, Self::Error> {
        self.get(ast).ok_or(KeyMissing)
    }
}

impl<const N: usize, T: Display> Manifest<usize> for [T; N] {
    type Error = IndexOutOfRange;

    fn manifest(&self, ast: &usize) -> Result<impl Display, Self::Error> {
        self.as_slice().get(*ast).ok_or(IndexOutOfRange(*ast))
    }
}

impl<const N: usize, T: Display> Manifest<BoundedInt<N>> for [T; N] {
    type Error = Infallible;

    fn manifest(&self, ast: &BoundedInt<N>) -> Result<impl Display, Self::Error> {
        Ok(unsafe { self.as_slice().get_unchecked(usize::from(*ast)) })
    }
}
