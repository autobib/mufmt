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

impl<A, F, T: Display, E> Manifest<A> for F
where
    F: Fn(&A) -> Result<T, E>,
{
    type Error = E;

    fn manifest(&self, ast: &A) -> Result<impl Display, Self::Error> {
        self(ast)
    }
}

macro_rules! impl_index_manifest {
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

impl_index_manifest!(Vec<T>, [T], &[T], &mut [T], VecDeque<T>);

macro_rules! impl_map_manifest {
    ($($name:ty => { $($bound:tt)* }),*) => {
        $(
            impl<Q, K, V> Manifest<Q> for $name
            where
                K: Borrow<Q> + $($bound)*,
                Q: $($bound)*,
                V: Display,
                {
                    type Error = KeyMissing;

                    fn manifest(&self, ast: &Q) -> Result<impl Display, Self::Error> {
                        self.get(ast).ok_or(KeyMissing)
                    }
                }
        )*
    };
}

impl_map_manifest!(
    HashMap<K, V> => { Eq + Hash },
    BTreeMap<K, V> => { Ord }
);

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
