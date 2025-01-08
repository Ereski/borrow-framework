//! A `no_std` set of utilities for more flexible borrowing than the ones
//! provided by the standard library.
//!
//! Due to Rust's lack of complete support for Higher Kinded Types (HKTs),
//! borrowing is not as powerful as it could be. Even with the introduction of
//! limited Generic Associated Types (GATs) in Rust 1.65, the standard library
//! has not gained useful APIs that take advantage of this functionality for
//! better borrowing.
//!
//! This crate introduces more flexible traits for working with borrowed data,
//! especially with types containing internal borrows, by relying on the HKT
//! framework introduced by
//! [generic-std](https://github.com/Ereski/generic-std). Compiler support for
//! GATs is not required.
//!
//! # Features
//!
//! This crate replaces [std::borrow] with more flexible types and traits.
//!
//! ## More Flexible Borrowing
//!
//! [Borrow] and [BorrowMut] are similar to the ones provided by the standard
//! library, but the borrowed type may be an arbitrary type. For example,
//! [Borrow::borrow] might directly return an [std::borrow::Cow].
//!
//! ## Saner `ToOwned`
//!
//! [ToOwned] is not tied to the borrow trait anymore and provides a
//! [ToOwned::into_owned] method. Also, no blanket implementation for `Clone`
//! types so something like `Cow::<'a, T>::to_owned` is finally able to return
//! the much saner `Cow<'static, T>`.
//!
//! ## Clone-On-Write For Types With Internal References
//!
//! [std::borrow::Cow] stores either the owned or the borrowed version of
//! another type, but the borrowed variant is required to be a reference. The
//! [Cow] type provided by this crate integrates with [Borrow] and [ToOwned],
//! allowing the borrowed variant to contain a non-reference type with internal
//! references.
//!
//! # Example
//!
//! Suppose you have a `Identifier<'a>` type that internally contains either a
//! borrowed or an owned string and you would like to create an
//! `Identifier<'static>` to store somewhere. This is not possible with
//! [std::borrow::ToOwned] because [std::borrow::ToOwned::Owned] must implement
//! [std::borrow::Borrow], and [std::borrow::Borrow::borrow] must return a
//! reference, not `Identifier<'a>`. But doing this is trivial with this crate's
//! [ToOwned]:
//!
//! ```rust
//! # use borrow_framework::ToOwned;
//! # struct Identifier<'a>(std::borrow::Cow<'a, str>);
//! impl<'a> ToOwned for Identifier<'a> {
//!     type Owned = Identifier<'static>;
//!
//!     fn to_owned(&self) -> Self::Owned {
//!         // Returns an `Identifier<'static>`
//!         # unimplemented!()
//!     }
//! }
//! ```
//!
//! Similarly, this crate's [Borrow] can return `Identifier<'a>` directly in
//! addition to normal references:
//!
//! ```rust
//! # use borrow_framework::{Borrow, Borrowed, BorrowHkt};
//! # struct Identifier<'a>(std::borrow::Cow<'a, str>);
//! struct BorrowIdentifier;
//!
//! impl<'a> BorrowHkt<'a> for BorrowIdentifier {
//!     type T = Identifier<'a>;
//! }
//!
//! impl<'a> Borrow<'a, BorrowIdentifier> for Identifier<'a> {
//!     fn borrow<'b>(&'a self) -> Borrowed<'b, BorrowIdentifier>
//!     where
//!         'a: 'b
//!     {
//!         // Returns an `Identifier<'b>`
//!         # unimplemented!()
//!     }
//! }
//!
//! struct BorrowIdentifierStr;
//!
//! impl<'a> BorrowHkt<'a> for BorrowIdentifierStr {
//!     type T = &'a str;
//! }
//!
//! impl<'a> Borrow<'a, BorrowIdentifierStr> for Identifier<'a> {
//!     fn borrow<'b>(&'a self) -> Borrowed<'b, BorrowIdentifierStr>
//!     where
//!         'a: 'b
//!     {
//!         // Returns a `&'b str`
//!         # unimplemented!()
//!     }
//! }
//! ```

#![cfg_attr(not(feature = "std"), no_std)]

use core::{
    cmp::Ordering,
    fmt::{self, Debug, Formatter},
    hash::{Hash, Hasher},
    marker::PhantomData,
};

/// Flexible borrowing trait.
///
/// This is similar to [std::borrow::Borrow] but allows non-reference types to
/// be used.
pub trait Borrow<'a, T>
where
    T: for<'b> BorrowHkt<'b>,
{
    /// Create a borrowed version of this type.
    fn borrow<'b>(&'a self) -> Borrowed<'b, T>
    where
        'a: 'b;
}

/// Trait for resolving a concrete type from a given lifetime `'a`, where `'a`
/// is the lifetime of the value being borrowed.
pub trait BorrowHkt<'a> {
    /// The borrowed type.
    type T;
}

/// Type alias to extract the concrete borrowed type from a [BorrowHkt].
pub type Borrowed<'a, T> = <T as BorrowHkt<'a>>::T;

/// Flexible mutable borrowing trait.
///
/// This is similar to [std::borrow::BorrowMut] but allows non-reference types
/// to be used.
pub trait BorrowMut<'a, T>: Borrow<'a, T>
where
    T: for<'b> BorrowMutHkt<'b>,
{
    /// Create a borrowed version of this type.
    fn borrow_mut<'b>(&'a mut self) -> BorrowedMut<'b, T>
    where
        'a: 'b;
}

/// Trait for resolving a concrete type from a given lifetime `'a`, where `'a`
/// is the lifetime of the value being mutably borrowed.
pub trait BorrowMutHkt<'a>: BorrowHkt<'a> {
    /// The borrowed type.
    type T;
}

/// Type alias to extract the concrete borrowed type from a [BorrowMutHkt].
pub type BorrowedMut<'a, T> = <T as BorrowMutHkt<'a>>::T;

/// Convert from a borrowed type into an owned type.
///
/// This is similar to [std::borrow::ToOwned] but is meant for types with
/// internal references, with support for `into_owned` and an additional `Sized`
/// constraint.
pub trait ToOwned: Sized {
    /// Owned type.
    type Owned;

    /// Create an owned version of this type by cloning if necessary.
    fn to_owned(&self) -> Self::Owned;

    /// Create an owned version of this type, consuming `self`.
    fn into_owned(self) -> Self::Owned {
        self.to_owned()
    }
}

#[cfg(feature = "std")]
impl<T> ToOwned for std::borrow::Cow<'_, T>
where
    T: std::borrow::ToOwned + 'static,
    T::Owned: Clone,
{
    type Owned = std::borrow::Cow<'static, T>;

    fn to_owned(&self) -> std::borrow::Cow<'static, T> {
        let owned = match self {
            Self::Borrowed(x) => T::to_owned(x),
            Self::Owned(x) => x.clone(),
        };

        std::borrow::Cow::Owned(owned)
    }

    fn into_owned(self) -> std::borrow::Cow<'static, T> {
        let owned = match self {
            Self::Borrowed(x) => T::to_owned(x),
            Self::Owned(x) => x,
        };

        std::borrow::Cow::Owned(owned)
    }
}

/// A clone-on-write container that contains either the owned or borrowed
/// version of some data.
///
/// Unlike [std::borrow::Cow], this type may hold non-reference types with
/// internal references in the borrowed variant. `T` is required to implement
/// [Cowable].
///
/// # Notes
///
/// - **Important**: The implementations of [PartialEq], [Eq], [PartialOrd] and
///   [Ord] assume that the results are the same regardless of which combination
///   of borrowed and owned versions are being compared.
/// - Some traits cannot have blanket implementations without support for
///   specialization in Rust, such as the [From] trait. Where possible the
///   functionality is provided by intrinsic methods instead.
pub enum Cow<'a, T>
where
    T: Cowable,
{
    /// Borrowed variant.
    Borrowed(CowableBorrowed<'a, T>),

    /// Owned variant.
    Owned(CowableOwned<T>),
}

impl<'a, T> Cow<'a, T>
where
    T: Cowable,
{
    /// Create a new [Cow] containing borrowed data.
    pub fn borrowed(borrowed: impl Into<CowableBorrowed<'a, T>>) -> Self {
        Self::Borrowed(borrowed.into())
    }

    /// Create a new [Cow] containing owned data.
    pub fn owned(owned: impl Into<CowableOwned<T>>) -> Self {
        Self::Owned(owned.into())
    }

    /// Return true if the data is borrowed.
    pub fn is_borrowed(&self) -> bool {
        matches!(self, Self::Borrowed(_))
    }

    /// Return true if the data is owned.
    pub fn is_owned(&self) -> bool {
        matches!(self, Self::Owned(_))
    }

    /// Unwrap the borrowed data, panicking if the data is owned.
    pub fn unwrap_borrowed(self) -> CowableBorrowed<'a, T> {
        match self {
            Self::Borrowed(x) => x,
            Self::Owned(_) => panic!("Cow contains owned data"),
        }
    }

    /// Unwrap the owned data, panicking if the data is borrowed.
    pub fn unwrap_owned(self) -> CowableOwned<T> {
        match self {
            Self::Borrowed(_) => panic!("Cow contains borrowed data"),
            Self::Owned(x) => x,
        }
    }
}

impl<'a, T> Cow<'a, T>
where
    T: Cowable,
    CowableBorrowed<'a, T>: ToOwned<Owned = CowableOwned<T>>,
{
    /// If this [Cow] contains and owned value, return a mutable reference to
    /// it. If it contains a borrowed value, make it owned and return a mutable
    /// reference to this new value.
    pub fn to_mut(&mut self) -> &mut CowableOwned<T> {
        match self {
            Self::Borrowed(x) => {
                // TODO: find a way to use `into_owned` here
                *self = Cow::Owned(x.to_owned());

                match self {
                    Self::Borrowed(_) => unreachable!(),
                    Self::Owned(x) => x,
                }
            }
            Self::Owned(x) => x,
        }
    }

    /// Unwrap this [Cow] into and owned value, calling [ToOwned::into_owned] if
    /// the data is borrowed.
    pub fn into_inner(self) -> CowableOwned<T> {
        match self {
            Self::Borrowed(x) => x.into_owned(),
            Self::Owned(x) => x,
        }
    }
}

impl<'a, T> Borrow<'a, BorrowCow<T>> for Cow<'a, T>
where
    T: Cowable,
    CowableBorrowed<'a, T>: Borrow<'a, T::BorrowHkt>,
    CowableOwned<T>: Borrow<'a, T::BorrowHkt>,
{
    fn borrow<'b>(&'a self) -> Borrowed<'b, BorrowCow<T>>
    where
        'a: 'b,
    {
        match self {
            Self::Borrowed(x) => Cow::Borrowed(x.borrow()),
            Self::Owned(x) => Cow::Borrowed(x.borrow()),
        }
    }
}

impl<'a, T> ToOwned for Cow<'a, T>
where
    T: Cowable,
    CowableBorrowed<'a, T>: ToOwned<Owned = CowableOwned<T>>,
    CowableOwned<T>: Clone,
{
    type Owned = Cow<'static, T>;

    fn to_owned(&self) -> Cow<'static, T> {
        match self {
            Self::Borrowed(x) => Cow::Owned(x.to_owned()),
            Self::Owned(x) => Cow::Owned(x.clone()),
        }
    }

    fn into_owned(self) -> Cow<'static, T> {
        match self {
            Self::Borrowed(x) => Cow::Owned(x.into_owned()),
            Self::Owned(x) => Cow::Owned(x),
        }
    }
}

impl<'a, T> Clone for Cow<'a, T>
where
    T: Cowable,
    CowableBorrowed<'a, T>: Clone,
    CowableOwned<T>: Clone,
{
    fn clone(&self) -> Self {
        match self {
            Self::Borrowed(x) => Self::Borrowed(x.clone()),
            Self::Owned(x) => Self::Owned(x.clone()),
        }
    }
}

impl<'a, T> Copy for Cow<'a, T>
where
    T: Cowable,
    CowableBorrowed<'a, T>: Copy,
    CowableOwned<T>: Copy,
{
}

impl<'a, T> Debug for Cow<'a, T>
where
    T: Cowable,
    CowableBorrowed<'a, T>: Debug,
    CowableOwned<T>: Debug,
{
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Self::Borrowed(x) => x.fmt(f),
            Self::Owned(x) => x.fmt(f),
        }
    }
}

impl<T> Default for Cow<'_, T>
where
    T: Cowable,
    CowableOwned<T>: Default,
{
    fn default() -> Self {
        Self::Owned(Default::default())
    }
}

impl<'a, T> Hash for Cow<'a, T>
where
    T: Cowable,
    CowableBorrowed<'a, T>: Hash,
    CowableOwned<T>: Hash,
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Self::Borrowed(x) => x.hash(state),
            Self::Owned(x) => x.hash(state),
        }
    }
}

impl<'a, T> PartialEq<Cow<'a, T>> for Cow<'a, T>
where
    T: Cowable,
    CowableBorrowed<'a, T>: PartialEq + PartialEq<CowableOwned<T>>,
    CowableOwned<T>: PartialEq + PartialEq<CowableBorrowed<'a, T>>,
{
    fn eq(&self, other: &Cow<'a, T>) -> bool {
        match (self, other) {
            (Self::Borrowed(a), Self::Borrowed(b)) => a.eq(b),
            (Self::Borrowed(a), Self::Owned(b)) => a.eq(b),
            (Self::Owned(a), Self::Borrowed(b)) => a.eq(b),
            (Self::Owned(a), Self::Owned(b)) => a.eq(b),
        }
    }
}

impl<'a, T> Eq for Cow<'a, T>
where
    T: Cowable,
    CowableBorrowed<'a, T>: Eq + PartialEq<CowableOwned<T>>,
    CowableOwned<T>: Eq + PartialEq<CowableBorrowed<'a, T>>,
{
}

impl<'a, T> PartialOrd for Cow<'a, T>
where
    T: Cowable,
    CowableBorrowed<'a, T>: PartialOrd + PartialOrd<CowableOwned<T>>,
    CowableOwned<T>: PartialOrd + PartialOrd<CowableBorrowed<'a, T>>,
{
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self, other) {
            (Self::Borrowed(a), Self::Borrowed(b)) => a.partial_cmp(b),
            (Self::Borrowed(a), Self::Owned(b)) => a.partial_cmp(b),
            (Self::Owned(a), Self::Borrowed(b)) => a.partial_cmp(b),
            (Self::Owned(a), Self::Owned(b)) => a.partial_cmp(b),
        }
    }

    fn ge(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Borrowed(a), Self::Borrowed(b)) => a.ge(b),
            (Self::Borrowed(a), Self::Owned(b)) => a.ge(b),
            (Self::Owned(a), Self::Borrowed(b)) => a.ge(b),
            (Self::Owned(a), Self::Owned(b)) => a.ge(b),
        }
    }

    fn gt(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Borrowed(a), Self::Borrowed(b)) => a.gt(b),
            (Self::Borrowed(a), Self::Owned(b)) => a.gt(b),
            (Self::Owned(a), Self::Borrowed(b)) => a.gt(b),
            (Self::Owned(a), Self::Owned(b)) => a.gt(b),
        }
    }

    fn le(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Borrowed(a), Self::Borrowed(b)) => a.le(b),
            (Self::Borrowed(a), Self::Owned(b)) => a.le(b),
            (Self::Owned(a), Self::Borrowed(b)) => a.le(b),
            (Self::Owned(a), Self::Owned(b)) => a.le(b),
        }
    }

    fn lt(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Borrowed(a), Self::Borrowed(b)) => a.lt(b),
            (Self::Borrowed(a), Self::Owned(b)) => a.lt(b),
            (Self::Owned(a), Self::Borrowed(b)) => a.lt(b),
            (Self::Owned(a), Self::Owned(b)) => a.lt(b),
        }
    }
}

impl<'a, T> Ord for Cow<'a, T>
where
    T: Cowable,
    CowableBorrowed<'a, T>: Ord + PartialOrd<CowableOwned<T>>,
    CowableOwned<T>: Ord + PartialOrd<CowableBorrowed<'a, T>>,
{
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Self::Borrowed(a), Self::Borrowed(b)) => a.cmp(b),
            (Self::Borrowed(a), Self::Owned(b)) => a.partial_cmp(b).unwrap(),
            (Self::Owned(a), Self::Borrowed(b)) => a.partial_cmp(b).unwrap(),
            (Self::Owned(a), Self::Owned(b)) => a.cmp(b),
        }
    }
}

/// Marker type implementing [BorrowHkt] for [Cow].
pub struct BorrowCow<T>(PhantomData<T>);

impl<'a, T> BorrowHkt<'a> for BorrowCow<T>
where
    T: Cowable,
{
    type T = Cow<'a, T>;
}

/// Trait for types that can be used with [Cow] through a [BorrowHkt].
///
/// This trait is automatically implemented for types that implement
/// [BorrowHkt] if [BorrowHkt::T] implements [ToOwned] for all lifetimes.
pub trait Cowable {
    /// The marker type implementing [BorrowHkt].
    type BorrowHkt: for<'a> BorrowHkt<'a>;

    /// The owned type.
    type Owned;
}

// This implementation relies on Rust's unification to "find" the correct owned
// type `O` for each `BorrowHkt`
impl<B, O> Cowable for B
where
    B: for<'a> BorrowHkt<'a>,
    for<'a> <B as BorrowHkt<'a>>::T: ToOwned<Owned = O>,
{
    type BorrowHkt = B;
    type Owned = O;
}

/// Type alias to extract the concrete borrowed type from a [Cowable].
pub type CowableBorrowed<'a, T> = Borrowed<'a, <T as Cowable>::BorrowHkt>;

/// Type alias to extract the concrete owned type from a [Cowable].
pub type CowableOwned<T> = <T as Cowable>::Owned;
