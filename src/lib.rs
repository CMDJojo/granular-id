//! This crate contains the type `GranularID`, which is a data type which can provide ID numbers in
//! a sequential order, where between any two ID:s, there are infinitely many *more granular* ID:s.
//! You can think of this as version numbers with an infinite granularity, so if there are versions
//! 1 and 2, there are ID:s 1.1, 1.2, 1.3 etc in-between them. Additionally, in-between ID 1.1 and
//! 1.2, there are infinitely many ID:s 1.1.1, 1.1.2 and so on.
//!
//! `GranularID`s is best used with any unsized integer type, where each component of the ID:s may
//! range from the minimum bound to the maximum bound of that integer type. The `GranularID` that
//! starts with the upper bound of the integer type is the very maximum `GranularID`. This means
//! that, using `u8`, all these `GranularID<u8>`s exist, in increasing order:
//! * `254`
//! * `254.0`
//! * `254.1`
//! * `254.1.0`
//! * `254.1.1`
//! * `254.1.*`
//! * ...
//! * `254.2`
//! * `254.3`
//! * `255`
//! `255` is the highest ID available of this type (i.e. there is no `255.0`, `255.1` etc), and is
//! the upper bound for this type. This constraint is added so that there is an upper bound to the
//! `GranularID<T>` type if `T` has an upper bound.
//!
//! Even though it is recommended to use unsized integers for ID components, any types conforming
//! to the appropriate [`num_traits`](https://docs.rs/num-traits/latest/num_traits/index.html) may
//! be used.
//!
//! You may also think of the ID:s as a tree structure, where `3` has the children `3.0`, `3.1` etc
//! up to `3.T::max`, and `5.3` having the siblings `5.4`, `5.5`, `5.6` etc following it. For this
//! reason, [`GranularId<T>::children`], [`GranularId<T>::next_siblings`],
//! [`GranularId<T>::previous_siblings`] and [`GranularId<T>::all_siblings`], as well as
//! [`GranularId<T>::parent`] exist. If you were to build a tree structure, you may have a
//! [`root`](GranularId<T>::root) ID from which you assign all nodes living in the root ID:s from
//! the children of that root, and in turn assign each child of each children an ID derived from its
//! own ID. In that way, you are maintaining a total ordering of the children (assuming the
//! component type is totally ordered) while being able to easily find the parent ID of any node.
//! The [`root`](GranularId<T>::root) ID is a special ID since it doesn't have any components, and
//! is always the lowest ID.

use std::{cmp, fmt, iter::Iterator};

use num_traits::{Bounded, CheckedAdd, CheckedSub, One};
use num_traits::bounds::{LowerBounded, UpperBounded};

/// This is the main data type `GranularID` which represents
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GranularId<T> {
    id: Vec<T>,
}

impl<T: fmt::Display> fmt::Display for GranularId<T> {
    /// An `GranularId` is displayed similarly to a version string, where the `GranularId` created
    /// from the vector `[1, 2, 3]` is displayed as `1.2.3`. If the `GranularId` is the root ID
    /// (doesn't have any components), it is displayed as `<root>`.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut iter = self.id.iter();
        if let Some(x) = iter.next() {
            write!(f, "{x}")?;
            for x in iter {
                write!(f, ".{x}")?;
            }
        } else {
            write!(f, "<root>")?;
        }
        Ok(())
    }
}

impl<T> PartialOrd for GranularId<T>
    where
        T: Ord,
{
    /// Since `GranularId`s does have a total ordering if and only if its type has a total ordering,
    /// this function never returns `None` and just returns the value [`GranularId<T>::cmp`] would
    /// return
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<T> Ord for GranularId<T>
    where
        T: Ord,
{
    /// When comparing two [`GranularId`]s, their relative positioning is determined by its first
    /// non-matching component. All ID:s starting with `1` is less than all ID:s starting with a `2`
    /// and `1.2` is ordered before `1.2.0`. Here is an example of ordered `GranularId`s:
    /// * `1`
    /// * `1.0`
    /// * `1.1`
    /// * `1.1.0`
    /// * `1.1.1`
    /// * `1.1.2`
    /// * `1.2`
    /// * `2`
    /// For a [`GranularId`] to have a total ordering, the component type must also have a total
    /// ordering.
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        Iterator::zip(self.id.iter(), &other.id)
            .map(|(a, b)| a.cmp(b))
            .find(|x| *x != cmp::Ordering::Equal)
            .unwrap_or_else(|| self.id.len().cmp(&other.id.len()))
    }
}

impl<T> LowerBounded for GranularId<T>
{
    /// The lower bound for any [`GranularId`] (the smallest ID) is the empty ID which contains no
    /// components.
    fn min_value() -> Self {
        Self {
            id: vec![],
        }
    }
}

impl<T> UpperBounded for GranularId<T> where T: UpperBounded {
    /// The upper bound for any [`GranularId`] (the largest ID) is the empty ID which contains one
    /// component, containing the upper bound of the component type.
    fn max_value() -> Self {
        Self {
            id: vec![T::max_value()],
        }
    }
}

impl<T> From<Vec<T>> for GranularId<T>
    where
        T: PartialEq + UpperBounded + Ord
{
    /// A vector of components may be turned into a `GranularId`. Keep in mind that the maximum
    /// `GranularId` of any type `T` is the one containing just the component `T::max`, attempting
    /// to convert any vector starting with `T::max` will result in the
    /// [`upper bound`](GranularId<T>::upper_bound) `GranularId` for that type.
    fn from(other: Vec<T>) -> Self {
        if other
            .first()
            .map_or(false, |x| x == &T::max_value())
        {
            Self {
                id: vec![T::max_value()],
            }
        } else {
            Self { id: other }
        }
    }
}

impl<T> From<GranularId<T>> for Vec<T>
{
    /// A `GranularId` can be turned into a vector of its components.
    fn from(other: GranularId<T>) -> Vec<T> {
        other.id
    }
}

impl<T> GranularId<T>
    where T: SequentialId
{
    /// Gets all the siblings of this `GranularId`, ordered from the smallest sibling to the largest
    /// sibling. This is all the `GranularId`s which starts the same as this `GranularId` but has
    /// its last component changed.
    ///
    /// ```rust
    /// use granular_id::GranularId;
    /// let id = GranularId::from(vec![1u8, 2, 2]); // id 1.2.2
    /// let mut all_siblings = id.all_siblings();
    /// assert_eq!(all_siblings.next().unwrap(), vec![1, 2, 0].into()); // id 1.2.0
    /// assert_eq!(all_siblings.next().unwrap(), vec![1, 2, 1].into()); // id 1.2.1
    /// assert_eq!(all_siblings.next().unwrap(), vec![1, 2, 2].into()); // id 1.2.2
    /// assert_eq!(all_siblings.next().unwrap(), vec![1, 2, 3].into()); // id 1.2.3
    /// ```
    #[must_use]
    pub fn all_siblings(&self) -> SequentialIds<T>
        where T: LowerBounded {
        let mut id = self.id.clone();
        id.pop();
        SequentialIds {
            current: Some(T::min_value()),
            base: id,
        }
    }

    /// Gets all the next siblings of this `GranularId`, ordered from the smallest sibling larger
    /// than this ID to the largest sibling. This is all the `GranularId`s which starts the same as
    /// this `GranularId` but has its last component changed to any larger value.
    ///
    /// ```rust
    /// use granular_id::GranularId;
    /// let id = GranularId::from(vec![1u8, 2, 2]); // id 1.2.2
    /// let mut next_siblings = id.next_siblings();
    /// assert_eq!(next_siblings.next().unwrap(), vec![1, 2, 3].into()); // id 1.2.3
    /// assert_eq!(next_siblings.next().unwrap(), vec![1, 2, 4].into()); // id 1.2.4
    /// assert_eq!(next_siblings.next().unwrap(), vec![1, 2, 5].into()); // id 1.2.5
    /// assert_eq!(next_siblings.next().unwrap(), vec![1, 2, 6].into()); // id 1.2.6
    /// ```
    #[must_use]
    pub fn next_siblings(&self) -> SequentialIds<T>
        where T: CheckedAdd {
        let mut id = self.id.clone();
        let current = id.pop().and_then(|x| x.checked_add(&T::one()));
        SequentialIds {
            current,
            base: id,
        }
    }

    /// Gets all direct children of this `GranularId`, ordered from the smallest child (which is
    /// larger than this ID, but smallest out of all children) to the largest child. This is all
    /// the `GranularId`s which starts with this `GranularId` but has one additional component.
    ///
    /// ```rust
    /// use granular_id::GranularId;
    /// let id = GranularId::from(vec![1u8, 2]); // id 1.2
    /// let mut children = id.children();
    /// assert_eq!(children.next().unwrap(), vec![1, 2, 0].into()); // id 1.2.0
    /// assert_eq!(children.next().unwrap(), vec![1, 2, 1].into()); // id 1.2.1
    /// assert_eq!(children.next().unwrap(), vec![1, 2, 2].into()); // id 1.2.2
    /// assert_eq!(children.next().unwrap(), vec![1, 2, 3].into()); // id 1.2.3
    /// ```
    #[must_use]
    pub fn children(&self) -> SequentialIds<T> where
        T: LowerBounded,
    {
        SequentialIds {
            current: Some(T::min_value()),
            base: self.id.clone(),
        }
    }
}

impl<T> GranularId<T>
    where T: BackSequentialId {
    /// Gets all the previous siblings of this `GranularId`, ordered from the largest sibling
    /// smaller than this ID to the smallest sibling. This is all the `GranularId`s which starts the
    /// same as this `GranularId` but has its last component changed to any smaller value.
    ///
    /// ```rust
    /// use granular_id::GranularId;
    /// let id = GranularId::from(vec![1u8, 2, 3]); // id 1.2.3
    /// let mut previous_siblings = id.previous_siblings();
    /// assert_eq!(previous_siblings.next().unwrap(), vec![1, 2, 2].into()); // id 1.2.2
    /// assert_eq!(previous_siblings.next().unwrap(), vec![1, 2, 1].into()); // id 1.2.1
    /// assert_eq!(previous_siblings.next().unwrap(), vec![1, 2, 0].into()); // id 1.2.0
    /// assert_eq!(previous_siblings.next(), None); // No more smaller siblings
    /// ```
    #[must_use]
    pub fn previous_siblings(&self) -> BackSequentialIds<T>
        where T: Bounded + One + Clone + CheckedSub
    {
        let mut id = self.id.clone();
        let current = id.pop().and_then(|x| x.checked_sub(&T::one()));
        BackSequentialIds {
            current,
            base: id,
        }
    }
}

impl<T> GranularId<T> {
    /// Removes the last component of this `GranularId`. To get the parent of any `GranularId`
    /// without mutating it, see [`GranularId::parent`]
    ///
    /// ```rust
    /// use granular_id::GranularId;
    /// let mut id: GranularId<u8> = vec![1, 2, 3].into(); // id 1.2.3
    /// id.pop();
    /// assert_eq!(id, vec![1, 2].into()); // id 1.2
    /// ```
    pub fn pop(&mut self) {
        self.id.pop();
    }

    /// Gets the parent of this `GranularId`, that is, the same `GranularId` with the last component
    /// removed.
    ///
    /// ```rust
    /// use granular_id::GranularId;
    /// let id: GranularId<u8> = vec![1, 2, 3].into(); // id 1.2.3
    /// assert_eq!(id.parent(), vec![1, 2].into()); // id 1.2
    /// ```
    #[must_use]
    pub fn parent(&self) -> Self
        where T: Clone {
        let mut id = self.id.clone();
        id.pop();
        Self {
            id
        }
    }

    /// Gets the root `GranularId` of any type, that is, a `GranularId` without any components.
    /// That `GranularId` is the smallest one of that type.
    ///
    /// ```rust
    /// use granular_id::GranularId;
    /// let id: GranularId<u8> = GranularId::root(); // id <root>
    /// assert_eq!(Into::<Vec<u8>>::into(id), vec![]);
    /// ```
    #[must_use]
    pub fn root() -> Self {
        Self { id: vec![] }
    }
}

pub struct SequentialIds<T> {
    current: Option<T>,
    base: Vec<T>,
}

pub trait SequentialId: UpperBounded + One + Clone + PartialEq + Ord + CheckedAdd {}

impl<T: UpperBounded + One + Clone + PartialEq + Ord + CheckedAdd> SequentialId for T {}

impl<T> Iterator for SequentialIds<T>
    where
        T: SequentialId,
{
    type Item = GranularId<T>;

    fn next(&mut self) -> Option<Self::Item> {
        if self
            .base
            .first()
            .map_or(false, |x| x >= &T::max_value())
        {
            return None;
        }

        let x = self.current.as_ref()?;
        let mut id = self.base.clone();
        id.push(x.clone());
        self.current = x.checked_add(&T::one());
        Some(GranularId { id })
    }
}

pub trait BackSequentialId: Bounded + One + Clone + CheckedSub {}

impl<T: Bounded + One + Clone + CheckedSub> BackSequentialId for T {}

pub struct BackSequentialIds<T> {
    current: Option<T>,
    base: Vec<T>,
}

impl<T> Iterator for BackSequentialIds<T>
    where
        T: BackSequentialId
{
    type Item = GranularId<T>;

    fn next(&mut self) -> Option<Self::Item> {
        let x = self.current.as_ref()?;
        let mut id = self.base.clone();
        id.push(x.clone());
        self.current = x.checked_sub(&T::one());
        Some(GranularId { id })
    }
}
