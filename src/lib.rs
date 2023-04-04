//! This crate contains the type `GranularId`, which is a data type which can provide ID numbers in
//! a sequential order, where between any two ID:s, there are infinitely many *more granular* ID:s.
//! You can think of this as version numbers with an infinite granularity, so if there are versions
//! 1 and 2, there are ID:s 1.1, 1.2, 1.3 etc in-between them. Additionally, in-between ID 1.1 and
//! 1.2, there are infinitely many ID:s 1.1.1, 1.1.2 and so on.
//!
//! `GranularId`s is best used with any unsized integer type, where each component of the ID:s may
//! range from the minimum bound to the maximum bound of that integer type. The `GranularId` that
//! starts with the upper bound of the integer type is the very maximum `GranularId`. This means
//! that, using `u8`, all these `GranularId<u8>`s exist, in increasing order:
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
//! `GranularId<T>` type if `T` has an upper bound.
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

use num_traits::bounds::{LowerBounded, UpperBounded};
use num_traits::{Bounded, CheckedAdd, CheckedSub, One};

/// The data type `GranularId` represents any ID which can have an arbitrary granularity,
/// meaning that there is indefinitely many `GranularId`s in-between any two `GranularId`s. It is
/// best used with unsized integer types such as `u8`, `u16`, `u32`, `u64` and `usize`, but may be
/// used with other data types implementing the required
/// [`num_traits`](https://docs.rs/num-traits/latest/num_traits/index.html) bounds.
///
/// An ID basically consists of multiple *components*
#[derive(Debug, Clone, PartialEq, Eq, Hash, Default)]
pub struct GranularId<T> {
    id: Vec<T>,
}

impl<T: fmt::Display> fmt::Display for GranularId<T> {
    /// A `GranularId` is displayed similarly to a version string, where the `GranularId` created
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
    /// and `1.2` is ordered before `1.2.0`. Here is an example of some ordered `GranularId`s:
    ///
    /// ```rust
    /// use num_traits::bounds::LowerBounded;
    /// use granular_id::GranularId;
    /// let vec: Vec<GranularId<u8>> = vec![
    ///     vec![1].into(),         // id 1
    ///     vec![1, 0].into(),      // id 1.0
    ///     vec![1, 1].into(),      // id 1.1
    ///     vec![1, 1, 0].into(),   // id 1.1.0
    ///     vec![1, 1, 1].into(),   // id 1.1.1
    ///     vec![1, 1, 2].into(),   // id 1.1.2
    ///     vec![1, 2].into(),      // id 1.2
    ///     vec![2].into(),         // id 2
    /// ];
    /// let mut min = GranularId::min_value();
    /// for id in vec {
    ///     assert!(id > min);
    ///     min = id;
    /// }
    /// ```
    ///
    /// For a [`GranularId`] to have a total ordering, the component type must also have a total
    /// ordering.
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        Iterator::zip(self.id.iter(), &other.id)
            .map(|(a, b)| a.cmp(b))
            .find(|x| *x != cmp::Ordering::Equal)
            .unwrap_or_else(|| self.id.len().cmp(&other.id.len()))
    }
}

impl<T> LowerBounded for GranularId<T> {
    /// The lower bound for any [`GranularId`] (the smallest ID) is the empty ID which contains no
    /// components.
    fn min_value() -> Self {
        Self { id: vec![] }
    }
}

impl<T> UpperBounded for GranularId<T>
where
    T: UpperBounded,
{
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
    T: PartialEq + UpperBounded,
{
    /// A vector of components may be turned into a `GranularId`. Keep in mind that the maximum
    /// `GranularId` of any type `T` is the one containing just the component `T::max`, attempting
    /// to convert any vector starting with `T::max` will result in the
    /// [`upper bound`](GranularId<T>::max_value) `GranularId` for that type.
    fn from(other: Vec<T>) -> Self {
        if other.first().map_or(false, |x| x == &T::max_value()) {
            Self {
                id: vec![T::max_value()],
            }
        } else {
            Self { id: other }
        }
    }
}

impl<T> From<&[T]> for GranularId<T>
where
    T: PartialEq + UpperBounded + Clone,
{
    /// A slice of components may be turned into a `GranularId`. Keep in mind that the maximum
    /// `GranularId` of any type `T` is the one containing just the component `T::max`, attempting
    /// to convert any vector starting with `T::max` will result in the
    /// [`upper bound`](GranularId<T>::max_value) `GranularId` for that type.
    fn from(other: &[T]) -> Self {
        if other.first().map_or(false, |x| x == &T::max_value()) {
            Self {
                id: vec![T::max_value()],
            }
        } else {
            Self { id: other.to_vec() }
        }
    }
}

impl<T> From<GranularId<T>> for Vec<T> {
    /// Turns a `GranularId` into a vector of its components.
    fn from(other: GranularId<T>) -> Vec<T> {
        other.id
    }
}

impl<T> GranularId<T>
where
    T: SequentialId,
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
    where
        T: LowerBounded,
    {
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
    where
        T: CheckedAdd,
    {
        let mut id = self.id.clone();
        let current = id.pop().and_then(|x| x.checked_add(&T::one()));
        SequentialIds { current, base: id }
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
    pub fn children(&self) -> SequentialIds<T>
    where
        T: LowerBounded,
    {
        SequentialIds {
            current: Some(T::min_value()),
            base: self.id.clone(),
        }
    }
}

impl<T> GranularId<T>
where
    T: BackSequentialId,
{
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
    where
        T: Bounded + One + Clone + CheckedSub,
    {
        let mut id = self.id.clone();
        let current = id.pop().and_then(|x| x.checked_sub(&T::one()));
        BackSequentialIds { current, base: id }
    }
}

impl<T> GranularId<T> {
    /// Checks whether this `GranularId` is the maximum value of this type. If it is, no
    /// other larger `GranularId`s exist of the same type.
    ///
    /// ```rust
    /// use granular_id::GranularId;
    /// let not_max: GranularId<u8> = vec![254].into();
    /// let max: GranularId<u8> = vec![255].into();
    /// assert!(!not_max.is_max_value());
    /// assert!(max.is_max_value());
    /// ```
    #[must_use]
    pub fn is_max_value(&self) -> bool
    where
        T: UpperBounded + PartialEq,
    {
        self == &Self::max_value()
    }

    /// Gets the granularity of this `GranularId`, which is the number of components it contains,
    /// or the "precision" it has
    ///
    /// ```rust
    ///
    /// use granular_id::GranularId;
    /// let id: GranularId<u8> = vec![1, 2, 3, 4].into(); // id 1.2.3.4, granularity 4
    /// assert_eq!(id.granularity(), 4);
    /// // Its children should have granularity 5:
    /// assert_eq!(id.children().next().unwrap().granularity(), 5);
    /// ```
    #[must_use]
    pub fn granularity(&self) -> usize {
        self.id.len()
    }

    /// Checks whether this `GranularId` is the root, which means not having any components.
    ///
    /// ```rust
    /// use granular_id::GranularId;
    /// let not_root: GranularId<u8> = vec![254].into();
    /// let root: GranularId<u8> = vec![].into();
    /// assert!(!not_root.is_root());
    /// assert!(root.is_root());
    /// ```
    #[must_use]
    pub fn is_root(&self) -> bool {
        self.id.is_empty()
    }

    /// Turns this `GranularId` into its parent, that is, the same `GranularId` with the last
    /// component removed. If this `GranularId` is the root (has no components), this function
    /// returns the root. For a mutating version, see [`GranularId::pop`], and for a copying
    /// version, see [`GranularId::parent`]. If this `GranularId` doesn't have any components (is
    /// the root ID), this function returns `None` since the root ID doesn't have a parent.
    ///
    /// ```rust
    /// use granular_id::GranularId;
    /// let id: GranularId<u8> = vec![1, 2, 3].into(); // id 1.2.3
    /// assert_eq!(id.into_parent(), Some(vec![1, 2].into())); // id 1.2
    /// ```
    #[must_use]
    pub fn into_parent(mut self) -> Option<Self> {
        if self.id.is_empty() {
            return None;
        }
        self.id.pop();
        Some(self)
    }

    /// Gets the parent of this `GranularId`, that is, the same `GranularId` with the last component
    /// removed. If this `GranularId` doesn't have any components (is the root ID), this function
    /// returns `None` since the root ID doesn't have a parent.
    ///
    /// ```rust
    /// use granular_id::GranularId;
    /// let id: GranularId<u8> = vec![1, 2, 3].into(); // id 1.2.3
    /// assert_eq!(id.parent(), Some(vec![1, 2].into())); // id 1.2
    /// ```
    #[must_use]
    pub fn parent(&self) -> Option<Self>
    where
        T: Clone,
    {
        if self.id.is_empty() {
            return None;
        }
        let mut id = self.id.clone();
        id.pop();
        Some(Self { id })
    }

    /// Returns an iterator over the ancestors of this `GranularId`. The iterator will yield all the
    /// ancestors, in order from the next-most parent until the root `GranularId`. This will give the
    /// same results as iteratively calling [`GranularId::parent`]. This function consumes the
    /// `GranularId`.
    ///
    ///```rust
    /// use granular_id::GranularId;
    /// let id: GranularId<u8> = vec![1, 2, 3].into(); // id 1.2.3
    /// let mut ancestors = id.into_ancestors();
    /// assert_eq!(ancestors.next(), Some(vec![1, 2].into())); // id 1.2
    /// assert_eq!(ancestors.next(), Some(vec![1].into())); // id 1
    /// assert_eq!(ancestors.next(), Some(vec![].into())); // root id
    /// assert_eq!(ancestors.next(), None); // There are no more ancestors at this point
    ///```
    #[must_use]
    pub fn into_ancestors(self) -> Ancestors<T> {
        Ancestors {
            current: Some(self),
        }
    }

    /// Returns an iterator over the ancestors of this `GranularId`. The iterator will yield all the
    /// ancestors, in order from the next-most parent until the root `GranularId`. This will give the
    /// same results as iteratively calling [`GranularId::parent`].
    ///
    ///```rust
    /// use granular_id::GranularId;
    /// let id: GranularId<u8> = vec![1, 2, 3].into(); // id 1.2.3
    /// let mut ancestors = id.ancestors();
    /// assert_eq!(ancestors.next(), Some(vec![1, 2].into())); // id 1.2
    /// assert_eq!(ancestors.next(), Some(vec![1].into())); // id 1
    /// assert_eq!(ancestors.next(), Some(vec![].into())); // root id
    /// assert_eq!(ancestors.next(), None); // There are no more parents at this point
    ///```
    #[must_use]
    pub fn ancestors(&self) -> Ancestors<T>
    where
        T: Clone,
    {
        Ancestors {
            current: Some(self.clone()),
        }
    }

    /// Removes the last component of this `GranularId`. To get the parent of any `GranularId`
    /// without mutating it, see [`GranularId::parent`]. The function returns the component popped,
    /// akin to [`Vec::pop`], which is `None` if this `GranularId` doesn't have a parent. In that
    /// case, this `GranularId` will remain unchanged as the root.
    ///
    /// ```rust
    /// use granular_id::GranularId;
    /// let mut id: GranularId<u8> = vec![1, 2, 3].into(); // id 1.2.3
    /// assert_eq!(id.pop(), Some(3)); // popping the last component '3'
    /// assert_eq!(id, vec![1, 2].into()); // id 1.2
    /// ```
    pub fn pop(&mut self) -> Option<T> {
        self.id.pop()
    }

    /// Pushes a new component to the `GranularId`, adding it as a new last component. Since the
    /// maximum bound for a `GranularId` of type `T` is `[T::max]`, if any component is pushed to
    /// such an ID, the call doesn't do anything.
    ///
    /// ```rust
    /// use granular_id::GranularId;
    /// let mut id: GranularId<u8> = vec![1, 2, 3].into(); // id 1.2.3
    /// id.push(4);
    /// assert_eq!(id, vec![1, 2, 3, 4].into()); // id 1.2.3.4
    /// ```
    pub fn push(&mut self, component: T)
    where
        T: UpperBounded + PartialEq,
    {
        if self != &Self::max_value() {
            self.id.push(component);
        }
    }

    /// Makes a new `GranularId`, adding the given component as its new last component. Since the
    /// maximum bound for a `GranularId` of type `T` is `[T::max]`, if any component is pushed to
    /// such an ID, the call returns a plain copy of the original `GranularId`.
    ///
    /// ```rust
    /// use granular_id::GranularId;
    /// let mut id: GranularId<u8> = vec![1, 2, 3].into(); // id 1.2.3
    /// assert_eq!(id.pushing(4), vec![1, 2, 3, 4].into()); // id 1.2.3.4
    /// ```
    #[must_use]
    pub fn pushing(&self, component: T) -> Self
    where
        T: UpperBounded + PartialEq + Clone,
    {
        if self == &Self::max_value() {
            self.clone()
        } else {
            let mut id = self.id.clone();
            id.push(component);
            Self { id }
        }
    }

    /// Appends all components from another `GranularId` to this `GranularId`, adding them as a new
    /// last components. Since the maximum bound for a `GranularId` of type `T` is `[T::max]`, if
    /// any components is appended to such an ID, the call doesn't do anything.
    ///
    /// ```rust
    /// use granular_id::GranularId;
    /// let mut id: GranularId<u8> = vec![1, 2, 3].into(); // id 1.2.3
    /// let id_2 = vec![4, 5, 6].into(); // id 4.5.6
    /// id.append(id_2);
    /// assert_eq!(id, vec![1, 2, 3, 4, 5, 6].into()); // id 1.2.3.4.5.6
    /// ```
    pub fn append(&mut self, mut other: GranularId<T>)
    where
        T: UpperBounded + PartialEq,
    {
        if self != &Self::max_value() {
            self.id.append(&mut other.id);
        }
    }

    /// Makes a new `GranularId`, appending all components from another `GranularId` to that
    /// `GranularId`, adding them as a new last components. Since the maximum bound for a
    /// `GranularId` of type `T` is `[T::max]`, if any components is appended to such an ID, the
    /// call returns a copy of the original `GranularId`.
    ///
    /// ```rust
    /// use granular_id::GranularId;
    /// let mut id: GranularId<u8> = vec![1, 2, 3].into(); // id 1.2.3
    /// let id_2 = vec![4, 5, 6].into(); // id 4.5.6
    /// assert_eq!(id.appending(id_2), vec![1, 2, 3, 4, 5, 6].into()); // id 1.2.3.4.5.6
    /// ```
    #[must_use]
    pub fn appending(&self, mut other: GranularId<T>) -> GranularId<T>
    where
        T: UpperBounded + PartialEq + Clone,
    {
        if self == &Self::max_value() {
            self.clone()
        } else {
            let mut id = self.id.clone();
            id.append(&mut other.id);
            Self { id }
        }
    }

    /// Appends all components from a `Vec` to this `GranularId`, adding them as a new
    /// last components. Since the maximum bound for a `GranularId` of type `T` is `[T::max]`, if
    /// any components is appended to such an ID, the call doesn't do anything.
    ///
    /// ```rust
    /// use granular_id::GranularId;
    /// let mut id: GranularId<u8> = vec![1, 2, 3].into(); // id 1.2.3
    /// id.append_vec(vec![4, 5, 6]);
    /// assert_eq!(id, vec![1, 2, 3, 4, 5, 6].into()); // id 1.2.3.4.5.6
    /// ```
    pub fn append_vec(&mut self, mut other: Vec<T>)
    where
        T: UpperBounded + PartialEq,
    {
        if self.id.is_empty() {
            // If this is empty, replace the internal vec, making sure to use into() to not
            // exceed max
            let other_id: GranularId<T> = other.into();
            self.id = other_id.id;
        } else if self != &Self::max_value() {
            self.id.append(&mut other);
        }
    }

    /// Makes a new `GranularId`, appending all components from a `Vec` to that
    /// `GranularId`, adding them as a new last components. Since the maximum bound for a
    /// `GranularId` of type `T` is `[T::max]`, if any components is appended to such an ID, the
    /// call returns a copy of the original `GranularId`.
    ///
    /// ```rust
    /// use granular_id::GranularId;
    /// let mut id: GranularId<u8> = vec![1, 2, 3].into(); // id 1.2.3
    /// assert_eq!(id.appending_vec(vec![4, 5, 6]), vec![1, 2, 3, 4, 5, 6].into()); // id 1.2.3.4.5.6
    /// ```
    #[must_use]
    pub fn appending_vec(&self, mut other: Vec<T>) -> GranularId<T>
    where
        T: UpperBounded + PartialEq + Clone,
    {
        if self.id.is_empty() {
            other.into()
        } else if self != &Self::max_value() {
            let mut id = self.id.clone();
            id.append(&mut other);
            Self { id }
        } else {
            self.clone()
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

impl<T> IntoIterator for GranularId<T> {
    type Item = T;
    type IntoIter = <Vec<T> as IntoIterator>::IntoIter;

    /// Turns this `GranularId` into an iterator over its components, consuming them.
    fn into_iter(self) -> Self::IntoIter {
        self.id.into_iter()
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
        if self.base.first().map_or(false, |x| x >= &T::max_value()) {
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
    T: BackSequentialId,
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

pub struct Ancestors<T> {
    current: Option<GranularId<T>>,
}

impl<T> Iterator for Ancestors<T>
where
    T: Clone,
{
    type Item = GranularId<T>;

    fn next(&mut self) -> Option<Self::Item> {
        self.current = self.current.as_ref().and_then(GranularId::parent);
        self.current.clone()
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use super::*;

    #[test]
    fn keys_in_hm() {
        // Create a HM
        let mut hm: HashMap<GranularId<u8>, &'static str> = HashMap::new();

        // Create three sample keys
        let id_1: GranularId<u8> = vec![1].into();
        let id_1_1: GranularId<u8> = vec![1, 1].into();
        let id_2: GranularId<u8> = vec![2].into();

        // Inserting sample values
        hm.insert(id_1.clone(), "abc");
        hm.insert(id_1_1.clone(), "def");
        hm.insert(id_2.clone(), "ghi");

        // Checking that they work as expected
        assert_eq!(hm.get(&id_1).unwrap(), &"abc");
        assert_eq!(hm.get(&id_1_1).unwrap(), &"def");
        assert_eq!(hm.get(&id_2).unwrap(), &"ghi");
    }

    #[test]
    fn readme_example() {
        // Create a new GranularId from a vec of u8 (id: 1.2.3)
        let id: GranularId<u8> = vec![1, 2, 3].into();

        // Get the parent ID (id: 1.2)
        let parent = id.parent().unwrap();
        assert_eq!(parent, vec![1, 2].into());

        // Iterate over the following siblings of 1.2.3
        let mut next_siblings = id.next_siblings();
        // First one is 1.2.4
        assert_eq!(next_siblings.next().unwrap(), vec![1, 2, 4].into());
        // Then, 1.2.5, etc
        assert_eq!(next_siblings.next().unwrap(), vec![1, 2, 5].into());
        assert_eq!(next_siblings.next().unwrap(), vec![1, 2, 6].into());

        // Get an iterator over childrens of 1.2.3
        let mut children = id.children();
        // First one is 1.2.3.0
        assert_eq!(children.next().unwrap(), vec![1, 2, 3, 0].into());
        // Then, 1.2.3.1, etc
        assert_eq!(children.next().unwrap(), vec![1, 2, 3, 1].into());
        assert_eq!(children.next().unwrap(), vec![1, 2, 3, 2].into());

        // Each parent is always smaller than all of its children
        assert!(parent < id);
    }
}
