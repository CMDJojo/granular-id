# granular-id

[![Crates.io](https://img.shields.io/crates/v/granular-id.svg)](https://crates.io/crates/granular-id)
[![Docs.rs](https://docs.rs/granular-id/badge.svg)](https://docs.rs/granular-id)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

This crate provides a data type `GranularId<T>` that can represent ID numbers with arbitrary precision.

## Features

- `GranularId<T>` is a sequence of components of type `T` that can be ordered and compared.
- Between any two `GranularId<T>`s, there are infinitely many more granular IDs.
- `GranularId<T>` is best used with any unsized integer type, such as `u8`, `u16`, `u32`, etc.
- `GranularId<T>` can also be used with any type that implements the appropriate `num_traits`.
- `GranularId<T>` has methods to access its parent, children, siblings, and other relations in a tree-like structure.

## Example usage

```rust
use granular_id::GranularId;

fn test() {
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
```

## Installation

Add this to your `Cargo.toml`:

```toml
[dependencies]
granular-id = "0.4.1"
```

## License

This project is licensed under the MIT license. See [LICENSE](LICENSE) for more details.
