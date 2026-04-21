//! Serde support for the AST.
//!
//! The AST types in [`crate::ast`] carry `Serialize`/`Deserialize` derives
//! only when the `serde` cargo feature is enabled (it is on by default).
//! This module is the home for anything serde-specific that is larger than
//! a derive attribute — custom wrapper types, binary-format helpers,
//! or format-versioning glue.
//!
//! Today it is intentionally thin: downstream consumers (e.g. the xezim
//! simulator) drive their own bincode/JSON pipeline directly off the AST
//! `Serialize` impls, so no helpers are required here yet. The module
//! exists so that any serde-adjacent code lands in one directory rather
//! than being sprinkled across `ast/*`.
//!
//! # Disabling serde
//!
//! Build without the default feature to drop the serde dependency and
//! compile the AST as pure data:
//!
//! ```text
//! cargo build --no-default-features
//! ```

// Re-export the serde crate so downstream code inside this crate can write
// `crate::serde::Serialize` instead of depending on the external name.
// (Outside this crate, users should depend on `serde` directly.)
#[cfg(feature = "serde")]
pub use ::serde::{Serialize, Deserialize};
