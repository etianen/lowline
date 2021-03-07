//! A more efficient `Cow<str>` and `Vec<Cow<str>>`.
//!
//! ```
//! use lowline::Str;
//!
//! let s = Str::from("moo");
//! assert_eq!(s, "moo");
//!
//1 let s = Str::from(String::from("moo"));
//! assert_eq!(s, "moo");
//! ```
//!
//! Compared to `Cow<str>`, `lowline::Str`:
//!
//! - Is only two words wide, half the size of `Cow<str>`.
//! - Supports zero-copy `serde` deserialization out-the-box.
//! - Provides more efficient access to the underlying `str` buffer.
//!
//! The maximum length of a `lowline::Str` is `u32::MAX`. Data exceeding this limit will be silently (but safely)
//! truncated.
//!
//! Inspired by http://troubles.md/abusing-rustc and https://crates.io/crates/beef.

pub use crate::str::Str;

#[cfg(feature = "serde")] mod serde;
#[cfg(test)] mod test;
mod str;

// Our implementation assumes that two `u32` can fit inside a `usize`.
#[cfg(not(target_pointer_width = "64"))]
compile_error!("only 64-bit targets are supported");
