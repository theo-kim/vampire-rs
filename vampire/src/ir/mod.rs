//! Pure-Rust intermediate representation for Vampire problems.
//!
//! This module defines [`Term`], [`Formula`], [`Sort`], [`Function`], [`Predicate`],
//! and [`Problem`] as plain Rust data structures, without any dependency on the
//! C++ Vampire library. It is the canonical representation for:
//!
//! - Serialising problems to TPTP (via [`Formula::to_tptp`], [`Problem::to_tptp`]).
//! - Consumers that construct problems without solving them (e.g. front-ends that
//!   pipe TPTP to an external subprocess prover).
//! - Other integrated provers that might plug into this crate in the future.
//!
//! When the `integrated-prover` feature is enabled, these types are lowered into
//! the linked Vampire library's native representation at solve time. Without the
//! feature, the IR still works for construction and serialisation — no C++ code
//! is linked.
//!
//! The IR is intentionally minimal: it models the logical structure of a TPTP
//! problem and nothing else. Proof search options, Vampire-specific tuning, and
//! the C-ABI types stay out of this module.

pub mod symbol;
pub mod term;
pub mod formula;
pub mod clause;
pub mod problem;
pub mod options;
pub(crate) mod tptp_emit;

pub use symbol::{Sort, Function, Predicate, Interp};
pub use term::{Term, VarId};
pub use formula::Formula;
pub use clause::{Clause, Literal, LitKind};
pub use problem::{Problem, LogicMode};
pub use options::Options;
