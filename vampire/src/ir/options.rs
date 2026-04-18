//! Prover options — pure data, no FFI.
//!
//! Consumed by the FFI solve path (when `integrated-prover` is on) and
//! carried through lowering.  Fields are crate-visible so `ffi.rs` can read
//! them while applying to the C++ library.

use std::time::Duration;

/// Configuration for the theorem prover.
///
/// Used at lowering + solve time.  Options are pure data and can be
/// constructed without any C++ linkage.
#[derive(Debug, Clone, Default)]
pub struct Options {
    pub(crate) timeout: Option<Duration>,
    pub(crate) extra_options: Vec<(String, String)>,
}

impl Options {
    /// Fresh options (no timeout, no extras).
    pub fn new() -> Self { Self::default() }

    /// Set a proof-search timeout.
    pub fn timeout(&mut self, duration: Duration) -> &mut Self {
        self.timeout = Some(duration);
        self
    }

    /// Set an arbitrary Vampire option by name and value (e.g.
    /// `set_option("mode", "casc")`).
    pub fn set_option(&mut self, name: impl Into<String>, value: impl Into<String>) -> &mut Self {
        self.extra_options.push((name.into(), value.into()));
        self
    }

    /// Read-only accessor for the configured timeout.
    pub fn timeout_duration(&self) -> Option<Duration> { self.timeout }

    /// Read-only accessor for the extra key/value options.
    pub fn extras(&self) -> &[(String, String)] { &self.extra_options }
}
