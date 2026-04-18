//! A TPTP problem — declarations plus axioms plus an optional conjecture.
//!
//! This is the pure-Rust counterpart of the existing FFI-backed `Problem`.
//! For now it lives alongside the FFI type without replacing it; once the
//! lowering pass lands it will become the canonical representation.

use super::formula::Formula;
use super::symbol::{Function, Predicate, Sort};

/// TPTP logic dialect used when this problem is serialised.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LogicMode {
    /// First-order form (`fof(...)`).
    Fof,
    /// Typed first-order form (`tff(...)`).
    Tff,
}

/// A pure-Rust TPTP problem.
///
/// `with_axiom` / `conjecture` append; callers are responsible for the order
/// and uniqueness they want to see in the output. Declarations (sorts,
/// functions, predicates) are emitted in insertion order before the axioms.
#[derive(Debug, Clone, Default)]
pub struct Problem {
    mode: LogicMode,
    sort_decls: Vec<Sort>,
    fn_decls:   Vec<Function>,
    pred_decls: Vec<Predicate>,
    axioms:     Vec<Formula>,
    conjecture: Option<Formula>,
}

impl Default for LogicMode { fn default() -> Self { LogicMode::Fof } }

impl Problem {
    /// New FOF problem.
    pub fn new()     -> Self { Self { mode: LogicMode::Fof, ..Self::default() } }
    /// New TFF problem.
    pub fn new_tff() -> Self { Self { mode: LogicMode::Tff, ..Self::default() } }

    pub fn mode(&self) -> LogicMode { self.mode }

    // -- Builders -------------------------------------------------------------

    pub fn with_axiom(&mut self, f: Formula) -> &mut Self {
        self.axioms.push(f);
        self
    }

    pub fn conjecture(&mut self, f: Formula) -> &mut Self {
        self.conjecture = Some(f);
        self
    }

    pub fn declare_sort(&mut self, s: Sort)      -> &mut Self { self.sort_decls.push(s);  self }
    pub fn declare_function(&mut self, f: Function) -> &mut Self { self.fn_decls.push(f); self }
    pub fn declare_predicate(&mut self, p: Predicate) -> &mut Self { self.pred_decls.push(p); self }

    // -- Accessors ------------------------------------------------------------

    pub fn axioms(&self)     -> &[Formula]      { &self.axioms }
    pub fn conjecture_ref(&self) -> Option<&Formula> { self.conjecture.as_ref() }
    pub fn sort_decls(&self) -> &[Sort]         { &self.sort_decls }
    pub fn fn_decls(&self)   -> &[Function]     { &self.fn_decls }
    pub fn pred_decls(&self) -> &[Predicate]    { &self.pred_decls }

    // -- Serialisation --------------------------------------------------------

    /// Serialise the problem to TPTP. Uses `tff(...)` for TFF mode,
    /// `fof(...)` otherwise. Type declarations for sorts / typed functions /
    /// typed predicates are emitted first (each on its own line).
    ///
    /// For custom naming, iterate `problem.axioms()` yourself and call
    /// `formula.to_tptp()` per entry — that's how downstream consumers add
    /// comments (e.g. the original source) and choose identifiers.
    pub fn to_tptp(&self) -> String {
        let kw = match self.mode { LogicMode::Tff => "tff", LogicMode::Fof => "fof" };
        let mut out = String::new();

        for s in &self.sort_decls {
            if let Some(d) = s.tptp_decl() { out.push_str(&d); out.push('\n'); }
        }
        for f in &self.fn_decls {
            if let Some(d) = f.tptp_decl() { out.push_str(&d); out.push('\n'); }
        }
        for p in &self.pred_decls {
            if let Some(d) = p.tptp_decl() { out.push_str(&d); out.push('\n'); }
        }
        for (i, ax) in self.axioms.iter().enumerate() {
            out.push_str(&format!("{kw}(axiom_{i}, axiom, {}).\n", ax.to_tptp()));
        }
        if let Some(c) = &self.conjecture {
            out.push_str(&format!("{kw}(conjecture, conjecture, {}).\n", c.to_tptp()));
        }
        out
    }
}
