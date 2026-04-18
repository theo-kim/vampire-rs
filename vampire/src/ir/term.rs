//! Pure-Rust term IR.

use super::symbol::Function;

/// A variable identifier. Variables are referenced by index (like De Bruijn-ish
/// numbering but with explicit integers chosen by the builder).
///
/// The index alone is the identity; stringification uses `X<idx>` to match
/// Vampire's conventional variable naming.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VarId(pub u32);

impl VarId {
    pub fn index(self) -> u32 { self.0 }

    /// TPTP variable identifier (`X0`, `X1`, ...).
    pub fn tptp_name(self) -> String { format!("X{}", self.0) }
}

/// A first-order term.
///
/// `Apply` holds its `Function` inline (not by reference). Symbols are cheap
/// clones (`Arc<str>` inside); duplicating them keeps the tree independent of
/// an external symbol table.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Term {
    /// A variable, e.g. `X0`.
    Var(VarId),

    /// A function application `f(t1, ..., tn)`. Arity-0 applications are
    /// the canonical constant form.
    Apply(Function, Vec<Term>),

    /// An integer literal, stored textually for exact precision.
    Int(String),

    /// A real literal.
    Real(String),

    /// A rational literal.
    Rational(String),
}

impl Term {
    /// Construct a variable term from a `u32` index.
    pub fn var(idx: u32) -> Self { Self::Var(VarId(idx)) }

    /// Construct a constant (arity-0 function application).
    pub fn constant(func: Function) -> Self {
        debug_assert_eq!(func.arity(), 0, "Term::constant requires arity 0");
        Self::Apply(func, Vec::new())
    }

    /// Construct `f(args...)`.
    pub fn apply(func: Function, args: Vec<Term>) -> Self {
        debug_assert_eq!(func.arity() as usize, args.len(),
            "Term::apply arity mismatch for {}", func.name());
        Self::Apply(func, args)
    }

    /// Integer literal.
    pub fn int(value: impl Into<String>) -> Self     { Self::Int(value.into()) }
    /// Real literal.
    pub fn real(value: impl Into<String>) -> Self    { Self::Real(value.into()) }
    /// Rational literal.
    pub fn rational(value: impl Into<String>) -> Self { Self::Rational(value.into()) }

    /// The free-variable indices appearing in this term.
    ///
    /// Used by quantifier wrappers to decide whether a variable is free in a
    /// sub-term. This is the "set of indices that occur somewhere"; binding
    /// structure is handled at the Formula level.
    pub fn free_vars(&self) -> impl Iterator<Item = VarId> + '_ {
        FreeVarsIter { stack: vec![self] }
    }
}

struct FreeVarsIter<'a> { stack: Vec<&'a Term> }

impl<'a> Iterator for FreeVarsIter<'a> {
    type Item = VarId;
    fn next(&mut self) -> Option<Self::Item> {
        while let Some(t) = self.stack.pop() {
            match t {
                Term::Var(v) => return Some(*v),
                Term::Apply(_, args) => self.stack.extend(args.iter().rev()),
                Term::Int(_) | Term::Real(_) | Term::Rational(_) => {}
            }
        }
        None
    }
}
