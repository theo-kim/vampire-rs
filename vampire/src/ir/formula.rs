//! Pure-Rust formula IR.

use super::symbol::{Predicate, Sort};
use super::term::{Term, VarId};

/// A first-order (and TFF) formula.
///
/// TFF typed variants (`EqTyped`, `ForallTyped`, `ExistsTyped`) carry an
/// explicit `Sort`; the untyped variants leave the sort implicit (`$i`).
/// Serialisation collapses untyped variants to TPTP FOF form automatically
/// based on the enclosing `Problem`'s logic mode.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Formula {
    /// `p(t1, ..., tn)`.
    Atom { pred: Predicate, args: Vec<Term> },

    /// `t1 = t2` (untyped).
    Eq(Term, Term),

    /// `t1 = t2` with an explicit TFF sort annotation on equality.
    EqTyped { lhs: Term, rhs: Term, sort: Sort },

    /// `F1 & F2 & ... & Fn`. Two or more conjuncts; binary use should pass
    /// two-element vectors.
    And(Vec<Formula>),

    /// `F1 | F2 | ... | Fn`.
    Or(Vec<Formula>),

    /// `~F`.
    Not(Box<Formula>),

    /// `F1 => F2`.
    Imp(Box<Formula>, Box<Formula>),

    /// `F1 <=> F2`.
    Iff(Box<Formula>, Box<Formula>),

    /// `![X] : F` — forall over a single variable, untyped.
    Forall(VarId, Box<Formula>),

    /// `![X: sort] : F` — forall over a TFF-typed variable.
    ForallTyped(VarId, Sort, Box<Formula>),

    /// `?[X] : F`.
    Exists(VarId, Box<Formula>),

    /// `?[X: sort] : F`.
    ExistsTyped(VarId, Sort, Box<Formula>),

    /// `$true`.
    True,

    /// `$false`.
    False,
}

impl Formula {
    // -- Atomic --
    pub fn atom(pred: Predicate, args: Vec<Term>) -> Self {
        debug_assert_eq!(pred.arity() as usize, args.len(),
            "Formula::atom arity mismatch for {}", pred.name());
        Self::Atom { pred, args }
    }
    pub fn eq(lhs: Term, rhs: Term)                                -> Self { Self::Eq(lhs, rhs) }
    pub fn eq_typed(lhs: Term, rhs: Term, sort: Sort)              -> Self { Self::EqTyped { lhs, rhs, sort } }

    // -- Boolean connectives --
    /// Conjunction. Flattens nested `And` and drops `True` operands; returns
    /// `True` if empty, or the single element if only one remains.
    pub fn and(fs: Vec<Formula>) -> Self {
        let mut flat: Vec<Formula> = Vec::with_capacity(fs.len());
        for f in fs {
            match f {
                Formula::True   => continue,
                Formula::False  => return Formula::False,
                Formula::And(inner) => flat.extend(inner),
                other           => flat.push(other),
            }
        }
        match flat.len() {
            0 => Formula::True,
            1 => flat.into_iter().next().unwrap(),
            _ => Formula::And(flat),
        }
    }

    /// Disjunction. Mirror of `and`.
    pub fn or(fs: Vec<Formula>) -> Self {
        let mut flat: Vec<Formula> = Vec::with_capacity(fs.len());
        for f in fs {
            match f {
                Formula::False  => continue,
                Formula::True   => return Formula::True,
                Formula::Or(inner) => flat.extend(inner),
                other           => flat.push(other),
            }
        }
        match flat.len() {
            0 => Formula::False,
            1 => flat.into_iter().next().unwrap(),
            _ => Formula::Or(flat),
        }
    }

    pub fn not(inner: Formula) -> Self {
        match inner {
            Formula::Not(f)  => *f,          // double-negation elimination
            Formula::True    => Formula::False,
            Formula::False   => Formula::True,
            other            => Formula::Not(Box::new(other)),
        }
    }

    pub fn imp(lhs: Formula, rhs: Formula) -> Self { Self::Imp(Box::new(lhs), Box::new(rhs)) }
    pub fn iff(lhs: Formula, rhs: Formula) -> Self { Self::Iff(Box::new(lhs), Box::new(rhs)) }

    // -- Quantifiers --
    pub fn forall(var: VarId, body: Formula)                       -> Self { Self::Forall(var, Box::new(body)) }
    pub fn forall_typed(var: VarId, sort: Sort, body: Formula)     -> Self { Self::ForallTyped(var, sort, Box::new(body)) }
    pub fn exists(var: VarId, body: Formula)                       -> Self { Self::Exists(var, Box::new(body)) }
    pub fn exists_typed(var: VarId, sort: Sort, body: Formula)     -> Self { Self::ExistsTyped(var, sort, Box::new(body)) }

    // -- Constants --
    pub const fn tt() -> Self { Self::True  }
    pub const fn ff() -> Self { Self::False }
}
