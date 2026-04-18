//! TPTP serialisation — pure-Rust walkers over [`Term`] and [`Formula`].
//!
//! The output shape matches Vampire's accepted TPTP dialect for FOF (`fof(...)`)
//! and TFF (`tff(...)`). Precedence is encoded with minimal parenthesisation: we
//! parenthesise only when a child's top-level operator is weaker than the parent.

use std::fmt::Write as _;

use super::symbol::Interp;
use super::term::Term;
use super::formula::Formula;

// -- Precedence ----------------------------------------------------------------
//
// Lowest → highest. Quantifiers bind tightest; Iff is weakest.
// We use this to decide when to parenthesise sub-formulas during emission.

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Prec {
    Iff = 0,
    Imp = 1,
    Or  = 2,
    And = 3,
    Not = 4,
    Quant = 5,
    Atom = 6,
}

fn top_prec(f: &Formula) -> Prec {
    match f {
        Formula::Iff(..)                              => Prec::Iff,
        Formula::Imp(..)                              => Prec::Imp,
        Formula::Or(..)                               => Prec::Or,
        Formula::And(..)                              => Prec::And,
        Formula::Not(_)                               => Prec::Not,
        Formula::Forall(..)      | Formula::ForallTyped(..) |
        Formula::Exists(..)      | Formula::ExistsTyped(..) => Prec::Quant,
        Formula::Atom { .. }     | Formula::Eq(..)    |
        Formula::EqTyped { .. }  | Formula::True      |
        Formula::False                                => Prec::Atom,
    }
}

fn emit_sub(out: &mut String, f: &Formula, parent: Prec) {
    if top_prec(f) < parent {
        out.push('(');
        emit_formula(out, f);
        out.push(')');
    } else {
        emit_formula(out, f);
    }
}

// -- Term ---------------------------------------------------------------------

pub(crate) fn term_to_tptp(t: &Term) -> String {
    let mut s = String::new();
    emit_term(&mut s, t);
    s
}

fn emit_term(out: &mut String, t: &Term) {
    match t {
        Term::Var(v) => { let _ = write!(out, "X{}", v.index()); }
        Term::Apply(func, args) => {
            let name = interp_name(func.interp()).unwrap_or_else(|| func.name().to_string());
            out.push_str(&name);
            if !args.is_empty() {
                out.push('(');
                for (i, a) in args.iter().enumerate() {
                    if i > 0 { out.push(','); }
                    emit_term(out, a);
                }
                out.push(')');
            }
        }
        Term::Int(v)      => out.push_str(v),
        Term::Real(v)     => out.push_str(v),
        Term::Rational(v) => out.push_str(v),
    }
}

// -- Formula ------------------------------------------------------------------

pub(crate) fn formula_to_tptp(f: &Formula) -> String {
    let mut s = String::new();
    emit_formula(&mut s, f);
    s
}

fn emit_formula(out: &mut String, f: &Formula) {
    match f {
        Formula::True  => out.push_str("$true"),
        Formula::False => out.push_str("$false"),

        Formula::Atom { pred, args } => {
            let name = interp_name(pred.interp()).unwrap_or_else(|| pred.name().to_string());
            out.push_str(&name);
            if !args.is_empty() {
                out.push('(');
                for (i, a) in args.iter().enumerate() {
                    if i > 0 { out.push(','); }
                    emit_term(out, a);
                }
                out.push(')');
            }
        }

        Formula::Eq(lhs, rhs) => {
            emit_term(out, lhs);
            out.push_str(" = ");
            emit_term(out, rhs);
        }

        Formula::EqTyped { lhs, rhs, sort: _ } => {
            // TFF equality is written the same way; the sort is carried for
            // the prover's internal type-checking, not for serialisation.
            emit_term(out, lhs);
            out.push_str(" = ");
            emit_term(out, rhs);
        }

        Formula::Not(inner) => {
            out.push('~');
            emit_sub(out, inner, Prec::Not);
        }

        Formula::And(parts) => emit_nary(out, parts, " & ", Prec::And),
        Formula::Or(parts)  => emit_nary(out, parts, " | ", Prec::Or),

        Formula::Imp(a, b) => {
            emit_sub(out, a, Prec::Imp);
            out.push_str(" => ");
            emit_sub(out, b, Prec::Imp);
        }

        Formula::Iff(a, b) => {
            emit_sub(out, a, Prec::Iff);
            out.push_str(" <=> ");
            emit_sub(out, b, Prec::Iff);
        }

        Formula::Forall(v, body) => {
            let _ = write!(out, "![X{}] : ", v.index());
            emit_sub(out, body, Prec::Quant);
        }
        Formula::ForallTyped(v, sort, body) => {
            let _ = write!(out, "![X{}: {}] : ", v.index(), sort.tptp_name());
            emit_sub(out, body, Prec::Quant);
        }
        Formula::Exists(v, body) => {
            let _ = write!(out, "?[X{}] : ", v.index());
            emit_sub(out, body, Prec::Quant);
        }
        Formula::ExistsTyped(v, sort, body) => {
            let _ = write!(out, "?[X{}: {}] : ", v.index(), sort.tptp_name());
            emit_sub(out, body, Prec::Quant);
        }
    }
}

fn emit_nary(out: &mut String, parts: &[Formula], sep: &str, self_prec: Prec) {
    for (i, p) in parts.iter().enumerate() {
        if i > 0 { out.push_str(sep); }
        emit_sub(out, p, self_prec);
    }
}

// -- Interpreted symbol names -------------------------------------------------

fn interp_name(i: Option<Interp>) -> Option<String> {
    i.map(|i| match i {
        Interp::Equal            => "=".to_string(),
        Interp::IntGreater       => "$greater".into(),
        Interp::IntGreaterEqual  => "$greatereq".into(),
        Interp::IntLess          => "$less".into(),
        Interp::IntLessEqual     => "$lesseq".into(),
        Interp::IntDivides       => "$divides".into(),
        Interp::IntSuccessor     => "$succ".into(),
        Interp::IntUnaryMinus    => "$uminus".into(),
        Interp::IntPlus          => "$sum".into(),
        Interp::IntMinus         => "$difference".into(),
        Interp::IntMultiply      => "$product".into(),
        Interp::IntAbs           => "$abs".into(),
        Interp::RatGreater       => "$greater".into(),
        Interp::RatGreaterEqual  => "$greatereq".into(),
        Interp::RatLess          => "$less".into(),
        Interp::RatLessEqual     => "$lesseq".into(),
        Interp::RatPlus          => "$sum".into(),
        Interp::RatMinus         => "$difference".into(),
        Interp::RatMultiply      => "$product".into(),
        Interp::RatQuotient      => "$quotient".into(),
        Interp::RealGreater      => "$greater".into(),
        Interp::RealGreaterEqual => "$greatereq".into(),
        Interp::RealLess         => "$less".into(),
        Interp::RealLessEqual    => "$lesseq".into(),
        Interp::RealPlus         => "$sum".into(),
        Interp::RealMinus        => "$difference".into(),
        Interp::RealMultiply     => "$product".into(),
        Interp::RealQuotient     => "$quotient".into(),
    })
}

// -- Public convenience wrappers ----------------------------------------------

impl Term {
    /// Serialise this term to TPTP syntax.
    pub fn to_tptp(&self) -> String { term_to_tptp(self) }
}

impl Formula {
    /// Serialise this formula to TPTP syntax (no enclosing parentheses).
    pub fn to_tptp(&self) -> String { formula_to_tptp(self) }
}
