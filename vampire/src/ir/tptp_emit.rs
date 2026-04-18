//! TPTP serialisation — pure-Rust walkers over [`Term`] and [`Formula`].
//!
//! The output shape matches Vampire's accepted TPTP dialect for FOF
//! (`fof(...)`) and TFF (`tff(...)`). Sub-formula parenthesisation is
//! minimal: a parent only parenthesises a child whose top-level operator
//! binds more loosely than its own.

use std::fmt::Write as _;

use super::formula::Formula;
use super::symbol::Interp;
use super::term::Term;

/// Operator precedence used to decide when a child formula needs to be
/// parenthesised.  Lowest first.
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
        Formula::Iff(..) => Prec::Iff,
        Formula::Imp(..) => Prec::Imp,
        Formula::Or(..)  => Prec::Or,
        Formula::And(..) => Prec::And,
        Formula::Not(_)  => Prec::Not,
        Formula::Forall(..)      | Formula::ForallTyped(..)
        | Formula::Exists(..)    | Formula::ExistsTyped(..) => Prec::Quant,
        Formula::Atom { .. }     | Formula::Eq(..)
        | Formula::EqTyped { .. }
        | Formula::True          | Formula::False          => Prec::Atom,
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

pub(crate) fn term_to_tptp(t: &Term) -> String {
    let mut s = String::new();
    emit_term(&mut s, t);
    s
}

fn emit_term(out: &mut String, t: &Term) {
    match t {
        Term::Var(v) => {
            let _ = write!(out, "X{}", v.index());
        }
        Term::Apply(func, args) => {
            let name = interp_name(func.interp()).unwrap_or_else(|| func.name().to_string());
            out.push_str(&name);
            if !args.is_empty() {
                out.push('(');
                for (i, a) in args.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    emit_term(out, a);
                }
                out.push(')');
            }
        }
        Term::Int(v) | Term::Real(v) | Term::Rational(v) => out.push_str(v),
    }
}

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
                    if i > 0 {
                        out.push(',');
                    }
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

        // TFF equality serialises the same way as FOF equality; the sort
        // is carried for the prover's internal type-checking, not for the
        // surface syntax.
        Formula::EqTyped { lhs, rhs, sort: _ } => {
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
        if i > 0 {
            out.push_str(sep);
        }
        emit_sub(out, p, self_prec);
    }
}

fn interp_name(i: Option<Interp>) -> Option<String> {
    i.map(|i| match i {
        Interp::Equal            => "=".to_string(),
        Interp::IntGreater       | Interp::RatGreater      | Interp::RealGreater      => "$greater".into(),
        Interp::IntGreaterEqual  | Interp::RatGreaterEqual | Interp::RealGreaterEqual => "$greatereq".into(),
        Interp::IntLess          | Interp::RatLess         | Interp::RealLess         => "$less".into(),
        Interp::IntLessEqual     | Interp::RatLessEqual    | Interp::RealLessEqual    => "$lesseq".into(),
        Interp::IntDivides       => "$divides".into(),
        Interp::IntSuccessor     => "$succ".into(),
        Interp::IntUnaryMinus    => "$uminus".into(),
        Interp::IntPlus          | Interp::RatPlus         | Interp::RealPlus         => "$sum".into(),
        Interp::IntMinus         | Interp::RatMinus        | Interp::RealMinus        => "$difference".into(),
        Interp::IntMultiply      | Interp::RatMultiply     | Interp::RealMultiply     => "$product".into(),
        Interp::IntAbs           => "$abs".into(),
        Interp::RatQuotient      | Interp::RealQuotient    => "$quotient".into(),
    })
}

impl Term {
    /// Serialises this term to TPTP syntax.
    ///
    /// # Examples
    ///
    /// ```
    /// use vampire_prover::ir::{Function, Term};
    ///
    /// let f = Function::new("f", 2);
    /// let t = Term::apply(f, vec![Term::var(0), Term::int("1")]);
    /// assert_eq!(t.to_tptp(), "f(X0,1)");
    /// ```
    pub fn to_tptp(&self) -> String {
        term_to_tptp(self)
    }
}

impl Formula {
    /// Serialises this formula to TPTP syntax (no enclosing parentheses).
    ///
    /// # Examples
    ///
    /// ```
    /// use vampire_prover::ir::{Formula, Predicate, Term};
    ///
    /// let p = Predicate::new("P", 1);
    /// let f = Formula::atom(p, vec![Term::var(0)]);
    /// assert_eq!(f.to_tptp(), "P(X0)");
    /// ```
    pub fn to_tptp(&self) -> String {
        formula_to_tptp(self)
    }
}
