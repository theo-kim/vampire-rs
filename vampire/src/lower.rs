//! Lower the pure-Rust [`crate::ir`] representation into the FFI types used
//! by the linked Vampire C++ library.
//!
//! The lowering is mechanical: each IR node is rebuilt as the corresponding
//! FFI node, walking the tree in a single pass.  The FFI constructors
//! themselves take the global lock (`synced`) per call and perform symbol
//! interning on the Vampire side, so repeated references to the same IR
//! symbol resolve to the same C++ signature entry.
//!
//! A problem lowered here is completely independent of the IR it came from —
//! the returned `Problem` can be mutated (extra axioms appended, options
//! changed) before calling `solve_and_prove`.

use crate::ir;
use crate::{Formula, Function, Options, Predicate, Problem, Sort, Term};

// -- Public entry point -------------------------------------------------------

/// Rebuild an [`ir::Problem`] as an FFI [`Problem`] ready for solving.
///
/// `opts` is consumed and set on the returned problem.
pub fn lower_problem(p: &ir::Problem, opts: Options) -> Problem {
    let mode_tff = matches!(p.mode(), ir::LogicMode::Tff);
    let mut out = if mode_tff { Problem::new_tff(opts) } else { Problem::new(opts) };

    for s in p.sort_decls()   { out.declare_sort(lower_sort(s)); }
    for f in p.fn_decls()     { out.declare_function(lower_function(f)); }
    for pd in p.pred_decls()  { out.declare_predicate(lower_predicate(pd)); }

    for ax in p.axioms()      { out.with_axiom(lower_formula(ax)); }
    if let Some(c) = p.conjecture_ref() {
        out.conjecture(lower_formula(c));
    }

    out
}

// -- Symbol lowering ----------------------------------------------------------

fn lower_sort(s: &ir::Sort) -> Sort {
    match s.tptp_name() {
        "$i"    => Sort::default_sort(),
        "$int"  => Sort::int(),
        "$real" => Sort::real(),
        "$rat"  => Sort::rational(),
        // `$o` is not exposed by the ffi `Sort`; user-defined sorts go
        // through `Sort::new`, which interns on the C++ side.
        name    => Sort::new(name),
    }
}

fn lower_function(f: &ir::Function) -> Function {
    if let Some(i) = f.interp() {
        return Function::interpreted(f.name(), lower_interp(i));
    }
    if f.is_typed() {
        let arg_sorts: Vec<Sort> = f.arg_sorts().iter().map(lower_sort).collect();
        let ret_sort = f.ret_sort()
            .map(lower_sort)
            .expect("typed ir::Function missing return sort");
        return Function::typed(f.name(), &arg_sorts, ret_sort);
    }
    Function::new(f.name(), f.arity())
}

fn lower_predicate(p: &ir::Predicate) -> Predicate {
    if let Some(i) = p.interp() {
        return Predicate::interpreted(p.name(), lower_interp(i));
    }
    if p.is_typed() {
        let arg_sorts: Vec<Sort> = p.arg_sorts().iter().map(lower_sort).collect();
        return Predicate::typed(p.name(), &arg_sorts);
    }
    Predicate::new(p.name(), p.arity())
}

fn lower_interp(i: ir::Interp) -> crate::Interp {
    use crate::Interp as F;
    use ir::Interp as I;
    match i {
        I::Equal            => F::Equal,
        I::IntGreater       => F::IntGreater,
        I::IntGreaterEqual  => F::IntGreaterEqual,
        I::IntLess          => F::IntLess,
        I::IntLessEqual     => F::IntLessEqual,
        I::IntDivides       => F::IntDivides,
        I::IntSuccessor     => F::IntSuccessor,
        I::IntUnaryMinus    => F::IntUnaryMinus,
        I::IntPlus          => F::IntPlus,
        I::IntMinus         => F::IntMinus,
        I::IntMultiply      => F::IntMultiply,
        I::IntAbs           => F::IntAbs,
        I::RatGreater       => F::RatGreater,
        I::RatGreaterEqual  => F::RatGreaterEqual,
        I::RatLess          => F::RatLess,
        I::RatLessEqual     => F::RatLessEqual,
        I::RatPlus          => F::RatPlus,
        I::RatMinus         => F::RatMinus,
        I::RatMultiply      => F::RatMultiply,
        I::RatQuotient      => F::RatQuotient,
        I::RealGreater      => F::RealGreater,
        I::RealGreaterEqual => F::RealGreaterEqual,
        I::RealLess         => F::RealLess,
        I::RealLessEqual    => F::RealLessEqual,
        I::RealPlus         => F::RealPlus,
        I::RealMinus        => F::RealMinus,
        I::RealMultiply     => F::RealMultiply,
        I::RealQuotient     => F::RealQuotient,
    }
}

// -- Term ---------------------------------------------------------------------

fn lower_term(t: &ir::Term) -> Term {
    match t {
        ir::Term::Var(v)       => Term::new_var(v.index()),
        ir::Term::Int(s)       => Term::int(s),
        ir::Term::Real(s)      => Term::real(s),
        ir::Term::Rational(s)  => Term::rational(s),
        ir::Term::Apply(func, args) => {
            let ffi_func = lower_function(func);
            if args.is_empty() {
                ffi_func.with(())
            } else {
                let lowered: Vec<Term> = args.iter().map(lower_term).collect();
                ffi_func.with(lowered.as_slice())
            }
        }
    }
}

// -- Formula ------------------------------------------------------------------

fn lower_formula(f: &ir::Formula) -> Formula {
    match f {
        ir::Formula::True  => Formula::new_true(),
        ir::Formula::False => Formula::new_false(),

        ir::Formula::Atom { pred, args } => {
            let ffi_pred = lower_predicate(pred);
            let lowered: Vec<Term> = args.iter().map(lower_term).collect();
            ffi_pred.with(lowered.as_slice())
        }

        ir::Formula::Eq(lhs, rhs) => {
            Formula::new_eq(lower_term(lhs), lower_term(rhs))
        }
        ir::Formula::EqTyped { lhs, rhs, sort } => {
            Formula::new_eq_typed(lower_term(lhs), lower_term(rhs), lower_sort(sort))
        }

        ir::Formula::Not(inner) => Formula::new_not(lower_formula(inner)),

        ir::Formula::And(parts) => match parts.len() {
            0 => Formula::new_true(),
            1 => lower_formula(&parts[0]),
            _ => {
                let lowered: Vec<Formula> = parts.iter().map(lower_formula).collect();
                Formula::new_and(&lowered)
            }
        },
        ir::Formula::Or(parts) => match parts.len() {
            0 => Formula::new_false(),
            1 => lower_formula(&parts[0]),
            _ => {
                let lowered: Vec<Formula> = parts.iter().map(lower_formula).collect();
                Formula::new_or(&lowered)
            }
        },

        ir::Formula::Imp(a, b) => lower_formula(a).imp(lower_formula(b)),
        ir::Formula::Iff(a, b) => lower_formula(a).iff(lower_formula(b)),

        ir::Formula::Forall(v, body) => Formula::new_forall(v.index(), lower_formula(body)),
        ir::Formula::Exists(v, body) => Formula::new_exists(v.index(), lower_formula(body)),

        ir::Formula::ForallTyped(v, sort, body) => {
            Formula::new_forall_typed(v.index(), lower_sort(sort), lower_formula(body))
        }
        ir::Formula::ExistsTyped(v, sort, body) => {
            Formula::new_exists_typed(v.index(), lower_sort(sort), lower_formula(body))
        }
    }
}
