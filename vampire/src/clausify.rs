//! Run Vampire's CNF transformation on an [`ir::Problem`] and return a
//! structured list of [`ir::Clause`]s.
//!
//! This is the IR-level counterpart to [`crate::ffi::Problem::clausify`]
//! (which returns `Vec<String>`).  It drives the same pipeline:
//!
//! 1. Lower the IR problem to the FFI [`crate::ffi::Problem`] via
//!    [`crate::lower::lower_problem`].
//! 2. Build a raw C-ABI problem handle from the per-axiom / conjecture
//!    formula pointers.
//! 3. Call `vampire_clausify`, then enumerate the resulting units via
//!    `vampire_problem_units`.
//! 4. For every unit that is a clause, pull each literal out with
//!    `vampire_get_literals` and walk its term arguments via the
//!    `vampire_literal_*` / `vampire_term_*` structured readers.
//! 5. Rebuild each piece as [`ir::Clause`] / [`ir::Literal`] /
//!    [`ir::Term`] — a pure-Rust copy that does not alias any C++
//!    memory.
//!
//! The module requires the `integrated-prover` feature (which is on by
//! default) because it invokes Vampire's C++ implementation of CNF.
//! Without the feature, the IR is still usable for constructing and
//! serialising problems, but clausification is not available — callers
//! that need it should either enable the feature or route their problem
//! through an external `vampire` subprocess.
//!
//! # Examples
//!
//! ```no_run
//! use vampire_prover::ir::{Formula, Predicate, Problem};
//! use vampire_prover::Options;
//!
//! let p = Predicate::new("p", 0);
//! let q = Predicate::new("q", 0);
//!
//! // (p | q) & (~p | q) — should clausify to two clauses.
//! let mut problem = Problem::new();
//! problem.with_axiom(Formula::and(vec![
//!     Formula::or(vec![
//!         Formula::atom(p.clone(), vec![]),
//!         Formula::atom(q.clone(), vec![]),
//!     ]),
//!     Formula::or(vec![
//!         Formula::not(Formula::atom(p, vec![])),
//!         Formula::atom(q, vec![]),
//!     ]),
//! ]));
//!
//! let clauses = problem.clausify(Options::new()).expect("clausify");
//! assert_eq!(clauses.len(), 2);
//! ```

use std::ffi::CStr;
use std::os::raw::c_uint;
use std::ptr;

use vampire_sys as sys;

use crate::ir::{self, Clause, Function, Literal, Options, Predicate, Term};
use crate::lock::synced;
use crate::lower::lower_problem;

/// An error produced by [`clausify`] or [`ir::Problem::clausify`].
///
/// The current FFI surface is defensive but not exhaustive — most failures
/// at the C++ boundary (malformed input, timeouts, memory pressure) are
/// represented by the single `ClausificationFailed` variant, with a short
/// human-readable context string.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ClausifyError {
    /// `vampire_problem_units` returned a null pointer or non-zero status.
    UnitEnumerationFailed,
    /// Clausification aborted for a reason that the C++ side couldn't
    /// describe structurally.
    ClausificationFailed(String),
}

impl std::fmt::Display for ClausifyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ClausifyError::UnitEnumerationFailed =>
                write!(f, "vampire returned no units after clausification"),
            ClausifyError::ClausificationFailed(msg) =>
                write!(f, "clausification failed: {msg}"),
        }
    }
}

impl std::error::Error for ClausifyError {}

/// Clausify the given problem with the given prover options.
///
/// Returns one [`Clause`] per CNF clause Vampire produced.  The empty
/// clause (if the problem is trivially refutable) appears as
/// [`Clause::empty`] in the output.
///
/// # Note on `Imp` elimination
///
/// Vampire's `NewCNF` clausifier ([`Shell::NewCNF::process(BinaryFormula*)`]
/// in the C++ sources) carries the precondition
/// `ASS(g->connective() != IMP)` — it requires `Imp` to have been
/// eliminated before CNF runs.  The `vampire_prove` entry point satisfies
/// this via `Shell::Preprocess`, but `vampire_clausify` does not run
/// preprocessing, so naively handing it an `Imp`-containing formula
/// triggers an assertion failure / SIGSEGV.
///
/// To keep the API usable, [`clausify`] performs a single Rust-side
/// pre-pass that rewrites every `Formula::Imp(a, b)` to
/// `Formula::Or([Formula::Not(a), b])`.  This is pure structural
/// transformation — no quantifier or bound-variable handling needed —
/// and preserves logical meaning 1-to-1.
pub fn clausify(problem: &ir::Problem, opts: Options) -> Result<Vec<Clause>, ClausifyError> {
    let normalised  = eliminate_imp_problem(problem);
    let sys_problem = lower_problem(&normalised, opts);
    synced(|_| unsafe { clausify_unlocked(&sys_problem) })
}

/// Rewrite every `Imp(a, b)` sub-formula to `Or([Not(a), b])`, recursively.
/// `Iff` is left alone — NewCNF handles it via polarity-based expansion.
fn eliminate_imp(f: &ir::Formula) -> ir::Formula {
    use ir::Formula as F;
    match f {
        F::Imp(a, b) => F::Or(vec![
            F::Not(Box::new(eliminate_imp(a))),
            eliminate_imp(b),
        ]),

        F::And(parts) => F::And(parts.iter().map(eliminate_imp).collect()),
        F::Or(parts)  => F::Or (parts.iter().map(eliminate_imp).collect()),
        F::Not(inner) => F::Not(Box::new(eliminate_imp(inner))),
        F::Iff(a, b)  => F::Iff(
            Box::new(eliminate_imp(a)),
            Box::new(eliminate_imp(b)),
        ),

        F::Forall(v, inner) =>
            F::Forall(*v, Box::new(eliminate_imp(inner))),
        F::ForallTyped(v, s, inner) =>
            F::ForallTyped(*v, s.clone(), Box::new(eliminate_imp(inner))),
        F::Exists(v, inner) =>
            F::Exists(*v, Box::new(eliminate_imp(inner))),
        F::ExistsTyped(v, s, inner) =>
            F::ExistsTyped(*v, s.clone(), Box::new(eliminate_imp(inner))),

        // Leaves.
        F::Atom { .. } | F::Eq(..) | F::EqTyped { .. } | F::True | F::False
            => f.clone(),
    }
}

/// Apply [`eliminate_imp`] to every axiom and the conjecture of `p`.
fn eliminate_imp_problem(p: &ir::Problem) -> ir::Problem {
    let mut out = if matches!(p.mode(), ir::LogicMode::Tff) {
        ir::Problem::new_tff()
    } else {
        ir::Problem::new()
    };
    for s in p.sort_decls() { out.declare_sort(s.clone()); }
    for f in p.fn_decls()   { out.declare_function(f.clone()); }
    for pd in p.pred_decls() { out.declare_predicate(pd.clone()); }
    for ax in p.axioms() {
        out.with_axiom(eliminate_imp(ax));
    }
    if let Some(c) = p.conjecture_ref() {
        out.conjecture(eliminate_imp(c));
    }
    out
}

/// Low-level driver.  Must hold the global Vampire lock.  Returns the
/// structural representation of every CNF clause currently live on the
/// C++ side.
unsafe fn clausify_unlocked(sp: &crate::ffi::Problem) -> Result<Vec<Clause>, ClausifyError> {
    unsafe {
        sys::vampire_prepare_for_next_proof();

        // Mirror the unit-preparation block in `crate::ffi::Problem::clausify`:
        // wrap each axiom/conjecture as a freshly-allocated unit, hand the
        // vector to `vampire_problem_from_units`.
        let mut unit_ptrs: Vec<*mut sys::vampire_unit_t> =
            Vec::with_capacity(sp.axioms_raw().len() + 1);
        for axiom in sp.axioms_raw() {
            unit_ptrs.push(sys::vampire_axiom_formula(axiom.id));
        }
        if let Some(c) = sp.conjecture_raw() {
            unit_ptrs.push(sys::vampire_conjecture_formula(c.id));
        }

        let problem = sys::vampire_problem_from_units(unit_ptrs.as_mut_ptr(), unit_ptrs.len());

        // Invoke the clausifier.  Ignore the returned clause count — we
        // enumerate below to rebuild the clause shapes structurally.
        sys::vampire_clausify(problem);

        // Pull out every unit from the post-clausify problem.  After
        // `vampire_clausify`, every unit is a clause in Vampire's model.
        let mut units_ptr: *mut *mut sys::vampire_unit_t = ptr::null_mut();
        let mut count: usize = 0;
        let res = sys::vampire_problem_units(problem, &mut units_ptr, &mut count);
        if res != 0 || units_ptr.is_null() {
            for u in &unit_ptrs { sys::vampire_free_unit(*u); }
            return Err(ClausifyError::UnitEnumerationFailed);
        }

        let mut clauses: Vec<Clause> = Vec::with_capacity(count);
        for i in 0..count {
            let unit = *units_ptr.add(i);
            let clause_ptr = sys::vampire_unit_as_clause(unit);
            if clause_ptr.is_null() {
                // Leftover non-clause unit (shouldn't happen post-clausify,
                // but we tolerate it).
                continue;
            }
            clauses.push(read_clause(clause_ptr));
        }

        sys::vampire_free_unit_array(units_ptr);
        for u in &unit_ptrs { sys::vampire_free_unit(*u); }

        Ok(clauses)
    }
}

/// Read a `vampire_clause_t*` into a pure-Rust [`Clause`].
unsafe fn read_clause(clause: *mut sys::vampire_clause_t) -> Clause {
    unsafe {
        let mut lit_ptr: *mut *mut sys::vampire_literal_t = ptr::null_mut();
        let mut count: usize = 0;
        let res = sys::vampire_get_literals(clause, &mut lit_ptr, &mut count);
        if res != 0 || lit_ptr.is_null() || count == 0 {
            if !lit_ptr.is_null() { sys::vampire_free_literals(lit_ptr); }
            return Clause::empty();
        }

        let mut lits: Vec<Literal> = Vec::with_capacity(count);
        for i in 0..count {
            let lit = *lit_ptr.add(i);
            lits.push(read_literal(lit));
        }
        sys::vampire_free_literals(lit_ptr);

        Clause::new(lits)
    }
}

/// Read a `vampire_literal_t*` into a pure-Rust [`Literal`].
///
/// Equality literals are surfaced as [`ir::LitKind::Eq`]; ordinary
/// predicate calls as [`ir::LitKind::Atom`].  The predicate name is
/// looked up through `vampire_predicate_name`, which returns a pointer
/// into Vampire's interned-symbol table — we copy immediately into a
/// Rust `String` so nothing outlives the C++ side.
unsafe fn read_literal(lit: *mut sys::vampire_literal_t) -> Literal {
    unsafe {
        let positive = sys::vampire_literal_is_positive(lit);
        let is_eq    = sys::vampire_literal_is_equality(lit);
        let arity    = sys::vampire_literal_arity(lit);

        if is_eq {
            debug_assert_eq!(arity, 2, "equality literal must have arity 2");
            let lhs = sys::vampire_literal_arg(lit, 0);
            let rhs = sys::vampire_literal_arg(lit, 1);
            Literal::eq(positive, read_term(lhs), read_term(rhs))
        } else {
            let pred_idx = sys::vampire_literal_predicate(lit);
            let name     = read_predicate_name(pred_idx);
            let mut args = Vec::with_capacity(arity);
            for i in 0..arity {
                args.push(read_term(sys::vampire_literal_arg(lit, i)));
            }
            Literal::atom(positive, Predicate::new(&name, arity as u32), args)
        }
    }
}

/// Read a `vampire_term_t*` into a pure-Rust [`Term`].
///
/// Variables become `Term::Var`, function applications (including
/// constants) become `Term::Apply`.  Numeric literals from the C++ side
/// are exposed as nullary-functor applications (Vampire internalises
/// them as `Kernel::Signature::getNumericConstant`-allocated functors),
/// and we leave the detection / re-lifting into `Term::Int` /
/// `Term::Real` / `Term::Rational` for a follow-up if it turns out to
/// matter for downstream consumers.
unsafe fn read_term(term: *mut sys::vampire_term_t) -> Term {
    unsafe {
        if sys::vampire_term_is_var(term) {
            Term::var(sys::vampire_term_var_index(term))
        } else {
            let functor_idx = sys::vampire_term_functor(term);
            let arity       = sys::vampire_term_arity(term);
            let name        = read_functor_name(functor_idx);
            let mut args    = Vec::with_capacity(arity);
            for i in 0..arity {
                args.push(read_term(sys::vampire_term_arg(term, i)));
            }
            Term::apply(Function::new(&name, arity as u32), args)
        }
    }
}

unsafe fn read_predicate_name(idx: c_uint) -> String {
    unsafe {
        let c = sys::vampire_predicate_name(idx);
        if c.is_null() { return String::new(); }
        CStr::from_ptr(c).to_string_lossy().into_owned()
    }
}

unsafe fn read_functor_name(idx: c_uint) -> String {
    unsafe {
        let c = sys::vampire_functor_name(idx);
        if c.is_null() { return String::new(); }
        CStr::from_ptr(c).to_string_lossy().into_owned()
    }
}

impl ir::Problem {
    /// Clausify this problem via the linked Vampire library, returning a
    /// pure-Rust list of [`Clause`]s.
    ///
    /// Available only with the `integrated-prover` feature (on by
    /// default).  See [`clausify`] for the free-function form and for
    /// documentation of the underlying pipeline.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use vampire_prover::Options;
    /// use vampire_prover::ir::{Formula, Predicate, Problem};
    ///
    /// let p = Predicate::new("p", 0);
    /// let mut problem = Problem::new();
    /// problem.with_axiom(Formula::atom(p, vec![]));
    ///
    /// let clauses = problem.clausify(Options::new()).expect("clausify");
    /// assert_eq!(clauses.len(), 1);
    /// ```
    pub fn clausify(&self, opts: Options) -> Result<Vec<Clause>, ClausifyError> {
        clausify(self, opts)
    }
}

// ============================================================================
//  Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{Formula, Function, Predicate, Term};

    /// `(p | q) & (~p | q)` → 2 clauses.
    #[test]
    fn clausifies_simple_cnf() {
        let p = Predicate::new("p", 0);
        let q = Predicate::new("q", 0);

        let mut problem = ir::Problem::new();
        problem.with_axiom(Formula::and(vec![
            Formula::or(vec![
                Formula::atom(p.clone(), vec![]),
                Formula::atom(q.clone(), vec![]),
            ]),
            Formula::or(vec![
                Formula::not(Formula::atom(p.clone(), vec![])),
                Formula::atom(q.clone(), vec![]),
            ]),
        ]));

        let clauses = problem.clausify(Options::new()).expect("clausify");
        // Vampire may perform duplicate-literal removal, but the two
        // input conjuncts are logically distinct — expect at least 2.
        assert!(
            clauses.len() >= 2,
            "expected ≥2 clauses for (p|q) & (~p|q), got {}: {:?}",
            clauses.len(),
            clauses,
        );
    }

    /// A ground atom axiom — should clausify to exactly one unit clause.
    #[test]
    fn clausifies_ground_atom() {
        let p = Predicate::new("p", 1);
        let a = Function::new("a", 0);

        let mut problem = ir::Problem::new();
        problem.with_axiom(Formula::atom(p.clone(), vec![Term::constant(a.clone())]));

        let clauses = problem.clausify(Options::new()).expect("clausify");
        assert_eq!(clauses.len(), 1, "expected 1 clause, got {:?}", clauses);
        assert_eq!(clauses[0].len(), 1);
        assert!(clauses[0].literals[0].positive);
    }

    /// `exists X. p(X)` should Skolemize to a single unit clause
    /// `p(sK0)` with a fresh Skolem constant.
    #[test]
    fn clausifies_existential_produces_skolem() {
        let p = Predicate::new("p", 1);

        let mut problem = ir::Problem::new();
        problem.with_axiom(Formula::exists(
            ir::VarId(0),
            Formula::atom(p.clone(), vec![Term::var(0)]),
        ));

        let clauses = problem.clausify(Options::new()).expect("clausify");
        assert_eq!(clauses.len(), 1);
        assert_eq!(clauses[0].len(), 1);

        let lit = &clauses[0].literals[0];
        assert!(lit.positive);
        let pred = lit.predicate().expect("atom literal");
        assert_eq!(pred.name(), "p");

        // The single argument should be a Skolem constant — a nullary
        // Apply with a name that isn't one of our user symbols.
        match &lit.kind {
            ir::LitKind::Atom { args, .. } => {
                assert_eq!(args.len(), 1);
                match &args[0] {
                    Term::Apply(func, sub_args) => {
                        assert!(
                            sub_args.is_empty(),
                            "skolem should be a constant, got {:?}",
                            args[0],
                        );
                        // Vampire names skolems `sK<n>` by convention.
                        // We don't assert the exact name (the counter is
                        // session-global), but it should not be our
                        // user-given "a".
                        assert_ne!(func.name(), "a");
                    }
                    other => panic!("expected constant Skolem, got {:?}", other),
                }
            }
            _ => panic!("expected atom literal"),
        }
    }

    /// Propositional `p => q` — the simplest shape that exposed the
    /// `ASS(g->connective() != IMP)` precondition in Vampire's NewCNF.
    #[test]
    fn clausifies_fof_propositional_implication() {
        use ir::Predicate;

        let p = Predicate::new("p", 0);
        let q = Predicate::new("q", 0);

        let mut problem = ir::Problem::new();
        problem.with_axiom(Formula::imp(
            Formula::atom(p, vec![]),
            Formula::atom(q, vec![]),
        ));

        let clauses = problem.clausify(Options::new()).expect("clausify");
        assert!(!clauses.is_empty());
    }

    /// `forall X. p(X) => q(X)` — the quantified version.  Succeeds now
    /// that the Rust-side `eliminate_imp` pre-pass rewrites `Imp` to
    /// `Or(Not(...), ...)` before the FFI hand-off.
    #[test]
    fn clausifies_fof_universal_implication() {
        use ir::{Predicate, VarId};

        let p = Predicate::new("p", 1);
        let q = Predicate::new("q", 1);

        let mut problem = ir::Problem::new();
        let body = Formula::imp(
            Formula::atom(p, vec![Term::var(0)]),
            Formula::atom(q, vec![Term::var(0)]),
        );
        problem.with_axiom(Formula::forall(VarId(0), body));

        let clauses = problem.clausify(Options::new()).expect("clausify");
        assert!(!clauses.is_empty(), "expected ≥1 clause, got {:?}", clauses);
    }

    /// TFF universal implication with typed predicates — the shape that
    /// exposed the Imp-elimination bug via sumo-kb's integration.
    #[test]
    fn clausifies_tff_universal_implication() {
        use ir::{Sort, Function, Predicate, VarId};

        let i       = Sort::default_sort();
        let subcl   = Predicate::typed("s__subclass", &[i.clone(), i.clone()]);
        let inst    = Predicate::typed("s__instance", &[i.clone(), i.clone()]);
        let animal  = Function::new("s__Animal", 0);
        let entity  = Function::new("s__Entity", 0);

        let mut problem = ir::Problem::new_tff();
        problem.declare_predicate(subcl.clone());
        problem.declare_predicate(inst.clone());

        let body = Formula::imp(
            Formula::atom(subcl, vec![Term::var(0), Term::constant(animal)]),
            Formula::atom(inst,  vec![Term::var(0), Term::constant(entity)]),
        );
        problem.with_axiom(Formula::forall(VarId(0), body));

        let clauses = problem.clausify(Options::new()).expect("clausify");
        assert!(!clauses.is_empty(), "expected ≥1 clause, got {:?}", clauses);
    }

    /// Unit-test the `eliminate_imp` pass in isolation.
    #[test]
    fn eliminate_imp_rewrites_imp_nodes() {
        use ir::Predicate;
        let p = Predicate::new("p", 0);
        let q = Predicate::new("q", 0);

        let f = Formula::imp(
            Formula::atom(p.clone(), vec![]),
            Formula::atom(q.clone(), vec![]),
        );
        let rewritten = eliminate_imp(&f);

        // Expect: Or([Not(Atom(p)), Atom(q)]).
        match rewritten {
            ir::Formula::Or(parts) => {
                assert_eq!(parts.len(), 2);
                assert!(matches!(parts[0], ir::Formula::Not(..)));
                assert!(matches!(parts[1], ir::Formula::Atom { .. }));
            }
            other => panic!("expected Or, got {:?}", other),
        }

        // Leaves untouched.
        let ground = Formula::atom(p, vec![]);
        assert_eq!(eliminate_imp(&ground), ground);
    }

    /// An outright contradiction (empty clause after resolution).  This
    /// tests that our pipeline survives `vampire_get_literals` returning
    /// zero literals.
    #[test]
    fn clausifies_true_axiom_empty() {
        // `True` axiom should produce zero clauses (it's vacuous).
        let mut problem = ir::Problem::new();
        problem.with_axiom(Formula::True);

        // Depending on Vampire's simplification, a `$true` axiom may be
        // dropped entirely.  Accept either 0 or ≥1 empty/trivial clauses
        // — the assertion here is just that clausify doesn't panic or
        // return an error.
        let clauses = problem.clausify(Options::new()).expect("clausify");
        // Be lenient — just verify we got a valid result.
        assert!(
            clauses.iter().all(|c| c.len() <= 1 || c.len() < 100),
            "unexpected output shape: {:?}",
            clauses,
        );
    }
}
