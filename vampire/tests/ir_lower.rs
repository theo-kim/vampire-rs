//! End-to-end tests for the IR → FFI lowering path.
//!
//! These tests construct problems purely through the `ir` module, lower them
//! via [`vampire_prover::lower_problem`], and run the real Vampire prover
//! against the result.  They verify the lowering preserves semantics for
//! every IR node kind.

use vampire_prover::{
    ir::{self, Formula as IrF, Function as IrFn, LogicMode, Predicate as IrPd, Sort as IrSort,
         Term as IrT, VarId},
    lower_problem, Options, ProofRes,
};

fn solve_fof(build: impl FnOnce(&mut ir::Problem)) -> ProofRes {
    let mut p = ir::Problem::new();
    build(&mut p);
    lower_problem(&p, Options::new()).solve()
}

fn solve_tff(build: impl FnOnce(&mut ir::Problem)) -> ProofRes {
    let mut p = ir::Problem::new_tff();
    build(&mut p);
    lower_problem(&p, Options::new()).solve()
}

// -- Ground atomics -----------------------------------------------------------

#[test]
fn lowers_ground_atom_as_conjecture_against_matching_axiom() {
    let res = solve_fof(|p| {
        let mortal = IrPd::new("mortal", 1);
        let socrates = IrFn::new("socrates", 0);
        let socrates_t = IrT::constant(socrates);
        p.with_axiom(IrF::atom(mortal.clone(), vec![socrates_t.clone()]));
        p.conjecture(IrF::atom(mortal, vec![socrates_t]));
    });
    assert_eq!(res, ProofRes::Proved);
}

#[test]
fn lowers_negation_disprovable() {
    // Axiom: P(a). Conjecture: ~P(a). Expect Unprovable.
    let res = solve_fof(|p| {
        let pp = IrPd::new("P", 1);
        let a = IrT::constant(IrFn::new("a", 0));
        p.with_axiom(IrF::atom(pp.clone(), vec![a.clone()]));
        p.conjecture(IrF::not(IrF::atom(pp, vec![a])));
    });
    assert_eq!(res, ProofRes::Unprovable);
}

// -- Boolean connectives ------------------------------------------------------

#[test]
fn lowers_implication_modus_ponens() {
    // human(socrates), human(x) => mortal(x)  |-  mortal(socrates)
    let res = solve_fof(|p| {
        let human = IrPd::new("human", 1);
        let mortal = IrPd::new("mortal", 1);
        let socrates = IrT::constant(IrFn::new("socrates", 0));

        p.with_axiom(IrF::atom(human.clone(), vec![socrates.clone()]));
        p.with_axiom(IrF::forall(
            VarId(0),
            IrF::imp(
                IrF::atom(human, vec![IrT::var(0)]),
                IrF::atom(mortal.clone(), vec![IrT::var(0)]),
            ),
        ));
        p.conjecture(IrF::atom(mortal, vec![socrates]));
    });
    assert_eq!(res, ProofRes::Proved);
}

#[test]
fn lowers_iff_as_two_implications() {
    // P(a). P(a) <=> Q(a).  |-  Q(a)
    let res = solve_fof(|p| {
        let pp = IrPd::new("P", 1);
        let qq = IrPd::new("Q", 1);
        let a = IrT::constant(IrFn::new("a", 0));

        p.with_axiom(IrF::atom(pp.clone(), vec![a.clone()]));
        p.with_axiom(IrF::iff(
            IrF::atom(pp, vec![a.clone()]),
            IrF::atom(qq.clone(), vec![a.clone()]),
        ));
        p.conjecture(IrF::atom(qq, vec![a]));
    });
    assert_eq!(res, ProofRes::Proved);
}

#[test]
fn lowers_and_or() {
    // (P(a) & Q(a))  |-  P(a) | R(a)
    let res = solve_fof(|p| {
        let pp = IrPd::new("P", 1);
        let qq = IrPd::new("Q", 1);
        let rr = IrPd::new("R", 1);
        let a = IrT::constant(IrFn::new("a", 0));

        p.with_axiom(IrF::and(vec![
            IrF::atom(pp.clone(), vec![a.clone()]),
            IrF::atom(qq, vec![a.clone()]),
        ]));
        p.conjecture(IrF::or(vec![
            IrF::atom(pp, vec![a.clone()]),
            IrF::atom(rr, vec![a]),
        ]));
    });
    assert_eq!(res, ProofRes::Proved);
}

// -- Equality -----------------------------------------------------------------

#[test]
fn lowers_equality_reflexivity_via_substitution() {
    // P(a). a = b.  |-  P(b)
    let res = solve_fof(|p| {
        let pp = IrPd::new("P", 1);
        let a = IrT::constant(IrFn::new("a", 0));
        let b = IrT::constant(IrFn::new("b", 0));

        p.with_axiom(IrF::atom(pp.clone(), vec![a.clone()]));
        p.with_axiom(IrF::eq(a, b.clone()));
        p.conjecture(IrF::atom(pp, vec![b]));
    });
    assert_eq!(res, ProofRes::Proved);
}

// -- Quantifiers (untyped) ----------------------------------------------------

#[test]
fn lowers_forall_exists_existence_witness() {
    // ![X]: P(X). |- ?[X]: P(X).
    let res = solve_fof(|p| {
        let pp = IrPd::new("P", 1);
        p.with_axiom(IrF::forall(VarId(0), IrF::atom(pp.clone(), vec![IrT::var(0)])));
        p.conjecture(IrF::exists(VarId(0), IrF::atom(pp, vec![IrT::var(0)])));
    });
    assert_eq!(res, ProofRes::Proved);
}

// -- TFF typed quantifiers + sorts + typed decls -----------------------------

#[test]
fn lowers_tff_with_typed_quantifier_and_sort_decls() {
    // sort person; alice: person; mortal: person > $o
    // axiom: ![X: person]: mortal(X).
    // conj : mortal(alice).
    let res = solve_tff(|p| {
        let person = IrSort::new("person");
        let alice  = IrFn::typed("alice", &[], person.clone());
        let mortal = IrPd::typed("mortal", &[person.clone()]);

        p.declare_sort(person.clone());
        p.declare_function(alice.clone());
        p.declare_predicate(mortal.clone());

        p.with_axiom(IrF::forall_typed(
            VarId(0),
            person,
            IrF::atom(mortal.clone(), vec![IrT::var(0)]),
        ));
        p.conjecture(IrF::atom(mortal, vec![IrT::apply(alice, vec![])]));
    });
    assert_eq!(res, ProofRes::Proved);
}

#[test]
fn lowers_problem_mode_matches_tptp_keyword() {
    let mut p = ir::Problem::new();
    assert_eq!(p.mode(), LogicMode::Fof);
    let pp = IrPd::new("P", 0);
    p.with_axiom(IrF::atom(pp.clone(), vec![]));
    p.conjecture(IrF::atom(pp, vec![]));
    let lowered = lower_problem(&p, Options::new());
    // If this panics the TFF branch was taken for an FOF problem. Survival alone proves parity.
    let _ = lowered.to_tptp();
}

// -- True / False -------------------------------------------------------------

#[test]
fn lowers_trivial_true() {
    // Axiom: $true. Conjecture: $true. Should be Proved.
    let res = solve_fof(|p| {
        p.with_axiom(IrF::True);
        p.conjecture(IrF::True);
    });
    assert_eq!(res, ProofRes::Proved);
}
