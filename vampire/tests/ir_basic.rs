//! Unit tests for the pure-Rust IR.
//!
//! These tests do not link or invoke the Vampire C++ library; they exercise
//! only the pure-Rust construction and serialisation paths.

use vampire_prover::ir::{Formula, Function, LogicMode, Predicate, Problem, Sort, Term, VarId};

// -- Term serialisation -------------------------------------------------------

#[test]
fn term_var_formats_as_x_index() {
    let t = Term::var(3);
    assert_eq!(t.to_tptp(), "X3");
}

#[test]
fn term_constant_has_no_parens() {
    let c = Term::constant(Function::new("socrates", 0));
    assert_eq!(c.to_tptp(), "socrates");
}

#[test]
fn term_function_application() {
    let f = Function::new("f", 2);
    let t = Term::apply(f, vec![Term::var(0), Term::var(1)]);
    assert_eq!(t.to_tptp(), "f(X0,X1)");
}

#[test]
fn term_nested_function() {
    let succ  = Function::new("succ", 1);
    let plus  = Function::new("plus", 2);
    let t = Term::apply(plus.clone(), vec![
        Term::apply(succ.clone(), vec![Term::var(0)]),
        Term::var(1),
    ]);
    assert_eq!(t.to_tptp(), "plus(succ(X0),X1)");
}

#[test]
fn term_int_real_rational_literals() {
    assert_eq!(Term::int("42").to_tptp(), "42");
    assert_eq!(Term::real("3.14").to_tptp(), "3.14");
    assert_eq!(Term::rational("1/3").to_tptp(), "1/3");
}

// -- Formula serialisation ----------------------------------------------------

#[test]
fn formula_atom() {
    let p = Predicate::new("P", 1);
    let a = Formula::atom(p, vec![Term::var(0)]);
    assert_eq!(a.to_tptp(), "P(X0)");
}

#[test]
fn formula_equality() {
    let eq = Formula::eq(Term::var(0), Term::var(1));
    assert_eq!(eq.to_tptp(), "X0 = X1");
}

#[test]
fn formula_negation_of_atom() {
    let p = Predicate::new("P", 0);
    let f = Formula::not(Formula::atom(p, vec![]));
    assert_eq!(f.to_tptp(), "~P");
}

#[test]
fn formula_double_negation_collapses() {
    let p = Predicate::new("P", 0);
    let f = Formula::not(Formula::not(Formula::atom(p, vec![])));
    assert_eq!(f.to_tptp(), "P");
}

#[test]
fn formula_and_two_atoms() {
    let p = Predicate::new("P", 0);
    let q = Predicate::new("Q", 0);
    let f = Formula::and(vec![
        Formula::atom(p, vec![]),
        Formula::atom(q, vec![]),
    ]);
    assert_eq!(f.to_tptp(), "P & Q");
}

#[test]
fn formula_and_flattens_nested() {
    let p = Predicate::new("P", 0);
    let q = Predicate::new("Q", 0);
    let r = Predicate::new("R", 0);
    let f = Formula::and(vec![
        Formula::and(vec![
            Formula::atom(p, vec![]),
            Formula::atom(q, vec![]),
        ]),
        Formula::atom(r, vec![]),
    ]);
    assert_eq!(f.to_tptp(), "P & Q & R");
}

#[test]
fn formula_and_drops_true_absorbs_false() {
    let p = Predicate::new("P", 0);
    assert_eq!(
        Formula::and(vec![Formula::True, Formula::atom(p.clone(), vec![])]).to_tptp(),
        "P",
    );
    assert_eq!(
        Formula::and(vec![Formula::atom(p, vec![]), Formula::False]).to_tptp(),
        "$false",
    );
}

#[test]
fn formula_or_dual_rules() {
    let p = Predicate::new("P", 0);
    assert_eq!(
        Formula::or(vec![Formula::False, Formula::atom(p.clone(), vec![])]).to_tptp(),
        "P",
    );
    assert_eq!(
        Formula::or(vec![Formula::atom(p, vec![]), Formula::True]).to_tptp(),
        "$true",
    );
}

#[test]
fn formula_imp_and_iff() {
    let p = Predicate::new("P", 0);
    let q = Predicate::new("Q", 0);
    let imp = Formula::imp(Formula::atom(p.clone(), vec![]), Formula::atom(q.clone(), vec![]));
    let iff = Formula::iff(Formula::atom(p, vec![]), Formula::atom(q, vec![]));
    assert_eq!(imp.to_tptp(), "P => Q");
    assert_eq!(iff.to_tptp(), "P <=> Q");
}

#[test]
fn formula_precedence_parenthesises_weaker_children() {
    let p = Predicate::new("P", 0);
    let q = Predicate::new("Q", 0);
    let r = Predicate::new("R", 0);
    // (P | Q) & R -- the | is weaker, so it must be parenthesised under &.
    let f = Formula::and(vec![
        Formula::or(vec![
            Formula::atom(p, vec![]),
            Formula::atom(q, vec![]),
        ]),
        Formula::atom(r, vec![]),
    ]);
    assert_eq!(f.to_tptp(), "(P | Q) & R");
}

#[test]
fn formula_precedence_skips_parens_for_higher_children() {
    let p = Predicate::new("P", 0);
    let q = Predicate::new("Q", 0);
    let r = Predicate::new("R", 0);
    // P & Q | R -- & is stronger, so no parens on the conjunction inside |.
    let f = Formula::or(vec![
        Formula::and(vec![
            Formula::atom(p, vec![]),
            Formula::atom(q, vec![]),
        ]),
        Formula::atom(r, vec![]),
    ]);
    assert_eq!(f.to_tptp(), "P & Q | R");
}

#[test]
fn formula_forall_untyped() {
    let p = Predicate::new("P", 1);
    let body = Formula::atom(p, vec![Term::var(0)]);
    let f = Formula::forall(VarId(0), body);
    assert_eq!(f.to_tptp(), "![X0] : P(X0)");
}

#[test]
fn formula_forall_typed() {
    let person = Sort::new("person");
    let p = Predicate::typed("mortal", &[person.clone()]);
    let body = Formula::atom(p, vec![Term::var(0)]);
    let f = Formula::forall_typed(VarId(0), person, body);
    assert_eq!(f.to_tptp(), "![X0: person] : mortal(X0)");
}

#[test]
fn formula_exists_typed() {
    let i = Sort::int();
    let gt_pred = Predicate::interpreted("$greater", vampire_prover::ir::Interp::IntGreater);
    let body = Formula::atom(gt_pred, vec![Term::var(0), Term::int("0")]);
    let f = Formula::exists_typed(VarId(0), i, body);
    assert_eq!(f.to_tptp(), "?[X0: $int] : $greater(X0,0)");
}

// -- Sort / declaration emission ---------------------------------------------

#[test]
fn sort_user_decl_is_tff_ttype() {
    let s = Sort::new("animal");
    assert_eq!(
        s.tptp_decl().unwrap(),
        "tff(animal_type, type, animal: $tType).",
    );
}

#[test]
fn sort_builtins_skip_decl() {
    for s in [Sort::default_sort(), Sort::int(), Sort::real(), Sort::rational(), Sort::bool()] {
        assert!(s.tptp_decl().is_none(), "builtin {} must not declare", s.tptp_name());
    }
}

#[test]
fn function_typed_decl_single_arg() {
    let person = Sort::new("person");
    let f = Function::typed("father_of", &[person.clone()], person);
    assert_eq!(
        f.tptp_decl().unwrap(),
        "tff(fn_father_of, type, father_of: person > person).",
    );
}

#[test]
fn function_typed_decl_multi_arg() {
    let person = Sort::new("person");
    let f = Function::typed("child_of", &[person.clone(), person.clone()], person);
    assert_eq!(
        f.tptp_decl().unwrap(),
        "tff(fn_child_of, type, child_of: (person * person) > person).",
    );
}

#[test]
fn predicate_typed_decl() {
    let person = Sort::new("person");
    let p = Predicate::typed("likes", &[person.clone(), person]);
    assert_eq!(
        p.tptp_decl().unwrap(),
        "tff(pred_likes_2, type, likes: (person * person) > $o).",
    );
}

#[test]
fn predicate_untyped_has_no_decl() {
    let p = Predicate::new("P", 3);
    assert!(p.tptp_decl().is_none());
}

// -- Problem-level emission ---------------------------------------------------

#[test]
fn problem_fof_emits_axioms_and_conjecture() {
    let mut pb = Problem::new();
    let p = Predicate::new("P", 1);
    let socrates = Term::constant(Function::new("socrates", 0));
    pb.with_axiom(Formula::atom(p.clone(), vec![socrates.clone()]));
    pb.conjecture(Formula::atom(p, vec![socrates]));

    let t = pb.to_tptp();
    assert!(t.contains("fof(axiom_0, axiom, P(socrates))."), "missing axiom: {}", t);
    assert!(t.contains("fof(conjecture, conjecture, P(socrates))."), "missing conj: {}", t);
}

#[test]
fn problem_tff_includes_sort_and_function_decls() {
    let mut pb = Problem::new_tff();
    let person = Sort::new("person");
    let alice  = Function::typed("alice", &[], person.clone());
    let mortal = Predicate::typed("mortal", &[person.clone()]);

    pb.declare_sort(person);
    pb.declare_function(alice.clone());
    pb.declare_predicate(mortal.clone());

    pb.with_axiom(Formula::atom(mortal, vec![Term::apply(alice, vec![])]));

    let t = pb.to_tptp();
    assert!(t.contains("tff(person_type, type, person: $tType)."), "{}", t);
    assert!(t.contains("tff(fn_alice, type, alice: person)."), "{}", t);
    assert!(t.contains("tff(pred_mortal_1, type, mortal: person > $o)."), "{}", t);
    assert!(t.contains("tff(axiom_0, axiom, mortal(alice))."), "{}", t);
}

#[test]
fn problem_mode_accessor() {
    assert_eq!(Problem::new().mode(),     LogicMode::Fof);
    assert_eq!(Problem::new_tff().mode(), LogicMode::Tff);
}
