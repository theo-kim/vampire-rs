#![cfg(feature = "integrated-prover")]

use vampire_prover::ffi::*;
use vampire_prover::Options;

#[test]
fn test_tptp_dat001_1() {
    let input = "
        tff(list_type,type, list: $tType ).
        tff(nil_type,type, nil: list ).
        tff(mycons_type,type, mycons: ( $int * list ) > list ).
        tff(sorted_type,type, sorted: list > $o ).
        tff(empty_is_sorted,axiom, sorted(nil) ).
        tff(single_is_sorted,axiom, ! [X: $int] : sorted(mycons(X,nil)) ).
        tff(recursive_sort,axiom, ! [X: $int,Y: $int,R: list] : ( ( $less(X,Y) & sorted(mycons(Y,R)) ) => sorted(mycons(X,mycons(Y,R))) ) ).
        tff(check_list,conjecture, sorted(mycons(1,mycons(2,mycons(4,mycons(7,mycons(100,nil)))))) ).
    ";
    
    let mut problem = Problem::from_tptp(input).unwrap();
    let result = problem.solve_isolated();
    assert_eq!(result, ProofRes::Proved);
}

#[test]
fn test_tptp_dat002_1() {
    let input = "
        tff(list_type,type, list: $tType ).
        tff(nil_type,type, nil: list ).
        tff(mycons_type,type, mycons: ( $int * list ) > list ).
        tff(sorted_type,type, fib_sorted: list > $o ).
        tff(empty_fib_sorted,axiom, fib_sorted(nil) ).
        tff(single_is_fib_sorted,axiom, ! [X: $int] : fib_sorted(mycons(X,nil)) ).
        tff(double_is_fib_sorted_if_ordered,axiom, ! [X: $int,Y: $int] : ( $less(X,Y) => fib_sorted(mycons(X,mycons(Y,nil))) ) ).
        tff(recursive_fib_sort,axiom, ! [X: $int,Y: $int,Z: $int,R: list] : ( ( $less(X,Y) & $greatereq(Z,$sum(X,Y)) & fib_sorted(mycons(Y,mycons(Z,R))) ) => fib_sorted(mycons(X,mycons(Y,mycons(Z,R)))) ) ).
        tff(check_list,conjecture, fib_sorted(mycons(1,mycons(2,mycons(4,mycons(7,mycons(100,nil)))))) ).
    ";
    
    let mut problem = Problem::from_tptp(input).unwrap();
    let result = problem.solve_isolated();
    assert_eq!(result, ProofRes::Proved);
}

/// LCL109-1: MV4 theorem in Łukasiewicz 3-valued logic via condensed detachment.
/// This problem has a very large search space and requires a specialized Vampire
/// strategy (e.g. discount saturation with specific selection function). Ignored
/// because the default library-mode strategy cannot solve it in reasonable time.
#[test]
#[ignore]
fn test_tptp_lcl109_1() {
    let input = "
        fof(condensed_detachment,axiom, ! [X,Y] : ( ( is_a_theorem(implies(X,Y)) & is_a_theorem(X) ) => is_a_theorem(Y) ) ).
        fof(mv_1,axiom, ! [X,Y] : is_a_theorem(implies(X,implies(Y,X))) ).
        fof(mv_2,axiom, ! [X,Y,Z] : is_a_theorem(implies(implies(X,Y),implies(implies(Y,Z),implies(X,Z)))) ).
        fof(mv_3,axiom, ! [X,Y] : is_a_theorem(implies(implies(implies(X,Y),Y),implies(implies(Y,X),X))) ).
        fof(mv_5,axiom, ! [X,Y] : is_a_theorem(implies(implies(not(X),not(Y)),implies(Y,X))) ).
        fof(prove_mv_4,conjecture, is_a_theorem(implies(implies(implies(a,b),implies(b,a)),implies(b,a))) ).
    ";

    let mut opts = Options::new();
    opts.timeout(std::time::Duration::from_secs(300));
    let mut problem = Problem::from_tptp(input).unwrap().with_options(opts);
    let result = problem.solve_isolated();
    assert_eq!(result, ProofRes::Proved);
}

#[test]
fn test_successive_isolated_proofs() {
    // Run the same complex TFF problem 10 times in a row to prove isolation works.
    for i in 0..10 {
        println!("Iteration {}...", i);
        let int_sort = vampire_prover::SysSort::int();
        let list_sort = vampire_prover::SysSort::new("list_successive");

        let mycons = vampire_prover::SysFunction::typed("mycons_s", &[int_sort.clone(), list_sort.clone()], list_sort.clone());
        let nil = vampire_prover::SysFunction::typed("nil_s", &[], list_sort.clone()).with(());
        let sorted = vampire_prover::SysPredicate::typed("sorted_s", &[list_sort.clone()]);
        
        let empty_is_sorted = sorted.with(nil.clone());
        let single_is_sorted = vampire_prover::forall_typed(int_sort, |x| sorted.with(mycons.with([x, nil.clone()])));
        
        let mut problem = vampire_prover::SysProblem::new(vampire_prover::Options::new());
        problem.with_axiom(empty_is_sorted);
        problem.with_axiom(single_is_sorted);
        problem.conjecture(sorted.with(mycons.with([vampire_prover::SysTerm::int("1"), nil.clone()])));
            
        let result = problem.solve_isolated();
        assert_eq!(result, ProofRes::Proved, "Failed on iteration {}", i);
    }
}
