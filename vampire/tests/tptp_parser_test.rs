use vampire_prover::{Problem, ProofRes};

#[test]
fn test_tptp_puz001() {
    let input = "
        fof(pelletier_21_1,axiom,( p => q )).
        fof(pelletier_21_2,axiom,( ~ p => r )).
        fof(pelletier_21_3,axiom,( q => s )).
        fof(pelletier_21_4,axiom,( r => s )).
        fof(pelletier_21,conjecture,( s )).
    ";
    
    let mut problem = Problem::from_tptp(input).unwrap();
    let result = problem.solve();
    assert_eq!(result, ProofRes::Proved);
}

#[test]
fn test_tptp_tff_basic() {
    let input = "
        tff(person_type, type, person: $tType).
        tff(socrates_type, type, socrates: person).
        tff(mortal_type, type, mortal: person > $o).
        tff(man_type, type, man: person > $o).
        
        tff(men_are_mortal, axiom, ![X: person] : (man(X) => mortal(X))).
        tff(socrates_is_man, axiom, man(socrates)).
        tff(socrates_is_mortal, conjecture, mortal(socrates)).
    ";
    
    let mut problem = Problem::from_tptp(input).unwrap();
    let result = problem.solve();
    assert_eq!(result, ProofRes::Proved);
}
