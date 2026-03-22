use crate::{Formula, Problem, Sort, Term, Predicate, Function, Options, Interp};
use std::collections::HashMap;
use winnow::prelude::*;
use winnow::ascii::multispace0;
use winnow::token::take_while;
use winnow::combinator::{alt, opt, delimited, separated};

type PResult<O> = winnow::Result<O>;

#[derive(Debug)]
pub enum ParseError {
    Message(String),
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ParseError::Message(m) => write!(f, "{}", m),
        }
    }
}

impl std::error::Error for ParseError {}

/// Context for the TPTP parser to track variables and symbols.
#[derive(Debug)]
struct Context {
    sorts: HashMap<String, Sort>,
    variables: Vec<HashMap<String, (u32, Option<Sort>)>>,
    next_var_id: u32,
    predicates: HashMap<(String, usize), Predicate>,
    functions: HashMap<(String, usize), Function>,
    has_tff_types: bool,
    // User-defined sorts declared via $tType (in insertion order)
    declared_sorts: Vec<Sort>,
    // Typed functions/predicates (in insertion order)
    declared_functions: Vec<Function>,
    declared_predicates: Vec<Predicate>,
}

impl Context {
    fn new() -> Self {
        let mut sorts = HashMap::new();
        sorts.insert("$i".to_string(), Sort::default_sort());
        sorts.insert("$int".to_string(), Sort::int());
        sorts.insert("$real".to_string(), Sort::real());
        sorts.insert("$rat".to_string(), Sort::rational());
        sorts.insert("$o".to_string(), Sort::new("$o"));

        Self {
            sorts,
            variables: vec![HashMap::new()],
            next_var_id: 0,
            predicates: HashMap::new(),
            functions: HashMap::new(),
            has_tff_types: false,
            declared_sorts: Vec::new(),
            declared_functions: Vec::new(),
            declared_predicates: Vec::new(),
        }
    }

    fn push_scope(&mut self) {
        self.variables.push(HashMap::new());
    }

    fn pop_scope(&mut self) {
        self.variables.pop();
    }

    fn add_variable(&mut self, name: &str, sort: Option<Sort>) -> u32 {
        let id = self.next_var_id;
        self.next_var_id += 1;
        self.variables.last_mut().unwrap().insert(name.to_string(), (id, sort));
        id
    }

    fn find_variable(&self, name: &str) -> Option<(u32, Option<Sort>)> {
        for scope in self.variables.iter().rev() {
            if let Some(v) = scope.get(name) {
                return Some(v.clone());
            }
        }
        None
    }

    fn get_sort(&mut self, name: &str) -> Sort {
        self.sorts.entry(name.to_string()).or_insert_with(|| Sort::new(name)).clone()
    }

    fn get_predicate(&mut self, name: &str, arity: usize) -> Predicate {
        self.predicates.entry((name.to_string(), arity))
            .or_insert_with(|| {
                // TPTP built-in interpreted predicates (default to integer interpretations)
                match name {
                    "$less"      => Predicate::interpreted(name, Interp::IntLess),
                    "$lesseq"    => Predicate::interpreted(name, Interp::IntLessEqual),
                    "$greater"   => Predicate::interpreted(name, Interp::IntGreater),
                    "$greatereq" => Predicate::interpreted(name, Interp::IntGreaterEqual),
                    _ => Predicate::new(name, arity as u32),
                }
            })
            .clone()
    }

    fn get_function(&mut self, name: &str, arity: usize) -> Function {
        self.functions.entry((name.to_string(), arity))
            .or_insert_with(|| {
                // TPTP built-in interpreted functions (default to integer interpretations)
                match name {
                    "$sum"        => Function::interpreted(name, Interp::IntPlus),
                    "$difference" => Function::interpreted(name, Interp::IntMinus),
                    "$product"    => Function::interpreted(name, Interp::IntMultiply),
                    "$uminus"     => Function::interpreted(name, Interp::IntUnaryMinus),
                    "$abs"        => Function::interpreted(name, Interp::IntAbs),
                    _ => Function::new(name, arity as u32),
                }
            })
            .clone()
    }
}

pub struct TptpParser;

impl TptpParser {
    pub fn parse(input: &str) -> Result<Problem, ParseError> {
        let mut ctx = Context::new();
        // Collect formulas and roles; we'll build the Problem once we know the mode.
        let mut formulas: Vec<(String, Formula)> = Vec::new();

        let mut current_input = input;
        while !current_input.is_empty() {
            current_input = skip_comments_and_whitespace(current_input);
            if current_input.is_empty() { break; }

            if current_input.starts_with("fof") {
                let mut stateful_input = winnow::Stateful { input: current_input, state: &mut ctx };
                let res = parse_fof.parse_next(&mut stateful_input)
                    .map_err(|e| ParseError::Message(format!("FOF error at '{}': {}", stateful_input.input.chars().take(20).collect::<String>(), e)))?;
                let (_name, role, formula) = res;
                current_input = stateful_input.input;
                formulas.push((role.to_string(), formula));
            } else if current_input.starts_with("tff") {
                let start_input = current_input;
                let mut type_input = winnow::Stateful { input: start_input, state: &mut ctx };
                if let Ok(_) = parse_tff_type.parse_next(&mut type_input) {
                    current_input = type_input.input;
                } else {
                    let mut formula_input = winnow::Stateful { input: start_input, state: &mut ctx };
                    let res = parse_tff_formula.parse_next(&mut formula_input)
                        .map_err(|e| ParseError::Message(format!("TFF error at '{}': {}", formula_input.input.chars().take(20).collect::<String>(), e)))?;
                    let (_name, role, formula) = res;
                    current_input = formula_input.input;
                    formulas.push((role.to_string(), formula));
                }
            } else {
                if let Some(pos) = current_input.find(|c| c == 'f' || c == 't') {
                     current_input = &current_input[pos..];
                } else {
                     break;
                }
            }
        }

        // Choose mode based on whether any TFF type declarations were encountered.
        let mut problem = if ctx.has_tff_types {
            Problem::new_tff(Options::new())
        } else {
            Problem::new(Options::new())
        };

        // Transfer type declarations to the problem (for to_tptp() support).
        for s in ctx.declared_sorts {
            problem.declare_sort(s);
        }
        for f in ctx.declared_functions {
            problem.declare_function(f);
        }
        for p in ctx.declared_predicates {
            problem.declare_predicate(p);
        }

        for (role, formula) in formulas {
            Self::add_to_problem(&mut problem, &role, formula);
        }

        Ok(problem)
    }

    fn add_to_problem(problem: &mut Problem, role: &str, formula: Formula) {
        match role {
            "axiom" | "hypothesis" | "definition" | "lemma" | "theorem" => {
                problem.with_axiom(formula);
            }
            "conjecture" => {
                problem.conjecture(formula);
            }
            "negated_conjecture" => {
                problem.with_axiom(formula);
            }
            _ => {}
        }
    }
}

fn skip_comments_and_whitespace(mut input: &str) -> &str {
    loop {
        let prev = input;
        input = input.trim_start();
        if input.starts_with('%') {
            if let Some(pos) = input.find('\n') {
                input = &input[pos..];
            } else {
                input = "";
            }
        } else if input.starts_with('[') {
             if let Some(pos) = input.find(']') {
                 input = &input[pos+1..];
             }
        }
        if input == prev { break; }
    }
    input
}

type Stream<'a, 'ctx> = winnow::Stateful<&'a str, &'ctx mut Context>;

fn ws<'a, 'ctx>(input: &mut Stream<'a, 'ctx>) -> PResult<()> {
    multispace0.parse_next(input).map(|_| ())
}

fn ident<'a, 'ctx>(input: &mut Stream<'a, 'ctx>) -> PResult<&'a str> {
    let _ = ws(input)?;
    let res = take_while(1.., |c: char| c.is_alphanumeric() || c == '_' || c == '$' || c == '+' || c == '-').parse_next(input)?;
    let _ = ws(input)?;
    Ok(res)
}

fn op<'a, 'ctx>(mut s: &'static str) -> impl FnMut(&mut Stream<'a, 'ctx>) -> PResult<&'a str> {
    move |input: &mut Stream<'a, 'ctx>| {
        let _ = ws(input)?;
        let res = s.parse_next(input)?;
        let _ = ws(input)?;
        Ok(res)
    }
}

fn punct<'a, 'ctx>(c: char) -> impl FnMut(&mut Stream<'a, 'ctx>) -> PResult<char> {
    move |input: &mut Stream<'a, 'ctx>| {
        let _ = ws(input)?;
        let res = winnow::token::one_of(c).parse_next(input)?;
        let _ = ws(input)?;
        Ok(res)
    }
}

fn parse_fof<'a, 'ctx>(input: &mut Stream<'a, 'ctx>) -> PResult<(&'a str, &'a str, Formula)> {
    let _ = op("fof").parse_next(input)?;
    let _ = punct('(').parse_next(input)?;
    let name = ident.parse_next(input)?;
    let _ = punct(',').parse_next(input)?;
    let role = ident.parse_next(input)?;
    let _ = punct(',').parse_next(input)?;
    let formula = parse_formula(input)?;
    let _ = punct(')').parse_next(input)?;
    let _ = punct('.').parse_next(input)?;
    Ok((name, role, formula))
}

fn parse_tff_type<'a, 'ctx>(input: &mut Stream<'a, 'ctx>) -> PResult<()> {
    let _ = op("tff").parse_next(input)?;
    let _ = punct('(').parse_next(input)?;
    let _name = ident.parse_next(input)?;
    let _ = punct(',').parse_next(input)?;
    let _type_role = op("type").parse_next(input)?;
    let _ = punct(',').parse_next(input)?;
    let symbol = ident.parse_next(input)?;
    let _ = punct(':').parse_next(input)?;
    // Parse the type expression and register the symbol
    parse_tff_type_expr(symbol, input)?;
    let _ = punct(')').parse_next(input)?;
    let _ = punct('.').parse_next(input)?;
    Ok(())
}

/// Parse an atomic sort name and return the Sort.
fn parse_sort_name<'a, 'ctx>(input: &mut Stream<'a, 'ctx>) -> PResult<Sort> {
    let name = ident.parse_next(input)?;
    Ok(input.state.get_sort(name))
}

/// Parse a comma-separated list of sorts inside `( s1 * s2 * ... )`.
fn parse_sort_product<'a, 'ctx>(input: &mut Stream<'a, 'ctx>) -> PResult<Vec<Sort>> {
    let _ = punct('(').parse_next(input)?;
    let sorts: Vec<Sort> = separated(1.., parse_sort_name, punct('*')).parse_next(input)?;
    let _ = punct(')').parse_next(input)?;
    Ok(sorts)
}

/// Parse a TFF type expression for a symbol and register it appropriately.
///
/// Handles:
/// - `$tType`               → register as new sort
/// - `sort`                 → register as 0-arity typed function (constant of that sort)
/// - `sort > $o`            → register as 1-arg typed predicate
/// - `( s1 * s2 ) > $o`    → register as multi-arg typed predicate
/// - `sort > ret`           → register as 1-arg typed function
/// - `( s1 * s2 ) > ret`   → register as multi-arg typed function
fn parse_tff_type_expr<'a, 'ctx>(symbol: &'a str, input: &mut Stream<'a, 'ctx>) -> PResult<()> {
    input.state.has_tff_types = true;

    // Check for $tType (new sort declaration)
    let trimmed = input.input.trim_start();
    if trimmed.starts_with("$tType") {
        let _ = op("$tType").parse_next(input)?;
        let s = input.state.get_sort(symbol); // registers the sort
        input.state.declared_sorts.push(s);
        return Ok(());
    }

    // Parse arg sorts: either `(s1 * s2 * ...)` or a single sort name
    let trimmed = input.input.trim_start();
    let arg_sorts: Vec<Sort> = if trimmed.starts_with('(') {
        parse_sort_product(input)?
    } else {
        let s = parse_sort_name(input)?;
        vec![s]
    };

    // Check for `>` (function/predicate type)
    if opt(op(">")).parse_next(input)?.is_some() {
        let ret_sort = parse_sort_name(input)?;
        let bool_sort = input.state.get_sort("$o");
        if ret_sort == bool_sort {
            // It's a predicate
            let p = Predicate::typed(symbol, &arg_sorts);
            input.state.predicates.insert((symbol.to_string(), arg_sorts.len()), p.clone());
            input.state.declared_predicates.push(p);
        } else {
            // It's a function
            let f = Function::typed(symbol, &arg_sorts, ret_sort);
            input.state.functions.insert((symbol.to_string(), arg_sorts.len()), f.clone());
            input.state.declared_functions.push(f);
        }
    } else {
        // No `>`, so this is a constant of the given sort (0-arity)
        // arg_sorts has exactly one element (the sort of the constant)
        let sort = arg_sorts.into_iter().next().unwrap();
        let f = Function::typed(symbol, &[], sort);
        input.state.functions.insert((symbol.to_string(), 0), f.clone());
        input.state.declared_functions.push(f);
    }

    Ok(())
}

fn parse_tff_formula<'a, 'ctx>(input: &mut Stream<'a, 'ctx>) -> PResult<(&'a str, &'a str, Formula)> {
    let _ = op("tff").parse_next(input)?;
    let _ = punct('(').parse_next(input)?;
    let name = ident.parse_next(input)?;
    let _ = punct(',').parse_next(input)?;
    let role = ident.parse_next(input)?;
    let _ = punct(',').parse_next(input)?;
    let formula = parse_formula(input)?;
    let _ = punct(')').parse_next(input)?;
    let _ = punct('.').parse_next(input)?;
    Ok((name, role, formula))
}

fn parse_formula<'a, 'ctx>(input: &mut Stream<'a, 'ctx>) -> PResult<Formula> {
    parse_equiv(input)
}

fn parse_equiv<'a, 'ctx>(input: &mut Stream<'a, 'ctx>) -> PResult<Formula> {
    let mut left = parse_impl(input)?;
    while let Some(connector) = opt(alt((op("<=>"), op("<~>"), op("~|"), op("~&")))).parse_next(input)? {
        let right = parse_impl(input)?;
        left = match connector {
            "<=>" => left.iff(right),
            _ => left,
        };
    }
    Ok(left)
}

fn parse_impl<'a, 'ctx>(input: &mut Stream<'a, 'ctx>) -> PResult<Formula> {
    let mut left = parse_or(input)?;
    if let Some(_) = opt(op("=>")).parse_next(input)? {
        let right = parse_impl(input)?;
        left = left >> right;
    } else if let Some(_) = opt(op("<=")).parse_next(input)? {
        let right = parse_or(input)?;
        left = right >> left;
    }
    Ok(left)
}

fn parse_or<'a, 'ctx>(input: &mut Stream<'a, 'ctx>) -> PResult<Formula> {
    let mut left = parse_and(input)?;
    while let Some(_) = opt(punct('|')).parse_next(input)? {
        let right = parse_and(input)?;
        left = left | right;
    }
    Ok(left)
}

fn parse_and<'a, 'ctx>(input: &mut Stream<'a, 'ctx>) -> PResult<Formula> {
    let mut left = parse_unary(input)?;
    while let Some(_) = opt(punct('&')).parse_next(input)? {
        let right = parse_and(input)?;
        left = left & right;
    }
    Ok(left)
}

fn parse_unary<'a, 'ctx>(input: &mut Stream<'a, 'ctx>) -> PResult<Formula> {
    if let Some(_) = opt(punct('~')).parse_next(input)? {
        Ok(!parse_unary(input)?)
    } else {
        parse_primary(input)
    }
}

fn parse_primary<'a, 'ctx>(input: &mut Stream<'a, 'ctx>) -> PResult<Formula> {
    if let Some(_) = opt(punct('(')).parse_next(input)? {
        let f = parse_formula(input)?;
        let _ = punct(')').parse_next(input)?;
        Ok(f)
    } else if let Some(_) = opt(punct('!')).parse_next(input)? {
        parse_quantifier('!', input)
    } else if let Some(_) = opt(punct('?')).parse_next(input)? {
        parse_quantifier('?', input)
    } else if let Some(_) = opt(op("$true")).parse_next(input)? {
        Ok(Formula::new_true())
    } else if let Some(_) = opt(op("$false")).parse_next(input)? {
        Ok(Formula::new_false())
    } else {
        parse_atom_or_eq(input)
    }
}

fn parse_quantifier<'a, 'ctx>(q: char, input: &mut Stream<'a, 'ctx>) -> PResult<Formula> {
    let vars: Vec<(String, Option<Sort>)> = delimited(punct('['), separated(1.., parse_typed_var, punct(',')), punct(']')).parse_next(input)?;
    let _ = punct(':').parse_next(input)?;
    
    input.state.push_scope();
    let mut var_infos = Vec::new();
    for (name, sort) in &vars {
        let id = input.state.add_variable(name, sort.clone());
        var_infos.push((id, sort.clone()));
    }
    
    let f_res = parse_formula(input);
    input.state.pop_scope();
    
    let mut f = f_res?;
    for (id, sort) in var_infos.into_iter().rev() {
        f = if q == '!' {
            if let Some(s) = sort {
                Formula::new_forall_typed(id, s, f)
            } else {
                Formula::new_forall(id, f)
            }
        } else {
            if let Some(s) = sort {
                Formula::new_exists_typed(id, s, f)
            } else {
                Formula::new_exists(id, f)
            }
        };
    }
    Ok(f)
}

fn parse_typed_var<'a, 'ctx>(input: &mut Stream<'a, 'ctx>) -> PResult<(String, Option<Sort>)> {
    let name = ident.parse_next(input)?;
    let sort = if let Some(_) = opt(punct(':')).parse_next(input)? {
        Some(parse_sort_name(input)?)
    } else {
        None
    };
    Ok((name.to_string(), sort))
}

fn parse_atom_or_eq<'a, 'ctx>(input: &mut Stream<'a, 'ctx>) -> PResult<Formula> {
    let name = ident.parse_next(input)?;

    if let Some(args) = opt(delimited(punct('('), separated(1.., parse_term, punct(',')), punct(')'))).parse_next(input)? {
        let args: Vec<Term> = args;
        let trimmed = input.input.trim_start();
        if trimmed.starts_with('=') && !trimmed.starts_with("=>") {
            // Equality: name(...) = rhs — need a function term on the left
            let func = input.state.get_function(name, args.len());
            let left_term = Term::new_function(&func, &args);
            let _ = op("=").parse_next(input)?;
            let right_term = parse_term(input)?;
            Ok(left_term.eq(right_term))
        } else if trimmed.starts_with("!=") {
            // Disequality: name(...) != rhs — need a function term on the left
            let func = input.state.get_function(name, args.len());
            let left_term = Term::new_function(&func, &args);
            let _ = op("!=").parse_next(input)?;
            let right_term = parse_term(input)?;
            Ok(!left_term.eq(right_term))
        } else {
            // Predicate atom: name(args) — do NOT create an intermediate function term
            let p = input.state.get_predicate(name, args.len());
            Ok(p.with(args))
        }
    } else {
        let trimmed = input.input.trim_start();
        if trimmed.starts_with('=') && !trimmed.starts_with("=>") {
            let left_term = if let Some((id, _)) = input.state.find_variable(name) {
                Term::new_var(id)
            } else if name.chars().all(|c| c.is_digit(10) || c == '.') {
                if name.contains('.') { Term::real(name) } else { Term::int(name) }
            } else {
                let func = input.state.get_function(name, 0);
                Term::new_function(&func, &[])
            };
            let _ = op("=").parse_next(input)?;
            let right_term = parse_term(input)?;
            Ok(left_term.eq(right_term))
        } else if trimmed.starts_with("!=") {
            let left_term = if let Some((id, _)) = input.state.find_variable(name) {
                Term::new_var(id)
            } else if name.chars().all(|c| c.is_digit(10) || c == '.') {
                if name.contains('.') { Term::real(name) } else { Term::int(name) }
            } else {
                let func = input.state.get_function(name, 0);
                Term::new_function(&func, &[])
            };
            let _ = op("!=").parse_next(input)?;
            let right_term = parse_term(input)?;
            Ok(!left_term.eq(right_term))
        } else {
            // 0-arity predicate atom
            let p = input.state.get_predicate(name, 0);
            Ok(p.with(()))
        }
    }
}

fn parse_term<'a, 'ctx>(input: &mut Stream<'a, 'ctx>) -> PResult<Term> {
    let name = ident.parse_next(input)?;
    
    if let Some(args) = opt(delimited(punct('('), separated(1.., parse_term, punct(',')), punct(')'))).parse_next(input)? {
        let args: Vec<Term> = args;
        let f = input.state.get_function(name, args.len());
        Ok(Term::new_function(&f, &args))
    } else {
        if let Some((id, _)) = input.state.find_variable(name) {
            Ok(Term::new_var(id))
        } else {
            if name.chars().all(|c: char| c.is_digit(10) || c == '.' || (c == '-' && name.len() > 1)) {
                if name.contains('.') {
                    Ok(Term::real(name))
                } else {
                    Ok(Term::int(name))
                }
            } else {
                let f = input.state.get_function(name, 0);
                Ok(Term::new_function(&f, &[]))
            }
        }
    }
}
