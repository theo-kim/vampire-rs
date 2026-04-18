//! Symbols — sorts, functions, predicates, interpreted theory symbols.
//!
//! All three are pure data: a name, an arity, optional type signature, and a
//! few flags. They do not carry a Vampire-library identifier; resolution to the
//! C++ signature happens at lowering time.

use std::sync::Arc;

// -- Sort ---------------------------------------------------------------------

/// A sort (type) in TFF.
///
/// Built-ins (`$i`, `$int`, `$real`, `$rat`, `$o`) carry the `is_builtin` flag
/// so `tptp_decl` knows not to emit a redundant declaration for them.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Sort {
    name: Arc<str>,
    is_builtin: bool,
}

impl Sort {
    /// Creates (or names) a user-defined sort.
    pub fn new(name: &str) -> Self {
        Self { name: name.into(), is_builtin: false }
    }

    /// `$i` — the default untyped individual sort.
    pub fn default_sort() -> Self { Self::builtin("$i") }
    /// `$int`.
    pub fn int()      -> Self { Self::builtin("$int") }
    /// `$real`.
    pub fn real()     -> Self { Self::builtin("$real") }
    /// `$rat`.
    pub fn rational() -> Self { Self::builtin("$rat") }
    /// `$o` — the Boolean sort.
    pub fn bool()     -> Self { Self::builtin("$o") }

    fn builtin(name: &str) -> Self { Self { name: name.into(), is_builtin: true } }

    /// The TPTP identifier for this sort (e.g. `"$int"`, or a user name).
    pub fn tptp_name(&self) -> &str { &self.name }

    /// `true` for the five built-in TPTP sorts.
    pub fn is_builtin(&self) -> bool { self.is_builtin }

    /// `tff(<name>_type, type, <name>: $tType).` — or `None` for built-ins.
    pub fn tptp_decl(&self) -> Option<String> {
        if self.is_builtin { return None; }
        Some(format!("tff({name}_type, type, {name}: $tType).", name = self.name))
    }
}

// -- Function -----------------------------------------------------------------

/// A function symbol. Arity 0 functions are constants.
///
/// `arg_sorts` + `ret_sort` are populated when the symbol was created via
/// [`Function::typed`] or [`Function::interpreted`]; they're empty / `None` for
/// untyped FOF functions built via [`Function::new`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Function {
    name: Arc<str>,
    arity: u32,
    arg_sorts: Vec<Sort>,
    ret_sort: Option<Sort>,
    kind: FuncKind,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum FuncKind {
    Untyped,
    Typed,
    Interpreted(Interp),
}

impl Function {
    /// Untyped FOF function.
    pub fn new(name: &str, arity: u32) -> Self {
        Self {
            name: name.into(),
            arity,
            arg_sorts: Vec::new(),
            ret_sort: None,
            kind: FuncKind::Untyped,
        }
    }

    /// Typed TFF function with explicit argument and return sorts.
    pub fn typed(name: &str, arg_sorts: &[Sort], return_sort: Sort) -> Self {
        Self {
            name: name.into(),
            arity: arg_sorts.len() as u32,
            arg_sorts: arg_sorts.to_vec(),
            ret_sort: Some(return_sort),
            kind: FuncKind::Typed,
        }
    }

    /// Interpreted theory function (e.g. `$sum`, `$product`).
    pub fn interpreted(name: &str, interp: Interp) -> Self {
        let arity = interp.default_arity();
        Self {
            name: name.into(),
            arity,
            arg_sorts: Vec::new(),
            ret_sort: None,
            kind: FuncKind::Interpreted(interp),
        }
    }

    pub fn name(&self)      -> &str { &self.name }
    pub fn arity(&self)     -> u32  { self.arity }
    pub fn arg_sorts(&self) -> &[Sort] { &self.arg_sorts }
    pub fn ret_sort(&self)  -> Option<&Sort> { self.ret_sort.as_ref() }
    pub fn is_typed(&self)  -> bool { matches!(self.kind, FuncKind::Typed) }
    pub fn interp(&self)    -> Option<Interp> {
        match self.kind { FuncKind::Interpreted(i) => Some(i), _ => None }
    }

    /// `tff(fn_<name>, type, <name>: <arg_sorts> > <ret_sort>).` — or `None`
    /// for untyped / interpreted.
    pub fn tptp_decl(&self) -> Option<String> {
        if !self.is_typed() { return None; }
        let ret = self.ret_sort.as_ref().unwrap().tptp_name();
        if self.arg_sorts.is_empty() {
            return Some(format!("tff(fn_{name}, type, {name}: {ret}).", name = self.name, ret = ret));
        }
        let args: Vec<&str> = self.arg_sorts.iter().map(|s| s.tptp_name()).collect();
        let args_str = if args.len() == 1 {
            args[0].to_string()
        } else {
            format!("({})", args.join(" * "))
        };
        Some(format!(
            "tff(fn_{name}, type, {name}: {args} > {ret}).",
            name = self.name, args = args_str, ret = ret,
        ))
    }
}

// -- Predicate ----------------------------------------------------------------

/// A predicate symbol. Equivalent to a function returning `$o`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Predicate {
    name: Arc<str>,
    arity: u32,
    arg_sorts: Vec<Sort>,
    kind: PredKind,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum PredKind {
    Untyped,
    Typed,
    Interpreted(Interp),
}

impl Predicate {
    pub fn new(name: &str, arity: u32) -> Self {
        Self { name: name.into(), arity, arg_sorts: Vec::new(), kind: PredKind::Untyped }
    }

    pub fn typed(name: &str, arg_sorts: &[Sort]) -> Self {
        Self {
            name: name.into(),
            arity: arg_sorts.len() as u32,
            arg_sorts: arg_sorts.to_vec(),
            kind: PredKind::Typed,
        }
    }

    pub fn interpreted(name: &str, interp: Interp) -> Self {
        Self {
            name: name.into(),
            arity: interp.default_arity(),
            arg_sorts: Vec::new(),
            kind: PredKind::Interpreted(interp),
        }
    }

    pub fn name(&self)      -> &str { &self.name }
    pub fn arity(&self)     -> u32  { self.arity }
    pub fn arg_sorts(&self) -> &[Sort] { &self.arg_sorts }
    pub fn is_typed(&self)  -> bool { matches!(self.kind, PredKind::Typed) }
    pub fn interp(&self)    -> Option<Interp> {
        match self.kind { PredKind::Interpreted(i) => Some(i), _ => None }
    }

    /// `tff(pred_<name>_<arity>, type, <name>: <sorts> > $o).` — or `None`.
    pub fn tptp_decl(&self) -> Option<String> {
        if !self.is_typed() { return None; }
        if self.arg_sorts.is_empty() {
            return Some(format!(
                "tff(pred_{name}_{arity}, type, {name}: $o).",
                name = self.name, arity = self.arity,
            ));
        }
        let args: Vec<&str> = self.arg_sorts.iter().map(|s| s.tptp_name()).collect();
        let args_str = if args.len() == 1 {
            args[0].to_string()
        } else {
            format!("({})", args.join(" * "))
        };
        Some(format!(
            "tff(pred_{name}_{arity}, type, {name}: {args} > $o).",
            name = self.name, arity = self.arity, args = args_str,
        ))
    }
}

// -- Interpreted theory symbols ----------------------------------------------

/// Interpreted theory symbols for arithmetic and comparison.
///
/// Kept 1:1 with the variants used by sumo-kb and vampire-sys; future prover
/// backends may expose a subset.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Interp {
    Equal,
    IntGreater,    IntGreaterEqual, IntLess,        IntLessEqual,
    IntDivides,    IntSuccessor,    IntUnaryMinus,
    IntPlus,       IntMinus,        IntMultiply,    IntAbs,
    RatGreater,    RatGreaterEqual, RatLess,        RatLessEqual,
    RatPlus,       RatMinus,        RatMultiply,    RatQuotient,
    RealGreater,   RealGreaterEqual, RealLess,      RealLessEqual,
    RealPlus,      RealMinus,       RealMultiply,   RealQuotient,
}

impl Interp {
    /// Default arity used when only a name + interp is supplied.
    pub fn default_arity(self) -> u32 {
        match self {
            Interp::IntUnaryMinus | Interp::IntSuccessor | Interp::IntAbs => 1,
            _ => 2,
        }
    }
}
