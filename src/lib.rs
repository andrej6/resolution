use std::fmt::{self, Formatter, Display};

/// An expression of truth-functional logic.
///
/// Hopefully this will also support first-order logic at some point.
#[derive(Debug)]
pub enum Expr {
    /// A conjunction of expressions (and).
    Conj(Box<Expr>, Box<Expr>),

    /// A disjunction of expressions (or).
    Disj(Box<Expr>, Box<Expr>),

    /// A negation of an expression (not).
    Neg(Box<Expr>),

    /// Material implication (if-then, implies).
    Impl(Box<Expr>, Box<Expr>),

    /// Bi-implication (if and only if).
    BiImpl(Box<Expr>, Box<Expr>),

    /// An atom, or proposition.
    Atom(String),
}

use Expr::*;

impl Expr {
    /// Consume two expressions and create the conjunction of them.
    pub fn and(a: Expr, b: Expr) -> Expr {
        Conj(Box::new(a), Box::new(b))
    }

    /// Consume two expressions and create the disjunction of them.
    pub fn or(a: Expr, b: Expr) -> Expr {
        Disj(Box::new(a), Box::new(b))
    }

    /// Consume an expression and create its negation.
    pub fn not(a: Expr) -> Expr {
        Neg(Box::new(a))
    }

    /// Consume two expressions and create the expression `a` implies `b`.
    pub fn if_then(a: Expr, b: Expr) -> Expr {
        Impl(Box::new(a), Box::new(b))
    }

    /// Consume two expressions and create the expression `a` if and only if `b`.
    pub fn iff(a: Expr, b: Expr) -> Expr {
        BiImpl(Box::new(a), Box::new(b))
    }

    /// Create a new atom (proposition) with the given name.
    pub fn atom(name: &str) -> Expr {
        Atom(String::from(name))
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Conj(a,b) => write!(f, "({} & {})", a, b),
            Disj(a,b) => write!(f, "({} | {})", a, b),
            Neg(a) => write!(f, "~{}", a),
            Impl(a,b) => write!(f, "({} -> {})", a, b),
            BiImpl(a,b) => write!(f, "({} <-> {})", a, b),
            Atom(s) => write!(f, "{}", s),
        }
    }
}
