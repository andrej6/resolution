use std::fmt::{self, Formatter, Display};

/// An expression of truth-functional logic.
///
/// Hopefully this will also support first-order logic at some point.
#[derive(Debug, Clone)]
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

impl Expr {
    /// Consume two expressions and create the conjunction of them.
    pub fn and(a: Expr, b: Expr) -> Expr {
        Expr::Conj(Box::new(a), Box::new(b))
    }

    /// Consume two expressions and create the disjunction of them.
    pub fn or(a: Expr, b: Expr) -> Expr {
        Expr::Disj(Box::new(a), Box::new(b))
    }

    /// Consume an expression and create its negation.
    pub fn not(a: Expr) -> Expr {
        Expr::Neg(Box::new(a))
    }

    /// Consume two expressions and create the expression `a` implies `b`.
    pub fn if_then(a: Expr, b: Expr) -> Expr {
        Expr::Impl(Box::new(a), Box::new(b))
    }

    /// Consume two expressions and create the expression `a` if and only if `b`.
    pub fn iff(a: Expr, b: Expr) -> Expr {
        Expr::BiImpl(Box::new(a), Box::new(b))
    }

    /// Create a new atom (proposition) with the given name.
    pub fn atom(name: &str) -> Expr {
        Expr::Atom(String::from(name))
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Expr::Conj(a,b) => write!(f, "({} & {})", a, b),
            Expr::Disj(a,b) => write!(f, "({} | {})", a, b),
            Expr::Neg(a) => write!(f, "~{}", a),
            Expr::Impl(a,b) => write!(f, "({} -> {})", a, b),
            Expr::BiImpl(a,b) => write!(f, "({} <-> {})", a, b),
            Expr::Atom(s) => write!(f, "{}", s),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn write_atom() {
        assert_eq!("P", format!("{}", Expr::atom("P")));
    }

    #[test]
    fn write_and() {
        let p = Expr::atom("P");
        let q = Expr::atom("Q");
        let exp = Expr::and(p,q);

        assert_eq!("(P & Q)", format!("{}", exp));
    }

    #[test]
    fn write_nested() {
        let p = Expr::atom("P");
        let q = Expr::atom("Q");
        let exp = Expr::if_then(p.clone(),q);
        let exp = Expr::not(exp);
        let exp = Expr::and(p, exp);

        assert_eq!("(P & ~(P -> Q))", format!("{}", exp));
    }
}
