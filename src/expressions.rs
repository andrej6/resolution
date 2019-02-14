/// Syntax tree representation for logical expressions.
///
/// Currently, only propositional (truth-functional) logic is supported.

use std::fmt::{self, Formatter, Display};
use regex::Regex;

/// A variable name.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct Var(String);

impl Var {
    /// Create a new variable with the given name. Checks the name
    /// against the regex `[a-zA-Z_][a-zA-Z0-9_]*`, and returns `None`
    /// if it doesn't match.
    pub fn new(name: &str) -> Option<Var> {
        lazy_static! {
            static ref RE: Regex = Regex::new("^[a-zA-Z_][a-zA-Z0-9_]*$").unwrap();
        }

        if RE.is_match(name) {
            Some(Var(String::from(name)))
        } else {
            None
        }
    }

    /// Create a new variable with the given name. Checks the name
    /// against the regex `[a-zA-Z_][a-zA-Z0-9_]*`, and panics if it doesn't
    /// match.
    pub fn new_unwrap(name: &str) -> Var {
        Var::new(name).unwrap()
    }

    /// Create a new variable with the given name. Checks the name
    /// against the regex `[a-zA-Z_][a-zA-Z0-9_]*`, and panics with the given
    /// message if it doesn't match.
    pub fn new_expect(name: &str, msg: &str) -> Var {
        Var::new(name).expect(msg)
    }
}

impl std::ops::Deref for Var {
    type Target = str;

    fn deref(&self) -> &str {
        &self.0
    }
}

/// A unary operator.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnarySym {
    Not,
}
use UnarySym::*;

/// A non-associative binary operator.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinarySym {
    Implies,
}
use BinarySym::*;

/// An associative binary operator.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AssocBinarySym {
    And,
    Or,
    Bicond,
}
use AssocBinarySym::*;

/// A logical expression.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    /// A predicate expression.
    Pred { name: Var, args: Vec<Var>, },

    /// A unary operator expression.
    UnaryOp { op: UnarySym, operand: Box<Expr>, },

    /// A non-associative binary operator expression.
    BinaryOp { op: BinarySym, left: Box<Expr>, right: Box<Expr>, },

    /// A string of operands joined by a single associative binary operator.
    AssocBinaryOp { op: AssocBinarySym, operands: Vec<Expr>, },
}

impl Expr {
    /// Create a conjunction of the given expressions. Returns `None` if
    /// there are fewer than two operands.
    pub fn and(operands: Vec<Expr>) -> Option<Expr> {
        if operands.len() < 2 {
            None
        } else {
            Some(Expr::AssocBinaryOp { op: And, operands, })
        }
    }

    /// Create a disjunction of the given expressions. Returns `None` if
    /// there are fewer than two operands.
    pub fn or(operands: Vec<Expr>) -> Option<Expr> {
        if operands.len() < 2 {
            None
        } else {
            Some(Expr::AssocBinaryOp { op: Or, operands })
        }
    }

    /// Consume an expression and create its negation.
    pub fn not(operand: Expr) -> Expr {
        Expr::UnaryOp { op: Not, operand: Box::new(operand), }
    }

    /// Consume two expressions and create the expression `left` implies `right`.
    pub fn implies(left: Expr, right: Expr) -> Expr {
        Expr::BinaryOp { op: Implies, left: Box::new(left), right: Box::new(right), }
    }

    /// Create a chain of biconditionals between the given expressions. Returns
    /// `None` if there are fewer than two operands.
    pub fn bicond(operands: Vec<Expr>) -> Option<Expr> {
        if operands.len() < 2 {
            None
        } else {
            Some(Expr::AssocBinaryOp { op: Bicond, operands })
        }
    }

    /// Create a new proposition with the given name.
    pub fn prop(name: Var) -> Expr {
        Expr::pred(name, Vec::new())
    }

    /// Create a new predicate with the given name and arguments. The arguments
    /// may be empty, in which case a proposition is created instead.
    pub fn pred(name: Var, args: Vec<Var>) -> Expr {
        Expr::Pred { name, args }
    }
}

impl Display for Var {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Display for UnarySym {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Not => write!(f, "~"),
        }
    }
}

impl Display for BinarySym {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Implies => write!(f, "->"),
        }
    }
}

impl Display for AssocBinarySym {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            And => write!(f, "&"),
            Or => write!(f, "|"),
            Bicond => write!(f, "<->"),
        }
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        use Expr::*;
        match self {
            // Proposition (predicate with no arguments)
            Pred { name, args } if args.len() == 0 => write!(f, "{}", name),
            
            // Predicate
            Pred { name, args } => {
                write!(f, "{}({})", name,
                    args.iter().map(<Var as ToString>::to_string).collect::<Vec<_>>().join(", "))
            },

            UnaryOp { op, operand } => {
                // Okay, so `operand` is a `&Box<Expr>`, so we need to deref
                // once to get a `Box<Expr>` and then deref again to get an `Expr`
                // and then make a ref from that so we don't move it in the pattern
                // match... boy, the borrow rules are bonkers...
                match &**operand {
                    // Put parentheses only around non-literal expressions
                    Pred{..} | UnaryOp{..} => write!(f, "{}{}", op, operand),
                    _ => write!(f, "{}({})", op, operand),
                }
            }

            BinaryOp { op, left, right } => {
                match &**left {
                    Pred{..} | UnaryOp{..} => write!(f, "{}", left),
                    _ => write!(f, "({})", left),
                }?;

                write!(f, " {} ", op)?;

                match &**right {
                    Pred{..} | UnaryOp{..} => write!(f, "{}", right),
                    _ => write!(f, "({})", right),
                }
            },

            AssocBinaryOp { op, operands } => {
                let operands = operands.iter().map(|x| {
                    match x {
                        Pred{..} | UnaryOp{..} => format!("{}", x),
                        _ => format!("({})", x),
                    }
                }).collect::<Vec<_>>().join(&format!(" {} ", op));

                write!(f, "{}", operands)
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn var_regex() {
        let _v = Var::new("P").expect("Valid variable name 'P' was rejected");
        if let Some(_) = Var::new("9a") {
            panic!("Invalid variable name '9a' was accepted");
        }
        if let Some(_) = Var::new("h\na") {
            panic!("Invalid variable name 'h\\na' was accepted");
        }
    }

    #[test]
    fn write_pred() {
        let v = Var::new_unwrap("P");

        let p = Expr::prop(v.clone());
        let s = format!("{}", p);
        assert_eq!(s, "P");

        let p = Expr::pred(v.clone(), vec!["a","b","c"].into_iter().map(Var::new_unwrap).collect());
        let s = format!("{}", p);
        assert_eq!(s, "P(a, b, c)");
    }

    #[test]
    fn write_unary() {
        let p = Expr::prop(Var::new_unwrap("P"));
        let q = Expr::prop(Var::new_unwrap("Q"));

        let exp = Expr::not(p.clone());
        let s = format!("{}", exp);
        assert_eq!(s, "~P");

        let exp = Expr::not(Expr::and(vec![p.clone(), q.clone()]).unwrap());
        let s = format!("{}", exp);
        assert_eq!(s, "~(P & Q)");
    }

    #[test]
    fn write_binary() {
        let p = Expr::prop(Var::new_unwrap("P"));
        let q = Expr::prop(Var::new_unwrap("Q"));
        let r = Expr::prop(Var::new_unwrap("R"));

        let exp = Expr::implies(p.clone(), q.clone());
        let s = format!("{}", exp);
        assert_eq!(s, "P -> Q");

        let exp = Expr::implies(Expr::not(r.clone()),
            Expr::or(vec![p.clone(), q.clone()]).unwrap());
        let s = format!("{}", exp);
        assert_eq!(s, "~R -> (P | Q)");
    }

    #[test]
    fn write_assoc_binary() {
        let p = Expr::prop(Var::new_unwrap("P"));
        let q = Expr::prop(Var::new_unwrap("Q"));

        let conj = Expr::and(vec![p.clone(), Expr::not(p.clone())]).unwrap();
        let s = format!("{}", conj);
        assert_eq!(s, "P & ~P");

        let disj = Expr::or(vec![q.clone(), p.clone(), conj]).unwrap();
        let s = format!("{}", disj);
        assert_eq!(s, "Q | P | (P & ~P)");
    }
}
