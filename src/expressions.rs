#![deprecated(
    note = "Work is in progress to redesign the AST. See the [`ast`](../ast/index.html) module."
)]

//! Syntax tree representation for logical expressions.
//!
//! Currently, only propositional (truth-functional) logic is represented.

use regex::Regex;
use std::fmt::{self, Display, Formatter};

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
}

/// Similar to [`Var::new()`], `Var::from()` creates a new `Var` with
/// the given name. Unlike [`Var::new()`], however, `Var::from()`
/// will panic if the regex test fails; it should not be used
/// to create a `Var` from user input. Hence, `From` is only
/// implemented for `&'static str`s (string literals).
///
/// [`Var::new()`]: struct.Var.html#method.new
impl From<&'static str> for Var {
    fn from(name: &'static str) -> Var {
        Var::new(name).unwrap()
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
    Pred { name: Var, args: Vec<Var> },

    /// A unary operator expression.
    UnaryOp { op: UnarySym, operand: Box<Expr> },

    /// A non-associative binary operator expression.
    BinaryOp {
        op: BinarySym,
        left: Box<Expr>,
        right: Box<Expr>,
    },

    /// A string of operands joined by a single associative binary operator.
    AssocBinaryOp {
        op: AssocBinarySym,
        operands: Vec<Expr>,
    },
}

impl Expr {
    /// Create a conjunction of the given expressions. Returns `None` if
    /// there are fewer than two operands.
    pub fn and(operands: Vec<Expr>) -> Option<Expr> {
        if operands.len() < 2 {
            None
        } else {
            Some(Expr::AssocBinaryOp { op: And, operands })
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
        Expr::UnaryOp {
            op: Not,
            operand: Box::new(operand),
        }
    }

    /// Consume two expressions and create the expression `left` implies `right`.
    pub fn implies(left: Expr, right: Expr) -> Expr {
        Expr::BinaryOp {
            op: Implies,
            left: Box::new(left),
            right: Box::new(right),
        }
    }

    /// Create a chain of biconditionals between the given expressions. Returns
    /// `None` if there are fewer than two operands.
    pub fn bicond(operands: Vec<Expr>) -> Option<Expr> {
        if operands.len() < 2 {
            None
        } else {
            Some(Expr::AssocBinaryOp {
                op: Bicond,
                operands,
            })
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

/* Unicode codepoints, for reference:
 * → : U+2192
 * ↔ : U+2194
 * ¬ : U+00AC
 * ∧ : U+2227
 * ∨ : U+2228
 * ⊤ : U+22A4
 * ⊥ : U+22A5
 * ∀ : U+2200
 * ∃ : U+2203
 */

impl Display for Var {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Display for UnarySym {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Not => write!(f, "¬"),
        }
    }
}

impl Display for BinarySym {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Implies => write!(f, "→"),
        }
    }
}

impl Display for AssocBinarySym {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            And => write!(f, "∧"),
            Or => write!(f, "∨"),
            Bicond => write!(f, "↔"),
        }
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        use Expr::*;
        match self {
            // Proposition (predicate with no arguments)
            Pred { name, args } if args.is_empty() => write!(f, "{}", name),

            // Predicate
            Pred { name, args } => write!(
                f,
                "{}({})",
                name,
                args.iter()
                    .map(<Var as ToString>::to_string)
                    .collect::<Vec<_>>()
                    .join(", ")
            ),

            UnaryOp { op, operand } => {
                match operand.as_ref() {
                    // Put parentheses only around non-literal expressions
                    Pred { .. } | UnaryOp { .. } => write!(f, "{}{}", op, operand),
                    _ => write!(f, "{}({})", op, operand),
                }
            }

            BinaryOp { op, left, right } => {
                match left.as_ref() {
                    Pred { .. } | UnaryOp { .. } => write!(f, "{}", left),
                    _ => write!(f, "({})", left),
                }?;

                write!(f, " {} ", op)?;

                match right.as_ref() {
                    Pred { .. } | UnaryOp { .. } => write!(f, "{}", right),
                    _ => write!(f, "({})", right),
                }
            }

            AssocBinaryOp { op, operands } => {
                let operands = operands
                    .iter()
                    .map(|x| match x {
                        Pred { .. } | UnaryOp { .. } => format!("{}", x),
                        _ => format!("({})", x),
                    })
                    .collect::<Vec<_>>()
                    .join(&format!(" {} ", op));

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
        let v = Var::from("P");

        let p = Expr::prop(v.clone());
        let s = format!("{}", p);
        assert_eq!(s, "P");

        let p = Expr::pred(
            v.clone(),
            vec!["a", "b", "c"].into_iter().map(Var::from).collect(),
        );
        let s = format!("{}", p);
        assert_eq!(s, "P(a, b, c)");
    }

    #[test]
    fn write_unary() {
        let p = Expr::prop(Var::from("P"));
        let q = Expr::prop(Var::from("Q"));

        let exp = Expr::not(p.clone());
        let s = format!("{}", exp);
        assert_eq!(s, "¬P");

        let exp = Expr::not(Expr::and(vec![p.clone(), q.clone()]).unwrap());
        let s = format!("{}", exp);
        assert_eq!(s, "¬(P ∧ Q)");
    }

    #[test]
    fn write_binary() {
        let p = Expr::prop(Var::from("P"));
        let q = Expr::prop(Var::from("Q"));
        let r = Expr::prop(Var::from("R"));

        let exp = Expr::implies(p.clone(), q.clone());
        let s = format!("{}", exp);
        assert_eq!(s, "P → Q");

        let exp = Expr::implies(
            Expr::not(r.clone()),
            Expr::or(vec![p.clone(), q.clone()]).unwrap(),
        );
        let s = format!("{}", exp);
        assert_eq!(s, "¬R → (P ∨ Q)");
    }

    #[test]
    fn write_assoc_binary() {
        let p = Expr::prop(Var::from("P"));
        let q = Expr::prop(Var::from("Q"));

        let conj = Expr::and(vec![p.clone(), Expr::not(p.clone())]).unwrap();
        let s = format!("{}", conj);
        assert_eq!(s, "P ∧ ¬P");

        let disj = Expr::or(vec![q.clone(), p.clone(), conj]).unwrap();
        let s = format!("{}", disj);
        assert_eq!(s, "Q ∨ P ∨ (P ∧ ¬P)");
    }
}
