//! AST for propositional logic expressions.

use std::fmt::{self, Display, Formatter};

/// A node in the syntax tree.
///
/// Until [box patterns] get stabilized, pattern matching across multiple levels
/// of a recursive data type is a pain. To help out a little bit, `Node` defines
/// inline `is_{variant}` methods for each variant, (i.e. [`is_conj`], [`is_disj`], etc.).
/// These can be used in match guards to make two-level matching a little more
/// ergonomic.
///
/// [box patterns]: https://doc.rust-lang.org/unstable-book/language-features/box-patterns.html
/// [`is_conj`]: #method.is_conj
/// [`is_disj`]: #method.is_disj
#[derive(Debug, PartialEq, Eq, Clone, is_enum_variant)]
pub enum Node {
    /// The conjunction (AND) of the two child expressions.
    Conj(Box<Node>, Box<Node>),

    /// The disjunction (OR) of the two child expressions.
    Disj(Box<Node>, Box<Node>),

    /// The negation of the child expression.
    Neg(Box<Node>),

    /// Material implication from the first child expression to the second.
    Impl(Box<Node>, Box<Node>),

    /// Biconditional between the two child expressions.
    Bicond(Box<Node>, Box<Node>),

    /// An atomic proposition.
    Prop(String),

    /// Tautology, constant True.
    Taut,

    /// Contradiction, constant False.
    Bottom,
}

use Node::*;

/// An enum to represent the arity of an AST node.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub enum Arity {
    Nullary,
    Unary,
    Binary,
}

impl Node {
    // Constructors

    /// Create a `Conj` from the given conjuncts.
    #[inline]
    pub fn and(p: Node, q: Node) -> Node {
        Conj(Box::new(p), Box::new(q))
    }

    /// Create a `Disj` from the given disjuncts.
    #[inline]
    pub fn or(p: Node, q: Node) -> Node {
        Disj(Box::new(p), Box::new(q))
    }

    /// Create a `Neg` negating the given `Node`.
    #[inline]
    pub fn not(p: Node) -> Node {
        Neg(Box::new(p))
    }

    /// Create an `Impl` from the given `Node`s (`p` implies `q`).
    #[inline]
    pub fn implies(p: Node, q: Node) -> Node {
        Impl(Box::new(p), Box::new(q))
    }

    /// Create a `Bicond` between the given `Node`s (`p` if and only if `q`).
    #[inline]
    pub fn iff(p: Node, q: Node) -> Node {
        Bicond(Box::new(p), Box::new(q))
    }

    /// Create a `Prop` with the given name.
    #[inline]
    pub fn prop(name: &str) -> Node {
        Prop(String::from(name))
    }

    // Inspection utilities

    /// Atomic `Node`s are leaf `Node`s, i.e. `Prop`, `Taut`, and `Bottom`.
    #[inline]
    pub fn is_atomic(&self) -> bool {
        match self {
            Prop(_) | Taut | Bottom => true,
            _ => false,
        }
    }

    /// A literal is an atomic or a negated atomic.
    #[inline]
    pub fn is_literal(&self) -> bool {
        match self {
            Neg(n) if n.is_atomic() => true,
            n if n.is_atomic() => true,
            _ => false,
        }
    }

    /// Is this `Node` an atomic or `Neg`?
    ///
    /// This predicate is mostly useful for pretty printing; atomics and
    /// negations do not require parentheses around them to disambiguate
    /// associativity.
    #[inline]
    pub fn is_atomic_or_neg(&self) -> bool {
        self.is_atomic() || self.is_neg()
    }

    /// Is this `Node` associative?
    #[inline]
    pub fn is_assoc(&self) -> bool {
        match self {
            Conj(_, _) | Disj(_, _) | Bicond(_, _) => true,
            _ => false,
        }
    }

    /// Is this `Node` commutative?
    #[inline]
    pub fn is_commut(&self) -> bool {
        self.is_assoc()
    }

    /// Return the arity of this `Node`. `Nullary` (leaf) nodes have no children,
    /// `Unary` nodes have one child, and `Binary` nodes have two children.
    #[inline]
    pub fn arity(&self) -> Arity {
        match self {
            Neg(_) => Arity::Unary,
            Prop(_) | Taut | Bottom => Arity::Nullary,
            _ => Arity::Binary,
        }
    }

    // Manipulation utilities

    /// Swaps the two children of a binary `Node`. For unary or leaf `Node`s,
    /// this is a no-op.
    #[inline]
    pub fn swap_children(&mut self) {
        match self {
            Conj(ref mut a, ref mut b)
            | Disj(ref mut a, ref mut b)
            | Impl(ref mut a, ref mut b)
            | Bicond(ref mut a, ref mut b) => std::mem::swap(a, b),
            _ => (),
        }
    }

    /// Swap the two children of a commutative binary `Node`. For unary, leaf, or
    /// non-cummutative binary `Node`s, this is a no-op.
    #[inline]
    pub fn commute(&mut self) {
        if self.is_commut() {
            self.swap_children();
        }
    }

    /// Convert the AST in-place to fully left-associative form.
    ///
    /// Specifically, this method will transform the AST so that all chains of
    /// associative `Node`s are fully left-associative. E.g., a `Conj` may only
    /// have one child that is also a `Conj`, and such a child must be the left
    /// one; similar for the other associative `Node` variants, `Disj` and
    /// `Bicond`.
    pub fn make_left_associative(&mut self) {}

    /// Eliminate all double-negations from the AST.
    pub fn elim_double_neg(&mut self) {
        if let Neg(child) = self {
            if let Neg(grandchild) = child.as_mut() {
                *self = grandchild.as_ref().clone();
                self.elim_double_neg();
            } else {
                child.elim_double_neg();
            }
        } else {
            let (left, right): (&mut Box<Node>, &mut Box<Node>) = match self {
                Conj(ref mut l, ref mut r) => (l, r),
                Disj(ref mut l, ref mut r) => (l, r),
                Impl(ref mut l, ref mut r) => (l, r),
                Bicond(ref mut l, ref mut r) => (l, r),
                _ => return,
            };

            left.elim_double_neg();
            right.elim_double_neg();
        }
    }

    /// Convert the AST in-place to canonical form; i.e. fully left-associative
    /// and with no double negation.
    ///
    /// This form is "canonical" in the sense that the permitted syntactic relationships
    /// between `Node`s is tightly controlled; it is _not_ "canonical" in the sense that
    /// any two equivalent logic expressions will reduce to the same canonical tree. In
    /// particular, this method does not sort the leaves of the AST in any way, nor does
    /// it de-duplicate them or apply any logical inferences or equivalences besides
    /// associativity of conjunction, disjunction, and biconditional, and double-negation
    /// elimination.
    pub fn canonicalize(&mut self) {
        self.make_left_associative();
        self.elim_double_neg();
    }

    /// Convert the `Node` in-place to conjunctive normal form.
    ///
    /// Specifically, this method
    pub fn make_cnf(&mut self) {}
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

impl Display for Node {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Conj(p, q)
                if (p.is_conj() && q.is_atomic_or_neg())
                    || (p.is_atomic_or_neg() && q.is_conj())
                    || (p.is_conj() && q.is_conj())
                    || (p.is_atomic_or_neg() && q.is_atomic_or_neg()) =>
            {
                write!(f, "{} ∧ {}", p, q)
            }
            Conj(p, q) if (p.is_conj() || p.is_atomic_or_neg()) && !q.is_conj() => {
                write!(f, "{} ∧ ({})", p, q)
            }
            Conj(p, q) if !p.is_conj() && (q.is_conj() || q.is_atomic_or_neg()) => {
                write!(f, "({}) ∧ {}", p, q)
            }
            Conj(p, q) => write!(f, "({}) ∧ ({})", p, q),

            Disj(p, q)
                if (p.is_disj() && q.is_atomic_or_neg())
                    || (p.is_atomic_or_neg() && q.is_disj())
                    || (p.is_disj() && q.is_disj())
                    || (p.is_atomic_or_neg() && q.is_atomic_or_neg()) =>
            {
                write!(f, "{} ∨ {}", p, q)
            }
            Disj(p, q) if (p.is_disj() || p.is_atomic_or_neg()) && !q.is_disj() => {
                write!(f, "{} ∨ ({})", p, q)
            }
            Disj(p, q) if !p.is_disj() && (q.is_disj() || q.is_atomic_or_neg()) => {
                write!(f, "({}) ∨ {}", p, q)
            }
            Disj(p, q) => write!(f, "({}) ∨ ({})", p, q),

            Neg(p) if p.is_atomic_or_neg() => write!(f, "¬{}", p),
            Neg(p) => write!(f, "¬({})", p),

            Impl(p, q) if p.is_atomic_or_neg() && q.is_atomic_or_neg() => {
                write!(f, "{} → {}", p, q)
            }
            Impl(p, q) if p.is_atomic_or_neg() && !q.is_atomic_or_neg() => {
                write!(f, "{} → ({})", p, q)
            }
            Impl(p, q) if !p.is_atomic_or_neg() && q.is_atomic_or_neg() => {
                write!(f, "({}) → {}", p, q)
            }
            Impl(p, q) => write!(f, "({}) → ({})", p, q),

            Bicond(p, q)
                if (p.is_bicond() && q.is_atomic_or_neg())
                    || (p.is_atomic_or_neg() && q.is_bicond())
                    || (p.is_bicond() && q.is_bicond())
                    || (p.is_atomic_or_neg() && q.is_atomic_or_neg()) =>
            {
                write!(f, "{} ↔ {}", p, q)
            }
            Bicond(p, q) if (p.is_bicond() || p.is_atomic_or_neg()) && !q.is_bicond() => {
                write!(f, "{} ↔ ({})", p, q)
            }
            Bicond(p, q) if !p.is_bicond() && (q.is_bicond() || q.is_atomic_or_neg()) => {
                write!(f, "({}) ↔ {}", p, q)
            }
            Bicond(p, q) => write!(f, "({}) ↔ ({})", p, q),

            Prop(s) => write!(f, "{}", s),

            Taut => write!(f, "⊤"),
            Bottom => write!(f, "⊥"),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn elim_double_neg_simple() {
        let mut node = Node::not(Node::not(Node::prop("P")));
        node.elim_double_neg();
        assert_eq!(node, Node::prop("P"));

        let mut node = Node::not(Node::not(Node::not(Node::prop("P"))));
        node.elim_double_neg();
        assert_eq!(node, Node::not(Node::prop("P")));

        let mut node = Node::not(Node::not(Node::not(Node::not(Node::prop("P")))));
        node.elim_double_neg();
        assert_eq!(node, Node::prop("P"));
    }

    #[test]
    fn elim_double_neg_complex() {
        // ~~P & ~Q == Q & ~Q
        let mut node = Node::and(
            Node::not(Node::not(Node::prop("P"))),
            Node::not(Node::prop("Q")),
        );
        node.elim_double_neg();
        assert_eq!(node, Node::and(Node::prop("P"), Node::not(Node::prop("Q"))));

        // ~(~~P & Q) --> ~~R == ~(P & Q) --> R
        let mut node = Node::implies(
            Node::not(Node::and(
                Node::not(Node::not(Node::prop("P"))),
                Node::prop("Q"),
            )),
            Node::not(Node::not(Node::prop("R"))),
        );
        node.elim_double_neg();
        assert_eq!(
            node,
            Node::implies(
                Node::not(Node::and(Node::prop("P"), Node::prop("Q"))),
                Node::prop("R")
            )
        );
    }
}
