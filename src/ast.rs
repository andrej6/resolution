//! AST for propositional logic expressions.

/// A node in the syntax tree.
#[derive(Debug, PartialEq, Eq, Clone)]
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
    Contra,
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
    /// Return whether or not the node is an atomic, i.e. a proposition,
    /// tautology, or contradiction.
    #[inline]
    pub fn is_atomic(&self) -> bool {
        match self {
            Prop(_) | Taut | Contra => true,
            _ => false,
        }
    }

    /// Return whether or not the node is a literal, i.e. an atomic or
    /// a negation of an atomic.
    #[inline]
    pub fn is_literal(&self) -> bool {
        match self {
            Neg(n) if n.is_atomic() => true,
            n if n.is_atomic() => true,
            _ => false,
        }
    }

    /// Return whether the node is associative.
    #[inline]
    pub fn is_assoc(&self) -> bool {
        match self {
            Conj(_, _) | Disj(_, _) | Bicond(_, _) => true,
            _ => false,
        }
    }

    /// Return whether or not the node is commutative.
    #[inline]
    pub fn is_commut(&self) -> bool {
        self.is_assoc()
    }

    /// Return the arity of this node. Nullary (leaf) nodes have no children,
    /// unary nodes have one child, and binary nodes have two children.
    #[inline]
    pub fn arity(&self) -> Arity {
        match self {
            Neg(_) => Arity::Unary,
            Prop(_) | Taut | Contra => Arity::Nullary,
            _ => Arity::Binary,
        }
    }

    /// Swaps the two children of a binary node. For unary or leaf nodes,
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

    /// Swap the two children of a commutative binary node. For unary, leaf, or
    /// non-cummutative binary nodes, this is a no-op.
    #[inline]
    pub fn commute(&mut self) {
        if self.is_commut() {
            self.swap_children();
        }
    }
}
