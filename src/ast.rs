//! AST for propositional logic expressions.

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

//use either::{self, Either};
use std::collections::HashMap;
use std::fmt::{self, Display, Formatter};
use std::num::NonZeroU32;

/// A node ID in an `Ast`.
#[derive(Debug, PartialOrd, Ord, PartialEq, Eq, Clone, Copy, Hash)]
#[repr(transparent)]
// `NonZeroU32` to enable memory layout optimization with `Option`s
pub struct NodeId(pub NonZeroU32);

impl Display for NodeId {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl std::ops::Deref for NodeId {
    type Target = NonZeroU32;
    fn deref(&self) -> &NonZeroU32 {
        &self.0
    }
}

impl std::ops::DerefMut for NodeId {
    fn deref_mut(&mut self) -> &mut NonZeroU32 {
        &mut self.0
    }
}

/// A binary logic symbol.
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum BinOpSym {
    /// Conjunction / AND.
    Conj,

    /// Disjunction / OR.
    Disj,

    /// Material implication.
    Impl,

    /// Biconditional.
    Bicond,
}

/// A unary logic symbol.
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum UnOpSym {
    /// Negation.
    Neg,
}

use BinOpSym::*;
use UnOpSym::*;

impl Display for BinOpSym {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Conj => write!(f, "∧"),
            Disj => write!(f, "∨"),
            Impl => write!(f, "→"),
            Bicond => write!(f, "↔"),
        }
    }
}

impl Display for UnOpSym {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "¬")
    }
}

/// An abstract syntax tree for propositional logic expressions.
#[derive(Debug, Clone)]
pub struct Ast {
    nodes: HashMap<NodeId, AstNode>,
    parents: HashMap<NodeId, NodeId>,
    root: Option<NodeId>,
    next_id: NodeId,
}

/// A node in the syntax tree.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum AstNode {
    /// A binary node; conjunction, disjunction, implication, or biconditional.
    BinOp {
        sym: BinOpSym,
        left: NodeId,
        right: NodeId,
    },

    /// A unary node; negation.
    UnOp { sym: UnOpSym, child: NodeId },

    /// An atomic proposition.
    Prop(String),

    /// Tautology, constant True.
    Taut,

    /// Contradiction, constant False.
    Bottom,
}

impl Ast {
    #![allow(dead_code)]

    /// Create a new `Ast` that represents an empty tree.
    pub fn new() -> Ast {
        Ast {
            nodes: HashMap::new(),
            parents: HashMap::new(),
            root: None,
            next_id: NodeId(NonZeroU32::new(1).unwrap()),
        }
    }

    /// Create a new `Ast` following the structure of the given `AstBuilder`.
    pub fn new_from_builder(builder: AstBuilder) -> Ast {
        let mut ast = Ast::new();
        ast.root = Some(ast.add_subtree_from_builder(builder.root));
        ast
    }

    pub fn traverse(&self) -> AstTraverse<'_> {
        AstTraverse {
            ast: self,
            node: self.root,
        }
    }

    /// Retrieve the next node ID for this `Ast`, incrementing the internal
    /// counter in the process.
    fn get_next_id_incr(&mut self) -> NodeId {
        let id = self.next_id;
        self.next_id = NodeId(NonZeroU32::new(id.get() + 1).unwrap());
        id
    }

    /// Add the given `AstNode` to the `Ast`, returning its ID. This method
    /// does not check that the node is connected to the rest of the tree;
    /// it simply adds it blindly.
    fn add_node(&mut self, node: AstNode) -> NodeId {
        let id = self.get_next_id_incr();
        self.nodes.insert(id, node);
        id
    }

    /// Set the parent of `child` to be `parent`.
    #[inline]
    fn set_node_parent(&mut self, child: NodeId, parent: NodeId) {
        self.parents.insert(child, parent);
    }

    /// Adds and connects the subtree whose root is `builder_node`, returning the
    /// ID of the root node.
    fn add_subtree_from_builder(&mut self, builder_node: AstBuilderNode) -> NodeId {
        let (node, left, right) = match builder_node {
            AstBuilderNode::BinOp { sym, left, right } => {
                let (left, right) = (
                    self.add_subtree_from_builder(*left),
                    self.add_subtree_from_builder(*right),
                );

                (AstNode::BinOp { sym, left, right }, Some(left), Some(right))
            }

            AstBuilderNode::UnOp { sym, child } => {
                let child = self.add_subtree_from_builder(*child);

                (AstNode::UnOp { sym, child }, Some(child), None)
            }

            AstBuilderNode::Prop(s) => (AstNode::Prop(s), None, None),
            AstBuilderNode::Taut => (AstNode::Taut, None, None),
            AstBuilderNode::Bottom => (AstNode::Bottom, None, None),
        };

        let id = self.add_node(node);
        if let Some(left) = left {
            self.set_node_parent(left, id);
        }
        if let Some(right) = right {
            self.set_node_parent(right, id);
        }

        id
    }

    /// Remove the `AstNode` with the given ID and return it if it existed.
    ///
    /// Note that this method may invalidate references elswhere in the tree.
    #[inline]
    fn remove_node(&mut self, id: NodeId) -> Option<AstNode> {
        self.parents.remove(&id);
        self.nodes.remove(&id)
    }

    /// Return an immutable reference to the `AstNode` with the given ID, if it
    /// exists.
    #[inline]
    fn get_node(&self, id: NodeId) -> Option<&AstNode> {
        self.nodes.get(&id)
    }

    /// Return a mutable reference to the `AstNode` with the given ID, if it
    /// exists.
    #[inline]
    fn get_node_mut(&mut self, id: NodeId) -> Option<&mut AstNode> {
        self.nodes.get_mut(&id)
    }

    fn get_parent_id(&self, id: NodeId) -> Option<&NodeId> {
        self.parents.get(&id)
    }

    /// Helper function for `Display` implementation. Prints the subtree rooted
    /// at the given ID, wrapped in parentheses if the root node is not a negation
    /// or an atomic.
    fn display_wrap_parens(&self, f: &mut Formatter, id: NodeId) -> fmt::Result {
        let node = self.get_node(id).unwrap();
        if node.is_atomic_or_neg() {
            self.display_recursive(f, id)
        } else {
            write!(f, "(")?;
            self.display_recursive(f, id)?;
            write!(f, ")")
        }
    }

    /// Helper function for `Display` implementation. Prints the subtree rooted
    /// at the given ID, wrapped in parentheses if the root node is not a negation,
    /// atomic, or associative node with the given symbol.
    fn display_wrap_parens_assoc(
        &self,
        f: &mut Formatter,
        id: NodeId,
        par_sym: BinOpSym,
    ) -> fmt::Result {
        use AstNode::*;
        let node = self.get_node(id).unwrap();
        match node {
            BinOp { sym, .. } if *sym == par_sym => self.display_recursive(f, id),
            n if n.is_atomic_or_neg() => self.display_recursive(f, id),
            _ => {
                write!(f, "(")?;
                self.display_recursive(f, id)?;
                write!(f, ")")
            }
        }
    }

    /// Helper function for `Display` implementation. Prints the subtree rooted
    /// at the given ID.
    fn display_recursive(&self, f: &mut Formatter, id: NodeId) -> fmt::Result {
        use AstNode::*;
        match self.get_node(id).unwrap() {
            BinOp {
                sym: Impl,
                left,
                right,
            } => {
                self.display_wrap_parens(f, *left)?;
                write!(f, " {} ", Impl)?;
                self.display_wrap_parens(f, *right)
            }

            BinOp { sym, left, right } => {
                self.display_wrap_parens_assoc(f, *left, *sym)?;
                write!(f, " {} ", sym)?;
                self.display_wrap_parens_assoc(f, *right, *sym)
            }

            UnOp { sym, child } => {
                write!(f, "{}", sym)?;
                self.display_wrap_parens(f, *child)
            }

            Prop(s) => write!(f, "{}", s),
            Taut => write!(f, "⊤"),
            Bottom => write!(f, "⊥"),
        }
    }
}

impl Display for Ast {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        if let Some(id) = self.root {
            self.display_recursive(f, id)
        } else {
            Ok(())
        }
    }
}

impl Default for Ast {
    fn default() -> Ast {
        Ast::new()
    }
}

impl AstNode {
    /// Is this `AstNode` a conjunction?
    #[inline]
    pub fn is_conj(&self) -> bool {
        match self {
            AstNode::BinOp { sym, .. } => *sym == Conj,
            _ => false,
        }
    }

    /// Is this `AstNode` a disjunction?
    #[inline]
    pub fn is_disj(&self) -> bool {
        match self {
            AstNode::BinOp { sym, .. } => *sym == Disj,
            _ => false,
        }
    }

    /// Is this `AstNode` an implication?
    #[inline]
    pub fn is_impl(&self) -> bool {
        match self {
            AstNode::BinOp { sym, .. } => *sym == Impl,
            _ => false,
        }
    }

    /// Is this `AstNode` a biconditional?
    #[inline]
    pub fn is_bicond(&self) -> bool {
        match self {
            AstNode::BinOp { sym, .. } => *sym == Bicond,
            _ => false,
        }
    }

    /// Is this `AstNode` a negation?
    #[inline]
    pub fn is_neg(&self) -> bool {
        match self {
            AstNode::UnOp { .. } => true,
            _ => false,
        }
    }

    /// Is this `AstNode` a proposition?
    #[inline]
    pub fn is_prop(&self) -> bool {
        match self {
            AstNode::Prop(..) => true,
            _ => false,
        }
    }

    /// Is this `AstNode` a tautology?
    #[inline]
    pub fn is_taut(&self) -> bool {
        match self {
            AstNode::Taut => true,
            _ => false,
        }
    }

    /// Is this `AstNode` bottom?
    #[inline]
    pub fn is_bottom(&self) -> bool {
        match self {
            AstNode::Bottom => true,
            _ => false,
        }
    }

    /// Is this `AstNode` atomic? (Atomic `AstNode`s are leaf nodes,
    /// i.e. `Prop`, `Taut`, and `Bottom`.)
    #[inline]
    pub fn is_atomic(&self) -> bool {
        match self {
            AstNode::Prop(_) | AstNode::Taut | AstNode::Bottom => true,
            _ => false,
        }
    }

    /// Is this `AstNode` an atomic or `Neg`?
    ///
    /// This predicate is mostly useful for pretty printing; atomics and
    /// negations do not require parentheses around them to disambiguate
    /// associativity.
    #[inline]
    pub fn is_atomic_or_neg(&self) -> bool {
        self.is_atomic() || self.is_neg()
    }

    /// Is this `AstNode` associative?
    #[inline]
    pub fn is_assoc(&self) -> bool {
        match self {
            AstNode::BinOp { sym, .. } => match sym {
                Conj | Disj | Bicond => true,
                _ => false,
            },
            _ => false,
        }
    }

    /// Is this `AstNode` commutative?
    #[inline]
    pub fn is_commut(&self) -> bool {
        self.is_assoc()
    }
}

#[derive(Debug, Clone)]
pub struct AstTraverse<'a> {
    ast: &'a Ast,
    node: Option<NodeId>,
}

///
impl<'a> AstTraverse<'a> {
    /// Return the parent `AstTraverse`.
    ///
    /// If the current `AstTraverse` is at the root node, or has no current node,
    /// returns an `AstTraverse` with no current node.
    pub fn parent(&self) -> AstTraverse<'a> {
        let node = if let Some(id) = self.node {
            self.ast.get_parent_id(id).cloned()
        } else {
            None
        };

        AstTraverse {
            ast: self.ast,
            node,
        }
    }

    /// Return an `AstTraverse` at the left child of the current node.
    ///
    /// If the node has only one child, return an `AstTraverse` at that child. If the
    /// node has no children, or there is no current node, returns an `AstTraverse` with
    /// no current node.
    pub fn left(&self) -> AstTraverse<'a> {
        use AstNode::*;

        let child_id = if let Some(id) = self.node {
            match self.ast.get_node(id).unwrap() {
                BinOp { left, .. } => Some(*left),
                UnOp { child, .. } => Some(*child),
                _ => None,
            }
        } else {
            None
        };

        AstTraverse {
            ast: self.ast,
            node: child_id,
        }
    }

    /// Return an `AstTraverse` at the right child of the current node.
    ///
    /// If the node has one or no children, return `None`.
    pub fn right(&self) -> AstTraverse<'a> {
        use AstNode::*;

        let child_id = if let Some(id) = self.node {
            match self.ast.get_node(id).unwrap() {
                BinOp { right, .. } => Some(*right),
                _ => None,
            }
        } else {
            None
        };

        AstTraverse {
            ast: self.ast,
            node: child_id,
        }
    }

    /// Return an `AstTraverse` at the first (leftmost) child of the current node.
    ///
    /// This method is simply an alias of [`AstTraverse::left`].
    ///
    /// [`AstTraverse::left`]: #method.left
    #[inline]
    pub fn first_child(&self) -> AstTraverse<'a> {
        self.left()
    }

    /// Return a reference to the current node, if the `AstTraverse` has one.
    #[inline]
    pub fn node(&self) -> Option<&'a AstNode> {
        if let Some(id) = self.node {
            self.ast.get_node(id)
        } else {
            None
        }
    }
}

/// A struct to efficiently build up the structure of an AST before conversion or insertion
/// into an [`Ast`].
///
/// This struct exists for technical reasons. The internal design of the [`Ast`] struct
/// makes it difficult to efficiently construct a tree while maintaining certain desirable
/// invariants, for instance that no node is lacking any of its children and that each `Ast`
/// contains only one tree. `AstBuilder` is a very simplified version of an `Ast` that allows
/// for efficient construction (but not manipulation) of trees.
///
/// [`Ast`]: struct.Ast.html
#[derive(Debug, Clone, PartialEq, Eq)]
#[repr(transparent)]
pub struct AstBuilder {
    root: AstBuilderNode,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum AstBuilderNode {
    BinOp {
        sym: BinOpSym,
        left: Box<AstBuilderNode>,
        right: Box<AstBuilderNode>,
    },
    UnOp {
        sym: UnOpSym,
        child: Box<AstBuilderNode>,
    },
    Prop(String),
    Taut,
    Bottom,
}

impl AstBuilder {
    #[inline]
    fn binop(sym: BinOpSym, left: AstBuilderNode, right: AstBuilderNode) -> AstBuilder {
        use AstBuilderNode::*;
        AstBuilder {
            root: BinOp {
                sym,
                left: Box::new(left),
                right: Box::new(right),
            },
        }
    }

    #[inline]
    fn unop(sym: UnOpSym, child: AstBuilderNode) -> AstBuilder {
        use AstBuilderNode::*;
        AstBuilder {
            root: UnOp {
                sym,
                child: Box::new(child),
            },
        }
    }

    /// Construct the conjunction of the two given `AstBuilder`s.
    #[inline]
    pub fn and(p: AstBuilder, q: AstBuilder) -> AstBuilder {
        AstBuilder::binop(Conj, p.root, q.root)
    }

    /// Construct the disjunction of the two given `AstBuilder`s.
    #[inline]
    pub fn or(p: AstBuilder, q: AstBuilder) -> AstBuilder {
        AstBuilder::binop(Disj, p.root, q.root)
    }

    /// Construct an implication between the two given `AstBuilder`s (`p` implies `q`).
    #[inline]
    pub fn implies(p: AstBuilder, q: AstBuilder) -> AstBuilder {
        AstBuilder::binop(Impl, p.root, q.root)
    }

    /// Construct a biconditional between the two given `AstBuilder`s.
    #[inline]
    pub fn iff(p: AstBuilder, q: AstBuilder) -> AstBuilder {
        AstBuilder::binop(Bicond, p.root, q.root)
    }

    /// Construct the negation of the given `AstBuilder`.
    #[inline]
    pub fn not(p: AstBuilder) -> AstBuilder {
        AstBuilder::unop(Neg, p.root)
    }

    /// Construct a proposition with the given name.
    #[inline]
    pub fn prop(name: &str) -> AstBuilder {
        AstBuilder {
            root: AstBuilderNode::Prop(String::from(name)),
        }
    }

    /// Return tautology.
    #[inline]
    pub fn taut() -> AstBuilder {
        AstBuilder {
            root: AstBuilderNode::Taut,
        }
    }

    /// Return contradiction.
    #[inline]
    pub fn bottom() -> AstBuilder {
        AstBuilder {
            root: AstBuilderNode::Bottom,
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn ast_new() {
        let ast = Ast::new();
        assert!(ast.nodes.is_empty());
        assert!(ast.root.is_none());
        assert_eq!(ast.next_id.get(), 1);
    }

    #[test]
    fn ast_builder_constructors() {
        use AstBuilderNode::*;
        use BinOpSym::*;
        use UnOpSym::*;

        // Proposition
        let builder = AstBuilder::prop("P");
        assert_eq!(builder.root, Prop(String::from("P")));

        // Negation
        let builder = AstBuilder::not(AstBuilder::prop("Q"));
        if let UnOp { sym: Neg, child } = builder.root {
            assert_eq!(*child, Prop(String::from("Q")));
        } else {
            panic!("Root is not negation");
        }

        // Conjunction
        let builder = AstBuilder::and(AstBuilder::prop("P"), AstBuilder::prop("Q"));
        if let BinOp {
            sym: Conj,
            left,
            right,
        } = builder.root
        {
            assert_eq!(*left, Prop(String::from("P")));
            assert_eq!(*right, Prop(String::from("Q")));
        } else {
            panic!("Root is not conjunction");
        }

        // Disjunction
        let builder = AstBuilder::or(AstBuilder::prop("P"), AstBuilder::prop("Q"));
        if let BinOp {
            sym: Disj,
            left,
            right,
        } = builder.root
        {
            assert_eq!(*left, Prop(String::from("P")));
            assert_eq!(*right, Prop(String::from("Q")));
        } else {
            panic!("Root is not disjunction");
        }

        // Implication
        let builder = AstBuilder::implies(AstBuilder::prop("P"), AstBuilder::prop("Q"));
        if let BinOp {
            sym: Impl,
            left,
            right,
        } = builder.root
        {
            assert_eq!(*left, Prop(String::from("P")));
            assert_eq!(*right, Prop(String::from("Q")));
        } else {
            panic!("Root is not implication");
        }

        // Biconditional
        let builder = AstBuilder::iff(AstBuilder::prop("P"), AstBuilder::prop("Q"));
        if let BinOp {
            sym: Bicond,
            left,
            right,
        } = builder.root
        {
            assert_eq!(*left, Prop(String::from("P")));
            assert_eq!(*right, Prop(String::from("Q")));
        } else {
            panic!("Root is not biconditional");
        }
    }

    #[test]
    fn ast_new_from_builder() {
        use AstNode::*;

        let builder = AstBuilder::and(AstBuilder::prop("P"), AstBuilder::prop("Q"));
        let ast = Ast::new_from_builder(builder);

        let root_id = ast.root.expect("Ast does not have root node ID");
        let root_node = ast
            .get_node(root_id)
            .expect("Ast's root node is not in map");
        let (left_id, right_id) = match *root_node {
            BinOp {
                sym: Conj,
                left,
                right,
            } => (left, right),
            _ => panic!("Root node is not conjunction"),
        };

        assert_eq!(
            *ast.get_parent_id(left_id)
                .expect("Left child has no parent"),
            root_id
        );
        assert_eq!(
            *ast.get_parent_id(right_id)
                .expect("Riht child has no parent"),
            root_id
        );

        let left = ast.get_node(left_id).expect("Left child is not in map");
        let right = ast.get_node(right_id).expect("Right child is not in map");

        match left {
            Prop(s) if s == "P" => (),
            _ => panic!("Left child is not \"P\""),
        }

        match right {
            Prop(s) if s == "Q" => (),
            _ => panic!("Right child is not \"Q\""),
        }
    }

    #[test]
    fn ast_traverse() {
        use AstNode::*;

        let ast = Ast::new_from_builder(AstBuilder::implies(
            AstBuilder::prop("P"),
            AstBuilder::not(AstBuilder::prop("Q")),
        ));

        let traverse = ast.traverse();
        assert_eq!(traverse.ast as *const Ast, &ast as *const Ast);
        assert_eq!(traverse.node, ast.root);

        let traverse = traverse.left();
        if let Prop(s) = traverse.node().expect("node() returned none") {
            assert_eq!(s, "P");
        } else {
            panic!("Left child is not proposition");
        }

        assert!(traverse.first_child().node().is_none());

        let traverse = traverse.parent();
        assert!(traverse.node.is_some());

        let traverse = traverse.right();
        if let UnOp { .. } = traverse.node().expect("node() returned none") {
            let traverse = traverse.left();
            if let Prop(s) = traverse.node().expect("node() returned none") {
                assert_eq!(s, "Q");
            } else {
                panic!("Negated child is not \"Q\"");
            }
        } else {
            panic!("Right child is not negation");
        }
    }
}
