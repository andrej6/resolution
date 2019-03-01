//! Terms and conjunctive normal form representation of logic expressions.

use std::cmp::{Eq, PartialEq};
use std::collections::HashSet;
use std::fmt::{self, Display, Formatter};
use std::hash::{Hash, Hasher};

/// A literal, i.e. a proposition or its negation.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct Literal {
    pub name: String,
    pub negated: bool,
}

impl Literal {
    /// Create a new, unnegated `Literal` with the given name.
    pub fn new(name: &str) -> Literal {
        Literal { name: name.into(), negated: false }
    }

    /// Create a new, negated `Literal` with the given name.
    pub fn new_negated(name: &str) -> Literal {
        Literal { name: name.into(), negated: true }
    }

    /// Negate the `Literal`, i.e. change it to negated if it is unnegated, and to
    /// unnegated if it was negated.
    pub fn negate(&mut self) {
        self.negated = !self.negated;
    }

    /// Create a copy of the `Literal` with its negation status reversed.
    pub fn clone_negated(&self) -> Literal {
        Literal { name: self.name.clone(), negated: !self.negated }
    }
}

impl Display for Literal {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        if self.negated {
            write!(f, "{}", self.name)
        } else {
            write!(f, "¬{}", self.name)
        }
    }
}

/// A CNF term, i.e. a generalized disjunction of literals.
#[derive(Debug, Clone, Default)]
pub struct Term(HashSet<Literal>);

impl Term {
    /// Create a new, empty `Term`.
    pub fn new() -> Term {
        Term(HashSet::new())
    }

    /// Add the given `Literal` to the `Term`, with the following caveats:
    /// 1. If an identical `Literal` is already in the `Term`, this method
    ///    is a no-op.
    /// 2. If a `Literal` with the same name but opposite negation is already
    ///    in the `Term`, this method removes that `Literal` instead of adding
    ///    the given one. This reflects the fact that P ∨ ¬P is a tautology.
    pub fn add(&mut self, lit: Literal) {
        let l2 = Literal{ name: lit.name.clone(), negated: !lit.negated };
        if !self.0.remove(&l2) {
            self.0.insert(lit);
        }
    }

    /// Remove the `Literal` equal to the given one, if it is present in the
    /// `Term`. Returns `true` if the `Literal` was present.
    pub fn remove(&mut self, lit: &Literal) -> bool {
        self.0.remove(lit)
    }

    /// Remove and return the `Literal` equal to the given one, if it is present
    /// in the `Term`.
    pub fn take(&mut self, lit: &Literal) -> Option<Literal> {
        self.0.take(lit)
    }
}

impl Display for Term {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(
            f,
            "{{ {} }}",
            self.0
                .iter()
                .map(|lit| lit.to_string())
                .collect::<Vec<String>>()
                .join(", ")
        )
    }
}

impl PartialEq for Term {
    fn eq(&self, other: &Self) -> bool {
        self.0.difference(&other.0).next() == None
    }
}

impl Eq for Term {}

/// The `Hash` implementation for `Term` is not the most efficient. Since a `Term` is
/// represented by an underlying (unordered) `HashSet` of [`Literal`]s, the `Hash`
/// implementation must sort the term's literals in order to produce consistent output.
/// Use this sparingly.
///
/// [`Literal`]: struct.Literal.html
impl Hash for Term {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut v: Vec<_> = self.0.iter().collect();
        v.sort_unstable();
        v.hash(state);
    }
}
