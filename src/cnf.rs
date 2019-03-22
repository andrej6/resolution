//! Clauses and conjunctive normal form representation of logic expressions.

//use super::common;
use std::cmp::{Eq, PartialEq};
use std::collections::{hash_set, HashSet};
use std::fmt::{self, Display, Formatter};
use std::hash::{Hash, Hasher};
use std::iter::{FromIterator, IntoIterator};

/// A literal, i.e. a proposition or its negation.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct Literal {
    pub name: String,
    pub negated: bool,
}

impl Literal {
    /// Create a new, unnegated `Literal` with the given name.
    pub fn new(name: &str) -> Literal {
        Literal {
            name: name.into(),
            negated: false,
        }
    }

    /// Create a new, negated `Literal` with the given name.
    pub fn new_negated(name: &str) -> Literal {
        Literal {
            name: name.into(),
            negated: true,
        }
    }

    /// Negate the `Literal`, i.e. change it to negated if it is unnegated, and to
    /// unnegated if it was negated.
    ///
    /// ```
    /// # use resolution::cnf::*;
    /// let mut lit = Literal::new("P");
    ///
    /// assert!(!lit.negated);
    /// lit.negate();
    /// assert!(lit.negated);
    /// lit.negate();
    /// assert!(!lit.negated);
    /// ```
    pub fn negate(&mut self) {
        self.negated = !self.negated;
    }

    /// Create a copy of the `Literal` with its negation status reversed.
    ///
    /// ```
    /// # use resolution::cnf::*;
    /// let lit1 = Literal::new("P");
    /// let lit2 = lit1.clone_negated();
    ///
    /// assert!(!lit1.negated);
    /// assert!(lit2.negated);
    /// assert_eq!(lit1.name, lit2.name);
    /// ```
    pub fn clone_negated(&self) -> Literal {
        Literal {
            name: self.name.clone(),
            negated: !self.negated,
        }
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

/// A CNF clause, i.e. a generalized disjunction of literals.
///
/// The [`cnf_clause!`] macro provides a convenient way to create `Clause`s.
///
/// [`cnf_clause!`]: ../macro.cnf_clause.html
#[derive(Debug, Clone, Default)]
pub struct Clause {
    literals: HashSet<Literal>,
}

impl Clause {
    /// Create a new, empty `Clause`.
    pub fn new() -> Clause {
        Clause {
            literals: HashSet::new(),
        }
    }

    /// Add the given `Literal` to the `Clause`, with the following caveats:
    /// 1. If an identical `Literal` is already in the `Clause`, this method
    ///    is a no-op.
    /// 2. If a `Literal` with the same name but opposite negation is already
    ///    in the `Clause`, this method removes that `Literal` instead of adding
    ///    the given one. This reflects the fact that P ∨ ¬P is a tautology.
    pub fn add(&mut self, lit: Literal) {
        let l2 = Literal {
            name: lit.name.clone(),
            negated: !lit.negated,
        };
        if !self.literals.remove(&l2) {
            self.literals.insert(lit);
        }
    }

    /// Remove the `Literal` equal to the given one, if it is present in the
    /// `Clause`. Returns `true` if the `Literal` was present.
    pub fn remove(&mut self, lit: &Literal) -> bool {
        self.literals.remove(lit)
    }

    /// Remove and return the `Literal` equal to the given one, if it is present
    /// in the `Clause`.
    pub fn take(&mut self, lit: &Literal) -> Option<Literal> {
        self.literals.take(lit)
    }

    /// Is this `Clause` empty?
    pub fn is_empty(&self) -> bool {
        self.literals.is_empty()
    }

    /// Return a `HashSet` of all of the `Literal`s in this `Clause`, negated.
    fn negated_literals(&self) -> HashSet<Literal> {
        let mut literals = HashSet::new();
        for lit in &self.literals {
            literals.insert(lit.clone_negated());
        }
        literals
    }

    /// Negate all `Literal`s in the `Clause`.
    pub fn negate_all(&mut self) {
        self.literals = self.negated_literals();
    }

    /// Create a copy of the `Clause` in which all `Literal`s are negated.
    pub fn clone_negated(&self) -> Clause {
        Clause {
            literals: self.negated_literals(),
        }
    }

    /// Return an iterator over references to the [`Literal`]s contained in this `Clause`.
    ///
    /// [`Literal`]: struct.Literal.html
    pub fn iter(&self) -> hash_set::Iter<Literal> {
        self.literals.iter()
    }

    /// Attempt to resolve two `Clause`s. If successful, returns the `Clause`
    /// resulting from the resolution.
    pub fn resolve(&self, other: &Clause) -> Option<Clause> {
        let neg_intersect = &self.negated_literals() & &other.literals;
        if neg_intersect.is_empty() {
            return None;
        }

        let other_diff = &other.literals - &neg_intersect;
        let intersect = neg_intersect.iter().map(Literal::clone_negated).collect();
        let self_diff = &self.literals - &intersect;
        Some(Clause {
            literals: &other_diff | &self_diff,
        })
    }
}

impl Display for Clause {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(
            f,
            "{{ {} }}",
            self.literals
                .iter()
                .map(|lit| lit.to_string())
                .collect::<Vec<String>>()
                .join(", ")
        )
    }
}

impl PartialEq for Clause {
    fn eq(&self, other: &Self) -> bool {
        self.literals.difference(&other.literals).next() == None
    }
}

impl Eq for Clause {}

/// The `Hash` implementation for `Clause` is not the most efficient. Since a `Clause` is
/// represented by an underlying (unordered) `HashSet` of [`Literal`]s, the `Hash`
/// implementation must sort the clause's literals in order to produce consistent output.
/// Use this sparingly.
///
/// [`Literal`]: struct.Literal.html
impl Hash for Clause {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut v: Vec<_> = self.literals.iter().collect();
        v.sort_unstable();
        v.hash(state);
    }
}

impl FromIterator<Literal> for Clause {
    fn from_iter<T>(iter: T) -> Clause
    where
        T: IntoIterator<Item = Literal>,
    {
        let mut t = Clause::new();
        for lit in iter {
            t.add(lit);
        }
        t
    }
}

impl IntoIterator for Clause {
    type Item = Literal;
    type IntoIter = hash_set::IntoIter<Literal>;
    fn into_iter(self) -> Self::IntoIter {
        self.literals.into_iter()
    }
}

impl<'a> IntoIterator for &'a Clause {
    type Item = &'a Literal;
    type IntoIter = hash_set::Iter<'a, Literal>;
    fn into_iter(self) -> Self::IntoIter {
        self.literals.iter()
    }
}

/// A convenience macro for creating [`Clause`]s. `cnf_clause!` takes a comma-separated
/// list of identifiers, each one of which is optionally prepended with a `~` character.
/// The result is a [`Clause`] containing [`Literal`]s with the given identifiers as names,
/// negated if the corresponding identifier was prefaced with a `~`.
///
/// ```
/// # #[macro_use] extern crate resolution;
/// # use resolution::cnf::*;
/// // Manually construct a Clause
/// let mut clause1 = Clause::new();
/// clause1.add(Literal::new("P"));
/// clause1.add(Literal::new_negated("Q"));
/// clause1.add(Literal::new("R"));
///
/// // Construct the same clause with `cnf_clause!`
/// let clause2 = cnf_clause!(P, ~Q, R);
/// assert_eq!(clause1, clause2);
///
/// // `Clause`s are irrespective of ordering
/// let clause3 = cnf_clause!(~Q, R, P);
/// assert_eq!(clause1, clause3);
/// ```
///
/// [`Clause`]: cnf/struct.Clause.html
/// [`Literal`]: cnf/struct.Literal.html
#[macro_export]
macro_rules! cnf_clause {
    (@accum () -> ($($body:tt)*)) => { vec![$($body)*] };
    (@accum (, $($tail:tt)*) -> ($($body:tt)*)) => { cnf_clause!(@accum ($($tail)*) -> ($($body)*)) };
    (@accum (~$name:ident $($tail:tt)*) -> ($($body:tt)*))
        => { cnf_clause!(@accum ($($tail)*) -> (Literal::new_negated(stringify!($name)), $($body)*)) };
    (@accum ($name:ident $($tail:tt)*) -> ($($body:tt)*))
        => { cnf_clause!(@accum ($($tail)*) -> (Literal::new(stringify!($name)), $($body)*)) };
    [$($props:tt)*] => {
        cnf_clause!(@accum ($($props)*) -> ()).into_iter().collect::<Clause>()
    };
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn clause_macro() {
        let t = cnf_clause!(P, Q);
        let mut expected = Clause::new();
        expected.add(Literal::new("P"));
        expected.add(Literal::new("Q"));
        assert_eq!(t, expected);

        let t = cnf_clause!(P, ~P);
        let expected = Clause::new();
        assert_eq!(t, expected);
    }

    #[test]
    fn resolve1() {
        let c1 = cnf_clause!(P);
        let c2 = cnf_clause!(~P);

        let res = c1.resolve(&c2).expect("Resolution returned None");
        assert!(res.is_empty());

        let res = c2.resolve(&c1).expect("Resolution returned None");
        assert!(res.is_empty());
    }

    #[test]
    fn resolve2() {
        let c1 = cnf_clause!(P, Q);
        let c2 = cnf_clause!(~P);
        let expected_res = cnf_clause!(Q);

        let res = c1.resolve(&c2).expect("Resolution returned None");
        assert_eq!(res, expected_res);

        let res = c2.resolve(&c1).expect("Resolution returned None");
        assert_eq!(res, expected_res);
    }

    #[test]
    fn resolve_multi() {
        let c1 = cnf_clause!(P, ~Q);
        let c2 = cnf_clause!(R, Q);
        let expected_res = cnf_clause!(P, R);

        let res = c1.resolve(&c2).expect("Resolution returned None");
        assert_eq!(res, expected_res);

        let res = c2.resolve(&c1).expect("Resolution returned None");
        assert_eq!(res, expected_res);
    }

    #[test]
    fn resolve_none() {
        let c1 = cnf_clause!(P);
        let c2 = cnf_clause!(Q);

        if let Some(_) = c1.resolve(&c2) {
            panic!("Resolution returned Some");
        }

        if let Some(_) = c2.resolve(&c1) {
            panic!("Resolution returned Some");
        }
    }

    #[test]
    fn resolve_self() {
        let t = cnf_clause!(P);
        if let Some(_) = t.resolve(&t) {
            panic!("Self-resolution returned Some");
        }
    }

    #[test]
    fn add_identical() {
        let mut t = cnf_clause!(P);
        t.add(Literal::new("P"));

        assert_eq!(t, cnf_clause!(P));
    }

    #[test]
    fn add_negated() {
        let mut t = cnf_clause!(P);
        t.add(Literal::new_negated("P"));

        assert_eq!(t, cnf_clause!());
    }

    #[test]
    fn collect() {
        let t = vec![Literal::new("P"), Literal::new("Q")]
            .into_iter()
            .collect::<Clause>();

        let mut expected = Clause::new();
        expected.add(Literal::new("P"));
        expected.add(Literal::new("Q"));

        assert_eq!(t, expected);
    }

    #[test]
    fn collect_negated() {
        let t = vec![Literal::new("P"), Literal::new_negated("P")]
            .into_iter()
            .collect::<Clause>();

        let expected = Clause::new();

        assert_eq!(t, expected);
    }
}
