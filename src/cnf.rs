//! Terms and conjunctive normal form representation of logic expressions.

use super::common;
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
    ///
    /// The name of each `Literal` is checked against the regex
    /// `[a-zA-Z_][a-zA-Z0-9_]*` and rejected if it does not match.
    ///
    /// ```
    /// # use resolution::cnf::*;
    /// let lit = Literal::new("valid_name").unwrap();
    /// assert_eq!(lit.name, "valid_name");
    /// assert!(!lit.negated);
    ///
    /// let invalid = Literal::new("Not a valid name");
    /// assert!(invalid.is_none());
    /// ```
    pub fn new(name: &str) -> Option<Literal> {
        if common::is_valid_name(name) {
            Some(Literal {
                name: name.into(),
                negated: false,
            })
        } else {
            None
        }
    }

    /// Create a new, negated `Literal` with the given name.
    ///
    /// The name of each `Literal` is checked against the regex `[a-zA-Z_][a-zA-Z0-9_]*`
    /// and rejected if it does not match.
    ///
    /// ```
    /// # use resolution::cnf::*;
    /// let lit = Literal::new_negated("valid_name").unwrap();
    /// assert_eq!(lit.name, "valid_name");
    /// assert!(lit.negated);
    ///
    /// let invalid = Literal::new_negated("Not a valid name");
    /// assert!(invalid.is_none());
    /// ```
    pub fn new_negated(name: &str) -> Option<Literal> {
        if common::is_valid_name(name) {
            Some(Literal {
                name: name.into(),
                negated: true,
            })
        } else {
            None
        }
    }

    /// Negate the `Literal`, i.e. change it to negated if it is unnegated, and to
    /// unnegated if it was negated.
    ///
    /// ```
    /// # use resolution::cnf::*;
    /// let mut lit = Literal::new("P").unwrap();
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
    /// let lit1 = Literal::new("P").unwrap();
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

/// A CNF term, i.e. a generalized disjunction of literals.
///
/// The [`cnf_term!`] macro provides a convenient way to create `Term`s.
///
/// [`cnf_term!`]: ../macro.cnf_term.html
#[derive(Debug, Clone, Default)]
pub struct Term {
    literals: HashSet<Literal>,
}

impl Term {
    /// Create a new, empty `Term`.
    pub fn new() -> Term {
        Term {
            literals: HashSet::new(),
        }
    }

    /// Add the given `Literal` to the `Term`, with the following caveats:
    /// 1. If an identical `Literal` is already in the `Term`, this method
    ///    is a no-op.
    /// 2. If a `Literal` with the same name but opposite negation is already
    ///    in the `Term`, this method removes that `Literal` instead of adding
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
    /// `Term`. Returns `true` if the `Literal` was present.
    pub fn remove(&mut self, lit: &Literal) -> bool {
        self.literals.remove(lit)
    }

    /// Remove and return the `Literal` equal to the given one, if it is present
    /// in the `Term`.
    pub fn take(&mut self, lit: &Literal) -> Option<Literal> {
        self.literals.take(lit)
    }

    /// Is this `Term` empty?
    pub fn is_empty(&self) -> bool {
        self.literals.is_empty()
    }

    /// Return a `HashSet` of all of the `Literal`s in this `Term`, negated.
    fn negated_literals(&self) -> HashSet<Literal> {
        let mut literals = HashSet::new();
        for lit in &self.literals {
            literals.insert(lit.clone_negated());
        }
        literals
    }

    /// Negate all `Literal`s in the `Term`.
    pub fn negate_all(&mut self) {
        self.literals = self.negated_literals();
    }

    /// Create a copy of the `Term` in which all `Literal`s are negated.
    pub fn clone_negated(&self) -> Term {
        Term {
            literals: self.negated_literals(),
        }
    }

    /// Return an iterator over references to the [`Literal`]s contained in this `Term`.
    ///
    /// [`Literal`]: struct.Literal.html
    pub fn iter(&self) -> hash_set::Iter<Literal> {
        self.literals.iter()
    }

    /// Attempt to resolve two `Term`s. If successful, returns the `Term`
    /// resulting from the resolution.
    pub fn resolve(&self, other: &Term) -> Option<Term> {
        let neg_intersect = &self.negated_literals() & &other.literals;
        if neg_intersect.is_empty() {
            return None;
        }

        let other_diff = &other.literals - &neg_intersect;
        let intersect = neg_intersect.iter().map(Literal::clone_negated).collect();
        let self_diff = &self.literals - &intersect;
        Some(Term {
            literals: &other_diff | &self_diff,
        })
    }
}

impl Display for Term {
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

impl PartialEq for Term {
    fn eq(&self, other: &Self) -> bool {
        self.literals.difference(&other.literals).next() == None
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
        let mut v: Vec<_> = self.literals.iter().collect();
        v.sort_unstable();
        v.hash(state);
    }
}

impl FromIterator<Literal> for Term {
    fn from_iter<T>(iter: T) -> Term
    where
        T: IntoIterator<Item = Literal>,
    {
        let mut t = Term::new();
        for lit in iter {
            t.add(lit);
        }
        t
    }
}

impl IntoIterator for Term {
    type Item = Literal;
    type IntoIter = hash_set::IntoIter<Literal>;
    fn into_iter(self) -> Self::IntoIter {
        self.literals.into_iter()
    }
}

impl<'a> IntoIterator for &'a Term {
    type Item = &'a Literal;
    type IntoIter = hash_set::Iter<'a, Literal>;
    fn into_iter(self) -> Self::IntoIter {
        self.literals.iter()
    }
}

/// A convenience macro for creating [`Term`]s. `cnf_term!` takes a comma-separated
/// list of identifiers, each one of which is optionally prepended with a `~` character.
/// The result is a [`Term`] containing [`Literal`]s with the given identifiers as names,
/// negated if the corresponding identifier was prefaced with a `~`.
///
/// ```
/// # #[macro_use] extern crate resolution;
/// # use resolution::cnf::*;
/// // Manually construct a Term
/// let mut term1 = Term::new();
/// term1.add(Literal::new("P").unwrap());
/// term1.add(Literal::new_negated("Q").unwrap());
/// term1.add(Literal::new("R").unwrap());
///
/// // Construct the same term with `cnf_term!`
/// let term2 = cnf_term!(P, ~Q, R);
/// assert_eq!(term1, term2);
///
/// // `Term`s are irrespective of ordering
/// let term3 = cnf_term!(~Q, R, P);
/// assert_eq!(term1, term3);
/// ```
///
/// [`Term`]: cnf/struct.Term.html
/// [`Literal`]: cnf/struct.Literal.html
#[macro_export]
macro_rules! cnf_term {
    (@accum () -> ($($body:tt)*)) => { vec![$($body)*] };
    (@accum (, $($tail:tt)*) -> ($($body:tt)*)) => { cnf_term!(@accum ($($tail)*) -> ($($body)*)) };
    (@accum (~$name:ident $($tail:tt)*) -> ($($body:tt)*))
        => { cnf_term!(@accum ($($tail)*) -> (Literal::new_negated(stringify!($name)).unwrap(), $($body)*)) };
    (@accum ($name:ident $($tail:tt)*) -> ($($body:tt)*))
        => { cnf_term!(@accum ($($tail)*) -> (Literal::new(stringify!($name)).unwrap(), $($body)*)) };
    [$($props:tt)*] => {
        cnf_term!(@accum ($($props)*) -> ()).into_iter().collect::<Term>()
    };
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn term_macro() {
        let t = cnf_term!(P, Q);
        let mut expected = Term::new();
        expected.add(Literal::new("P").unwrap());
        expected.add(Literal::new("Q").unwrap());
        assert_eq!(t, expected);

        let t = cnf_term!(P, ~P);
        let expected = Term::new();
        assert_eq!(t, expected);
    }

    #[test]
    fn resolve1() {
        let t1 = cnf_term!(P);
        let t2 = cnf_term!(~P);

        let res = t1.resolve(&t2).expect("Resolution returned None");
        assert!(res.is_empty());

        let res = t2.resolve(&t1).expect("Resolution returned None");
        assert!(res.is_empty());
    }

    #[test]
    fn resolve2() {
        let t1 = cnf_term!(P, Q);
        let t2 = cnf_term!(~P);
        let expected_res = cnf_term!(Q);

        let res = t1.resolve(&t2).expect("Resolution returned None");
        assert_eq!(res, expected_res);

        let res = t2.resolve(&t1).expect("Resolution returned None");
        assert_eq!(res, expected_res);
    }

    #[test]
    fn resolve_multi() {
        let t1 = cnf_term!(P, ~Q);
        let t2 = cnf_term!(R, Q);
        let expected_res = cnf_term!(P, R);

        let res = t1.resolve(&t2).expect("Resolution returned None");
        assert_eq!(res, expected_res);

        let res = t2.resolve(&t1).expect("Resolution returned None");
        assert_eq!(res, expected_res);
    }

    #[test]
    fn resolve_none() {
        let t1 = cnf_term!(P);
        let t2 = cnf_term!(Q);

        if let Some(_) = t1.resolve(&t2) {
            panic!("Resolution returned Some");
        }

        if let Some(_) = t2.resolve(&t1) {
            panic!("Resolution returned Some");
        }
    }

    #[test]
    fn resolve_self() {
        let t = cnf_term!(P);
        if let Some(_) = t.resolve(&t) {
            panic!("Self-resolution returned Some");
        }
    }

    #[test]
    fn add_identical() {
        let mut t = cnf_term!(P);
        t.add(Literal::new("P").unwrap());

        assert_eq!(t, cnf_term!(P));
    }

    #[test]
    fn add_negated() {
        let mut t = cnf_term!(P);
        t.add(Literal::new_negated("P").unwrap());

        assert_eq!(t, cnf_term!());
    }

    #[test]
    fn collect() {
        let t = vec![Literal::new("P"), Literal::new("Q")]
            .into_iter()
            .map(|o| o.unwrap())
            .collect::<Term>();

        let mut expected = Term::new();
        expected.add(Literal::new("P").unwrap());
        expected.add(Literal::new("Q").unwrap());

        assert_eq!(t, expected);
    }

    #[test]
    fn collect_negated() {
        let t = vec![Literal::new("P"), Literal::new_negated("P")]
            .into_iter()
            .map(|o| o.unwrap())
            .collect::<Term>();

        let expected = Term::new();

        assert_eq!(t, expected);
    }
}
