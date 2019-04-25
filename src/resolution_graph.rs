//! Collections of `Clauses` and resolution graphs.

use crate::cnf::Clause;
use std::cmp::{Eq, Ord, Ordering, PartialEq, PartialOrd};
use std::collections::{HashMap, HashSet};
use std::convert::From;
use std::fmt::{self, Display, Formatter};
use std::hash::{Hash, Hasher};
use std::num::NonZeroU32;

/// An ID for a `Clause` in a `ResolutionGraph`.
#[derive(Debug, PartialOrd, Ord, PartialEq, Eq, Clone, Copy, Hash)]
#[repr(transparent)]
pub struct ClauseId(pub NonZeroU32);

impl ClauseId {
    pub fn new(n: u32) -> Option<ClauseId> {
        let n = NonZeroU32::new(n);
        if n.is_none() {
            None
        } else {
            Some(ClauseId(n.unwrap()))
        }
    }
}

impl From<NonZeroU32> for ClauseId {
    fn from(n: NonZeroU32) -> ClauseId {
        ClauseId(n)
    }
}

impl Display for ClauseId {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl std::ops::Deref for ClauseId {
    type Target = NonZeroU32;
    fn deref(&self) -> &NonZeroU32 {
        &self.0
    }
}

impl std::ops::DerefMut for ClauseId {
    fn deref_mut(&mut self) -> &mut NonZeroU32 {
        &mut self.0
    }
}

/// A single resolution in a `ResolutionGraph`. This struct's ordering, comparison,
/// and hash implementations treat the pair of `ClauseId`s as unordered.
#[derive(Debug, Clone)]
pub struct ResolutionParents(ClauseId, ClauseId);

impl ResolutionParents {
    pub fn new(parent1: ClauseId, parent2: ClauseId) -> ResolutionParents {
        if parent1 < parent2 {
            ResolutionParents(parent1, parent2)
        } else {
            ResolutionParents(parent2, parent1)
        }
    }

    pub fn first_parent(&self) -> ClauseId {
        self.0
    }

    pub fn second_parent(&self) -> ClauseId {
        self.1
    }
}

impl PartialEq for ResolutionParents {
    fn eq(&self, rhs: &ResolutionParents) -> bool {
        self.first_parent() == rhs.first_parent() && self.second_parent() == rhs.second_parent()
    }
}

impl Eq for ResolutionParents {}

impl PartialOrd for ResolutionParents {
    fn partial_cmp(&self, rhs: &ResolutionParents) -> Option<Ordering> {
        match self.first_parent().cmp(&rhs.first_parent()) {
            Ordering::Less => Some(Ordering::Less),
            Ordering::Greater => Some(Ordering::Greater),
            Ordering::Equal => Some(self.second_parent().cmp(&rhs.second_parent())),
        }
    }
}

impl Ord for ResolutionParents {
    fn cmp(&self, rhs: &ResolutionParents) -> Ordering {
        self.partial_cmp(rhs).unwrap()
    }
}

impl Hash for ResolutionParents {
    fn hash<H: Hasher>(&self, h: &mut H) {
        self.first_parent().hash(h);
        self.second_parent().hash(h);
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct Resolution {
    parents: ResolutionParents,
    child: ClauseId,
}

impl Resolution {
    pub fn new(parent1: ClauseId, parent2: ClauseId, child: ClauseId) -> Resolution {
        Resolution {
            parents: ResolutionParents::new(parent1, parent2),
            child
        }
    }

    pub fn first_parent(&self) -> ClauseId {
        self.parents.first_parent()
    }

    pub fn second_parent(&self) -> ClauseId {
        self.parents.second_parent()
    }

    pub fn child(&self) -> ClauseId {
        self.child
    }
}

/// A collection of `Clause`s, together with resolutions between them.
#[derive(Debug, Clone)]
pub struct ResolutionGraph {
    clauses: HashMap<ClauseId, Clause>,
    resolutions: HashSet<Resolution>,
    next_id: ClauseId,
}

impl ResolutionGraph {
    /// Create a new, empty `ResolutionGraph`.
    pub fn new() -> ResolutionGraph {
        ResolutionGraph {
            clauses: HashMap::new(),
            resolutions: HashSet::new(),
            next_id: ClauseId::new(1).unwrap(),
        }
    }

    fn get_next_id_incr(&mut self) -> ClauseId {
        let id = self.next_id;
        self.next_id = NonZeroU32::new(id.get() + 1).unwrap().into();
        id
    }

    /// Add a new `Clause` to the `ResolutionGraph`, and return its `ClauseId`.
    ///
    /// Note that this function does not ensure uniqueness of `Clause`s.
    pub fn add_clause(&mut self, clause: Clause) -> ClauseId {
        let id = self.get_next_id_incr();
        self.clauses.insert(id, clause);
        id
    }

    /// Get the `Clause` with the given `ClauseId`.
    ///
    /// Returns `None` if there is no `Clause` with the given ID in the `ResolutionGraph`.
    pub fn get_clause(&self, id: ClauseId) -> Option<&Clause> {
        self.clauses.get(&id)
    }

    /// Get a mutable reference to the `Clause` with the given `ClauseId`.
    ///
    /// Returns `None` if there is not `Clause` with the given ID in the `ResolutionGraph`.
    pub fn get_clause_mut(&mut self, id: ClauseId) -> Option<&mut Clause> {
        self.clauses.get_mut(&id)
    }

    /// Add a resolution between `Clause`s in the graph.
    ///
    /// Returns `Err` if any of the `Clause`s named in the given `Resolution` do not
    /// exist in the graph, or if the resolution is already part of the graph. Note
    /// that this function will happily allow incorrect
    /// resolutions to be added; to verify correctness, use the `verify_correct()` or
    /// `verify()` functions.
    pub fn add_resolution(&mut self, resolution: Resolution) -> Result<(), &str> {
        let Resolution {
            parents: ResolutionParents(a, b),
            child,
        } = resolution;
        self.clauses
            .get(&a)
            .ok_or("First parent is not a clause in this graph")?;
        self.clauses
            .get(&b)
            .ok_or("Second parent is not a clause in this graph")?;
        self.clauses
            .get(&child)
            .ok_or("Child is not a clause in this graph")?;
        if self.resolutions.contains(&resolution) {
            Err("Resolution is already a part of this graph.")
        } else {
            self.resolutions.insert(resolution);
            Ok(())
        }
    }

    /// Add a resolution between `Clause`s in the graph.
    ///
    /// Returns `Err` if any of the `Clause`s named do not
    /// exist in the graph. Note that this function will happily allow incorrect
    /// resolutions to be added; to verify correctness, use the `verify()` or
    /// `verify_correct()` functions.
    pub fn add_resolution_ids(
        &mut self,
        parent1: ClauseId,
        parent2: ClauseId,
        child: ClauseId,
    ) -> Result<(), &str> {
        self.add_resolution(Resolution { parents: ResolutionParents(parent1, parent2), child })
    }

    pub fn verify(&self) -> Result<(), ResolutionErr> {
        let res = self.verify_correct();
        let complete = self.verify_complete();

        if let Err(mut res) = res {
            res.incomplete = !complete;
            Err(res)
        } else if !complete {
            Err(ResolutionErr {
                graph: &self,
                failed: Vec::new(),
                incorrect: Vec::new(),
                incomplete: true,
            })
        } else {
            Ok(())
        }
    }

    /// Verify the correctness of all resolutions in the graph.
    pub fn verify_correct(&self) -> Result<(), ResolutionErr> {
        let mut failed = Vec::new();
        let mut incorrect = Vec::new();
        for res in &self.resolutions {
            let Resolution {
                parents: ResolutionParents(a, b),
                child,
            } = res;
            let (a, b, child) = (
                self.get_clause(*a).unwrap(),
                self.get_clause(*b).unwrap(),
                self.get_clause(*child).unwrap(),
            );

            let true_resolve = a.resolve(b);
            if true_resolve.is_none() {
                failed.push(res);
            } else if true_resolve.unwrap() != *child {
                incorrect.push(res);
            }
        }

        if !failed.is_empty() || !incorrect.is_empty() {
            Err(ResolutionErr {
                graph: &self,
                failed,
                incorrect,
                incomplete: false,
            })
        } else {
            Ok(())
        }
    }

    pub fn verify_complete(&self) -> bool {
        for (&id1, p1) in &self.clauses {
            for (&id2, p2) in &self.clauses {
                if id1 == id2 {
                    continue;
                }

                for (&idc, c) in &self.clauses {
                    if idc == id1 || idc == id2 {
                        continue;
                    }

                    if let Some(clause) = p1.resolve(&p2) {
                        if c == &clause {
                            let res = Resolution::new(id1, id2, idc);
                            if !self.resolutions.contains(&res) {
                                return false;
                            }
                        }
                    }
                }
            }
        }
        true
    }
}

impl std::default::Default for ResolutionGraph {
    #[inline]
    fn default() -> ResolutionGraph {
        ResolutionGraph::new()
    }
}

/// A record of failed and incorrect resolutions in a `ResolutionGraph`.
///
/// Failed resolutions are those which attempt to resolve two clauses that
/// cannot be resolved. Incorrect resolutions are those which resolve two
/// clauses that can be correctly resolved, but for which an incorrect
/// result is given.
#[derive(Debug)]
pub struct ResolutionErr<'a> {
    pub graph: &'a ResolutionGraph,
    pub failed: Vec<&'a Resolution>,
    pub incorrect: Vec<&'a Resolution>,
    pub incomplete: bool,
}

impl<'a> Display for ResolutionErr<'a> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        if !self.failed.is_empty() {
            writeln!(f, "The following clauses cannot be resolved:")?;
            for res in &self.failed {
                let Resolution {
                    parents: ResolutionParents(a, b), ..
                } = res;
                writeln!(
                    f,
                    "  {}, {}",
                    self.graph.get_clause(*a).unwrap(),
                    self.graph.get_clause(*b).unwrap(),
                )?;
            }
        }

        if !self.incorrect.is_empty() {
            writeln!(f, "The following resolutions are incorrect:")?;
            for res in &self.incorrect {
                let Resolution {
                    parents: ResolutionParents(a, b),
                    child,
                } = res;
                writeln!(
                    f,
                    "  {}, {} |- {}",
                    self.graph.get_clause(*a).unwrap(),
                    self.graph.get_clause(*b).unwrap(),
                    self.graph.get_clause(*child).unwrap(),
                )?;
            }
        }

        if self.incomplete {
            writeln!(
                f,
                "The graph is incomplete; there are still clauses that can be resolved."
            )?;
        }

        Ok(())
    }
}

impl<'a> std::error::Error for ResolutionErr<'a> {}

#[cfg(test)]
mod test {
    use super::*;
    use crate::cnf::Literal;

    #[test]
    fn basic_graph() {
        let mut graph = ResolutionGraph::new();
        let a = graph.add_clause(cnf_clause!(P, Q));
        let b = graph.add_clause(cnf_clause!(~P, R));

        assert_eq!(graph.get_clause(a).unwrap(), &cnf_clause!(P, Q));
        assert_eq!(graph.get_clause(b).unwrap(), &cnf_clause!(~P, R));
        assert!(graph.get_clause(ClauseId::new(100).unwrap()).is_none());
    }

    #[test]
    fn graph_correct_resolution() {
        let mut graph = ResolutionGraph::new();
        let a = graph.add_clause(cnf_clause!(P, Q));
        let b = graph.add_clause(cnf_clause!(~P, R));
        let c = graph.add_clause(cnf_clause!(Q, R));

        graph.add_resolution_ids(a, b, c).unwrap();

        graph.verify().expect("Expected correct resolution");
    }

    #[test]
    fn graph_failed_resolution() {
        let mut graph = ResolutionGraph::new();
        let a = graph.add_clause(cnf_clause!(P, Q));
        let b = graph.add_clause(cnf_clause!(~R, S));
        let c = graph.add_clause(cnf_clause!(Q, R));

        graph.add_resolution_ids(a, b, c).unwrap();

        let r = graph.verify();
        assert!(r.is_err());
        println!("===graph_failed_resolution===\n{}", r.err().unwrap());
    }

    #[test]
    fn graph_incorrect_resolution() {
        let mut graph = ResolutionGraph::new();
        let a = graph.add_clause(cnf_clause!(P, Q));
        let b = graph.add_clause(cnf_clause!(~P, R));
        let c = graph.add_clause(cnf_clause!(Q, S));

        graph.add_resolution_ids(a, b, c).unwrap();

        let r = graph.verify();
        assert!(r.is_err());
        println!("===graph_incorrect_resolution===\n{}", r.err().unwrap());
    }

    #[test]
    fn graph_incomplete_resolution() {
        let mut graph = ResolutionGraph::new();
        let a = graph.add_clause(cnf_clause!(P, Q));
        let b = graph.add_clause(cnf_clause!(~P, R));
        let c = graph.add_clause(cnf_clause!(Q, R));
        let _d = graph.add_clause(cnf_clause!(~R, T));

        graph.add_resolution_ids(a, b, c).unwrap();

        let r = graph.verify();
        assert!(r.is_err());
        println!("===graph_incomplete_resolution===\n{}", r.err().unwrap());
    }

    #[test]
    fn graph_multiple_failures() {
        let mut graph = ResolutionGraph::new();
        let p_q = graph.add_clause(cnf_clause!(P, Q));
        let np_r = graph.add_clause(cnf_clause!(~P, R));
        let q_s = graph.add_clause(cnf_clause!(Q, S));
        let q_nr = graph.add_clause(cnf_clause!(Q, ~R));
        let t_v = graph.add_clause(cnf_clause!(T, V));
        let q_r = graph.add_clause(cnf_clause!(Q, R));

        graph.add_resolution_ids(p_q, np_r, q_s).unwrap();
        graph.add_resolution_ids(q_s, q_nr, t_v).unwrap();
        graph.add_resolution_ids(p_q, np_r, q_r).unwrap();

        let r = graph.verify();
        assert!(r.is_err());
        println!("===graph_multiple_failures===\n{}", r.err().unwrap());
    }
}
