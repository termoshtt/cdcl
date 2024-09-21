use crate::{selector, Clause, Literal, CNF};
use std::collections::BTreeSet;
use std::num::NonZeroU32;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DecisionLevel {
    decision: Literal,
    implicated: Vec<Implicated>,
}

impl DecisionLevel {
    /// Create a new decision level with new decision
    pub fn new(decision: Literal) -> Self {
        Self {
            decision,
            implicated: vec![],
        }
    }

    /// Number of literals in the decision level
    pub fn len(&self) -> usize {
        self.implicated.len() + 1
    }

    pub fn literals(&self) -> impl Iterator<Item = &Literal> {
        std::iter::once(&self.decision).chain(self.implicated.iter().map(|i| &i.literal))
    }

    pub fn supp(&self) -> BTreeSet<NonZeroU32> {
        self.literals().map(|l| l.id).collect()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Implicated {
    literal: Literal,
    reason: Clause,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Default)]
pub struct Trail {
    decision_levels: Vec<DecisionLevel>,
}

impl Trail {
    /// Number of literals in the trail
    pub fn len(&self) -> usize {
        self.decision_levels.iter().map(DecisionLevel::len).sum()
    }

    pub fn is_empty(&self) -> bool {
        self.decision_levels.is_empty()
    }

    pub fn literals(&self) -> impl Iterator<Item = &Literal> {
        self.decision_levels
            .iter()
            .flat_map(DecisionLevel::literals)
    }

    pub fn supp(&self) -> BTreeSet<NonZeroU32> {
        self.decision_levels
            .iter()
            .flat_map(DecisionLevel::supp)
            .collect()
    }

    pub fn push_implicated(&mut self, literal: Literal, reason: Clause) {
        self.decision_levels
            .last_mut()
            .expect("Pushing to empty trail")
            .implicated
            .push(Implicated { literal, reason });
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CDCL {
    expr: CNF,
    selector: fn(&CNF) -> usize,
    trail: Trail,
}

impl CDCL {
    pub fn new(expr: CNF, selector: fn(&CNF) -> usize) -> Self {
        Self {
            expr,
            selector,
            trail: Trail::default(),
        }
    }

    /// Seek every possible implicated literals
    ///
    /// This process returns if
    /// - A conflict clause is found. In this case, the conflict clause is returned. The solver should backjump.
    /// - All implications are resolved. In this case, `None` is returned. The solver should make a decision.
    ///
    fn unit_propagation(&mut self) -> Option<&Clause> {
        let CNF::Valid(clauses) = &self.expr else {
            unreachable!("Start implication with conflicting CNF");
        };
        'unit_propagation: loop {
            for clause in clauses {
                let mut c = clause.clone();
                for l in self.trail.literals() {
                    c.substitute(*l);
                    if c.is_conflicted() {
                        return Some(clause);
                    }
                }
                if let Some(lit) = c.as_unit() {
                    self.trail.push_implicated(lit, clause.clone());
                    continue 'unit_propagation;
                }
            }
            break;
        }
        None
    }
}
