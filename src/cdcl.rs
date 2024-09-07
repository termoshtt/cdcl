use crate::{Clause, Literal, CNF};

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
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CDCL {
    expr: CNF,
    selector: fn(&CNF) -> usize,
    trail: Vec<DecisionLevel>,
}

enum ClauseState {
    /// Clause is satisfied for given the Trail state
    Satisfied,
    /// Clause is conflicting
    Conflict,
    /// Clause contains a single unassigned literal
    Unit(Literal),
    /// Clause contains two or more unassigned literals
    Undetermined,
}

pub fn check_clause(_trail: &Trail, clause: &Clause) -> ClauseState {
    if matches!(clause, Clause::Conflicted) {
        return ClauseState::Conflict;
    }

    todo!()
}

impl CDCL {
    pub fn new(expr: CNF, selector: fn(&CNF) -> usize) -> Self {
        Self {
            expr,
            selector,
            trail: vec![],
        }
    }
}
