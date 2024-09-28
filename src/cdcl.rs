use crate::{Clause, Literal, Solution, CNF};
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
    trail: Trail,
}

impl CDCL {
    pub fn new(expr: CNF) -> Self {
        Self {
            expr,
            trail: Trail::default(),
        }
    }

    fn make_decision(&mut self) -> Option<Solution> {
        let supp = self.expr.supp();
        let trail_supp = self.trail.supp();
        let mut remaining = supp.difference(&trail_supp);
        if let Some(id) = remaining.next() {
            let level = DecisionLevel::new(Literal {
                id: *id,
                positive: true,
            });
            self.trail.decision_levels.push(level);
            return None;
        }
        Some(Solution::Sat(self.trail.literals().cloned().collect()))
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

    pub fn solve(&mut self) -> Solution {
        if let Some(solution) = self.expr.is_solved() {
            return solution;
        }
        loop {
            if let Some(solution) = self.make_decision() {
                return solution;
            }
            if let Some(_conflict) = self.unit_propagation() {
                // Backjump
                todo!()
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{clause, lit};

    #[test]
    fn unit_propagation() {
        let expr = clause![-1, 2] & clause![-2, 3] & clause![-3, 4];
        let mut cdcl = CDCL::new(expr);

        // First decision, this must be 1 since it is the smallest id
        cdcl.make_decision();
        assert_eq!(cdcl.trail.decision_levels[0].decision, lit!(1));

        let conflicted = cdcl.unit_propagation();
        assert!(conflicted.is_none());

        assert_eq!(
            cdcl.trail.decision_levels[0],
            DecisionLevel {
                decision: lit!(1),
                implicated: vec![
                    Implicated {
                        literal: lit!(2),
                        reason: clause![-1, 2]
                    },
                    Implicated {
                        literal: lit!(3),
                        reason: clause![-2, 3]
                    },
                    Implicated {
                        literal: lit!(4),
                        reason: clause![-3, 4]
                    }
                ],
            }
        );
    }

    #[test]
    fn unit_propagation_conflict() {
        let expr = clause![-1, 2] & clause![-1, -2];
        let mut cdcl = CDCL::new(expr);

        // First decision, this must be 1 since it is the smallest id
        cdcl.make_decision();
        assert_eq!(cdcl.trail.decision_levels[0].decision, lit!(1));

        // Since clauses are scanned in order, [-1, 2] yields the x2 literal,
        // and then [-1, -2] yields a conflict
        let conflicted = cdcl.unit_propagation();
        assert_eq!(conflicted.unwrap(), &clause![-1, -2]);
    }

    #[test]
    fn solve_single_solution_cases() {
        for (expr, expected) in crate::testing::single_solution_cases() {
            dbg!(&expr, &expected);
            let mut cdcl = CDCL::new(expr);
            let solution = cdcl.solve();
            assert_eq!(solution, expected);
        }
    }
}
