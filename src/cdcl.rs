use crate::{pending_once, Clause, Literal, Solution, CNF};
use std::{collections::BTreeSet, fmt, num::NonZeroU32};

pub async fn cdcl(expr: CNF) -> Solution {
    let mut cdcl = CDCL::new(expr);
    cdcl.solve().await
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DecisionLevel {
    decision: Option<Literal>,
    implicated: Vec<Implicated>,
}

impl DecisionLevel {
    /// Root decision level
    pub fn root() -> Self {
        Self {
            decision: None,
            implicated: vec![],
        }
    }

    /// Create a new decision level with new decision
    pub fn new(decision: Literal) -> Self {
        Self {
            decision: Some(decision),
            implicated: vec![],
        }
    }

    /// Number of literals in the decision level
    pub fn len(&self) -> usize {
        self.implicated.len() + self.decision.iter().count()
    }

    pub fn is_empty(&self) -> bool {
        self.decision.is_none() && self.implicated.is_empty()
    }

    pub fn literals(&self) -> impl Iterator<Item = &Literal> {
        self.decision
            .iter()
            .chain(self.implicated.iter().map(|i| &i.literal))
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Trail {
    decision_levels: Vec<DecisionLevel>,
}

impl fmt::Display for Trail {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let level_width = self.decision_levels.len().to_string().len();
        let supp = self.supp();
        let Some(max_id) = supp.last() else {
            // No output for empty trail
            return Ok(());
        };
        let literal_width = max_id.to_string().len() + 2;

        for (i, level) in self.decision_levels.iter().enumerate() {
            if let Some(decision) = &level.decision {
                writeln!(
                    f,
                    "{:>literal_width$} | {i:>level_width$} | Λ",
                    decision.to_string()
                )?;
            }
            for imp in &level.implicated {
                writeln!(
                    f,
                    "{:>literal_width$} | {i:>level_width$} | {}",
                    imp.literal.to_string(),
                    imp.reason
                )?;
            }
        }
        Ok(())
    }
}

impl Default for Trail {
    fn default() -> Self {
        Self {
            decision_levels: vec![DecisionLevel::root()],
        }
    }
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

    /// Current decision level. This returns 0 if in the root level.
    pub fn level(&self) -> usize {
        self.decision_levels.len() - 1
    }

    pub fn backjump(&mut self, level: usize) {
        self.decision_levels.truncate(level + 1);
    }

    pub fn level_of(&self, id: NonZeroU32) -> Option<usize> {
        self.decision_levels
            .iter()
            .position(|l| l.literals().any(|l2| l2.id == id))
    }

    pub fn push_implicated(&mut self, literal: Literal, reason: Clause) {
        self.decision_levels
            .last_mut()
            .expect("Pushing to empty trail")
            .implicated
            .push(Implicated { literal, reason });
    }

    fn current_level(&self) -> &DecisionLevel {
        self.decision_levels
            .last()
            .expect("Current level is always present")
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Default)]
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
    async fn unit_propagation(&mut self) -> Option<Clause> {
        let CNF::Valid(clauses) = &self.expr else {
            unreachable!("Start implication with conflicting CNF");
        };
        'unit_propagation: loop {
            for clause in clauses {
                let mut c = clause.clone();
                for l in self.trail.literals() {
                    pending_once().await;
                    c.substitute(*l);
                    if c.is_conflicted() {
                        return Some(clause.clone());
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

    pub async fn solve(&mut self) -> Solution {
        'cdcl: loop {
            if let Some(solution) = self.expr.is_solved() {
                return solution;
            }
            pending_once().await;

            if let Some(mut conflict) = self.unit_propagation().await {
                // Backjump
                for i in self.trail.current_level().implicated.iter().rev() {
                    if let Ok(c) = conflict.clone().resolution(i.reason.clone()) {
                        if let Some(lit) = c.as_unit() {
                            self.expr = self.expr.clone() & lit;
                            self.trail.backjump(0);
                            continue 'cdcl;
                        }
                        if c.is_conflicted() {
                            // This means ⊥ can be derived from clauses
                            return Solution::UnSat;
                        }
                        conflict = c;
                    }
                }
                let mut levels: Vec<_> = conflict
                    .literals()
                    .expect("Already checked")
                    .map(|lit| {
                        self.trail
                            .level_of(lit.id)
                            .expect("Literal of conflict clause must be in trail")
                    })
                    .collect();
                let n = levels.len();
                assert!(n > 0, "Conflict clause must have at least one literal");
                levels.sort_unstable();
                assert_eq!(
                    levels[n - 1],
                    self.trail.level(),
                    "Conflict clause must have one literal from the current decision level"
                );
                self.trail.backjump(if n > 1 { levels[n - 2] } else { 0 });
                if self.expr.add_clause(conflict).is_err() {
                    return Solution::UnSat;
                }
                continue 'cdcl;
            }
            if let Some(solution) = self.make_decision() {
                return solution;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{block_on, clause, lit};

    #[test]
    fn unit_propagation() {
        let expr = clause![-1, 2] & clause![-2, 3] & clause![-3, 4];
        let mut cdcl = CDCL::new(expr);

        // First decision, this must be 1 since it is the smallest id
        cdcl.make_decision();
        assert_eq!(cdcl.trail.decision_levels[1].decision, Some(lit!(1)));

        let conflicted = block_on(cdcl.unit_propagation());
        assert!(conflicted.is_none());

        insta::assert_snapshot!(cdcl.trail.to_string(), @r###"
        x1 | 1 | Λ
        x2 | 1 | ¬x1 ∨ x2
        x3 | 1 | ¬x2 ∨ x3
        x4 | 1 | ¬x3 ∨ x4
        "###);
    }

    #[test]
    fn unit_propagation_conflict() {
        let expr = clause![-1, 2] & clause![-1, -2];
        let mut cdcl = CDCL::new(expr);

        // First decision, this must be 1 since it is the smallest id
        cdcl.make_decision();
        assert_eq!(cdcl.trail.decision_levels[1].decision, Some(lit!(1)));

        // Since clauses are scanned in order, [-1, 2] yields the x2 literal,
        // and then [-1, -2] yields a conflict
        let conflicted = block_on(cdcl.unit_propagation());
        assert_eq!(conflicted.unwrap(), clause![-1, -2]);

        insta::assert_snapshot!(cdcl.trail.to_string(), @r"
        x1 | 1 | Λ
        x2 | 1 | ¬x1 ∨ x2
        ");
    }

    #[test]
    fn solve_single_solution_cases() {
        for (expr, expected) in crate::testing::single_solution_cases() {
            let mut cdcl = CDCL::new(expr);
            let solution = block_on(cdcl.solve());
            assert_eq!(solution, expected);
        }
    }

    #[test]
    fn solve_unsat() {
        // From Knuth 4B (112)
        let expr = clause![1, 2, 3, 4]
            & clause![1, -2]
            & clause![-1, -2, -3]
            & clause![-1, 3]
            & clause![2, -3]
            & clause![3, -4];

        let mut cdcl = CDCL::new(expr);
        let solution = block_on(cdcl.solve());
        assert_eq!(solution, Solution::UnSat);
    }
}
