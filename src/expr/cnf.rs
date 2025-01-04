use super::{Clause, Literal};
use crate::{Solution, State};
use anyhow::Result;
use proptest::prelude::*;
use std::{
    collections::BTreeSet,
    fmt,
    hash::{Hash, Hasher},
    num::NonZeroU32,
    ops::{BitAnd, BitOr, Not},
};

/// An expression in boolean logic of [Conjunctive Normal Form](https://en.wikipedia.org/wiki/Conjunctive_normal_form)
///
/// ```rust
/// use cdcl::lit;
///
/// // (x1 ∧ x2) ∨ x3 = (x1 ∨ x3) ∧ (x2 ∨ x3)
/// let expr = (lit!(1) & lit!(2)) | lit!(3);
/// assert_eq!(expr.to_string(), "(x1 ∨ x3) ∧ (x2 ∨ x3)");
///
/// // x1 ∨ (x2 ∧ x3) = (x1 ∨ x2) ∧ (x1 ∨ x3)
/// let expr = lit!(1) | (lit!(2) & lit!(3));
/// assert_eq!(expr.to_string(), "(x1 ∨ x2) ∧ (x1 ∨ x3)");
///
/// // (x1 ∧ x2) ∨ (x3 ∧ x4) = (x1 ∨ x3) ∧ (x1 ∨ x4) ∧ (x2 ∨ x3) ∧ (x2 ∨ x4)
/// let expr = (lit!(1) & lit!(2)) | (lit!(3) & lit!(4));
/// assert_eq!(expr.to_string(), "(x1 ∨ x3) ∧ (x1 ∨ x4) ∧ (x2 ∨ x3) ∧ (x2 ∨ x4)");
///
/// // ¬(x1 ∧ x2) = ¬x1 ∨ ¬x2
/// let expr = !(lit!(1) & lit!(2));
/// assert_eq!(expr.to_string(), "(¬x1 ∨ ¬x2)");
///
/// // ¬(x1 ∨ x2) ∧ x3 = ¬x1 ∧ ¬x2 ∧ x3
/// let expr = !(lit!(1) | lit!(2)) & lit!(3);
/// assert_eq!(expr.to_string(), "(¬x1) ∧ (¬x2) ∧ (x3)");
/// ```
#[derive(Clone, PartialEq, Eq, Hash, Default)]
pub enum CNF {
    Valid(Vec<Clause>),
    #[default]
    Conflicted,
}

impl FromIterator<Clause> for CNF {
    fn from_iter<T: IntoIterator<Item = Clause>>(iter: T) -> Self {
        Self::from_clauses(iter.into_iter().collect())
    }
}

impl From<bool> for CNF {
    fn from(value: bool) -> Self {
        if value {
            CNF::tautology()
        } else {
            CNF::Conflicted
        }
    }
}

impl From<Literal> for CNF {
    fn from(literal: Literal) -> Self {
        CNF::from(Clause::from(literal))
    }
}

impl From<Clause> for CNF {
    fn from(clause: Clause) -> Self {
        if clause.is_conflicted() {
            CNF::Conflicted
        } else {
            Self::Valid(vec![clause])
        }
    }
}

impl PartialEq<Clause> for CNF {
    fn eq(&self, other: &Clause) -> bool {
        match (self.is_tautology(), other.is_tautology()) {
            (true, true) => return true,
            (false, true) | (true, false) => return false,
            _ => {}
        }
        match self {
            Self::Valid(clauses) => clauses.len() == 1 && clauses[0] == *other,
            Self::Conflicted => &Clause::Conflicted == other,
        }
    }
}

impl PartialEq<Literal> for CNF {
    fn eq(&self, other: &Literal) -> bool {
        match self {
            Self::Valid(clauses) => clauses.len() == 1 && clauses[0] == *other,
            Self::Conflicted => false,
        }
    }
}

/// An error type for short-circuiting conflict detection during normalization
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct DetectConflict;

impl CNF {
    pub fn from_clauses(clauses: Vec<Clause>) -> Self {
        let mut new = Self::Valid(clauses);
        // Conflict is allowed
        let _ = new.normalize();
        new
    }

    pub fn from_rgbd(cnf: rgbd::CNF) -> Self {
        Self::from_clauses(cnf.clauses.into_iter().map(Clause::from).collect())
    }

    /// Parse CNF from DIMACS format
    ///
    /// ```rust
    /// use cdcl::CNF;
    ///
    /// let expr = CNF::from_dimacs_format(r#"
    /// p cnf 5 3
    /// 1 -5 4 0
    /// -1 5 3 4 0
    /// -3 -4 0
    /// "#).unwrap();
    ///
    /// // Note the expression are sorted automatically
    /// assert_eq!(
    ///     expr.to_string(),
    ///     "(¬x3 ∨ ¬x4) ∧ (x1 ∨ x4 ∨ ¬x5) ∧ (¬x1 ∨ x3 ∨ x4 ∨ x5)"
    /// );
    /// ```
    pub fn from_dimacs_format(input: &str) -> Result<Self> {
        let cnf = rgbd::CNF::from_dimacs_format_str(input)?;
        Ok(Self::from_rgbd(cnf))
    }

    pub fn lit(id: i32) -> Self {
        let lit = Literal::new(id);
        let clause = Clause::from(lit);
        Self::Valid(vec![clause])
    }

    pub fn tautology() -> Self {
        Self::Valid(Vec::new())
    }

    pub fn is_tautology(&self) -> bool {
        match self {
            Self::Valid(clauses) => clauses.iter().all(Clause::is_tautology),
            Self::Conflicted => false,
        }
    }

    pub fn is_conflicted(&self) -> bool {
        matches!(self, Self::Conflicted)
    }

    pub fn supp(&self) -> BTreeSet<NonZeroU32> {
        match self {
            Self::Valid(clauses) => clauses.iter().flat_map(Clause::supp).collect(),
            Self::Conflicted => BTreeSet::new(),
        }
    }

    pub fn literals(&self) -> impl Iterator<Item = &Literal> {
        static EMPTY: Vec<Clause> = Vec::new();
        let clauses = match self {
            Self::Valid(clauses) => clauses,
            Self::Conflicted => &EMPTY,
        };
        clauses.iter().filter_map(Clause::literals).flatten()
    }

    pub fn is_solved(&self) -> Option<Solution> {
        match self {
            Self::Valid(..) => {
                if self.is_tautology() {
                    Some(Solution::Sat(State::default()))
                } else {
                    None
                }
            }
            Self::Conflicted => Some(Solution::UnSat),
        }
    }

    pub fn substitute(&mut self, lit: Literal) -> Result<(), DetectConflict> {
        let Self::Valid(clauses) = self else {
            return Err(DetectConflict);
        };
        for clause in clauses.iter_mut() {
            clause.substitute(lit);
            if clause == &Clause::Conflicted {
                *self = Self::Conflicted;
                return Err(DetectConflict);
            }
        }
        Ok(())
    }

    pub fn evaluate(&mut self, state: &State) -> bool {
        for lit in state.iter() {
            if self.substitute(*lit).is_err() {
                return false;
            }
        }
        self.is_solved().is_some()
    }

    /// Clauses in AND expression
    ///
    /// ```rust
    /// use cdcl::{CNF, lit};
    ///
    /// // (x1 ∧ x2) ∨ x3 = (x1 ∨ x3) ∧ (x2 ∨ x3)
    /// let expr = (lit!(1) & lit!(2)) | lit!(3);
    /// let clauses = expr.clauses().unwrap();
    /// assert_eq!(clauses.len(), 2);
    /// assert_eq!(clauses[0], lit!(1) | lit!(3)); // x1 ∨ x3
    /// assert_eq!(clauses[1], lit!(2) | lit!(3)); // x2 ∨ x3
    ///
    /// // Non-AND expression is a single clause
    /// let expr: CNF = lit!(1).into();
    /// let clauses = expr.clauses().unwrap();
    /// assert_eq!(clauses.len(), 1);
    /// assert_eq!(clauses[0], lit!(1));
    ///
    /// let expr: CNF = (lit!(1) | lit!(2)).into();
    /// let clauses = expr.clauses().unwrap();
    /// assert_eq!(clauses.len(), 1);
    /// assert_eq!(clauses[0], lit!(1) | lit!(2));
    /// ```
    ///
    pub fn clauses(&self) -> Option<&[Clause]> {
        match self {
            Self::Valid(clauses) => Some(clauses),
            Self::Conflicted => None,
        }
    }

    /// Add a clause to the expression
    ///
    /// ```rust
    /// use cdcl::{CNF, Clause, lit};
    ///
    /// // x1 ∧ x2
    /// let mut expr = lit!(1) & lit!(2);
    /// expr.add_clause(lit!(3).into()).unwrap();
    /// assert_eq!(expr, lit!(1) & lit!(2) & lit!(3));
    ///
    /// // Redundant clauses are not added, e.g. (x1 ∧ x2) ∧ (x1 ∨ x2) = x1 ∧ x2
    /// let mut expr = lit!(1) & lit!(2);
    /// expr.add_clause(lit!(1) | lit!(2)).unwrap();
    /// assert_eq!(expr, lit!(1) & lit!(2));
    ///
    /// // Conflicting clauses are converted to CNF::Conflicted
    /// let mut expr = lit!(1) & lit!(2);
    /// assert!(expr.add_clause(Clause::Conflicted).is_err());
    ///
    /// // x1 ∧ ¬x1 = ⊥
    /// let mut expr: CNF = lit!(1).into();
    /// assert!(expr.add_clause(lit!(-1).into()).is_err());
    /// ```
    pub fn add_clause(&mut self, clause: Clause) -> Result<(), DetectConflict> {
        if clause.is_conflicted() {
            *self = Self::Conflicted;
            return Err(DetectConflict);
        }
        let Self::Valid(clauses) = self else {
            return Err(DetectConflict);
        };
        for c in clauses.iter() {
            if c.implies(&clause) {
                // No need to add
                return Ok(());
            }
        }
        clauses.push(clause);
        self.cleanup()
    }

    /// List up all unit clauses, single variable or its negation, as a [State] with remaining clauses as a new [CNF]
    ///
    /// ```rust
    /// use cdcl::{CNF, state};
    ///
    /// // x1 ∧ x2
    /// let expr = CNF::lit(1) & CNF::lit(2);
    /// let state = expr.take_unit_clauses();
    /// assert_eq!(state, state![1, 2]);
    /// // x1 ∧ x2 ∧ (x3 ∨ x4)
    /// let expr = CNF::lit(1) & CNF::lit(2) & (CNF::lit(3) | CNF::lit(4));
    /// let state = expr.take_unit_clauses();
    /// assert_eq!(state, state![1, 2]);
    /// ```
    pub fn take_unit_clauses(&self) -> State {
        match self {
            Self::Valid(clauses) => {
                let mut state = State::default();
                for clause in clauses {
                    if let Some(lit) = clause.as_unit() {
                        state.insert(lit);
                    }
                }
                state
            }
            Self::Conflicted => State::default(),
        }
    }

    /// Propagate unit clauses
    ///
    /// ```rust
    /// use cdcl::{CNF, lit};
    ///
    /// // x1 ∧ x2 ∧ (¬x1 ∨ x3) = x1 ∧ x2 ∧ x3
    /// let mut expr = lit!(1) & lit!(2) & (lit!(-1) | lit!(3));
    /// expr.unit_propagation().unwrap();
    /// assert_eq!(expr, lit!(1) & lit!(2) & lit!(3));
    /// ```
    pub fn unit_propagation(&mut self) -> Result<(), DetectConflict> {
        loop {
            let hash = self.current_hash();
            let Self::Valid(clauses) = self else {
                return Err(DetectConflict);
            };
            let mut units = BTreeSet::new();
            for clause in clauses {
                if let Some(lit) = clause.as_unit() {
                    units.insert(lit);
                    continue;
                }
                for lit in units.iter() {
                    clause.substitute(*lit);
                    if clause.is_conflicted() {
                        *self = Self::Conflicted;
                        return Err(DetectConflict);
                    }
                }
            }
            self.cleanup()?;
            self.remove_implied_clauses()?;

            if hash == self.current_hash() {
                break;
            }
        }
        Ok(())
    }

    fn current_hash(&self) -> u64 {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        self.hash(&mut hasher);
        hasher.finish()
    }

    /// Fast cleanup. For full cleanup, use `normalize` instead
    ///
    /// - Remove tautologies
    /// - Convert conflicting clauses to `CNF::Conflicted`
    /// - Sort and dedup clauses
    /// - Detect unit conflict
    ///
    fn cleanup(&mut self) -> Result<(), DetectConflict> {
        let Self::Valid(clauses) = self else {
            return Err(DetectConflict);
        };
        let mut i = 0;
        while i < clauses.len() {
            if clauses[i].is_conflicted() {
                *self = Self::Conflicted;
                return Err(DetectConflict);
            }
            if clauses[i].is_tautology() {
                clauses.swap_remove(i);
                continue;
            }
            i += 1;
        }

        clauses.sort_unstable();
        clauses.dedup();

        // Detect unit conflict
        for i in 1..clauses.len() {
            if clauses[i].num_literals() > 1 {
                break;
            }
            if let (Some(a), Some(b)) = (clauses[i - 1].as_unit(), clauses[i].as_unit()) {
                if a == !b {
                    *self = Self::Conflicted;
                    return Err(DetectConflict);
                }
            }
        }

        Ok(())
    }

    /// Remove redundant clauses, e.g. (x1 ∨ x2) ∧ (x1 ∨ x2 ∨ x3) = (x1 ∨ x2)
    fn remove_implied_clauses(&mut self) -> Result<(), DetectConflict> {
        let Self::Valid(clauses) = self else {
            return Err(DetectConflict);
        };
        // Assumes clauses are sorted in graded lexical order, and antecedent is before consequent
        let mut i = 0;
        'outer: while i < clauses.len() {
            for j in 0..i {
                if clauses[j].implies(&clauses[i]) {
                    clauses.swap_remove(i);
                    continue 'outer;
                }
            }
            i += 1;
        }
        Ok(())
    }

    pub fn normalize(&mut self) -> Result<(), DetectConflict> {
        self.cleanup()?;
        self.remove_implied_clauses()?;
        self.unit_propagation()?;
        Ok(())
    }

    pub fn normalized_eq(&self, other: impl Into<Self>) -> bool {
        let mut a = self.clone();
        let mut b = other.into();
        match (a.normalize(), b.normalize()) {
            (Ok(()), Ok(())) => a == b,
            (Err(_), Err(_)) => true,
            _ => false,
        }
    }
}

impl fmt::Debug for CNF {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.is_tautology() {
            return write!(f, "⊤");
        }
        match self {
            Self::Valid(clauses) => {
                for (i, clause) in clauses.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ∧ ")?;
                    }
                    write!(f, "({:?})", clause)?;
                }
                Ok(())
            }
            Self::Conflicted => write!(f, "⊥"),
        }
    }
}

impl fmt::Display for CNF {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(self, f)
    }
}

impl BitAnd for CNF {
    type Output = Self;
    fn bitand(self, rhs: Self) -> Self {
        match (self, rhs) {
            (mut new @ CNF::Valid(..), CNF::Valid(rhs)) => {
                for c in rhs {
                    if new.add_clause(c).is_err() {
                        return CNF::Conflicted;
                    };
                }
                new
            }
            _ => CNF::Conflicted,
        }
    }
}

impl BitOr for CNF {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self {
        if self.is_tautology() || rhs.is_tautology() {
            return CNF::tautology();
        }
        match (self, rhs) {
            (CNF::Conflicted, other) | (other, CNF::Conflicted) => other,
            (CNF::Valid(lhs), CNF::Valid(rhs)) => {
                let mut new = CNF::tautology();
                for c in &lhs {
                    for d in &rhs {
                        if new.add_clause(c.clone() | d.clone()).is_err() {
                            return CNF::Conflicted;
                        }
                    }
                }
                new
            }
        }
    }
}

impl Not for CNF {
    type Output = Self;
    fn not(self) -> Self::Output {
        match self {
            CNF::Valid(clauses) => {
                let mut out = CNF::Conflicted;
                for clause in clauses {
                    out = out | !clause;
                }
                out
            }
            CNF::Conflicted => CNF::tautology(),
        }
    }
}

impl BitOr<Literal> for CNF {
    type Output = Self;
    fn bitor(self, rhs: Literal) -> Self {
        self | CNF::from(rhs)
    }
}

impl BitOr<Clause> for CNF {
    type Output = Self;
    fn bitor(self, rhs: Clause) -> Self {
        self | CNF::from(rhs)
    }
}
impl_bitor_inverse!(Literal, CNF);
impl_bitor_inverse!(Clause, CNF);

impl BitAnd<Literal> for CNF {
    type Output = Self;
    fn bitand(mut self, rhs: Literal) -> Self {
        if self.add_clause(rhs.into()).is_err() {
            Self::Conflicted
        } else {
            self
        }
    }
}

impl BitAnd<Clause> for CNF {
    type Output = Self;
    fn bitand(mut self, rhs: Clause) -> Self {
        let _ = self.add_clause(rhs);
        self
    }
}

impl_bitand_inverse!(Literal, CNF);
impl_bitand_inverse!(Clause, CNF);

impl Arbitrary for CNF {
    type Parameters = ();
    type Strategy = BoxedStrategy<Self>;

    fn arbitrary_with(_: Self::Parameters) -> Self::Strategy {
        prop_oneof![
            Just(CNF::Conflicted),
            Just(CNF::tautology()),
            proptest::collection::vec(Clause::arbitrary(), 0..5).prop_map(CNF::from_clauses),
        ]
        .boxed()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{block_on, dpll};

    proptest! {
        #[test]
        fn test_commutative(a: CNF, b: CNF) {
            assert_eq!(a.clone() | b.clone(), b.clone() | a.clone());
            assert_eq!(a.clone() & b.clone(), b.clone() & a.clone());
        }

        #[test]
        fn test_commutative_literal(a: CNF, b: Literal) {
            assert_eq!(a.clone() | b, b | a.clone());
            assert_eq!(a.clone() & b, b & a.clone());
        }

        #[test]
        fn test_tautology(a: CNF) {
            assert_eq!(a.clone() | !a, CNF::tautology());
        }

        #[test]
        fn test_conflict(a: CNF) {
            // Although CNF try to normalize given expression,
            // it is not guaranteed to reduce to CNF::Conflicted for all UNSAT expressions
            // since it is also a NP-hard problem
            // Instead, we can check it is UNSAT by DPLL.
            assert_eq!(
                block_on(dpll(dbg!(a.clone() & dbg!(!a)))),
                Solution::UnSat
            );
        }

        #[test]
        fn test_dedup(a: CNF) {
            assert_eq!(a.clone() | a.clone(), a);
        }

        #[test]
        fn test_associativity(a: CNF, b: CNF, c: CNF) {
            assert_eq!((a.clone() & b.clone()) & c.clone(), a.clone() & (b.clone() & c.clone()));
            assert_eq!((a.clone() | b.clone()) | c.clone(), a.clone() | (b.clone() | c.clone()));
        }

        #[test]
        fn test_distributivity(a: CNF, b: CNF, c: CNF) {
            prop_assert!((a.clone() & (b.clone() | c.clone())).normalized_eq((a.clone() & b.clone()) | (a.clone() & c.clone())));
            prop_assert!((a.clone() | (b.clone() & c.clone())).normalized_eq((a.clone() | b.clone()) & (a.clone() | c.clone())));
        }

        #[test]
        fn test_absorption_or(a: CNF, b: CNF) {
            prop_assert!((a.clone() | (a.clone() & b.clone())).normalized_eq(a));
        }

        #[test]
        fn test_absorption_and(a: CNF, b: CNF) {
            assert_eq!(a.clone() & (a.clone() | b.clone()), a.clone());
        }
    }
}
