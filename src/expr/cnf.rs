use super::{Clause, Literal};
use crate::{Solution, State};
use anyhow::Result;
use std::{
    collections::BTreeSet,
    fmt,
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
        Self::Valid(vec![clause])
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

impl CNF {
    pub fn from_clauses(clauses: Vec<Clause>) -> Self {
        let mut new = Self::Valid(clauses);
        new.normalize();
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

    pub fn supp(&self) -> BTreeSet<NonZeroU32> {
        match self {
            Self::Valid(clauses) => clauses.iter().flat_map(Clause::supp).collect(),
            Self::Conflicted => BTreeSet::new(),
        }
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

    pub fn substitute(&mut self, lit: Literal) {
        if let Self::Valid(clauses) = self {
            for clause in clauses.iter_mut() {
                clause.substitute(lit);
                if clause == &Clause::Conflicted {
                    *self = Self::Conflicted;
                    return;
                }
            }
        }
        self.normalize();
        // Do nothing if the CNF is already conflicted
    }

    pub fn evaluate(&mut self, state: &State) -> bool {
        for lit in state.iter() {
            self.substitute(*lit);
            if self == &Self::Conflicted {
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

    pub fn add_clause(&mut self, clause: Clause) {
        if let Self::Valid(clauses) = self {
            clauses.push(clause);
        }
        self.normalize();
        // Do nothing if the CNF is already conflicted
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

    fn normalize(&mut self) {
        if let Self::Valid(clauses) = self {
            let mut i = 0;
            while i < clauses.len() {
                if clauses[i].is_conflicted() {
                    *self = Self::Conflicted;
                    return;
                }
                if clauses[i].is_tautology() {
                    clauses.swap_remove(i);
                    continue;
                }
                i += 1;
            }
            clauses.sort_unstable();
            clauses.dedup();

            // absorb
            let mut units = BTreeSet::new();
            for clause in clauses.iter() {
                debug_assert!(clause.num_literals() >= 1);
                if let Some(lit) = clause.as_unit() {
                    units.insert(lit);
                } else {
                    break;
                }
            }
            let mut i = 0;
            while i < clauses.len() {
                if clauses[i].num_literals() <= 1 {
                    i += 1;
                    continue;
                }
                if clauses[i].intersect(&units) {
                    clauses.swap_remove(i);
                    continue;
                }
                i += 1;
            }
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
            (CNF::Valid(mut lhs), CNF::Valid(mut rhs)) => {
                lhs.append(&mut rhs);
                CNF::from_clauses(lhs)
            }
            _ => CNF::Conflicted,
        }
    }
}

impl BitOr for CNF {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self {
        match (self, rhs) {
            (CNF::Conflicted, other) | (other, CNF::Conflicted) => other,
            (CNF::Valid(lhs), CNF::Valid(rhs)) => {
                let mut inner = Vec::new();
                for c in &lhs {
                    for d in &rhs {
                        inner.push(c.clone() | d.clone())
                    }
                }
                CNF::from_clauses(inner)
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
        self.add_clause(rhs.into());
        self
    }
}

impl BitAnd<Clause> for CNF {
    type Output = Self;
    fn bitand(mut self, rhs: Clause) -> Self {
        self.add_clause(rhs);
        self
    }
}

impl_bitand_inverse!(Literal, CNF);
impl_bitand_inverse!(Clause, CNF);
