use crate::Solution;

use super::{Expr, State};
use anyhow::Result;
use maplit::btreeset;
use std::{
    collections::BTreeSet,
    fmt,
    num::NonZeroU32,
    ops::{BitAnd, BitOr, Not},
};

/// A literal in [Conjunctive Normal Form](https://en.wikipedia.org/wiki/Conjunctive_normal_form)
///
/// # Order
///
/// - Literals are ordered by their ID
/// - If the IDs are the same, positive literals are less than negative literals
///
/// ```rust
/// use cdcl::Literal;
///
/// let a = Literal::new(1);
/// let b = Literal::new(-1);
/// let c = Literal::new(2);
/// let d = Literal::new(-2);
///
/// assert!(a < b); // x1 < ¬x1
/// assert!(b < c); // ¬x1 < x2
/// assert!(c < d); // x2 < ¬x2
/// ```
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Literal {
    pub id: NonZeroU32,
    pub positive: bool,
}

impl Literal {
    /// Similar to DIMACS format, literals are 1-indexed and negative literals are negated
    pub fn new(lit: i32) -> Self {
        assert!(lit != 0, "0 is not allowed for ID");
        if lit > 0 {
            Self {
                id: NonZeroU32::new(lit as u32).unwrap(),
                positive: true,
            }
        } else {
            Self {
                id: NonZeroU32::new((-lit) as u32).unwrap(),
                positive: false,
            }
        }
    }
}

impl From<i32> for Literal {
    fn from(id: i32) -> Self {
        Self::new(id)
    }
}

impl Not for Literal {
    type Output = Self;

    fn not(self) -> Self::Output {
        Self::Output {
            positive: !self.positive,
            ..self
        }
    }
}

impl PartialOrd for Literal {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Literal {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match self.id.cmp(&other.id) {
            std::cmp::Ordering::Equal => self.positive.cmp(&other.positive).reverse(),
            ordering => ordering,
        }
    }
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.positive {
            write!(f, "x{}", self.id)
        } else {
            write!(f, "¬x{}", self.id)
        }
    }
}

impl fmt::Debug for Literal {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self)
    }
}

/// A clause in [Conjunctive Normal Form](https://en.wikipedia.org/wiki/Conjunctive_normal_form)
///
/// # Order
///
/// - `Clause::Conflicted` is always less than any other clauses
/// - Other clauses are in graded lexical order, i.e. the number of literals is the primary key.
///
/// ```rust
/// use cdcl::Clause;
///
/// let a = Clause::from_literals(&[1.into(), 2.into()]);
/// let b = Clause::from_literals(&[1.into()]);
/// let c = Clause::from_literals(&[2.into()]);
/// let d = Clause::from_literals(&[]);
/// let e = Clause::Conflicted;
///
/// assert!(e < d);
/// assert!(d < b);
/// assert!(b < c); // since 1 < 2
/// assert!(c < a);
/// ```
///
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Clause {
    Valid { literals: BTreeSet<Literal> },
    Conflicted,
}

impl PartialOrd for Clause {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Clause {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match (self, other) {
            (Self::Valid { literals: a }, Self::Valid { literals: b }) => {
                match a.len().cmp(&b.len()) {
                    std::cmp::Ordering::Equal => a.cmp(b),
                    ordering => ordering,
                }
            }
            (Self::Conflicted, Self::Conflicted) => std::cmp::Ordering::Equal,
            (Self::Conflicted, Self::Valid { .. }) => std::cmp::Ordering::Less,
            (Self::Valid { .. }, Self::Conflicted) => std::cmp::Ordering::Greater,
        }
    }
}

impl Clause {
    pub fn from_literals(literals: &[Literal]) -> Self {
        Self::Valid {
            literals: literals.iter().cloned().collect(),
        }
    }

    pub fn as_unit(&self) -> Option<Literal> {
        match self {
            Self::Valid { literals } => {
                if literals.len() == 1 {
                    literals.iter().next().copied()
                } else {
                    None
                }
            }
            Self::Conflicted => None,
        }
    }

    pub fn substitute(&mut self, lit: Literal) {
        if let Self::Valid { literals } = self {
            // Remove the literal itself
            literals.take(&lit);

            // If the clause contains the negation of the literal, it means the clause is conflicted
            if literals.take(&!lit).is_some() {
                *self = Self::Conflicted;
            };
        }
        // Do nothing if the clause is already conflicted
    }
}

impl From<Literal> for Clause {
    fn from(literal: Literal) -> Self {
        Self::Valid {
            literals: btreeset! {literal},
        }
    }
}

impl From<Vec<i32>> for Clause {
    fn from(literals: Vec<i32>) -> Self {
        Self::Valid {
            literals: literals.into_iter().map(Literal::new).collect(),
        }
    }
}

impl fmt::Display for Clause {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Conflicted => write!(f, "⊥"),
            Self::Valid { literals } => {
                for (i, literal) in literals.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ∨ ")?;
                    }
                    write!(f, "{}", literal)?;
                }
                Ok(())
            }
        }
    }
}

impl fmt::Debug for Clause {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self)
    }
}

/// An [Expr] in [Conjunctive Normal Form](https://en.wikipedia.org/wiki/Conjunctive_normal_form)
///
/// ```rust
/// use cdcl::CNF;
///
/// // (x0 ∧ x1) ∨ x2 = (x0 ∨ x2) ∧ (x1 ∨ x2)
/// let expr = (CNF::lit(0) & CNF::lit(1)) | CNF::lit(2);
/// assert_eq!(expr.to_string(), "(x0 ∨ x2) ∧ (x1 ∨ x2)");
///
/// // x0 ∨ (x1 ∧ x2) = (x0 ∨ x1) ∧ (x0 ∨ x2)
/// let expr = CNF::lit(0) | (CNF::lit(1) & CNF::lit(2));
/// assert_eq!(expr.to_string(), "(x0 ∨ x1) ∧ (x0 ∨ x2)");
///
/// // (x0 ∧ x1) ∨ (x2 ∧ x3) = (x0 ∨ x2) ∧ (x0 ∨ x3) ∧ (x1 ∨ x2) ∧ (x1 ∨ x3)
/// let expr = (CNF::lit(0) & CNF::lit(1)) | (CNF::lit(2) & CNF::lit(3));
/// assert_eq!(expr.to_string(), "(x0 ∨ x2) ∧ (x0 ∨ x3) ∧ (x1 ∨ x2) ∧ (x1 ∨ x3)");
///
/// // ¬(x0 ∧ x1) = ¬x0 ∨ ¬x1
/// let expr = !(CNF::lit(0) & CNF::lit(1));
/// assert_eq!(expr.to_string(), "¬x0 ∨ ¬x1");
///
/// // ¬(x0 ∨ x1) ∧ x2 = ¬x0 ∧ ¬x1 ∧ x2
/// let expr = !(CNF::lit(0) | CNF::lit(1)) & CNF::lit(2);
/// assert_eq!(expr.to_string(), "¬x0 ∧ ¬x1 ∧ x2");
/// ```
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum CNF {
    Valid(Vec<Clause>),
    Conflicted,
}

impl From<bool> for CNF {
    fn from(value: bool) -> Self {
        if value {
            CNF::Valid(Vec::new())
        } else {
            CNF::Conflicted
        }
    }
}

impl CNF {
    pub fn from_rgbd(cnf: rgbd::CNF) -> Self {
        Self::Valid(cnf.clauses.into_iter().map(Clause::from).collect())
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

    pub fn is_solved(&self) -> Option<Solution> {
        match self {
            Self::Valid(clauses) => {
                if clauses.is_empty() {
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
            for clause in clauses {
                clause.substitute(lit);
                if clause == &Clause::Conflicted {
                    *self = Self::Conflicted;
                    return;
                }
            }
        }
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
    /// use cdcl::{CNF, Expr};
    ///
    /// // (x0 ∧ x1) ∨ x2 = (x0 ∨ x2) ∧ (x1 ∨ x2)
    /// let expr = (CNF::lit(0) & CNF::lit(1)) | CNF::lit(2);
    /// let clauses = expr.clauses().cloned().collect::<Vec<Expr>>();
    /// assert_eq!(
    ///     clauses,
    ///     vec![
    ///         Expr::variable(0) | Expr::variable(2), // x0 ∨ x2
    ///         Expr::variable(1) | Expr::variable(2)  // x1 ∨ x2
    ///     ]
    /// );
    ///
    /// // Non-AND expression is a single clause
    /// let expr = CNF::lit(0);
    /// let clauses = expr.clauses().cloned().collect::<Vec<Expr>>();
    /// assert_eq!(clauses, vec![Expr::variable(0)]);
    ///
    /// let expr = CNF::lit(0) | CNF::lit(1);
    /// let clauses = expr.clauses().cloned().collect::<Vec<Expr>>();
    /// assert_eq!(clauses, vec![Expr::variable(0) | Expr::variable(1)]);
    /// ```
    ///
    pub fn clauses(&self) -> Option<&[Clause]> {
        match self {
            Self::Valid(clauses) => Some(clauses),
            Self::Conflicted => None,
        }
    }

    /// List up all unit clauses, single variable or its negation, as a [State] with remaining clauses as a new [CNF]
    ///
    /// ```rust
    /// use cdcl::{CNF, State, Expr};
    /// use maplit::btreemap;
    ///
    /// // x0 ∧ x1
    /// let expr = CNF::lit(0) & CNF::lit(1);
    /// let (state, cnf) = expr.take_unit_clauses();
    /// assert_eq!(state, btreemap! { 0 => true, 1 => true });
    /// assert_eq!(cnf, CNF::from(true));
    ///
    /// // x0 ∧ x1 ∧ (x2 ∨ x3)
    /// let expr = CNF::lit(0) & CNF::lit(1) & (CNF::lit(2) | CNF::lit(3));
    /// let (state, cnf) = expr.take_unit_clauses();
    /// assert_eq!(state, btreemap! { 0 => true, 1 => true });
    /// assert_eq!(cnf, CNF::lit(2) | CNF::lit(3));
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
}

impl fmt::Debug for CNF {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Valid(clauses) => {
                for (i, clause) in clauses.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ∧ ")?;
                    }
                    write!(f, "{:?}", clause)?;
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
                lhs.sort_unstable();
                lhs.dedup();
                CNF::Valid(lhs)
            }
            _ => CNF::Conflicted,
        }
    }
}

impl BitOr for CNF {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self {
        todo!()
    }
}

impl Not for CNF {
    type Output = Self;

    fn not(self) -> Self {
        todo!()
    }
}
