use crate::Solution;

use super::State;
use anyhow::{bail, Result};
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
/// use cdcl::lit;
///
/// let a = lit!(1);
/// let b = lit!(-1);
/// let c = lit!(2);
/// let d = lit!(-2);
///
/// assert!(a < b); // x1 < ¬x1
/// assert!(b < c); // ¬x1 < x2
/// assert!(c < d); // x2 < ¬x2
/// ```
///
/// # Operations
///
/// `|` operator is overloaded to create a [Clause] from two literals
///
/// ```rust
/// use cdcl::lit;
///
/// let a = lit!(1);
/// let b = lit!(-1);
/// let c = lit!(2);
///
/// assert_eq!((a | a).to_string(), "x1"); // deduped
/// assert_eq!((a | b).to_string(), "x1 ∨ ¬x1");
/// assert_eq!((a | b | c).to_string(), "x1 ∨ ¬x1 ∨ x2");
/// ```
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Literal {
    pub id: NonZeroU32,
    pub positive: bool,
}

#[macro_export]
macro_rules! lit {
    ($lit:expr) => {
        $crate::Literal::new($lit)
    };
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

impl BitAnd for Literal {
    type Output = CNF;
    fn bitand(self, rhs: Self) -> Self::Output {
        CNF::from(self) & CNF::from(rhs)
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

impl BitOr for Literal {
    type Output = Clause;
    fn bitor(self, rhs: Self) -> Self::Output {
        Clause::Valid {
            literals: btreeset! {self, rhs},
        }
    }
}

impl BitOr<Clause> for Literal {
    type Output = Clause;
    fn bitor(self, rhs: Clause) -> Self::Output {
        match rhs {
            Clause::Valid { mut literals } => {
                literals.insert(self);
                Clause::Valid { literals }
            }
            // ⊥ ∨ x = x
            Clause::Conflicted => self.into(),
        }
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
/// use cdcl::{clause, Clause};
///
/// let a = clause![1, 2];
/// let b = clause![1];
/// let c = clause![2];
/// let d = clause![];
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

#[macro_export]
macro_rules! clause {
    ($($lit:expr),*) => {
        $crate::Clause::from_literals(&[$($lit.into()),*])
    };
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

    pub fn supp(&self) -> BTreeSet<NonZeroU32> {
        match self {
            Self::Valid { literals } => literals.iter().map(|lit| lit.id).collect(),
            Self::Conflicted => BTreeSet::new(),
        }
    }

    pub fn always_true() -> Self {
        Self::Valid {
            literals: BTreeSet::new(),
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

    pub fn remove_literal(&mut self, id: NonZeroU32) {
        if let Self::Valid { literals } = self {
            literals.retain(|lit| lit.id != id);
        }
        // Do nothing if the clause is already conflicted
    }

    /// Get the resolvant of two clauses
    ///
    /// ```rust
    /// use cdcl::{clause, lit};
    ///
    /// let a = clause![1, 2];
    /// let b = clause![-1, 3];
    /// assert_eq!(a.resolusion(b).unwrap().to_string(), "x2 ∨ x3");
    /// ```
    ///
    /// <https://en.wikipedia.org/wiki/Resolution_(logic)>
    pub fn resolusion(mut self, mut other: Self) -> Result<Self> {
        let common: Vec<NonZeroU32> = self.supp().intersection(&other.supp()).cloned().collect();
        if common.is_empty() {
            bail!("No common literals for resolution");
        }
        if common.len() > 1 {
            bail!("Multiple common literals for resolution");
        }
        let common = common[0];
        self.remove_literal(common);
        other.remove_literal(common);
        Ok(self | other)
    }
}

impl From<Literal> for Clause {
    fn from(literal: Literal) -> Self {
        Self::Valid {
            literals: btreeset! {literal},
        }
    }
}

impl PartialEq<Literal> for Clause {
    fn eq(&self, other: &Literal) -> bool {
        match self {
            Self::Valid { literals } => literals.len() == 1 && literals.contains(other),
            Self::Conflicted => false,
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
                if literals.is_empty() {
                    return write!(f, "⊤");
                }
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

impl BitOr for Clause {
    type Output = Self;
    fn bitor(self, rhs: Self) -> Self {
        match (self, rhs) {
            (Clause::Valid { mut literals }, Clause::Valid { literals: mut rhs }) => {
                literals.append(&mut rhs);
                Clause::Valid { literals }
            }
            // ⊥ ∨ x = x ∨ ⊥ = x
            (Clause::Conflicted, out) | (out, Clause::Conflicted) => out,
        }
    }
}

impl BitOr<Literal> for Clause {
    type Output = Self;
    fn bitor(self, rhs: Literal) -> Self {
        match self {
            Clause::Valid { mut literals } => {
                literals.insert(rhs);
                Clause::Valid { literals }
            }
            Clause::Conflicted => Clause::Conflicted,
        }
    }
}

impl Not for Clause {
    type Output = CNF;
    fn not(self) -> Self::Output {
        match self {
            Clause::Valid { literals } => {
                let mut inner = Vec::new();
                for lit in literals {
                    inner.push(Clause::from(!lit));
                }
                CNF::Valid(inner)
            }
            Clause::Conflicted => CNF::always_true(),
        }
    }
}

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
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum CNF {
    Valid(Vec<Clause>),
    Conflicted,
}

impl FromIterator<Clause> for CNF {
    fn from_iter<T: IntoIterator<Item = Clause>>(iter: T) -> Self {
        let mut inner: Vec<_> = iter.into_iter().collect();
        inner.sort_unstable();
        inner.dedup();
        Self::Valid(inner)
    }
}

impl From<bool> for CNF {
    fn from(value: bool) -> Self {
        if value {
            CNF::always_true()
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
    pub fn from_rgbd(cnf: rgbd::CNF) -> Self {
        let mut inner: Vec<_> = cnf.clauses.into_iter().map(Clause::from).collect();
        inner.sort_unstable();
        inner.dedup();
        Self::Valid(inner)
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

    pub fn always_true() -> Self {
        Self::Valid(Vec::new())
    }

    pub fn is_true(&self) -> bool {
        match self {
            Self::Valid(clauses) => {
                clauses.is_empty() || (clauses.len() == 1 && clauses[0] == Clause::always_true())
            }
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
                if self.is_true() {
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
            clauses.sort_unstable();
            clauses.dedup();
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
}

impl fmt::Debug for CNF {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.is_true() {
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
        match (self, rhs) {
            (CNF::Conflicted, other) | (other, CNF::Conflicted) => other,
            (CNF::Valid(lhs), CNF::Valid(rhs)) => {
                let mut inner = Vec::new();
                for c in &lhs {
                    for d in &rhs {
                        inner.push(c.clone() | d.clone())
                    }
                }
                inner.sort_unstable();
                inner.dedup();
                CNF::Valid(inner)
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
            CNF::Conflicted => CNF::always_true(),
        }
    }
}

impl BitOr<Literal> for CNF {
    type Output = Self;
    fn bitor(self, rhs: Literal) -> Self {
        self | CNF::from(rhs)
    }
}

impl BitOr<CNF> for Literal {
    type Output = CNF;
    fn bitor(self, rhs: CNF) -> CNF {
        CNF::from(self) | rhs
    }
}

impl BitAnd<Literal> for CNF {
    type Output = Self;
    fn bitand(self, rhs: Literal) -> Self {
        self & CNF::from(rhs)
    }
}

impl BitAnd<CNF> for Literal {
    type Output = CNF;
    fn bitand(self, rhs: CNF) -> CNF {
        CNF::from(self) & rhs
    }
}
