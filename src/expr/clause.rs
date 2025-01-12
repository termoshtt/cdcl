use super::{Literal, CNF};
use anyhow::{bail, Result};
use maplit::btreeset;
use proptest::prelude::*;
use std::{
    collections::BTreeSet,
    fmt,
    num::NonZeroU32,
    ops::{BitAnd, BitOr, Not},
};

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
    /// Parse a clause from a DIMACS format string
    ///
    /// ```rust
    /// use cdcl::Clause;
    /// let clause = Clause::from_dimacs("1 2 0");
    /// assert_eq!(clause.to_string(), "x1 ∨ x2");
    ///
    /// // Empty clause means a conflict
    /// let clause = Clause::from_dimacs("0");
    /// assert_eq!(clause.to_string(), "⊥");
    /// ```
    pub fn from_dimacs(s: &str) -> Self {
        let literals: BTreeSet<Literal> = s
            .split_whitespace()
            .filter_map(|s| s.parse::<i32>().ok())
            .take_while(|&i| i != 0)
            .map(Literal::new)
            .collect();
        if literals.is_empty() {
            Self::Conflicted
        } else {
            Self::new(literals)
        }
    }

    /// Convert the clause to a DIMACS format string
    ///
    /// ```rust
    /// use cdcl::Clause;
    /// let clause = Clause::from_dimacs("1 2 0");
    /// assert_eq!(clause.as_dimacs().unwrap(), "1 2 0");
    ///
    /// // Empty clause means a conflict
    /// let clause = Clause::conflicted();
    /// assert_eq!(clause.as_dimacs().unwrap(), "0");
    ///
    /// // Tautology cannot be converted
    /// let clause = Clause::tautology();
    /// assert!(clause.as_dimacs().is_err());
    /// ```
    pub fn as_dimacs(&self) -> Result<String> {
        match self {
            Self::Valid { literals } => {
                if literals.is_empty() {
                    bail!("Tautology cannot be converted to DIMACS format");
                }
                let mut s = String::new();
                for lit in literals {
                    s.push_str(&lit.as_i32().to_string());
                    s.push(' ');
                }
                s.push('0');
                Ok(s)
            }
            // Empty clause `0` corresponds to a conflict
            Self::Conflicted => Ok("0".to_string()),
        }
    }

    pub fn literals(&self) -> Option<impl DoubleEndedIterator<Item = &Literal>> {
        match self {
            Self::Valid { literals } => Some(literals.iter()),
            Self::Conflicted => None,
        }
    }

    /// Number of literals in the clause
    pub fn num_literals(&self) -> usize {
        match self {
            Self::Valid { literals } => literals.len(),
            Self::Conflicted => 0,
        }
    }

    pub fn contains(&self, lit: Literal) -> bool {
        match self {
            Self::Valid { literals } => literals.contains(&lit),
            Self::Conflicted => false,
        }
    }

    /// Check if the clause intersects with another set of literals
    ///
    /// ```rust
    /// use cdcl::{clause, lit};
    /// use std::collections::BTreeSet;
    ///
    /// let a = clause![1, 2];
    /// let b = BTreeSet::from_iter(vec![lit!(1), lit!(3)]);
    /// assert!(a.intersect(&b));
    ///
    /// let a = clause![1, 2];
    /// let b = BTreeSet::from_iter(vec![lit!(3), lit!(4)]);
    /// assert!(!a.intersect(&b));
    /// ```
    pub fn intersect(&self, other: &BTreeSet<Literal>) -> bool {
        match self {
            Self::Valid { literals } => literals.intersection(other).next().is_some(),
            Self::Conflicted => false,
        }
    }

    /// Check if `self` then `other`
    ///
    /// ```rust
    /// use cdcl::{clause, lit};
    ///
    /// let a = clause![1, 2];
    /// let b = clause![1, 2, 3];
    /// assert!(a.implies(&b));
    ///
    /// let c = clause![1, -2];
    /// assert!(!a.implies(&c));
    ///
    /// let d = clause![2];
    /// assert!(d.implies(&a));
    /// assert!(d.implies(&b));
    /// assert!(!d.implies(&c));
    /// ```
    pub fn implies(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Valid { literals: a }, Self::Valid { literals: b }) => a.is_subset(b),
            (Self::Conflicted, _) => true,
            (_, Self::Conflicted) => false,
        }
    }

    pub fn remove(&mut self, lit: Literal) -> bool {
        if let Self::Valid { literals } = self {
            literals.remove(&lit)
        } else {
            false
        }
    }

    pub fn is_tautology(&self) -> bool {
        match self {
            Self::Valid { literals } => literals.is_empty(),
            Self::Conflicted => false,
        }
    }

    pub fn is_conflicted(&self) -> bool {
        matches!(self, Self::Conflicted)
    }

    fn check_tautology(&mut self) {
        if let Self::Valid { literals } = self {
            if literals.is_empty() {
                // This is already regarded as a tautology
                return;
            }
            let mut iter = literals.iter().peekable();
            let mut prev = iter.next().expect("Already checked");
            for lit in iter {
                // The negation of some literal must be next to it since sorted.
                if prev.id == lit.id && prev.positive != lit.positive {
                    literals.clear();
                    return;
                }
                prev = lit;
            }
        }
    }

    pub fn new(literals: BTreeSet<Literal>) -> Self {
        let mut new = Self::Valid { literals };
        new.check_tautology();
        new
    }

    pub fn from_literals(literals: &[Literal]) -> Self {
        Self::new(literals.iter().cloned().collect())
    }

    pub fn supp(&self) -> BTreeSet<NonZeroU32> {
        match self {
            Self::Valid { literals } => literals.iter().map(|lit| lit.id).collect(),
            Self::Conflicted => BTreeSet::new(),
        }
    }

    pub fn tautology() -> Self {
        Self::Valid {
            literals: BTreeSet::new(),
        }
    }

    pub fn conflicted() -> Self {
        Self::Conflicted
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

    /// Partially evaluate the clause with given literal
    ///
    /// ```rust
    /// use cdcl::{clause, lit};
    ///
    /// // x1 ∨ x2 is always true when x1 is true
    /// let mut a = clause![1, 2];
    /// a.substitute(lit!(1));
    /// assert!(a.is_tautology());
    ///
    /// // x1 ∨ x2 becomes x2 when x1 is false
    /// let mut a = clause![1, 2];
    /// a.substitute(lit!(-1));
    /// assert_eq!(a, lit!(2));
    ///
    /// // x1 becomes ⊥ when ¬x1 is true
    /// let mut a = clause![1];
    /// a.substitute(lit!(-1));
    /// assert!(a.is_conflicted());
    /// ```
    pub fn substitute(&mut self, lit: Literal) {
        if let Self::Valid { literals } = self {
            // If the clause contains the literal, it means the clause is always true
            if literals.take(&lit).is_some() {
                literals.clear();
            }

            // If the clause contains the negation of the literal, it is removed
            if literals.take(&!lit).is_some() && literals.is_empty() {
                *self = Self::Conflicted;
            }
        }
        // Do nothing if the clause is already conflicted
    }

    /// Get the resolvent of two clauses
    ///
    /// ```rust
    /// use cdcl::{clause, lit};
    ///
    /// let a = clause![1, 2];
    /// let b = clause![-1, 3];
    /// assert_eq!(a.resolution(b).unwrap().to_string(), "x2 ∨ x3");
    ///
    /// let a = clause![1, 2];
    /// let b = clause![-1, 3];
    /// assert_eq!(b.resolution(a).unwrap().to_string(), "x2 ∨ x3");
    ///
    /// // No pair
    /// let a = clause![1, 2];
    /// let b = clause![3, 4];
    /// assert!(a.resolution(b).is_err());
    ///
    /// // x1 and x1 cannot be a pair
    /// let a = clause![1, 2];
    /// let b = clause![1, 3];
    /// assert!(a.resolution(b).is_err());
    ///
    /// // Multiple pairs
    /// let a = clause![1, 2];
    /// let b = clause![-1, -2];
    /// assert_eq!(a.resolution(b).unwrap().to_string(), "⊤");
    /// ```
    ///
    /// <https://en.wikipedia.org/wiki/Resolution_(logic)>
    pub fn resolution(mut self, mut other: Self) -> Result<Self> {
        let candidates: Vec<NonZeroU32> =
            self.supp().intersection(&other.supp()).cloned().collect();
        for id in candidates {
            let p = Literal { id, positive: true };
            let n = Literal {
                id,
                positive: false,
            };
            for (a, b) in [(p, n), (n, p)] {
                if self.contains(a) && other.contains(b) {
                    self.remove(a);
                    other.remove(b);
                    return Ok(self | other);
                }
            }
        }
        bail!("No common literals for resolution");
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
        Self::new(literals.into_iter().map(Literal::new).collect())
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
        if self.is_tautology() || rhs.is_tautology() {
            return Clause::tautology();
        }
        match (self, rhs) {
            (Clause::Valid { mut literals }, Clause::Valid { literals: mut rhs }) => {
                literals.append(&mut rhs);
                Clause::new(literals)
            }
            // ⊥ ∨ x = x ∨ ⊥ = x
            (Clause::Conflicted, out) | (out, Clause::Conflicted) => out,
        }
    }
}

impl BitOr<Literal> for Clause {
    type Output = Self;
    fn bitor(self, rhs: Literal) -> Self {
        if self.is_tautology() {
            return Clause::tautology();
        }
        match self {
            Clause::Valid { mut literals } => {
                literals.insert(rhs);
                Clause::new(literals)
            }
            Clause::Conflicted => Clause::Conflicted,
        }
    }
}
impl_bitor_inverse!(Literal, Clause);

impl BitAnd for Clause {
    type Output = CNF;
    fn bitand(self, rhs: Self) -> Self::Output {
        CNF::from_clauses(vec![self, rhs])
    }
}

impl BitAnd<Literal> for Clause {
    type Output = CNF;
    fn bitand(self, rhs: Literal) -> Self::Output {
        CNF::from(self) & CNF::from(rhs)
    }
}
impl_bitand_inverse!(Literal, Clause);

impl Not for Clause {
    type Output = CNF;
    fn not(self) -> Self::Output {
        if self.is_tautology() {
            return CNF::Conflicted;
        }
        match self {
            Clause::Valid { literals } => {
                CNF::from_clauses(literals.iter().map(|lit| Clause::from(!*lit)).collect())
            }
            Clause::Conflicted => CNF::tautology(),
        }
    }
}

impl Arbitrary for Clause {
    type Parameters = ();
    type Strategy = BoxedStrategy<Self>;

    fn arbitrary_with(_: Self::Parameters) -> Self::Strategy {
        prop_oneof![
            Just(Clause::Conflicted),
            Just(Clause::tautology()),
            proptest::collection::vec(any::<Literal>(), 0..5)
                .prop_map(|literals| Clause::from_literals(&literals))
        ]
        .boxed()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    proptest! {
        #[test]
        fn test_commutative_or(a: Clause, b: Clause) {
            assert_eq!(a.clone() | b.clone(), b.clone() | a.clone());
        }

        #[test]
        fn test_commutative_and(a: Clause, b: Clause) {
            assert_eq!(a.clone() & b.clone(), b.clone() & a.clone());
        }

        #[test]
        fn test_commutative_literal(a: Clause, b: Literal) {
            assert_eq!(a.clone() | b, b | a.clone());
            assert_eq!(a.clone() & b, b & a.clone());
        }

        #[test]
        fn test_tautology(a: Clause) {
            assert_eq!(a.clone() | !a, Clause::tautology());
        }

        #[test]
        fn test_conflict(a: Clause) {
            prop_assert!((a.clone() & !a).normalize().is_err());
        }

        #[test]
        fn test_dedup(a: Clause) {
            assert_eq!(a.clone() | a.clone(), a);
        }

        #[test]
        fn test_associativity_and(a: Clause, b: Clause, c: Clause) {
            prop_assert!(((a.clone() & b.clone()) & c.clone()).normalized_eq(a.clone() & (b.clone() & c.clone())));
        }

        #[test]
        fn test_associativity_or(a: Clause, b: Clause, c: Clause) {
            assert_eq!((a.clone() | b.clone()) | c.clone(), a.clone() | (b.clone() | c.clone()));
        }

        #[test]
        fn test_distributivity(a: Clause, b: Clause, c: Clause) {
            prop_assert!((a.clone() & (b.clone() | c.clone())).normalized_eq((a.clone() & b.clone()) | (a.clone() & c.clone())));
            prop_assert!((a.clone() | (b.clone() & c.clone())).normalized_eq((a.clone() | b.clone()) & (a.clone() | c.clone())));
        }

        #[test]
        fn test_absorption(a: Clause, b: Clause) {
            prop_assert!((a.clone() | (a.clone() & b.clone())).normalized_eq(a.clone()));
            prop_assert!((a.clone() & (a.clone() | b.clone())).normalized_eq(a.clone()));
        }
    }
}
