use super::{Clause, CNF};
use maplit::btreeset;
use proptest::prelude::*;
use std::{
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
/// assert_eq!((a | b).to_string(), "⊤");
/// assert_eq!((a | b | c).to_string(), "⊤");
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

    pub fn as_i32(&self) -> i32 {
        if self.positive {
            self.id.get() as i32
        } else {
            -(self.id.get() as i32)
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

impl BitOr for Literal {
    type Output = Clause;
    fn bitor(self, rhs: Self) -> Self::Output {
        if self == rhs {
            return self.into();
        }
        if self.id == rhs.id {
            debug_assert_eq!(self.positive, !rhs.positive);
            return Clause::tautology();
        }
        Clause::Valid {
            literals: btreeset! {self, rhs},
        }
    }
}

impl BitAnd for Literal {
    type Output = CNF;
    fn bitand(self, rhs: Self) -> Self::Output {
        if self == rhs {
            return self.into();
        }
        if self.id == rhs.id {
            debug_assert_eq!(self.positive, !rhs.positive);
            return Clause::Conflicted.into();
        }
        CNF::from(self) & CNF::from(rhs)
    }
}

impl Arbitrary for Literal {
    type Parameters = ();
    type Strategy = BoxedStrategy<Self>;

    fn arbitrary_with(_: Self::Parameters) -> Self::Strategy {
        (
            any::<u32>().prop_filter("0 is not allowed for ID", |&id| id != 0),
            any::<bool>(),
        )
            .prop_map(|(id, positive)| Self {
                id: NonZeroU32::new(id).unwrap(),
                positive,
            })
            .boxed()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    proptest! {
        #[test]
        fn test_zero_id_is_not_allowed(lit: Literal) {
            assert_ne!(lit.id.get(), 0);
        }

        #[test]
        fn test_double_negation(lit: Literal) {
            assert_eq!(!(!lit), lit);
        }

        #[test]
        fn test_order_of_negation(lit: Literal) {
            let negated = !lit;
            if lit.positive {
                assert!(negated > lit);
            } else {
                assert!(lit > negated);
            }
        }

        #[test]
        fn test_tautology(lit: Literal) {
            assert_eq!(lit | !lit, Clause::tautology())
        }

        #[test]
        fn test_conflict(lit: Literal) {
            assert_eq!(lit & !lit, Clause::Conflicted)
        }

        #[test]
        fn test_dedup(lit: Literal) {
            assert_eq!(lit | lit, lit);
        }

        #[test]
        fn test_commutative(a: Literal, b: Literal) {
            assert_eq!(a | b, b | a);
            assert_eq!(a & b, b & a);
        }

        #[test]
        fn test_associativity(a: Literal, b: Literal, c: Literal) {
            assert_eq!((a & b) & c, a & (b & c));
            assert_eq!((a | b) | c, a | (b | c));
        }

        #[test]
        fn test_distributivity(a: Literal, b: Literal, c: Literal) {
            assert_eq!(a & (b | c), (a & b) | (a & c));
            assert_eq!(a | (b & c), (a | b) & (a | c));
        }

        #[test]
        fn test_absorption(a: Literal, b: Literal) {
            let mut x = a | (a & b);
            let mut y = a & (a | b);
            x.normalize().unwrap();
            y.normalize().unwrap();
            assert_eq!(x, a);
            assert_eq!(y, a);
        }
    }
}
