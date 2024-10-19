use super::{Clause, CNF};
use maplit::btreeset;
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
