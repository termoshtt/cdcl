use super::{Expr, State};
use anyhow::Result;
use maplit::btreeset;
use std::{
    collections::BTreeSet,
    fmt,
    num::NonZeroU32,
    ops::{BitAnd, BitOr, Not},
};

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Literal {
    pub id: NonZeroU32,
    pub positive: bool,
}

impl Literal {
    pub fn new(id: u32, positive: bool) -> Self {
        Self {
            id: NonZeroU32::new(id).expect("0 is not allowed for ID"),
            positive,
        }
    }
}

impl From<u32> for Literal {
    fn from(id: u32) -> Self {
        Self::new(id, true)
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
        match self.id.partial_cmp(&other.id)? {
            std::cmp::Ordering::Equal => self.positive.partial_cmp(&other.positive),
            ordering => Some(ordering),
        }
    }
}

impl Ord for Literal {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.partial_cmp(other).unwrap()
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
        match (self, other) {
            (Self::Valid { literals: a }, Self::Valid { literals: b }) => {
                match a.len().partial_cmp(&b.len()) {
                    Some(std::cmp::Ordering::Equal) => a.partial_cmp(b),
                    ordering => ordering,
                }
            }
            (Self::Conflicted, Self::Conflicted) => Some(std::cmp::Ordering::Equal),
            (Self::Conflicted, Self::Valid { .. }) => Some(std::cmp::Ordering::Less),
            (Self::Valid { .. }, Self::Conflicted) => Some(std::cmp::Ordering::Greater),
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
/// let expr = (CNF::variable(0) & CNF::variable(1)) | CNF::variable(2);
/// assert_eq!(expr.to_string(), "(x0 ∨ x2) ∧ (x1 ∨ x2)");
///
/// // x0 ∨ (x1 ∧ x2) = (x0 ∨ x1) ∧ (x0 ∨ x2)
/// let expr = CNF::variable(0) | (CNF::variable(1) & CNF::variable(2));
/// assert_eq!(expr.to_string(), "(x0 ∨ x1) ∧ (x0 ∨ x2)");
///
/// // (x0 ∧ x1) ∨ (x2 ∧ x3) = (x0 ∨ x2) ∧ (x0 ∨ x3) ∧ (x1 ∨ x2) ∧ (x1 ∨ x3)
/// let expr = (CNF::variable(0) & CNF::variable(1)) | (CNF::variable(2) & CNF::variable(3));
/// assert_eq!(expr.to_string(), "(x0 ∨ x2) ∧ (x0 ∨ x3) ∧ (x1 ∨ x2) ∧ (x1 ∨ x3)");
///
/// // ¬(x0 ∧ x1) = ¬x0 ∨ ¬x1
/// let expr = !(CNF::variable(0) & CNF::variable(1));
/// assert_eq!(expr.to_string(), "¬x0 ∨ ¬x1");
///
/// // ¬(x0 ∨ x1) ∧ x2 = ¬x0 ∧ ¬x1 ∧ x2
/// let expr = !(CNF::variable(0) | CNF::variable(1)) & CNF::variable(2);
/// assert_eq!(expr.to_string(), "¬x0 ∧ ¬x1 ∧ x2");
/// ```
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct CNF(Expr);

impl std::ops::Deref for CNF {
    type Target = Expr;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl From<bool> for CNF {
    fn from(value: bool) -> Self {
        CNF(Expr::from(value))
    }
}

impl CNF {
    pub fn from_rgbd(cnf: rgbd::CNF) -> Self {
        let inner = cnf
            .clauses
            .into_iter()
            .map(|clause| {
                let inner = clause
                    .into_iter()
                    .map(|var| {
                        if var >= 0 {
                            Expr::variable(var as usize)
                        } else {
                            !Expr::variable((-var) as usize)
                        }
                    })
                    .collect::<BTreeSet<Expr>>();
                Expr::Or(inner)
            })
            .collect();
        Self(Expr::And(inner))
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

    pub fn variable(id: usize) -> Self {
        CNF(Expr::Var { id })
    }

    pub fn as_expr(&self) -> &Expr {
        &self.0
    }

    pub fn substitute(&self, id: usize, value: bool) -> Self {
        CNF(self.0.substitute(id, value))
    }

    /// Clauses in AND expression
    ///
    /// ```rust
    /// use cdcl::{CNF, Expr};
    ///
    /// // (x0 ∧ x1) ∨ x2 = (x0 ∨ x2) ∧ (x1 ∨ x2)
    /// let expr = (CNF::variable(0) & CNF::variable(1)) | CNF::variable(2);
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
    /// let expr = CNF::variable(0);
    /// let clauses = expr.clauses().cloned().collect::<Vec<Expr>>();
    /// assert_eq!(clauses, vec![Expr::variable(0)]);
    ///
    /// let expr = CNF::variable(0) | CNF::variable(1);
    /// let clauses = expr.clauses().cloned().collect::<Vec<Expr>>();
    /// assert_eq!(clauses, vec![Expr::variable(0) | Expr::variable(1)]);
    /// ```
    ///
    pub fn clauses(&self) -> Box<dyn Iterator<Item = &Expr> + '_> {
        match &self.0 {
            Expr::And(inner) => Box::new(inner.iter()),
            expr => Box::new(Some(expr).into_iter()),
        }
    }

    /// List up all unit clauses, single variable or its negation, as a [State] with remaining clauses as a new [CNF]
    ///
    /// ```rust
    /// use cdcl::{CNF, State, Expr};
    /// use maplit::btreemap;
    ///
    /// // x0 ∧ x1
    /// let expr = CNF::variable(0) & CNF::variable(1);
    /// let (state, cnf) = expr.take_unit_clauses();
    /// assert_eq!(state, btreemap! { 0 => true, 1 => true });
    /// assert_eq!(cnf, CNF::from(true));
    ///
    /// // x0 ∧ x1 ∧ (x2 ∨ x3)
    /// let expr = CNF::variable(0) & CNF::variable(1) & (CNF::variable(2) | CNF::variable(3));
    /// let (state, cnf) = expr.take_unit_clauses();
    /// assert_eq!(state, btreemap! { 0 => true, 1 => true });
    /// assert_eq!(cnf, CNF::variable(2) | CNF::variable(3));
    /// ```
    pub fn take_unit_clauses(&self) -> (State, CNF) {
        let mut state = State::new();
        let mut clauses = BTreeSet::new();
        for clause in self.clauses() {
            match clause {
                Expr::Var { id } => {
                    state.insert(*id, true);
                }
                Expr::Not(expr) => {
                    if let Expr::Var { id } = expr.as_ref() {
                        state.insert(*id, false);
                    } else {
                        clauses.insert(clause.clone());
                    }
                }
                clause => {
                    clauses.insert(clause.clone());
                }
            }
        }
        (
            state,
            CNF(match clauses.len() {
                0 => Expr::True,
                1 => clauses.first().unwrap().clone(),
                _ => Expr::And(clauses),
            }),
        )
    }
}

impl fmt::Debug for CNF {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl fmt::Display for CNF {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl BitAnd for CNF {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self {
        CNF(self.0 & rhs.0)
    }
}

impl BitOr for CNF {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self {
        // Distributive Law
        match (self.0, rhs.0) {
            (Expr::And(lhs), Expr::And(rhs)) => {
                // (a ∧ b) ∨ (c ∧ d) = (a ∨ c) ∧ (a ∨ d) ∧ (b ∨ c) ∧ (b ∨ d)
                let mut result = BTreeSet::new();
                for a in &lhs {
                    for b in &rhs {
                        result.insert(a.clone() | b.clone());
                    }
                }
                CNF(Expr::And(result))
            }
            (Expr::And(inner), c) | (c, Expr::And(inner)) => {
                // (a ∧ b) ∨ c = (a ∨ c) ∧ (b ∨ c)
                CNF(Expr::And(
                    inner.into_iter().map(|a| a | c.clone()).collect(),
                ))
            }
            (lhs, rhs) => CNF(lhs | rhs),
        }
    }
}

impl Not for CNF {
    type Output = Self;

    fn not(self) -> Self {
        // De Morgan's Law
        match self.0 {
            Expr::And(inner) => CNF(Expr::Or(inner.into_iter().map(Not::not).collect())),
            Expr::Or(inner) => CNF(Expr::And(inner.into_iter().map(Not::not).collect())),
            a => CNF(!a),
        }
    }
}
