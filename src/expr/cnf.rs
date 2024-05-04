use super::Expr;
use anyhow::{bail, Context, Result};
use std::{
    collections::BTreeSet,
    fmt,
    ops::{BitAnd, BitOr, Not},
};

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
    /// Parse CNF from DIMACS format
    ///
    /// ```rust
    /// use cdcl::CNF;
    ///
    /// let (expr, num_variables, num_clauses) = CNF::from_dimacs_format(r#"
    /// p cnf 5 3
    /// 1 -5 4 0
    /// -1 5 3 4 0
    /// -3 -4 0
    /// "#).unwrap();
    ///
    /// // Note the expression are sorted automatically
    /// assert_eq!(
    ///     expr.to_string(),
    ///     "(x0 ∨ ¬x3 ∨ ¬x4) ∧ (x0 ∨ x1 ∨ x4 ∨ ¬x5) ∧ (x0 ∨ ¬x1 ∨ x3 ∨ x4 ∨ x5)"
    /// );
    /// assert_eq!(num_variables, 5);
    /// assert_eq!(num_clauses, 3);
    /// ```
    pub fn from_dimacs_format(input: &str) -> Result<(Self, usize, usize)> {
        let mut lines = input.lines().filter_map(|line| {
            let line = line.trim();
            if line.is_empty() {
                // Emtpy line is ignored
                return None;
            }
            if line.starts_with(['c', 'C']) {
                // Comment
                return None;
            }
            Some(line.split(' ').collect::<Vec<&str>>())
        });
        let header = lines.next().context("Missing header")?;
        if header.len() != 4 || header[0].to_lowercase() != "p" || header[1].to_lowercase() != "cnf"
        {
            bail!("Invalid header: {}", header.join(" "));
        }
        let num_variables = header[2].parse::<usize>()?;
        let num_clauses = header[3].parse::<usize>()?;

        let clauses = lines
            .map(|line| -> Result<Expr> {
                let clause = line
                    .iter()
                    .map(|&s| -> Result<Expr> {
                        let id = s.parse::<i32>()?;
                        Ok(if id >= 0 {
                            Expr::variable(id as usize)
                        } else {
                            !Expr::variable((-id) as usize)
                        })
                    })
                    .collect::<Result<BTreeSet<Expr>>>()?;
                Ok(if clause.len() == 1 {
                    clause.last().unwrap().clone()
                } else {
                    Expr::Or(clause)
                })
            })
            .collect::<Result<BTreeSet<Expr>>>()?;

        Ok((CNF(Expr::And(clauses)), num_variables, num_clauses))
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

#[cfg(test)]
mod tests {
    use super::CNF;

    #[test]
    fn dimacs_comment() {
        CNF::from_dimacs_format(
            r#"
            c This is a comment
            p cnf 5 3
            1 -5 4 0
            -1 5 3 4 0
            -3 -4 0
            "#,
        )
        .unwrap();
    }
}
