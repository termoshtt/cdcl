/// Conjunctive normal form
#[derive(Debug, Clone, PartialEq)]
pub enum CNF {
    And(Box<CNF>, Box<CNF>),
    Or(Box<CNF>, Box<CNF>),
    Not(Box<CNF>),
    Var(String),
    True,
}
