use crate::{Solution, State, CNF};
use maplit::btreemap;

pub fn single_solution_cases() -> Vec<(CNF, Solution)> {
    vec![
        // True
        (CNF::from(true), Solution::Sat(State::default())),
        // False
        (CNF::from(false), Solution::UnSat),
        // x3
        (CNF::variable(3), Solution::Sat(btreemap! { 3 => true })),
        // ¬x3
        (!CNF::variable(3), Solution::Sat(btreemap! { 3 => false })),
        // x3 ∧ x4
        (
            CNF::variable(3) & CNF::variable(4),
            Solution::Sat(btreemap! { 3 => true, 4 => true }),
        ),
        // x3 ∧ ¬x4
        (
            CNF::variable(3) & !CNF::variable(4),
            Solution::Sat(btreemap! { 3 => true, 4 => false }),
        ),
        // ¬x3 ∧ x4
        (
            !CNF::variable(3) & CNF::variable(4),
            Solution::Sat(btreemap! { 3 => false, 4 => true }),
        ),
        // ¬x3 ∧ ¬x4
        (
            !CNF::variable(3) & !CNF::variable(4),
            Solution::Sat(btreemap! { 3 => false, 4 => false }),
        ),
        // x3 ∧ x4 ∧ x5
        (
            CNF::variable(3) & CNF::variable(4) & CNF::variable(5),
            Solution::Sat(btreemap! { 3 => true, 4 => true, 5 => true }),
        ),
    ]
}
