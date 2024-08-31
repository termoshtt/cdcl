use crate::{Solution, State, CNF};
use maplit::btreeset;

pub fn single_solution_cases() -> Vec<(CNF, Solution)> {
    vec![
        // True
        (CNF::from(true), Solution::Sat(State::default())),
        // False
        (CNF::from(false), Solution::UnSat),
        // x3
        (CNF::lit(3), Solution::Sat(btreeset! { 3.into() })),
        // ¬x3
        (!CNF::lit(3), Solution::Sat(btreeset! { (-3).into() })),
        // x3 ∧ x4
        (
            CNF::lit(3) & CNF::lit(4),
            Solution::Sat(btreeset! { 3.into(), 4.into() }),
        ),
        // x3 ∧ ¬x4
        (
            CNF::lit(3) & !CNF::lit(4),
            Solution::Sat(btreeset! { 3.into(), (-4).into() }),
        ),
        // ¬x3 ∧ x4
        (
            !CNF::lit(3) & CNF::lit(4),
            Solution::Sat(btreeset! { (-3).into(), 4.into() }),
        ),
        // ¬x3 ∧ ¬x4
        (
            !CNF::lit(3) & !CNF::lit(4),
            Solution::Sat(btreeset! { (-3).into(), (-4).into() }),
        ),
        // x3 ∧ x4 ∧ x5
        (
            CNF::lit(3) & CNF::lit(4) & CNF::lit(5),
            Solution::Sat(btreeset! { 3.into(), 4.into(), 5.into() }),
        ),
    ]
}
