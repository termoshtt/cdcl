use crate::{state, Solution, State, CNF};

pub fn single_solution_cases() -> Vec<(CNF, Solution)> {
    vec![
        // True
        (CNF::from(true), Solution::Sat(State::default())),
        // False
        (CNF::from(false), Solution::UnSat),
        // x3
        (CNF::lit(3), Solution::Sat(state![3])),
        // ¬x3
        (!CNF::lit(3), Solution::Sat(state![-3])),
        // x3 ∧ x4
        (CNF::lit(3) & CNF::lit(4), Solution::Sat(state![3, 4])),
        // x3 ∧ ¬x4
        (CNF::lit(3) & !CNF::lit(4), Solution::Sat(state![3, -4])),
        // ¬x3 ∧ x4
        (!CNF::lit(3) & CNF::lit(4), Solution::Sat(state![-3, 4])),
        // ¬x3 ∧ ¬x4
        (!CNF::lit(3) & !CNF::lit(4), Solution::Sat(state![-3, -4])),
        // x3 ∧ x4 ∧ x5
        (
            CNF::lit(3) & CNF::lit(4) & CNF::lit(5),
            Solution::Sat(state![3, 4, 5]),
        ),
    ]
}
