use crate::{take_minimal_id, CancelToken, Literal, Solution, Solver, State, CNF};
use std::num::NonZeroU32;

#[derive(Default)]
pub struct DPLL {}

impl Solver for DPLL {
    fn name(&self) -> &'static str {
        "dpll"
    }
    fn solve_cancelable(&mut self, expr: CNF, cancel_token: CancelToken) -> Solution {
        dpll(expr, take_minimal_id, cancel_token)
    }
}

pub fn dpll(
    mut input: CNF,
    selector: fn(&CNF) -> NonZeroU32,
    cancel_token: CancelToken,
) -> Solution {
    let mut state = State::default();

    // Unit propagation
    loop {
        if cancel_token.is_canceled() {
            return Solution::Canceled;
        }
        let units = input.take_unit_clauses();
        if units.is_empty() {
            break;
        }
        for lit in units.into_iter() {
            input.substitute(lit);
            state.insert(lit);
        }
    }

    match input.is_solved() {
        Some(Solution::Sat(..)) => return Solution::Sat(state),
        Some(Solution::UnSat) => return Solution::UnSat,
        _ => {}
    }

    let fix = selector(&input);
    for value in [true, false] {
        let lit = Literal {
            id: fix,
            positive: value,
        };
        log::trace!("Decision: {}", lit);
        let mut new = input.clone();
        new.substitute(lit);
        match dpll(new, selector, cancel_token.clone()) {
            Solution::Sat(mut sub_state) => {
                state.append(&mut sub_state);
                state.insert(lit);
                return Solution::Sat(state);
            }
            Solution::UnSat => continue,
            Solution::Canceled => return Solution::Canceled,
        }
    }
    Solution::UnSat
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_dpll() {
        let cancel_token = CancelToken::new();

        for (expr, expected) in crate::testing::single_solution_cases() {
            assert_eq!(
                dpll(expr.clone(), crate::take_minimal_id, cancel_token.clone()),
                expected,
                "Failed on {expr:?}",
            );
        }
    }
}
