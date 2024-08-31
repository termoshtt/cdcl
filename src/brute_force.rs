use crate::{take_minimal_id, CancelToken, Literal, Solution, Solver, CNF};
use std::num::NonZeroU32;

pub struct BruteForce {}

impl Solver for BruteForce {
    fn name(&self) -> &'static str {
        "brute_force"
    }

    fn solve_cancelable(&mut self, expr: CNF, cancel_token: CancelToken) -> Solution {
        brute_force(expr, take_minimal_id, cancel_token)
    }
}

pub fn brute_force(
    input: CNF,
    selector: fn(&CNF) -> NonZeroU32,
    cancel_token: CancelToken,
) -> Solution {
    if let Some(solution) = input.is_solved() {
        return solution;
    }

    if cancel_token.is_canceled() {
        return Solution::Canceled;
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
        match brute_force(new, selector, cancel_token.clone()) {
            Solution::Sat(mut state) => {
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
    fn test_brute_force() {
        let cancel_token = CancelToken::new();

        for (expr, expected) in crate::testing::single_solution_cases() {
            assert_eq!(
                brute_force(expr.clone(), take_minimal_id, cancel_token.clone()),
                expected,
                "Failed on {expr:?}",
            );
        }

        // x3 ∨ x4
        let mut expr = CNF::lit(3) | CNF::lit(4);
        let result = brute_force(expr.clone(), take_minimal_id, cancel_token.clone());
        assert!(expr.evaluate(result.as_sat().unwrap()));
    }
}
