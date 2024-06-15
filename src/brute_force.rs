use crate::{take_minimal_id, CancelToken, Expr, Solution, Solver, State, CNF};

pub struct BruteForce {}

impl Solver for BruteForce {
    fn name(&self) -> &'static str {
        "brute_force"
    }

    fn solve_cancelable(&mut self, expr: CNF, cancel_token: CancelToken) -> Solution {
        brute_force(expr, take_minimal_id, cancel_token)
    }
}

pub fn brute_force(input: CNF, selector: fn(&CNF) -> usize, cancel_token: CancelToken) -> Solution {
    match *input.as_expr() {
        // Already solved
        Expr::True => return Solution::Sat(State::default()),
        // Never feasible
        Expr::False => return Solution::UnSat,
        _ => {}
    }

    if cancel_token.is_canceled() {
        return Solution::Canceled;
    }

    let fix = selector(&input);
    for value in [true, false] {
        log::trace!("Set x{} = {}", fix, value);
        match brute_force(input.substitute(fix, value), selector, cancel_token.clone()) {
            Solution::Sat(mut state) => {
                state.insert(fix, value);
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
        let expr = CNF::variable(3) | CNF::variable(4);
        let result = brute_force(expr.clone(), take_minimal_id, cancel_token.clone());
        assert_eq!(expr.evaluate(result.as_sat().unwrap()), Expr::True);
    }
}
