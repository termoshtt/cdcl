use crate::{CancelToken, Expr, Solution, Solver, State, CNF};

pub struct BruteForce {}

impl Solver for BruteForce {
    fn name(&self) -> &'static str {
        "brute_force"
    }

    fn solve_cancelable(&mut self, expr: CNF, cancel_token: CancelToken) -> Solution {
        brute_force(expr, take_minimal_id, cancel_token)
    }
}

pub fn take_minimal_id(cnf: &CNF) -> usize {
    assert!(cnf.as_bool().is_none());
    *cnf.variables()
        .first()
        .expect("Non-boolean CNF expression must have at least one variable.")
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
        log::info!("Canceled");
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
    use maplit::btreemap;

    #[test]
    fn test_brute_force() {
        let cancel_token = CancelToken::new();
        // True
        assert_eq!(
            brute_force(CNF::from(true), take_minimal_id, cancel_token.clone()),
            Solution::Sat(State::default())
        );
        // False
        assert_eq!(
            brute_force(CNF::from(false), take_minimal_id, cancel_token.clone()),
            Solution::UnSat
        );

        // x3
        assert_eq!(
            brute_force(CNF::variable(3), take_minimal_id, cancel_token.clone()),
            Solution::Sat(btreemap! { 3 => true })
        );
        // ¬x3
        assert_eq!(
            brute_force(!CNF::variable(3), take_minimal_id, cancel_token.clone()),
            Solution::Sat(btreemap! { 3 => false })
        );

        // x3 ∧ x4
        assert_eq!(
            brute_force(
                CNF::variable(3) & CNF::variable(4),
                take_minimal_id,
                cancel_token.clone()
            ),
            Solution::Sat(btreemap! { 3 => true, 4 => true })
        );
        // x3 ∧ ¬x4
        assert_eq!(
            brute_force(
                !CNF::variable(3) & CNF::variable(4),
                take_minimal_id,
                cancel_token.clone()
            ),
            Solution::Sat(btreemap! { 3 => false, 4 => true })
        );
        // ¬x3 ∧ x4
        assert_eq!(
            brute_force(
                !CNF::variable(3) & !CNF::variable(4),
                take_minimal_id,
                cancel_token.clone()
            ),
            Solution::Sat(btreemap! { 3 => false, 4 => false })
        );

        // x3 ∧ x4 ∧ x5
        assert_eq!(
            brute_force(
                CNF::variable(3) & CNF::variable(4) & CNF::variable(5),
                take_minimal_id,
                cancel_token.clone()
            ),
            Solution::Sat(btreemap! { 3 => true, 4 => true, 5 => true })
        );

        // x3 ∨ x4
        let expr = CNF::variable(3) | CNF::variable(4);
        let result = brute_force(expr.clone(), take_minimal_id, cancel_token.clone());
        assert_eq!(expr.evaluate(result.as_sat().unwrap()), Expr::True);
    }
}
