use crate::{take_minimal_id, Literal, Solution, CNF};

pub struct BruteForce {}

pub fn brute_force(input: CNF) -> Solution {
    if let Some(solution) = input.is_solved() {
        return solution;
    }

    let fix = take_minimal_id(&input);
    for value in [true, false] {
        let lit = Literal {
            id: fix,
            positive: value,
        };
        log::trace!("Decision: {}", lit);
        let mut new = input.clone();
        if new.substitute(lit).is_err() {
            continue;
        }
        match brute_force(new) {
            Solution::Sat(mut state) => {
                state.insert(lit);
                return Solution::Sat(state);
            }
            Solution::UnSat => continue,
        }
    }
    Solution::UnSat
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_brute_force() {
        for (expr, expected) in crate::testing::single_solution_cases() {
            assert_eq!(brute_force(expr.clone()), expected, "Failed on {expr:?}",);
        }

        // x3 ∨ x4
        let mut expr = CNF::lit(3) | CNF::lit(4);
        let result = brute_force(expr.clone());
        assert!(expr.evaluate(result.as_sat().unwrap()));
    }
}
