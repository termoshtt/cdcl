use crate::{pending_once, take_minimal_id, Literal, Solution, CNF};

pub struct BruteForce {}

#[async_recursion::async_recursion]
pub async fn brute_force(input: CNF) -> Solution {
    if let Some(solution) = input.is_solved() {
        return solution;
    }
    pending_once().await;

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
        match brute_force(new).await {
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
    use crate::block_on;

    #[test]
    fn test_brute_force() {
        for (expr, expected) in crate::testing::single_solution_cases() {
            assert_eq!(
                block_on(brute_force(expr.clone())),
                expected,
                "Failed on {expr:?}",
            );
        }

        // x3 ∨ x4
        let mut expr = CNF::lit(3) | CNF::lit(4);
        let result = block_on(brute_force(expr.clone()));
        assert!(expr.evaluate(result.as_sat().unwrap()));
    }
}
