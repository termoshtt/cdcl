use crate::CNF;

pub fn take_minimal_id(cnf: &CNF) -> usize {
    assert!(cnf.as_bool().is_none());
    *cnf.variables()
        .first()
        .expect("Non-boolean CNF expression must have at least one variable.")
}
