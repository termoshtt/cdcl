use crate::CNF;
use std::num::NonZeroU32;

pub fn take_minimal_id(cnf: &CNF) -> NonZeroU32 {
    let mut supp = cnf.supp();
    supp.pop_first().expect("CNF is empty")
}
