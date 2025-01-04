use crate::CNF;
use anyhow::{bail, Result};
use std::num::NonZeroU32;

pub fn take_minimal_id(cnf: &CNF) -> Result<NonZeroU32> {
    let CNF::Valid(clauses) = cnf else {
        bail!("Cannot take minimal id from a conflicted CNF")
    };
    let mut min_id = None;
    for c in clauses {
        let Some(literals) = c.literals() else {
            continue;
        };
        for l in literals {
            let id = l.id;
            if let Some(current) = min_id {
                if id < current {
                    min_id = Some(id);
                }
            } else {
                min_id = Some(id);
            }
        }
    }
    if let Some(min_id) = min_id {
        return Ok(min_id);
    } else {
        bail!("Cannot take minimal id from an empty CNF")
    }
}
