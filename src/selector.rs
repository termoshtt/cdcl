use crate::CNF;
use anyhow::{Context, Result};
use std::num::NonZeroU32;

pub fn take_minimal_id(cnf: &CNF) -> Result<NonZeroU32> {
    cnf.literals()
        .map(|l| l.id)
        .min()
        .context("Cannot take minimal id from CNF")
}
