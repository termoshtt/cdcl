use super::StatusStack;
use crate::{Literal, State};
use std::{
    collections::{BTreeSet, HashMap},
    num::NonZeroU32,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IdMapping(HashMap<NonZeroU32, usize>);

impl IdMapping {
    pub fn new(literals: &BTreeSet<NonZeroU32>) -> Self {
        Self(
            literals
                .into_iter()
                .enumerate()
                .map(|(new, &original)| (original, new))
                .collect(),
        )
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    #[allow(dead_code)]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn translate(&self, lit: Literal) -> u32 {
        2 * (self.0[&lit.id] as u32 + 1) + if lit.positive { 0 } else { 1 }
    }

    pub fn as_state(&self, stack: &StatusStack) -> State {
        self.0
            .iter()
            .map(|(&id, &d)| Literal {
                id,
                positive: stack.get(d).is_true(),
            })
            .collect()
    }
}
