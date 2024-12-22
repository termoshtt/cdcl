use crate::Clause;
use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ResolutionTraceEntry {
    Append(Clause),
    Delete(Clause),
}

impl fmt::Display for ResolutionTraceEntry {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ResolutionTraceEntry::Append(clause) => write!(f, "{}", clause),
            ResolutionTraceEntry::Delete(clause) => write!(f, "d {}", clause),
        }
    }
}

#[derive(Debug, Default, Clone, PartialEq, Eq, Hash)]
pub struct ResolutionTrace(Vec<ResolutionTraceEntry>);

impl ResolutionTrace {
    pub fn append(&mut self, clause: Clause) {
        self.0.push(ResolutionTraceEntry::Append(clause));
    }

    pub fn delete(&mut self, clause: Clause) {
        self.0.push(ResolutionTraceEntry::Delete(clause));
    }
}
