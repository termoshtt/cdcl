#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct StatusStack(Vec<Status>);

impl StatusStack {
    /// Implicit depth of the search tree + 1
    pub fn d(&self) -> u32 {
        self.0.len() as u32 + 1
    }

    fn m_d(&self) -> Status {
        debug_assert!(!self.0.is_empty());
        *self.0.last().unwrap()
    }

    pub fn flip(&mut self) -> Option<u32> {
        debug_assert!(!self.0.is_empty());
        let md = self.0.last_mut().unwrap();
        *md = match *md {
            Status::TryT => Status::TryFAfterT,
            Status::TryF => Status::TryTAfterF,
            _ => return None,
        };
        Some(self.next_literal())
    }

    /// Stack new status in A2
    pub fn select(&mut self, status: Status) {
        self.0.push(status);
    }

    /// Pop the last status, and returns next literal `l = 2d + m_d & 1`
    pub fn backtrack(&mut self) -> Option<u32> {
        self.0.pop()?;
        Some(self.next_literal())
    }

    fn next_literal(&self) -> u32 {
        2 * self.d() + (self.m_d() as u32 & 1)
    }

    pub fn get(&self, index: usize) -> Status {
        self.0[index]
    }
}

/// Search status for each literal
#[derive(Debug, Clone, PartialEq, Eq, Copy, PartialOrd, Ord)]
pub enum Status {
    /// Try `1` before trying `0`
    TryT = 0,
    /// Try `0` before trying `1`
    TryF = 1,
    /// Try `1` after trying `0` has failed
    TryTAfterF = 2,
    /// Try `0` after trying `1` has failed
    TryFAfterT = 3,
    /// Try `1` for the pure literal
    PureT = 4,
    /// Try `0` for the pure literal
    PureF = 5,
}

impl Status {
    pub fn is_true(&self) -> bool {
        match self {
            Self::TryT | Self::TryTAfterF | Self::PureT => true,
            _ => false,
        }
    }
}

impl PartialEq<u32> for Status {
    fn eq(&self, other: &u32) -> bool {
        *self as u32 == *other
    }
}

impl PartialOrd<u32> for Status {
    fn partial_cmp(&self, other: &u32) -> Option<std::cmp::Ordering> {
        (*self as u32).partial_cmp(other)
    }
}

impl From<u32> for Status {
    fn from(value: u32) -> Self {
        match value {
            0 => Self::TryT,
            1 => Self::TryF,
            2 => Self::TryTAfterF,
            3 => Self::TryFAfterT,
            4 => Self::PureT,
            5 => Self::PureF,
            _ => unreachable!("Status out of range"),
        }
    }
}
