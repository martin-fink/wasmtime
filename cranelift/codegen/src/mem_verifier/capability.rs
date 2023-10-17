use crate::mem_verifier::symbolic_value::SymbolicValue;
use core::fmt::{Display, Formatter};
#[cfg(feature = "enable-serde")]
use serde::{Deserialize, Serialize};
use std::prelude::v1::String;

/// A capability allows accessing Memory
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct MemoryAccessCapability {
    /// The value pointing to the begin of the memory this capability corresponds to
    pub begin: SymbolicValue,

    /// The value indicating the size of the capability
    pub size: SymbolicValue,

    /// The name for the capability for debugging purposes
    pub name: String,

    /// If we know a minimum size for the capability
    pub min_size: Option<u8>,
}

impl MemoryAccessCapability {
    /// Create a new capability
    pub fn new(begin: SymbolicValue, size: SymbolicValue, name: &str) -> Self {
        Self {
            begin,
            size,
            name: String::from(name),
            min_size: None,
        }
    }
    /// Create a new capability for an area we know has a minimum size
    pub fn with_min_size(
        begin: SymbolicValue,
        size: SymbolicValue,
        name: &str,
        min_size: u8,
    ) -> Self {
        Self {
            begin,
            size,
            name: String::from(name),
            min_size: Some(min_size),
        }
    }
}

impl Display for MemoryAccessCapability {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "allow {}[0...{}] ;; {}",
            self.begin, self.size, self.name
        )
    }
}
