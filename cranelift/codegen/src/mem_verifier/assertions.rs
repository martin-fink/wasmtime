use crate::ir::Value;
use crate::mem_verifier::constraint::ValueConstraint;
use crate::{ir, Reg};
use core::fmt::{Debug, Display, Formatter};
use regalloc2::VReg;
#[cfg(feature = "enable-serde")]
use serde::{Deserialize, Serialize};
use std::hash::Hash;

/// The type of assertion
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
enum ValueAssertionType {
    // The value should be checked before being used
    Assertion,
    // The value can be assumed without being used
    Assumption,
}

impl Display for ValueAssertionType {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self {
            ValueAssertionType::Assertion => write!(f, "assert"),
            ValueAssertionType::Assumption => write!(f, "assume"),
        }
    }
}

/// A value assertion
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct ValueAssertion {
    /// The constraint
    pub constraint: ValueConstraint,
    /// The type
    assertion_type: ValueAssertionType,
}

impl ValueAssertion {
    /// Creates a new assertion
    pub fn new_assertion(constraint: ValueConstraint) -> Self {
        Self {
            constraint,
            assertion_type: ValueAssertionType::Assertion,
        }
    }

    /// Creates a new assumption
    pub fn new_assumption(constraint: ValueConstraint) -> Self {
        Self {
            constraint,
            assertion_type: ValueAssertionType::Assumption,
        }
    }

    /// Returns true if the assertion is an assertion and should be checked
    pub fn is_assertion(&self) -> bool {
        matches!(self.assertion_type, ValueAssertionType::Assertion)
    }

    /// Returns true if the assertion is useful (i.e. does not contain unknown)
    pub fn is_useful(&self) -> bool {
        self.constraint.is_useful()
    }

    /// Convert an assertion to an assumption
    pub fn to_assumption(self) -> Self {
        Self::new_assumption(self.constraint)
    }

    /// Display the assertion with a given value
    pub fn display<'a, T: Display>(&'a self, value: &'a T) -> ValueAssertionDisplay<'a, T> {
        ValueAssertionDisplay(self, value)
    }
}

/// Display a value assertion for a value
pub struct ValueAssertionDisplay<'a, T: Display>(&'a ValueAssertion, &'a T);

impl<'a, T: Display> Display for ValueAssertionDisplay<'a, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "{} {} {}",
            self.0.assertion_type, self.1, self.0.constraint
        )
    }
}

/// Value or const
/// This enum is intended to be used as a key for value -> constraint maps
#[derive(Copy, Clone, Eq, PartialEq, Hash)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub enum ValueOrConst {
    /// Value
    Value(ir::Value),
    /// Constant value
    Const(i64),
}

impl Display for ValueOrConst {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self {
            ValueOrConst::Value(v) => write!(f, "{}", v),
            ValueOrConst::Const(c) => write!(f, "{}", c),
        }
    }
}

impl Debug for ValueOrConst {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self)
    }
}

impl From<ir::Value> for ValueOrConst {
    fn from(value: Value) -> Self {
        Self::Value(value)
    }
}

/// Register or const
/// This enum is intended to be used as a key for register -> constraint maps
#[derive(Copy, Clone, Eq, PartialEq, Hash)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub enum RegOrConst {
    /// Register
    Reg(VReg),
    /// Constant value
    Const(i64),
}

impl RegOrConst {
    /// check if self is Const
    pub fn is_const(&self) -> bool {
        matches!(self, Self::Const(_))
    }
}

impl Display for RegOrConst {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self {
            RegOrConst::Reg(r) => write!(f, "{}", r),
            RegOrConst::Const(c) => write!(f, "{}", c),
        }
    }
}

impl Debug for RegOrConst {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self)
    }
}

impl From<Reg> for RegOrConst {
    fn from(reg: Reg) -> Self {
        Self::Reg(reg.into())
    }
}

impl From<VReg> for RegOrConst {
    fn from(reg: VReg) -> Self {
        Self::Reg(reg)
    }
}
