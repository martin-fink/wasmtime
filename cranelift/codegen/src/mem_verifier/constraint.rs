use crate::mem_verifier::capability::MemoryAccessCapability;
use crate::mem_verifier::symbolic_value::SymbolicValue;
use alloc::rc::Rc;
use core::fmt::{Debug, Display, Formatter};
#[cfg(feature = "enable-serde")]
use serde::{Deserialize, Serialize};
use std::mem::take;
use std::prelude::v1::Vec;

/// A constraint on a value
/// TODO: add another field 'includingEq'/'excludingEq'
#[derive(Default, Clone, Eq, PartialEq, Hash)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub enum ValueConstraint {
    /// No constraint
    #[default]
    None,
    /// Not equal to a value
    Neq(SymbolicValue),
    /// Equal to a value
    Eq(SymbolicValue),
    /// Lower/Eq than a value
    LowerEq(SymbolicValue),
    /// Greater/Eq than a value
    GreaterEq(SymbolicValue),
    /// In bounds
    InBounds(SymbolicValue, SymbolicValue),
}

impl From<MemoryAccessCapability> for ValueConstraint {
    fn from(value: MemoryAccessCapability) -> Self {
        Self::InBounds(value.begin.clone(), value.begin.offset(value.size))
    }
}

impl ValueConstraint {
    /// Eq constructor
    pub fn eq(value: SymbolicValue) -> Self {
        Self::Eq(value)
    }

    /// Neq constructor
    pub fn neq(value: SymbolicValue) -> Self {
        Self::Neq(value)
    }

    /// in bounds constructor
    pub fn in_bounds(lower: SymbolicValue, upper: SymbolicValue) -> Self {
        let mut val = Self::InBounds(lower, upper);
        val.simplify();
        val
    }

    /// Check if the constraint is useful
    pub fn is_useful(&self) -> bool {
        match self {
            ValueConstraint::None => false,
            ValueConstraint::Eq(val)
            | ValueConstraint::LowerEq(val)
            | ValueConstraint::GreaterEq(val) => !val.contains_unknown(),
            ValueConstraint::InBounds(a, b) => !a.contains_unknown() || !b.contains_unknown(),
            // for now we only care about non-zero
            ValueConstraint::Neq(val) => matches!(val, SymbolicValue::Const(0)),
        }
    }

    /// Offset the constraint by a value
    pub fn offset_neg(&self, other: SymbolicValue) -> Self {
        let mut val = match self {
            ValueConstraint::None => self.clone(),
            ValueConstraint::Eq(val) => ValueConstraint::Eq(val.clone().offset_neg(other)),
            ValueConstraint::Neq(val) => ValueConstraint::Neq(val.clone().offset_neg(other)),
            ValueConstraint::LowerEq(val) => {
                ValueConstraint::LowerEq(val.clone().offset_neg(other))
            }
            ValueConstraint::GreaterEq(val) => {
                ValueConstraint::GreaterEq(val.clone().offset_neg(other))
            }
            ValueConstraint::InBounds(a, b) => ValueConstraint::InBounds(
                a.clone().offset_neg(other.clone()),
                b.clone().offset_neg(other),
            ),
        };
        val.simplify();
        val
    }

    /// Offset the constraint by a value
    pub fn offset(self, other: SymbolicValue) -> Self {
        let mut val = match self {
            ValueConstraint::None => self,
            ValueConstraint::Eq(val) => ValueConstraint::Eq(val.offset(other)),
            ValueConstraint::Neq(val) => ValueConstraint::Neq(val.offset(other)),
            ValueConstraint::LowerEq(val) => ValueConstraint::LowerEq(val.offset(other)),
            ValueConstraint::GreaterEq(val) => ValueConstraint::GreaterEq(val.offset(other)),
            ValueConstraint::InBounds(a, b) => {
                ValueConstraint::InBounds(a.offset(other.clone()), b.offset(other))
            }
        };
        val.simplify();
        val
    }

    /// Offset the constraint by a value
    pub fn scaled(self, value: u64) -> Self {
        let mut val = match self {
            ValueConstraint::None => self,
            ValueConstraint::Eq(val) => ValueConstraint::Eq(val.scaled(value)),
            ValueConstraint::Neq(val) => ValueConstraint::Neq(val.scaled(value)),
            ValueConstraint::LowerEq(val) => ValueConstraint::LowerEq(val.scaled(value)),
            ValueConstraint::GreaterEq(val) => ValueConstraint::GreaterEq(val.scaled(value)),
            ValueConstraint::InBounds(a, b) => {
                ValueConstraint::InBounds(a.scaled(value), b.scaled(value))
            }
        };
        val.simplify();
        val
    }

    /// Apply a constraint to a value
    pub fn apply(&self, to: SymbolicValue) -> SymbolicValue {
        match self {
            ValueConstraint::None => to,
            ValueConstraint::Eq(val) => val.clone(),
            // we just care about non-zero for now
            ValueConstraint::Neq(val) => match (val, to) {
                (SymbolicValue::Const(0), SymbolicValue::Either(a, b)) => match (&*a, &*b) {
                    (SymbolicValue::Const(0), other) | (other, SymbolicValue::Const(0)) => {
                        other.clone()
                    }
                    (a, b) => SymbolicValue::either(a.clone(), b.clone()),
                },
                (_, to) => to,
            },
            ValueConstraint::LowerEq(val) => to.bound_upper(val.clone()),
            ValueConstraint::GreaterEq(val) => val.clone().bound_upper(to),
            ValueConstraint::InBounds(a, b) => {
                SymbolicValue::bounded(SymbolicValue::bounded(a.clone(), to), b.clone())
            }
        }
        .simplify()
    }

    /// Clamp down the constraint
    pub fn lower_eq(self, value: SymbolicValue) -> Self {
        let mut val = match self {
            ValueConstraint::None => ValueConstraint::LowerEq(value),
            ValueConstraint::Eq(val) => ValueConstraint::InBounds(val, value),
            ValueConstraint::Neq(_) => ValueConstraint::LowerEq(value),
            ValueConstraint::LowerEq(bound) => {
                if value.ordered() < bound.ordered() {
                    ValueConstraint::LowerEq(value)
                } else if bound.ordered() < value.ordered() {
                    ValueConstraint::LowerEq(bound)
                } else if bound.ordered() == value.ordered() {
                    ValueConstraint::LowerEq(value)
                } else {
                    ValueConstraint::LowerEq(bound.bound_upper(value))
                }
            }
            ValueConstraint::GreaterEq(bound) => ValueConstraint::InBounds(bound, value),
            ValueConstraint::InBounds(a, b) => ValueConstraint::InBounds(a, b),
        };
        val.simplify();
        val
    }

    /// Clamp down the constraint
    pub fn greater_eq(self, value: SymbolicValue) -> Self {
        let mut val = match self {
            ValueConstraint::None => Self::GreaterEq(value),
            ValueConstraint::Eq(val) => ValueConstraint::InBounds(value, val),
            ValueConstraint::Neq(_) => ValueConstraint::GreaterEq(value),
            ValueConstraint::LowerEq(bound) => ValueConstraint::InBounds(value, bound),
            ValueConstraint::GreaterEq(bound) => {
                if value.ordered() > bound.ordered() {
                    ValueConstraint::GreaterEq(value)
                } else if bound.ordered() > value.ordered() {
                    ValueConstraint::GreaterEq(bound)
                } else if bound.ordered() == value.ordered() {
                    ValueConstraint::GreaterEq(value)
                } else {
                    ValueConstraint::GreaterEq(value.bound_upper(bound))
                }
            }
            ValueConstraint::InBounds(a, b) => ValueConstraint::InBounds(a, b),
        };
        val.simplify();
        val
    }

    fn values(&mut self) -> Vec<&mut SymbolicValue> {
        match self {
            ValueConstraint::None => vec![],
            ValueConstraint::Neq(val) => vec![val],
            ValueConstraint::Eq(val) => vec![val],
            ValueConstraint::LowerEq(val) => vec![val],
            ValueConstraint::GreaterEq(val) => vec![val],
            ValueConstraint::InBounds(val1, val2) => vec![val1, val2],
        }
    }

    /// Simplifies a constraint
    pub fn simplify(&mut self) {
        match self {
            ValueConstraint::Eq(val) if val.is_lower_upper_bound() => {
                let SymbolicValue::Bounded(a, b) = val else {
                    unreachable!();
                };
                if a.is_unknown() {
                    *self = Self::LowerEq((&**b).clone());
                } else {
                    debug_assert!(b.is_unknown());
                    *self = Self::GreaterEq((&**a).clone());
                }
            }
            ValueConstraint::Eq(val)
            | ValueConstraint::Neq(val)
            | ValueConstraint::LowerEq(val)
            | ValueConstraint::GreaterEq(val)
                if val.is_unknown() =>
            {
                *self = ValueConstraint::None;
            }
            ValueConstraint::InBounds(a, b) if a.is_unknown() && b.is_unknown() => {
                *self = ValueConstraint::None;
            }
            ValueConstraint::InBounds(a, val) if a.is_unknown() => {
                *self = Self::LowerEq(take(val));
            }
            ValueConstraint::InBounds(val, b) if b.is_unknown() => {
                *self = Self::GreaterEq(take(val));
            }
            ValueConstraint::InBounds(a, b) if a.ordered() >= b.ordered() => {
                *self = ValueConstraint::eq(SymbolicValue::Bottom);
            }
            _ => {}
        }
    }

    /// Clamp down the constraint
    pub fn clamp(mut self, other: &Self) -> Self {
        if !other.is_useful() {
            return self;
        }

        self.simplify();
        match self {
            ValueConstraint::None => other.clone(),
            ValueConstraint::Eq(a) if a.is_unknown() => other.clone(),
            ValueConstraint::Eq(val) if other.check_in_bounds(&val) => ValueConstraint::Eq(val),
            ValueConstraint::Eq(_) => ValueConstraint::eq(SymbolicValue::Bottom),
            ValueConstraint::LowerEq(val) => other.clone().lower_eq(val),
            ValueConstraint::GreaterEq(val) => other.clone().greater_eq(val),
            ValueConstraint::InBounds(_, _) => unimplemented!(),
            ValueConstraint::Neq(val) => match other {
                ValueConstraint::Eq(inner) if matches!(inner, SymbolicValue::Either(_, _)) => {
                    let SymbolicValue::Either(a, b) = inner else {
                        unreachable!();
                    };
                    let a = if val.ordered() == a.ordered() {
                        Rc::new(SymbolicValue::Bottom)
                    } else {
                        a.clone()
                    };
                    let b = if val.ordered() == b.ordered() {
                        Rc::new(SymbolicValue::Bottom)
                    } else {
                        b.clone()
                    };

                    ValueConstraint::eq(SymbolicValue::Either(a, b).simplify())
                }
                other if other.check_in_bounds(&val) => ValueConstraint::eq(SymbolicValue::Bottom),
                other => other.clone(),
            },
        }
    }

    /// Check if a value matches the constraint
    pub fn check_in_bounds(&self, value: &SymbolicValue) -> bool {
        self.check_in_bounds_with_access_size(value, 0)
    }

    /// Clamp down the constraint with access size
    pub fn check_in_bounds_with_access_size(&self, value: &SymbolicValue, access_size: u8) -> bool {
        // if the value is Either(0, addr), we extract the 0. We allow memory accesses to 0, as those will trap.
        let value = match value {
            value @ SymbolicValue::Either(a, b) => match (&**a, &**b) {
                (SymbolicValue::Const(0), value) | (value, SymbolicValue::Const(0)) => value,
                _ => value,
            },
            value => value,
        };
        let access_size = i64::from(access_size);

        match self {
            ValueConstraint::None => value != &SymbolicValue::Bottom,
            ValueConstraint::Eq(bound) => access_size == 0 && bound.ordered() == value.ordered(),
            ValueConstraint::Neq(bound) => bound.ordered() != value.ordered(),
            ValueConstraint::LowerEq(bound) => {
                value.clone().offset_const_neg(access_size).ordered() <= bound.ordered()
            }
            ValueConstraint::GreaterEq(bound) => value.ordered() >= bound.ordered(),
            ValueConstraint::InBounds(a, b) => {
                let gt = value.ordered() >= a.ordered();
                let modified_upper_val = b.clone().offset_const_neg(access_size);
                let lt = value.ordered() <= modified_upper_val.ordered();
                // eprintln!(
                //     "{} >= {}\n  -> {}\n{} <= {}\n  -> {}",
                //     value, a, gt, value, modified_upper_val, lt
                // );
                gt && lt
            }
        }
    }

    /// If `self` is an Eq, Lower, or Higher constraint, and the value contains a constant offset, extract and return it
    pub fn extract_const_offset(&self) -> Option<(Self, i64)> {
        match self {
            Self::Eq(val) | Self::LowerEq(val) | Self::GreaterEq(val) => {
                if let Some((inner, c)) = val.extract_const_offset() {
                    let inner = inner.clone();
                    let constraint = match self {
                        Self::Eq(_) => Self::Eq(inner),
                        Self::LowerEq(_) => Self::LowerEq(inner),
                        Self::GreaterEq(_) => Self::GreaterEq(inner),
                        _ => unreachable!(),
                    };
                    Some((constraint, c))
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Checks if the value is an offset with a const value
    pub fn has_const_offset(&self) -> bool {
        match self {
            Self::Eq(val) | Self::GreaterEq(val) | Self::LowerEq(val) => val.has_const_offset(),
            _ => false,
        }
    }
}

impl Display for ValueConstraint {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self {
            ValueConstraint::None => write!(f, "unconstrained"),
            ValueConstraint::Eq(val) => write!(f, "= {val}"),
            ValueConstraint::Neq(val) => write!(f, "!= {val}"),
            ValueConstraint::LowerEq(val) => write!(f, "<= {val}"),
            ValueConstraint::GreaterEq(val) => write!(f, ">= {val}"),
            ValueConstraint::InBounds(lower, upper) => write!(f, "{lower}...{upper}"),
        }
    }
}

impl Debug for ValueConstraint {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self)
    }
}
