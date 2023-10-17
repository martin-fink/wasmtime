use crate::fx::FxHashMap;
use crate::ir;
use crate::ir::GlobalValueData;
use crate::mem_verifier::trunc_i64_to_width;
use alloc::borrow::Cow;
use alloc::rc::Rc;
use core::fmt::{Debug, Display, Formatter};
#[cfg(feature = "enable-serde")]
use serde::{Deserialize, Serialize};
use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::VecDeque;
use std::mem::{swap, take};
use std::ops::Deref;
use std::prelude::v1::Vec;

/// A special symbolic value only equal to itself
#[derive(Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub enum SpecialValue {
    /// The vmctx value
    VmCtx,
    /// The pointer to the return value area
    RetAreaPtr,
}

/// Enum describing the symbolic value
#[derive(Clone, Hash, PartialEq, Eq, PartialOrd, Ord, Default)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub enum SymbolicValue {
    /// The default case, top value for the lattice
    #[default]
    Unknown,
    /// A special value, only equal to itself
    Special(SpecialValue),
    /// Constant value
    Const(i64),
    /// The bottom value
    Bottom,
    /// An offset from a fixed value
    Offset(Rc<SymbolicValue>, Rc<SymbolicValue>),
    /// A negative offset
    OffsetNeg(Rc<SymbolicValue>, Rc<SymbolicValue>),
    /// bounded by lower, upper bounds
    Bounded(Rc<SymbolicValue>, Rc<SymbolicValue>),
    /// Either of two values
    Either(Rc<SymbolicValue>, Rc<SymbolicValue>),
    /// A multiplication
    Scale(Rc<SymbolicValue>, u64),
    /// Load
    Load(Rc<SymbolicValue>),
}

unsafe impl Send for SymbolicValue {}

thread_local! {
    static COMPARISON_CACHE: RefCell<FxHashMap<SymbolicValue, FxHashMap<SymbolicValue, Option<CustomOrdering>>>> = RefCell::new(FxHashMap::default());
    static SIMPLIFICATION_CACHE: RefCell<FxHashMap<SymbolicValue, SymbolicValue>> = RefCell::new(FxHashMap::default());
}

/// The max depth of loads
pub const MAX_LOAD_DEPTH: usize = 8;

impl SymbolicValue {
    /// Helper function creating an offset to reduce boilerplate
    pub fn offset(self, other: SymbolicValue) -> Self {
        Self::Offset(Rc::new(self), Rc::new(other)).simplify()
    }

    /// Helper to construct the either variant
    pub fn either(a: SymbolicValue, b: SymbolicValue) -> Self {
        Self::Either(Rc::new(a), Rc::new(b)).simplify()
    }

    /// Helper to construct the bounded variant
    pub fn bounded(a: SymbolicValue, b: SymbolicValue) -> Self {
        Self::Bounded(Rc::new(a), Rc::new(b)).simplify()
    }

    /// Add a const offset
    pub fn offset_const(self, c: i64) -> Self {
        if c == 0 {
            return self;
        }
        self.offset(Self::Const(c))
    }

    /// Helper function creating an offset to reduce boilerplate
    pub fn offset_neg(self, other: SymbolicValue) -> Self {
        Self::OffsetNeg(Rc::new(self), Rc::new(other)).simplify()
    }

    /// Add a const offset
    pub fn offset_const_neg(self, c: i64) -> Self {
        if c == 0 {
            return self;
        }
        self.offset_neg(Self::Const(c))
    }

    /// Umin
    pub fn bound_upper(self, other: Self) -> Self {
        Self::Bounded(Rc::new(self), Rc::new(other)).simplify()
    }

    /// Umin with a constant
    pub fn bound_upper_const(self, c: i64) -> Self {
        self.bound_upper(Self::Const(c))
    }

    /// Scale a value by a constant
    pub fn scaled(self, c: u64) -> Self {
        if c == 1 {
            return self;
        }
        Self::Scale(Rc::new(self), c).simplify()
    }

    /// Left-shift a value
    pub fn shifted(self, c: u8) -> Self {
        self.scaled(1_u64.overflowing_shl(c.into()).0)
    }

    /// Load
    pub fn load(self) -> Self {
        Self::Load(Rc::new(self))
    }

    /// Check if the value is not unknown, a range, etc.
    pub fn is_fixed_value(&self) -> bool {
        match self {
            SymbolicValue::Unknown => false,
            SymbolicValue::Special(_) => true,
            SymbolicValue::Const(_) => true,
            SymbolicValue::Offset(a, b) => a.is_fixed_value() && b.is_fixed_value(),
            SymbolicValue::OffsetNeg(a, _) => a.is_fixed_value(),
            SymbolicValue::Scale(a, _) => a.is_fixed_value(),
            SymbolicValue::Load(ptr) => ptr.is_fixed_value(),
            SymbolicValue::Bounded(_, _) => false,
            SymbolicValue::Either(_, _) => false,
            SymbolicValue::Bottom => true,
        }
    }

    /// Create a SymbolicValue from a GlobalValue
    pub fn from_global_value(func: &ir::Function, gv: ir::GlobalValue) -> Self {
        match func
            .global_values
            .get(gv)
            .expect("Usage of undefined global value")
        {
            GlobalValueData::VMContext => Self::Special(SpecialValue::VmCtx),
            GlobalValueData::Load { base, offset, .. } => Self::from_global_value(func, *base)
                .offset_const(i64::from(*offset))
                .load(),
            GlobalValueData::IAddImm { base, offset, .. } => {
                Self::from_global_value(func, *base).offset_const(offset.bits())
            }
            GlobalValueData::Symbol { .. } => Self::Unknown,
            GlobalValueData::DynScaleTargetConst { .. } => Self::Unknown,
        }
        .simplify()
    }

    /// Truncate integers to a smaller representation
    pub fn trunc_const_to_bit_width(&mut self, width: u32) {
        if width == 64 {
            // we are already at 64 bits
            return;
        } else if !width.is_power_of_two() {
            unimplemented!("cannot truncate to width {width}")
        };

        let mut worklist = VecDeque::new();
        worklist.push_back(self);

        while let Some(value) = worklist.pop_front() {
            match value {
                SymbolicValue::Const(c) => {
                    if *c < 0 {
                        *c = trunc_i64_to_width(*c, width);
                    }
                }
                SymbolicValue::Offset(a, b) => {
                    worklist.push_back(&mut *Rc::make_mut(a));
                    worklist.push_back(&mut *Rc::make_mut(b));
                }
                SymbolicValue::OffsetNeg(a, b) => {
                    worklist.push_back(&mut *Rc::make_mut(a));
                    worklist.push_back(&mut *Rc::make_mut(b));
                }
                SymbolicValue::Scale(a, _) => worklist.push_back(&mut *Rc::make_mut(a)),
                SymbolicValue::Bounded(a, b) => {
                    worklist.push_back(&mut *Rc::make_mut(a));
                    worklist.push_back(&mut *Rc::make_mut(b));
                }
                SymbolicValue::Either(a, b) => {
                    worklist.push_back(&mut *Rc::make_mut(a));
                    worklist.push_back(&mut *Rc::make_mut(b));
                }
                // we don't truncate into loads
                SymbolicValue::Load(ptr) => worklist.push_back(&mut *Rc::make_mut(ptr)),
                SymbolicValue::Unknown | SymbolicValue::Special(_) | SymbolicValue::Bottom => {}
            }
        }
    }

    fn simplify_offset_impl(&mut self) {
        let Self::Offset(base, offset) = self else {
            unreachable!();
        };
        let base = Rc::make_mut(base);
        let offset = Rc::make_mut(offset);
        base.simplify_impl();
        offset.simplify_impl();

        match (&mut *base, &mut *offset) {
            (Self::Bottom, _) | (_, Self::Bottom) => *self = Self::Bottom,
            (Self::Unknown, Self::Unknown) => *self = Self::Unknown,
            (Self::Load(ptr1), Self::Load(ptr2)) if ptr1.is_unknown() && ptr2.is_unknown() => {
                *self = Self::Unknown
            }
            (Self::Const(a), Self::Const(b)) => *self = Self::Const(a.wrapping_add(*b)),
            (Self::Const(0), a) | (a, Self::Const(0)) => *self = take(a),
            (Self::Const(a), b) => *self = Self::Offset(Rc::new(take(b)), Rc::new(Self::Const(*a))),
            (a, Self::Const(c)) if *c < 0 => {
                *self = Self::OffsetNeg(Rc::new(take(a)), Rc::new(Self::Const(-*c)))
            }
            (Self::Offset(a, b), c) | (c, Self::Offset(a, b)) => match (&**b, c) {
                (Self::Const(b), Self::Const(c)) => {
                    *self = Self::Offset(take(a), Rc::new(Self::Const(b.wrapping_add(*c))))
                }
                (Self::Const(b), c) => {
                    *self = Self::Offset(
                        Rc::new(Self::Offset(take(a), Rc::new(take(c)))),
                        Rc::new(Self::Const(*b)),
                    )
                }
                _ => {}
            },
            (Self::OffsetNeg(a, b), c) => match (&mut *Rc::make_mut(b), c) {
                (Self::Const(b), Self::Const(c)) if b == c => *self = (**a).clone(),
                (Self::Const(b), Self::Const(c)) => {
                    *self = Self::Offset(take(a), Rc::new(Self::Const(c.wrapping_sub(*b))))
                }
                (b, c) => {
                    *self = Self::OffsetNeg(
                        Rc::new(Self::Offset(take(a), Rc::new(take(c)))),
                        Rc::new(take(b)),
                    );
                    self.simplify_impl();
                }
            },
            (Self::Bounded(a, b), c) | (c, Self::Bounded(a, b)) => {
                let mut offset1 = Self::Offset(take(a), Rc::new(c.clone()));
                let mut offset2 = Self::Offset(take(b), Rc::new(take(c)));
                offset1.simplify_impl();
                offset2.simplify_impl();
                *self = Self::Bounded(Rc::new(offset1), Rc::new(offset2));
            }
            (Self::Either(a, b), c) | (c, Self::Either(a, b)) => {
                let mut lhs = Self::Offset(take(a), Rc::new(c.clone()));
                let mut rhs = Self::Offset(take(b), Rc::new(take(c)));
                lhs.simplify_impl();
                rhs.simplify_impl();
                *self = Self::Either(Rc::new(lhs), Rc::new(rhs))
            }
            _ => {}
        }
    }

    fn simplify_offset_neg_impl(&mut self) {
        let Self::OffsetNeg(base, offset) = self else {
            unreachable!();
        };
        let base = Rc::make_mut(base);
        let offset = Rc::make_mut(offset);
        base.simplify_impl();
        offset.simplify_impl();

        match (&mut *base, &mut *offset) {
            (Self::Unknown, Self::Unknown) => *self = Self::Unknown,
            (Self::Load(ptr1), Self::Load(ptr2)) if ptr1.is_unknown() && ptr2.is_unknown() => {
                *self = Self::Unknown
            }
            (Self::Const(a), Self::Const(b)) => *self = Self::Const(a.wrapping_sub(*b)),
            (a, Self::Const(0)) => *self = take(a),
            (Self::OffsetNeg(a, b), Self::Const(c)) => match &**b {
                Self::Const(b) => {
                    *self =
                        Self::OffsetNeg(take(a), Rc::new(SymbolicValue::Const(b.wrapping_add(*c))))
                }
                _ => {}
            },
            (Self::Bounded(a, b), c) | (c, Self::Bounded(a, b)) => {
                *self = Self::Bounded(
                    Rc::new(Self::OffsetNeg(take(a), Rc::new(c.clone())).simplify()),
                    Rc::new(Self::OffsetNeg(take(b), Rc::new(take(c))).simplify()),
                )
            }
            (Self::Either(a, b), c) | (c, Self::Either(a, b)) => {
                *self = Self::Either(
                    Rc::new(Self::OffsetNeg(take(a), Rc::new(c.clone()))),
                    Rc::new(Self::OffsetNeg(take(b), Rc::new(take(c)))),
                )
            }
            (Self::Offset(a, b), c) => match (&**b, c) {
                (Self::Const(b), Self::Const(c)) if b == c => *self = (**a).clone(),
                (Self::Const(b), Self::Const(c)) => {
                    *self = Self::Offset(take(a), Rc::new(Self::Const(b.wrapping_sub(*c))))
                }
                _ => {}
            },
            _ => {}
        }
    }

    /// Simplify a symbolic value according to some rewriting rules
    pub fn simplify_impl(&mut self) {
        if let Some(result) = SIMPLIFICATION_CACHE.with(|cache| cache.borrow().get(&self).cloned())
        {
            *self = result.clone();
            return;
        }

        let cache_key = self.clone();

        match self {
            Self::Special(_) | Self::Unknown | Self::Const(_) | Self::Bottom => {}
            Self::Offset(_, _) => self.simplify_offset_impl(),
            Self::OffsetNeg(_, _) => self.simplify_offset_neg_impl(),
            Self::Scale(_, 0) => {
                *self = Self::Const(0);
            }
            Self::Scale(a, 1) => {
                let a = Rc::make_mut(a);
                a.simplify_impl();
                *self = take(&mut *a);
            }
            Self::Scale(a, scale) => {
                let a = Rc::make_mut(a);
                a.simplify_impl();

                match a {
                    Self::Bottom => *self = Self::Bottom,
                    Self::Const(a) => *self = Self::Const((*a as u64).wrapping_mul(*scale) as i64),
                    Self::Scale(_, inner_scale) => match inner_scale.checked_mul(*scale) {
                        Some(scale) => *inner_scale = scale,
                        // For overflows, short-circuit to unknown
                        None => *self = Self::Unknown,
                    },
                    Self::Offset(a, b) => {
                        *self = Self::Offset(
                            Rc::new(Self::Scale(take(a), *scale)),
                            Rc::new(Self::Scale(take(b), *scale)),
                        );
                    }
                    Self::OffsetNeg(a, b) => {
                        *self = Self::OffsetNeg(
                            Rc::new(Self::Scale(take(a), *scale)),
                            Rc::new(Self::Scale(take(b), *scale)),
                        );
                    }
                    Self::Bounded(a, b) => {
                        *self = Self::Bounded(
                            Rc::new(Self::Scale(take(a), *scale)),
                            Rc::new(Self::Scale(take(b), *scale)),
                        );
                    }
                    Self::Either(a, b) => {
                        *self = Self::Either(
                            Rc::new(Self::Scale(take(a), *scale)),
                            Rc::new(Self::Scale(take(b), *scale)),
                        );
                    }
                    _ => {}
                }
            }
            Self::Load(ptr) => {
                let ptr = Rc::make_mut(ptr);
                ptr.simplify_impl();
                if let Self::Bottom = ptr {
                    *self = Self::Bottom;
                }
            }
            Self::Bounded(a, b) => {
                let a = Rc::make_mut(a);
                let b = Rc::make_mut(b);
                a.simplify_impl();
                b.simplify_impl();

                match (a, b) {
                    (Self::Bottom, _) | (_, Self::Bottom) => *self = Self::Bottom,
                    (Self::Bounded(a, _), c) if a.ordered() > c.ordered() => *self = Self::Bottom,
                    (c, Self::Bounded(_, a)) if c.ordered() >= a.ordered() => *self = Self::Bottom,
                    (Self::Bounded(a, b), c) if b.is_unknown() => {
                        *self = Self::Bounded(take(a), Rc::new(take(c)))
                    }
                    (Self::Bounded(a, b), c)
                        if b.ordered() == c.ordered() || b.ordered() < c.ordered() =>
                    {
                        *self = Self::Bounded(take(a), take(b))
                    }
                    (Self::Bounded(a, b), c)
                        if c.ordered() == b.ordered() || c.ordered() < b.ordered() =>
                    {
                        *self = Self::Bounded(take(a), Rc::new(take(c)))
                    }
                    (c, Self::Bounded(a, b)) if a.ordered() == c.ordered() => {
                        *self = Self::Bounded(take(a), take(b))
                    }
                    _ => {}
                }
            }
            Self::Either(a, b) => {
                let a = Rc::make_mut(a);
                let b = Rc::make_mut(b);
                a.simplify_impl();
                b.simplify_impl();

                match (a, b) {
                    (Self::Either(a, b), c) | (c, Self::Either(a, b)) => {
                        if &**a == c {
                            *self = Self::Either(take(b), Rc::new(take(c)));
                        } else if &**b == c {
                            *self = Self::Either(take(a), Rc::new(take(c)));
                        }
                    }
                    (Self::Bottom, a) | (a, Self::Bottom) => *self = take(a),
                    (a, b) if a == b => *self = take(a),
                    _ => {}
                }
            }
        }

        self.trunc_load_depth(MAX_LOAD_DEPTH);
        self.simplify_load_from_bounded_ptr();

        SIMPLIFICATION_CACHE.with(|cache| {
            let mut cache = cache.borrow_mut();
            cache.insert(cache_key, self.clone());
        });
    }

    /// Simplify a value and return it
    pub fn simplify(mut self) -> Self {
        self.simplify_impl();
        self
    }

    fn simplify_load_from_bounded_ptr(&mut self) {
        let Self::Bounded(l, u) = self else {
            return;
        };

        match &mut *Rc::make_mut(l) {
            Self::Bounded(l1, u1) => {
                if u1.contains_unknown() {
                    if let Self::Load(_) = &**u1 {
                        *self = Self::Bounded(
                            Rc::new(Self::Bounded(
                                l1.clone(),
                                Rc::new(Self::Load(Rc::new(Self::Unknown))),
                            )),
                            u.clone(),
                        );
                    }
                }
            }
            Self::Offset(a, b) => {
                // if one of the values contains unknown, we need it to be in b
                if a.contains_unknown() {
                    swap(a, b);
                }
                if b.contains_unknown() {
                    if let Self::Load(_) = &**b {
                        *self = Self::Bounded(
                            Rc::new(Self::Offset(
                                a.clone(),
                                Rc::new(Self::Load(Rc::new(Self::Unknown))),
                            )),
                            u.clone(),
                        );
                        return;
                    }
                }
            }
            _ => {}
        }
    }

    /// Removes zero from (0 | val)
    pub fn simplify_either_or_null(&mut self) {
        let Self::Either(a, b) = self else {
            return;
        };
        match (&**a, &**b) {
            (Self::Const(0), a) | (a, Self::Const(0)) => *self = a.clone(),
            _ => {}
        }
    }

    /// Simplifies the following pattern:
    /// Load(0 | ptr) -> Load(ptr)
    /// We can do this, as loading from 0 will trap and execution will not reach the point where we encounter this
    pub fn simplify_load_from_val_or_null(&mut self) {
        if let Self::Load(ptr) = self {
            let ptr = Rc::make_mut(ptr);
            ptr.simplify_either_or_null();
        }
    }

    /// Check if one value includes the other
    pub fn is_included(&self, (min, max): (&Self, &Self)) -> bool {
        self.ordered() >= min.ordered() && self.ordered() < max.ordered()
    }

    /// Return an ordered version of this symbolic value
    pub fn ordered(&self) -> OrderedSymbolicValue {
        OrderedSymbolicValue(self)
    }

    /// Check if self is unknown
    pub fn is_unknown(&self) -> bool {
        matches!(self, Self::Unknown)
    }

    /// Return true if `self` is either `bounded(unknown, b)` or `bounded(a, unknown)`
    pub fn is_lower_upper_bound(&self) -> bool {
        match self {
            Self::Bounded(a, b) => a.is_unknown() || b.is_unknown(),
            _ => false,
        }
    }

    /// Truncate a value at a given depth
    pub fn trunc_load_depth(&mut self, max_depth: usize) {
        if self.load_depth() < max_depth {
            return;
        }

        if max_depth == 0 {
            *self = Self::Unknown;
        }

        match self {
            SymbolicValue::Unknown
            | SymbolicValue::Special(_)
            | SymbolicValue::Const(_)
            | SymbolicValue::Bottom => {}
            SymbolicValue::Load(ptr) => {
                let ptr = Rc::make_mut(ptr);
                ptr.trunc_load_depth(max_depth - 1);
            }
            SymbolicValue::Scale(a, _) => {
                let a = Rc::make_mut(a);
                a.trunc_load_depth(max_depth);
            }
            SymbolicValue::Offset(a, b)
            | SymbolicValue::OffsetNeg(a, b)
            | SymbolicValue::Bounded(a, b)
            | SymbolicValue::Either(a, b) => {
                let a = Rc::make_mut(a);
                a.trunc_load_depth(max_depth);
                let b = Rc::make_mut(b);
                b.trunc_load_depth(max_depth);
            }
        }
    }

    /// load depth
    pub fn load_depth(&self) -> usize {
        match self {
            SymbolicValue::Unknown
            | SymbolicValue::Special(_)
            | SymbolicValue::Const(_)
            | SymbolicValue::Bottom => 0,
            SymbolicValue::Scale(a, _) | SymbolicValue::OffsetNeg(a, _) => a.load_depth(),
            SymbolicValue::Load(ptr) => 1 + ptr.load_depth(),
            SymbolicValue::Offset(a, b)
            | SymbolicValue::Bounded(a, b)
            | SymbolicValue::Either(a, b) => usize::max(a.load_depth(), b.load_depth()),
        }
    }

    /// Check if self contains unknown
    pub fn contains_unknown(&self) -> bool {
        match self {
            SymbolicValue::Unknown => true,
            SymbolicValue::Special(_) | SymbolicValue::Const(_) | SymbolicValue::Bottom => false,
            SymbolicValue::Offset(a, b)
            | SymbolicValue::Bounded(a, b)
            | SymbolicValue::Either(a, b)
            | SymbolicValue::OffsetNeg(a, b) => a.contains_unknown() || b.contains_unknown(),
            SymbolicValue::Scale(a, _) | SymbolicValue::Load(a) => a.contains_unknown(),
        }
    }

    fn is_offset(&self) -> bool {
        matches!(self, Self::Offset(_, _))
    }

    fn is_const(&self) -> bool {
        matches!(self, Self::Const(_))
    }

    /// If `self` is an Offset or OffsetNeg with a constant value, extract the constant
    pub fn extract_const_offset(&self) -> Option<(&Self, i64)> {
        // if self.simplify has been called, only the very last operand should be a const
        match self {
            outer @ Self::Offset(a, b) | outer @ Self::OffsetNeg(a, b) if b.is_const() => {
                let Self::Const(c) = &**b else {
                    unreachable!();
                };
                let mut c = *c;
                if matches!(outer, Self::OffsetNeg(_, _)) {
                    c = c.wrapping_neg();
                }

                Some((&**a, c))
            }
            _ => None,
        }
    }

    /// Checks if `self` is an offset with a constant value
    pub fn has_const_offset(&self) -> bool {
        match self {
            Self::Offset(_, offset) | Self::OffsetNeg(_, offset) => {
                matches!(&**offset, Self::Const(_))
            }
            _ => false,
        }
    }

    fn nested_offset_operands(&self) -> Vec<(Cow<Self>, bool)> {
        let mut operands = Vec::new();

        let mut worklist = VecDeque::new();
        worklist.push_back((self, false));

        while let Some((val, neg)) = worklist.pop_front() {
            if let Self::Offset(a, b) = val {
                worklist.push_back((a, neg ^ false));
                worklist.push_back((b, neg ^ false));
            } else if let Self::OffsetNeg(a, b) = val {
                worklist.push_back((a, neg ^ false));
                worklist.push_back((b, neg ^ true));
            } else {
                let operand = match val {
                    Self::Const(c) if *c < 0 => (Cow::Owned(SymbolicValue::Const(-*c)), !neg),
                    val => (Cow::Borrowed(val), neg),
                };
                operands.push(operand);
            }
        }

        operands
    }

    fn cmp_offset(&self, other: &Self) -> Option<CustomOrdering> {
        let mut lhs_operands = self.nested_offset_operands();
        let mut rhs_operands = other.nested_offset_operands();
        // we sort using structural comparison on the enum. This allows us to do this algorithm in O(n log(n)) instead
        // of O(n^2).
        // First sort by the value, then by the bool
        let cmp_func = |(a, a_neg): &(Cow<SymbolicValue>, bool),
                        (b, b_neg): &(Cow<SymbolicValue>, bool)| {
            let val_cmp = a.cmp(b);
            if let Ordering::Equal = val_cmp {
                a_neg.cmp(b_neg)
            } else {
                val_cmp
            }
        };
        lhs_operands.sort_by(cmp_func);
        rhs_operands.sort_by(cmp_func);

        let mut remove_indices = vec![];

        let mut i = 0;
        let mut j = 0;
        while i < lhs_operands.len() && j < rhs_operands.len() {
            let (lhs, lhs_neg) = &lhs_operands[i];
            let (rhs, rhs_neg) = &rhs_operands[j];

            if lhs.is_unknown() && rhs.is_unknown() {
                // we cannot compare unknown
                return None;
            }

            // we check for structural as well as symbolic equivalence here
            if (lhs == rhs || lhs.ordered() == rhs.ordered()) && lhs_neg == rhs_neg {
                remove_indices.push((i, j));
                i += 1;
                j += 1;
            } else {
                // this comparison is an autogenerated order over the structure of the enum itself, not the value
                // we do this so we can search for duplicates in linear time instead of O(n^2)
                if lhs < rhs {
                    i += 1;
                } else if lhs > rhs {
                    j += 1;
                } else if lhs_neg < rhs_neg {
                    i += 1;
                } else if lhs_neg > rhs_neg {
                    j += 1;
                } else {
                    unimplemented!("lhs: {lhs}\nrhs: {rhs}")
                }
            }
        }

        for (removed, (i, j)) in remove_indices.iter().enumerate() {
            lhs_operands.remove(*i - removed);
            rhs_operands.remove(*j - removed);
        }

        if lhs_operands.is_empty() && rhs_operands.is_empty() {
            return Some(CustomOrdering::Equal);
        }
        if lhs_operands.is_empty() {
            // we assume that here we only have negative operands but the whole product is not negative, unless all
            // operands are.
            if rhs_operands.iter().all(|(_, is_negative)| *is_negative) {
                return Some(CustomOrdering::Greater);
            }
            return Some(CustomOrdering::Less);
        }
        if rhs_operands.is_empty() {
            if lhs_operands.iter().all(|(_, is_negative)| *is_negative) {
                return Some(CustomOrdering::Less);
            }
            return Some(CustomOrdering::Greater);
        }

        // we only handle the case when lhs and rhs have both one element
        if lhs_operands.len() == 1 && rhs_operands.len() == 1 {
            let (lhs, lhs_neg) = lhs_operands.first().unwrap();
            let (rhs, rhs_neg) = rhs_operands.first().unwrap();

            match (*lhs_neg, *rhs_neg) {
                (false, false) => lhs.ordered().fuzzy_partial_cmp(&rhs.ordered()),
                (true, true) => rhs.ordered().fuzzy_partial_cmp(&lhs.ordered()),
                _ => None,
            }
        } else {
            None
        }
    }
}

/// Ordered symbolic value
#[derive(Debug, Copy, Clone)]
pub struct OrderedSymbolicValue<'a>(&'a SymbolicValue);

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
enum CustomOrdering {
    Less,
    LessEqual,
    Equal,
    GreaterEqual,
    Greater,
}

impl From<Ordering> for CustomOrdering {
    fn from(value: Ordering) -> Self {
        match value {
            Ordering::Less => Self::Less,
            Ordering::Equal => Self::Equal,
            Ordering::Greater => Self::Greater,
        }
    }
}

impl<'a> Display for OrderedSymbolicValue<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl<'a> PartialEq for OrderedSymbolicValue<'a> {
    fn eq(&self, other: &Self) -> bool {
        matches!(self.fuzzy_partial_cmp(other), Some(CustomOrdering::Equal))
    }
}

impl<'a> OrderedSymbolicValue<'a> {
    fn fuzzy_partial_cmp(&self, other: &Self) -> Option<CustomOrdering> {
        if let Some(result) = COMPARISON_CACHE.with(|cache| {
            cache
                .borrow()
                .get(self.0)
                .and_then(|inner| inner.get(other.0))
                .copied()
        }) {
            return result;
        }

        let ordering = match (self.0, other.0) {
            (SymbolicValue::Special(a), SymbolicValue::Special(b)) if a == b => {
                Some(CustomOrdering::Equal)
            }
            (SymbolicValue::Bottom, SymbolicValue::Bottom) => Some(CustomOrdering::Equal),
            (SymbolicValue::Bottom, _) | (_, SymbolicValue::Bottom) => None,
            (SymbolicValue::Unknown, _) | (_, SymbolicValue::Unknown) => None,
            (SymbolicValue::Const(c1), SymbolicValue::Const(c2)) => {
                // we only support unsigned comparisons
                let c1 = *c1 as usize;
                let c2 = *c2 as usize;
                c1.partial_cmp(&c2).map(CustomOrdering::from)
            }
            (SymbolicValue::Bounded(a, b), SymbolicValue::Bounded(c, d)) => {
                let a = a.ordered();
                let b = b.ordered();
                let c = c.ordered();
                let d = d.ordered();
                if b <= c {
                    Some(CustomOrdering::Less)
                } else if a >= d {
                    Some(CustomOrdering::Greater)
                } else if a == c && b == d {
                    Some(CustomOrdering::Equal)
                } else if b <= d {
                    Some(CustomOrdering::LessEqual)
                } else if a >= c {
                    Some(CustomOrdering::GreaterEqual)
                } else {
                    None
                }
            }
            (SymbolicValue::Bounded(a, b), c) => {
                let a = a.ordered();
                let b = b.ordered();
                let c = c.ordered();

                if b <= c {
                    Some(CustomOrdering::Less)
                } else if c < a {
                    Some(CustomOrdering::Greater)
                } else if c == a || c >= a && c < b {
                    Some(CustomOrdering::Equal)
                } else if a <= c {
                    Some(CustomOrdering::LessEqual)
                } else if b >= c {
                    Some(CustomOrdering::GreaterEqual)
                } else {
                    None
                }
            }
            (c, SymbolicValue::Bounded(a, b)) => {
                let a = a.ordered();
                let c = c.ordered();
                let b = b.ordered();

                if c < a {
                    Some(CustomOrdering::Less)
                } else if c >= b {
                    Some(CustomOrdering::Greater)
                } else if c == a || c >= a && c < b {
                    Some(CustomOrdering::Equal)
                } else if c <= b {
                    Some(CustomOrdering::LessEqual)
                } else if c >= a {
                    Some(CustomOrdering::GreaterEqual)
                } else {
                    None
                }
            }
            (SymbolicValue::Either(a, b), c) => {
                let cmp1 = a.ordered().fuzzy_partial_cmp(&c.ordered());
                let cmp2 = b.ordered().fuzzy_partial_cmp(&c.ordered());
                match (cmp1, cmp2) {
                    (Some(CustomOrdering::Equal), Some(CustomOrdering::Equal)) => {
                        Some(CustomOrdering::Equal)
                    }
                    (Some(CustomOrdering::Equal), a) | (a, Some(CustomOrdering::Equal)) => a,
                    (cmp1, cmp2) if cmp1 == cmp2 => cmp1,
                    _ => None,
                }
            }
            (c, SymbolicValue::Either(a, b)) => {
                let cmp1 = c.ordered().fuzzy_partial_cmp(&a.ordered());
                let cmp2 = c.ordered().fuzzy_partial_cmp(&b.ordered());
                match (cmp1, cmp2) {
                    (Some(CustomOrdering::Equal), Some(CustomOrdering::Equal)) => {
                        Some(CustomOrdering::Equal)
                    }
                    (Some(CustomOrdering::Equal), a) | (a, Some(CustomOrdering::Equal)) => a,
                    (cmp1, cmp2) if cmp1 == cmp2 => cmp1,
                    _ => None,
                }
            }
            (SymbolicValue::Offset(_, _), _)
            | (_, SymbolicValue::Offset(_, _))
            | (SymbolicValue::OffsetNeg(_, _), _)
            | (_, SymbolicValue::OffsetNeg(_, _)) => self.0.cmp_offset(other.0),
            (SymbolicValue::Scale(val1, scale1), SymbolicValue::Scale(val2, scale2)) => {
                debug_assert!(*scale1 > 1);
                debug_assert!(*scale2 > 1);
                let val1 = val1.ordered();
                let val2 = val2.ordered();
                if val1 == val2 {
                    scale1.partial_cmp(scale2).map(CustomOrdering::from)
                } else if val1 > val2 && scale1 >= scale2 {
                    Some(CustomOrdering::Greater)
                } else if val1 < val2 && scale1 <= scale2 {
                    Some(CustomOrdering::Less)
                } else {
                    None
                }
            }
            (SymbolicValue::Scale(a, scale), b) => {
                debug_assert!(*scale > 1);
                if a.ordered() >= b.ordered() {
                    Some(CustomOrdering::Greater)
                } else {
                    None
                }
            }
            (a, SymbolicValue::Scale(b, scale)) => {
                debug_assert!(*scale > 1);
                if b.ordered() >= a.ordered() {
                    Some(CustomOrdering::Less)
                } else {
                    None
                }
            }
            (SymbolicValue::Load(ptr1), SymbolicValue::Load(ptr2)) => {
                if let Some(CustomOrdering::Equal) =
                    ptr1.ordered().fuzzy_partial_cmp(&ptr2.ordered())
                {
                    Some(CustomOrdering::Equal)
                } else {
                    None
                }
            }
            _ => None,
        };

        COMPARISON_CACHE.with(|cache| {
            let mut cache = cache.borrow_mut();
            cache
                .entry(self.0.clone())
                .or_default()
                .insert(other.0.clone(), ordering);
        });

        ordering
    }
}

impl<'a> PartialOrd for OrderedSymbolicValue<'a> {
    fn partial_cmp(&self, _other: &Self) -> Option<Ordering> {
        unimplemented!(
            "do not call this function directly. Instead, call the gt/ge/lt/le functions"
        )
    }

    fn lt(&self, other: &Self) -> bool {
        matches!(self.fuzzy_partial_cmp(other), Some(CustomOrdering::Less))
    }

    fn le(&self, other: &Self) -> bool {
        matches!(
            self.fuzzy_partial_cmp(other),
            Some(CustomOrdering::Less)
                | Some(CustomOrdering::LessEqual)
                | Some(CustomOrdering::Equal)
        )
    }

    fn gt(&self, other: &Self) -> bool {
        matches!(self.fuzzy_partial_cmp(other), Some(CustomOrdering::Greater))
    }

    fn ge(&self, other: &Self) -> bool {
        matches!(
            self.fuzzy_partial_cmp(other),
            Some(CustomOrdering::Greater)
                | Some(CustomOrdering::GreaterEqual)
                | Some(CustomOrdering::Equal)
        )
    }
}

impl<'a> Deref for OrderedSymbolicValue<'a> {
    type Target = SymbolicValue;

    fn deref(&self) -> &Self::Target {
        self.0
    }
}

impl Debug for SymbolicValue {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        write!(f, "{self}")
    }
}

impl Display for SymbolicValue {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self {
            SymbolicValue::Special(val) => write!(f, "{val}"),
            SymbolicValue::Const(val) => match val {
                // we pretty-print some useful constants
                255 => write!(f, "u8::MAX"),
                65535 => write!(f, "u16::MAX"),
                4294967295 => write!(f, "u32::MAX"),
                // -128 => write!(f, "i8::MIN"),
                127 => write!(f, "i8::MAX"),
                // -32768 => write!(f, "i16::MIN"),
                32767 => write!(f, "i16::MAX"),
                // -2147483648 => write!(f, "i32::MIN"),
                2147483647 => write!(f, "i32::MAX"),
                // -9223372036854775808 => write!(f, "i64::MIN"),
                9223372036854775807 => write!(f, "i64::MAX"),
                _ => write!(f, "{val}"),
            },
            SymbolicValue::Scale(val, scale) => write!(f, "({val} * {scale})"),
            SymbolicValue::Offset(base, offset) => write!(f, "({base} + {offset})"),
            SymbolicValue::OffsetNeg(base, offset) => write!(f, "({base} - {offset})"),
            SymbolicValue::Load(ptr) => write!(f, "*{ptr}"),
            SymbolicValue::Bounded(a, b) => {
                write!(f, "umin({}, {})", a, b)
            }
            SymbolicValue::Unknown => write!(f, "unknown"),
            SymbolicValue::Either(a, b) => write!(f, "({a} | {b})"),
            SymbolicValue::Bottom => write!(f, "bottom"),
        }
    }
}

impl Debug for SpecialValue {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self)
    }
}

impl Display for SpecialValue {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self {
            SpecialValue::VmCtx => write!(f, "vmctx"),
            SpecialValue::RetAreaPtr => write!(f, "ret_area_ptr"),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::mem_verifier::symbolic_value::{CustomOrdering, SpecialValue, SymbolicValue};
    use alloc::rc::Rc;

    #[test]
    fn test_simplify_offset_const() {
        assert_eq!(
            SymbolicValue::Offset(
                Rc::new(SymbolicValue::Const(10)),
                Rc::new(SymbolicValue::Special(SpecialValue::VmCtx)),
            )
            .simplify(),
            SymbolicValue::Offset(
                Rc::new(SymbolicValue::Special(SpecialValue::VmCtx)),
                Rc::new(SymbolicValue::Const(10)),
            ),
        );
    }

    #[test]
    fn test_simplify_offset_zero() {
        assert_eq!(
            SymbolicValue::Offset(
                Rc::new(SymbolicValue::Unknown),
                Rc::new(SymbolicValue::Const(0)),
            )
            .simplify(),
            SymbolicValue::Unknown,
        );
    }

    #[test]
    fn test_simplify_offset_nested() {
        assert_eq!(
            SymbolicValue::Offset(
                Rc::new(SymbolicValue::Offset(
                    Rc::new(SymbolicValue::Offset(
                        Rc::new(SymbolicValue::Const(2)),
                        Rc::new(SymbolicValue::Special(SpecialValue::VmCtx)),
                    )),
                    Rc::new(SymbolicValue::Const(10))
                )),
                Rc::new(SymbolicValue::Const(10)),
            )
            .simplify(),
            SymbolicValue::Offset(
                Rc::new(SymbolicValue::Special(SpecialValue::VmCtx)),
                Rc::new(SymbolicValue::Const(22)),
            ),
        );
    }

    #[test]
    fn test_comparison_const() {
        assert!(SymbolicValue::Const(10).ordered() < SymbolicValue::Const(11).ordered());
    }

    #[test]
    fn test_comparison_unknown() {
        assert!(matches!(
            SymbolicValue::Unknown
                .ordered()
                .fuzzy_partial_cmp(&SymbolicValue::Unknown.ordered()),
            None
        ));
        assert!(matches!(
            SymbolicValue::Unknown
                .ordered()
                .fuzzy_partial_cmp(&SymbolicValue::Special(SpecialValue::VmCtx).ordered()),
            None
        ));
        assert!(matches!(
            SymbolicValue::Unknown
                .ordered()
                .fuzzy_partial_cmp(&SymbolicValue::Bottom.ordered()),
            None
        ));
        assert!(matches!(
            SymbolicValue::Unknown
                .ordered()
                .fuzzy_partial_cmp(&SymbolicValue::Const(5).ordered()),
            None
        ));
    }

    #[test]
    fn test_comparison_offset() {
        assert!(
            SymbolicValue::Offset(
                Rc::new(SymbolicValue::Special(SpecialValue::VmCtx)),
                Rc::new(SymbolicValue::Const(1))
            )
            .ordered()
                < SymbolicValue::Offset(
                    Rc::new(SymbolicValue::Special(SpecialValue::VmCtx)),
                    Rc::new(SymbolicValue::Const(2))
                )
                .ordered()
        );
    }

    #[test]
    fn test_comparison_offset_2() {
        assert!(
            SymbolicValue::Offset(
                Rc::new(SymbolicValue::Const(1)),
                Rc::new(SymbolicValue::Special(SpecialValue::VmCtx)),
            )
            .ordered()
                < SymbolicValue::Offset(
                    Rc::new(SymbolicValue::Special(SpecialValue::VmCtx)),
                    Rc::new(SymbolicValue::Const(2)),
                )
                .ordered()
        );
    }

    #[test]
    fn test_comparison_offset_unknown() {
        let val1 = SymbolicValue::Offset(
            Rc::new(SymbolicValue::Unknown),
            Rc::new(SymbolicValue::Const(1)),
        );
        let val2 = SymbolicValue::Offset(
            Rc::new(SymbolicValue::Unknown),
            Rc::new(SymbolicValue::Const(2)),
        );
        assert!(matches!(
            val1.ordered().fuzzy_partial_cmp(&val2.ordered()),
            None
        ));
        assert!(matches!(
            val1.ordered().fuzzy_partial_cmp(&val2.ordered()),
            None
        ));
        assert!(matches!(
            val1.ordered().fuzzy_partial_cmp(&val2.ordered()),
            None
        ));
    }

    #[test]
    fn test_cmp_offset() {
        assert!(
            SymbolicValue::Offset(
                Rc::new(SymbolicValue::Special(SpecialValue::VmCtx)),
                Rc::new(SymbolicValue::Const(32))
            )
            .ordered()
                >= SymbolicValue::Special(SpecialValue::VmCtx).ordered()
        );
        assert!(
            SymbolicValue::Special(SpecialValue::VmCtx).ordered()
                < SymbolicValue::Offset(
                    Rc::new(SymbolicValue::Special(SpecialValue::VmCtx)),
                    Rc::new(SymbolicValue::Const(32))
                )
                .ordered()
        );
    }

    #[test]
    fn test_cmp_offset_2() {
        assert!(
            SymbolicValue::Offset(
                Rc::new(SymbolicValue::Special(SpecialValue::VmCtx)),
                Rc::new(SymbolicValue::Const(32))
            )
            .ordered()
                < SymbolicValue::Offset(
                    Rc::new(SymbolicValue::Special(SpecialValue::VmCtx)),
                    Rc::new(SymbolicValue::Const(64))
                )
                .ordered()
        );
    }

    #[test]
    fn test_load_offset() {
        assert_eq!(
            SymbolicValue::Load(Rc::new(SymbolicValue::Offset(
                Rc::new(SymbolicValue::Special(SpecialValue::VmCtx)),
                Rc::new(SymbolicValue::Const(80)),
            )))
            .ordered()
            .fuzzy_partial_cmp(
                &SymbolicValue::Offset(
                    Rc::new(SymbolicValue::Load(Rc::new(SymbolicValue::Offset(
                        Rc::new(SymbolicValue::Special(SpecialValue::VmCtx)),
                        Rc::new(SymbolicValue::Const(80)),
                    )))),
                    Rc::new(SymbolicValue::Load(Rc::new(SymbolicValue::Offset(
                        Rc::new(SymbolicValue::Special(SpecialValue::VmCtx)),
                        Rc::new(SymbolicValue::Const(88)),
                    ))))
                )
                .ordered()
            ),
            Some(CustomOrdering::Less)
        );
    }

    #[test]
    fn test_comparison_bound_neg_offset() {
        assert!(
            SymbolicValue::OffsetNeg(
                Rc::new(SymbolicValue::Load(Rc::new(SymbolicValue::Special(
                    SpecialValue::VmCtx
                )))),
                Rc::new(SymbolicValue::Const(4))
            )
            .ordered()
                < SymbolicValue::Load(Rc::new(SymbolicValue::Special(SpecialValue::VmCtx)))
                    .ordered()
        )
    }

    #[test]
    fn test_offset_unknown() {
        assert_eq!(
            SymbolicValue::Offset(
                Rc::new(SymbolicValue::Unknown),
                Rc::new(SymbolicValue::Unknown),
            )
            .simplify(),
            SymbolicValue::Unknown,
        )
    }

    #[test]
    fn test_load_neq() {
        let load1 = SymbolicValue::Special(SpecialValue::VmCtx).load();
        let load2 = SymbolicValue::Special(SpecialValue::VmCtx)
            .offset_const(80)
            .load();

        assert!(!(load1.ordered() <= load2.ordered()));
        assert!(!(load1.ordered() >= load2.ordered()));
        assert!(!(load1.ordered() < load2.ordered()));
        assert!(!(load1.ordered() > load2.ordered()));
        assert!(!(load1.ordered() == load2.ordered()));
    }

    #[test]
    fn test_simplify_nested_umin() {
        let nested = SymbolicValue::Bounded(
            Rc::new(SymbolicValue::Bounded(
                Rc::new(SymbolicValue::Special(SpecialValue::VmCtx).load()),
                Rc::new(
                    SymbolicValue::Special(SpecialValue::VmCtx)
                        .offset_const(80)
                        .load(),
                ),
            )),
            Rc::new(
                SymbolicValue::Special(SpecialValue::VmCtx)
                    .offset_const(80)
                    .load(),
            ),
        );

        assert_eq!(
            nested.simplify(),
            SymbolicValue::Bounded(
                Rc::new(SymbolicValue::Special(SpecialValue::VmCtx).load()),
                Rc::new(
                    SymbolicValue::Special(SpecialValue::VmCtx)
                        .offset_const(80)
                        .load()
                )
            )
        )
    }

    #[test]
    fn test_simplify_nested_umin_offset() {
        let val = SymbolicValue::Bounded(
            Rc::new(SymbolicValue::Unknown),
            Rc::new(SymbolicValue::Offset(
                Rc::new(SymbolicValue::Load(Rc::new(SymbolicValue::Offset(
                    Rc::new(SymbolicValue::Special(SpecialValue::VmCtx)),
                    Rc::new(SymbolicValue::Const(80)),
                )))),
                Rc::new(SymbolicValue::Const(0)),
            )),
        );

        assert_eq!(
            val.simplify(),
            SymbolicValue::Bounded(
                Rc::new(SymbolicValue::Unknown),
                Rc::new(SymbolicValue::Load(Rc::new(SymbolicValue::Offset(
                    Rc::new(SymbolicValue::Special(SpecialValue::VmCtx)),
                    Rc::new(SymbolicValue::Const(80)),
                ))))
            )
        );
    }

    #[test]
    fn test_offset_switched_eq() {
        let base = SymbolicValue::Special(SpecialValue::VmCtx)
            .offset_const(80)
            .load();
        let len = SymbolicValue::Special(SpecialValue::VmCtx)
            .offset_const(88)
            .load();

        assert!(
            base.clone().offset(len.clone()).ordered()
                == len.clone().offset(base.clone()).ordered()
        )
    }

    #[test]
    fn test_offset_in_bounds() {
        let base = SymbolicValue::Special(SpecialValue::VmCtx)
            .offset_const(96)
            .load();
        let bound = SymbolicValue::Special(SpecialValue::VmCtx)
            .offset_const(112)
            .load();

        let a = SymbolicValue::Bounded(
            Rc::new(base.clone().offset(SymbolicValue::Unknown)),
            Rc::new(bound.clone().offset_const_neg(4).offset(base.clone())),
        );
        assert!(a.ordered() >= base.ordered());
        assert!(a.ordered() <= bound.clone().offset(base.clone()).ordered());
        assert!(a.ordered() <= base.clone().offset(bound.clone()).ordered());
    }

    #[test]
    fn test_offset_nested() {
        let base = SymbolicValue::Special(SpecialValue::VmCtx)
            .offset_const(80)
            .load();
        let bound = SymbolicValue::Special(SpecialValue::VmCtx)
            .offset_const(88)
            .load();
        let access_size = SymbolicValue::Const(4);

        assert_eq!(
            SymbolicValue::OffsetNeg(
                Rc::new(SymbolicValue::Offset(
                    Rc::new(base.clone()),
                    Rc::new(bound.clone())
                )),
                Rc::new(access_size.clone())
            )
            .ordered()
            .fuzzy_partial_cmp(
                &SymbolicValue::OffsetNeg(
                    Rc::new(SymbolicValue::Offset(
                        Rc::new(bound.clone()),
                        Rc::new(base.clone()),
                    )),
                    Rc::new(access_size.clone())
                )
                .ordered()
            ),
            Some(CustomOrdering::Equal)
        )
    }

    #[test]
    fn test_umin_lt() {
        let a = SymbolicValue::Bounded(
            Rc::new(SymbolicValue::Unknown),
            Rc::new(SymbolicValue::Special(SpecialValue::VmCtx).load()),
        );

        assert!(a.ordered() <= SymbolicValue::Special(SpecialValue::VmCtx).load().ordered())
    }

    #[test]
    fn simplify_unknown_bounded() {
        let lower = SymbolicValue::Special(SpecialValue::VmCtx)
            .offset_const(72)
            .load();
        let upper = SymbolicValue::Special(SpecialValue::VmCtx)
            .offset_const(80)
            .load();

        let a = SymbolicValue::Bounded(
            Rc::new(SymbolicValue::Bounded(
                Rc::new(lower.clone()),
                Rc::new(SymbolicValue::Unknown),
            )),
            Rc::new(upper.clone()),
        );

        assert_eq!(
            a.simplify(),
            SymbolicValue::Bounded(Rc::new(lower.clone()), Rc::new(upper.clone()),)
        )
    }

    #[test]
    fn simplify_bound() {
        let a = SymbolicValue::Bounded(
            Rc::new(SymbolicValue::Unknown),
            Rc::new(SymbolicValue::Bounded(
                Rc::new(SymbolicValue::Special(SpecialValue::VmCtx).load()),
                Rc::new(SymbolicValue::Const(u32::MAX.into())),
            )),
        );

        assert_eq!(a.clone().simplify(), a);
    }

    #[test]
    fn test_cmp_offset_3() {
        let base = SymbolicValue::Special(SpecialValue::VmCtx)
            .offset_const(72)
            .load();
        let bound = SymbolicValue::Special(SpecialValue::VmCtx)
            .offset_const(80)
            .load()
            .offset(base.clone());

        assert!(base.ordered() <= bound.ordered());
    }

    #[test]
    fn test_cmp_scaled() {
        let a = SymbolicValue::Special(SpecialValue::VmCtx).load();
        let b = a.clone().scaled(8);

        assert!(a.ordered() < b.ordered());
        assert!(b.ordered() > a.ordered());

        let a = SymbolicValue::Unknown.load();
        let b = a.clone().scaled(8);
        assert!(!(a.ordered() > b.ordered()));
        assert!(!(b.ordered() < a.ordered()));
    }

    #[test]
    fn cmp_umin() {
        let base = SymbolicValue::Special(SpecialValue::VmCtx)
            .offset_const(72)
            .load();
        let len = SymbolicValue::Special(SpecialValue::VmCtx)
            .offset_const(80)
            .load()
            .scaled(8);

        let umin = SymbolicValue::Bounded(
            Rc::new(SymbolicValue::Unknown.offset(base.clone())),
            Rc::new(len.clone().offset(base.clone())),
        );

        assert_eq!(len.ordered(), len.ordered());

        assert_eq!(
            format!("{umin}"),
            "umin((unknown + *(vmctx + 72)), ((*(vmctx + 80) * 8) + *(vmctx + 72)))"
        );
        assert!(umin.ordered() >= base.ordered());
        assert!(umin.ordered() <= len.clone().offset(base.clone()).ordered());
    }

    #[test]
    fn test_cmp_offset_4() {
        let base = SymbolicValue::Special(SpecialValue::VmCtx)
            .offset_const(80)
            .load();
        let bound = SymbolicValue::Special(SpecialValue::VmCtx)
            .offset_const(88)
            .load();

        let a = bound.clone().offset(base.clone()).offset_const_neg(8);
        let b = base.clone().offset(bound.clone());

        assert!(a.ordered() <= b.ordered());
    }

    #[test]
    fn test_cmp_varptr() {
        let base = SymbolicValue::Special(SpecialValue::VmCtx)
            .offset_const(80)
            .load();
        let bound = SymbolicValue::Special(SpecialValue::VmCtx)
            .offset_const(88)
            .load();

        let ptr_range = SymbolicValue::Bounded(Rc::new(base), Rc::new(bound));

        let base = ptr_range.clone().load();
        let bound = ptr_range.clone().load().offset_const(80);

        let value = ptr_range.clone().load().offset_const(16);

        assert!(value.ordered() >= base.ordered());
        assert!(value.ordered() <= bound.ordered());
    }

    #[test]
    fn test_simplify_either_bottom() {
        let val = SymbolicValue::Either(
            Rc::new(SymbolicValue::Bottom),
            Rc::new(SymbolicValue::Special(SpecialValue::VmCtx)),
        )
        .simplify();

        assert_eq!(val, SymbolicValue::Special(SpecialValue::VmCtx))
    }

    #[test]
    fn test_leq() {
        let base = SymbolicValue::Special(SpecialValue::VmCtx)
            .offset_const(72)
            .load();
        let bound = SymbolicValue::Special(SpecialValue::VmCtx)
            .offset_const(80)
            .load()
            .scaled(8);

        let val = bound
            .clone()
            .offset(base.clone())
            .bound_upper(base.clone().offset_const(34359738360));

        assert_eq!(
            format!("{}", val),
            "umin(((*(vmctx + 80) * 8) + *(vmctx + 72)), (*(vmctx + 72) + 34359738360))"
        );

        let upper = base.clone().offset(bound.clone());
        assert_eq!(
            format!("{}", upper),
            "(*(vmctx + 72) + (*(vmctx + 80) * 8))"
        );

        assert!(val.ordered() <= upper.ordered());
    }

    #[test]
    fn test_bounded_const() {
        let val = SymbolicValue::Bounded(
            Rc::new(SymbolicValue::Const(242124)),
            Rc::new(SymbolicValue::Bounded(
                Rc::new(
                    SymbolicValue::Special(SpecialValue::VmCtx)
                        .offset_const(104)
                        .load()
                        .offset_const(8)
                        .load(),
                ),
                Rc::new(SymbolicValue::Const(u32::MAX.into())),
            )),
        );

        assert!(SymbolicValue::Const(242124).ordered() <= SymbolicValue::Const(242124).ordered());
        assert!(SymbolicValue::Const(242124).ordered() >= SymbolicValue::Const(242124).ordered());

        assert!(val.ordered() >= SymbolicValue::Const(242124).ordered());
    }

    #[test]
    fn test_const_geq() {
        let value = SymbolicValue::Bounded(
            Rc::new(SymbolicValue::Const(242124)),
            Rc::new(
                SymbolicValue::Special(SpecialValue::VmCtx)
                    .offset_const(104)
                    .load()
                    .offset_const(8)
                    .load(),
            ),
        );

        assert!(value.ordered() >= SymbolicValue::Const(242124).ordered());
        assert!(value.ordered() <= SymbolicValue::Const(242124).ordered());
    }

    #[test]
    fn simplify_umin_umin_const() {
        let val = SymbolicValue::Bounded(
            Rc::new(SymbolicValue::Bounded(
                Rc::new(SymbolicValue::Unknown),
                Rc::new(SymbolicValue::Const(10)),
            )),
            Rc::new(SymbolicValue::Const(20)),
        );
        assert_eq!(
            val.clone().simplify(),
            SymbolicValue::Bounded(
                Rc::new(SymbolicValue::Unknown),
                Rc::new(SymbolicValue::Const(10)),
            )
        );
    }

    #[test]
    fn test_load_from_ptr_or_null() {
        let mut load = SymbolicValue::Load(Rc::new(SymbolicValue::Either(
            Rc::new(SymbolicValue::Const(0)),
            Rc::new(
                SymbolicValue::Special(SpecialValue::VmCtx)
                    .offset_const(80)
                    .load(),
            ),
        )));

        load.simplify_load_from_val_or_null();

        assert_eq!(
            load,
            SymbolicValue::Load(Rc::new(
                SymbolicValue::Special(SpecialValue::VmCtx)
                    .offset_const(80)
                    .load()
            ))
        );
    }

    #[test]
    fn test_bounded_const_offset() {
        let base = SymbolicValue::Special(SpecialValue::VmCtx)
            .offset_const(736)
            .load();
        let len = SymbolicValue::Special(SpecialValue::VmCtx)
            .offset_const(744)
            .load();

        let a = SymbolicValue::Bounded(
            Rc::new(SymbolicValue::Unknown),
            Rc::new(SymbolicValue::OffsetNeg(
                Rc::new(SymbolicValue::Offset(
                    Rc::new(base.clone()),
                    Rc::new(len.clone()),
                )),
                Rc::new(SymbolicValue::Const(96)),
            )),
        );
        let b = SymbolicValue::OffsetNeg(
            Rc::new(SymbolicValue::Offset(
                Rc::new(base.clone()),
                Rc::new(len.clone()),
            )),
            Rc::new(SymbolicValue::Const(8)),
        );

        assert!(a.ordered() <= b.ordered());
    }

    #[test]
    fn test_bounded_const_const() {
        let x = SymbolicValue::Bounded(
            Rc::new(SymbolicValue::Bounded(
                Rc::new(SymbolicValue::Special(SpecialValue::VmCtx)),
                Rc::new(SymbolicValue::Const(10)),
            )),
            Rc::new(SymbolicValue::Const(5)),
        );
        assert_eq!(
            x.simplify(),
            SymbolicValue::Bounded(
                Rc::new(SymbolicValue::Special(SpecialValue::VmCtx)),
                Rc::new(SymbolicValue::Const(5)),
            )
        );
    }

    #[test]
    fn test_offset_neg_offset() {
        let x = SymbolicValue::Offset(
            Rc::new(SymbolicValue::OffsetNeg(
                Rc::new(SymbolicValue::Special(SpecialValue::VmCtx)),
                Rc::new(SymbolicValue::Const(4)),
            )),
            Rc::new(SymbolicValue::Const(8)),
        );

        assert_eq!(
            x.simplify(),
            SymbolicValue::Offset(
                Rc::new(SymbolicValue::Special(SpecialValue::VmCtx)),
                Rc::new(SymbolicValue::Const(4))
            )
        );
    }
}
