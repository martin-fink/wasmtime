use crate::fx::FxHashMap;
use crate::machinst::VCodeConstants;
use crate::mem_verifier::assertions::{RegOrConst, ValueAssertion};
use crate::mem_verifier::capability::MemoryAccessCapability;
use crate::mem_verifier::constraint::ValueConstraint;
use crate::MachInst;
use core::fmt::{Display, Formatter};
use regalloc2::{Inst, VReg};
use std::collections::HashMap;
use std::prelude::rust_2015::String;
use std::prelude::v1::Vec;

/// map which register definition maps to which instruction index
pub type DefMap = HashMap<VReg, Inst>;

/// Map from register to constraint
pub type ConstraintEnv = FxHashMap<RegOrConst, ValueConstraint>;

/// Context for the verifier
pub struct VerifierCtx<'a, I: MachInst> {
    /// Instruction data for all instructions dominating the instruction being checked
    pub insts: &'a [I],
    /// Map from register to instruction defining the register
    pub def_map: &'a DefMap,
    /// Alias map for vregs
    pub vreg_aliases: &'a FxHashMap<VReg, VReg>,
    /// Already verified constraints to be used to build SymbolicValues
    pub verified_constraints: &'a ConstraintEnv,
    /// Constants
    pub constants: &'a VCodeConstants,
}

/// Verify memory accesses
pub trait MemAccessVerifier<I: MachInst> {
    /// Verifies the annotation corresponding to the IR value of reg
    fn verify_reg_assertion(
        &self,
        reg: VReg,
        assertion: &ValueAssertion,
        ctx: VerifierCtx<I>,
    ) -> Result<(), Error>;

    /// Verify that a memory access matches one of the capabilities of this function
    fn verify_memory_access(
        &self,
        inst: &I,
        capabilities: &[MemoryAccessCapability],
        ctx: VerifierCtx<I>,
    ) -> Result<(), Error>;

    /// Get the outgoing constraints for a block
    fn get_outgoing_constraints(
        &self,
        terminator: Inst,
        ctx: VerifierCtx<I>,
    ) -> Result<Vec<ConstraintEnv>, Error>;
}

/// Represents an error while lifting from VCode to SymbolicValue
#[derive(Debug)]
pub struct Error {
    message: String,
}

impl Error {
    /// Create a new error
    pub fn new(message: String) -> Self {
        Self { message }
    }
}

impl Display for Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl std::error::Error for Error {}
