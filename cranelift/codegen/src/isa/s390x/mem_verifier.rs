//! S390X specific code to lift instructions to `SymbolicValue`s

use crate::isa::s390x::inst::Inst;
use crate::mem_verifier::assertions::ValueAssertion;
use crate::mem_verifier::capability::MemoryAccessCapability;
use crate::mem_verifier::verifier::{ConstraintEnv, Error, MemAccessVerifier, VerifierCtx};
use regalloc2::VReg;
use std::prelude::rust_2015::Vec;

/// Verify memory accesses
pub struct S390xMemAccessVerifier;

impl S390xMemAccessVerifier {
    /// Create a new instance of the verifier
    pub fn new() -> Self {
        Self {}
    }
}

impl MemAccessVerifier<Inst> for S390xMemAccessVerifier {
    fn verify_reg_assertion(
        &self,
        _reg: VReg,
        _assertion: &ValueAssertion,
        _ctx: VerifierCtx<Inst>,
    ) -> Result<(), Error> {
        todo!()
    }

    fn verify_memory_access(
        &self,
        _inst: &Inst,
        _capabilities: &[MemoryAccessCapability],
        _ctx: VerifierCtx<Inst>,
    ) -> Result<(), Error> {
        todo!()
    }

    fn get_outgoing_constraints(
        &self,
        _terminator: regalloc2::Inst,
        _ctx: VerifierCtx<Inst>,
    ) -> Result<Vec<ConstraintEnv>, Error> {
        todo!()
    }
}
