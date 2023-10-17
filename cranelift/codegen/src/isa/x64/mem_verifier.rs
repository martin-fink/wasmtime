//! X86 specific code to lift instructions to `SymbolicValue`s

use crate::fx::FxHashMap;
use crate::isa::x64::args::{
    AluRmiROpcode, Amode, Avx512Opcode, AvxOpcode, CmpOpcode, ExtMode, GprMem, GprMemImm, Imm8Reg,
    OperandSize, RegMem, RegMemImm, ShiftKind, SseOpcode, SyntheticAmode, XmmMem, XmmMemAligned,
    XmmMemAlignedImm, XmmMemImm, CC,
};
use crate::isa::x64::inst::regs;
use crate::isa::x64::lower::isle::generated_code::MInst;
use crate::isa::x64::Inst;
use crate::machinst;
use crate::machinst::{VCodeConstant, VCodeConstants};
use crate::mem_verifier::assertions::{RegOrConst, ValueAssertion};
use crate::mem_verifier::capability::MemoryAccessCapability;
use crate::mem_verifier::constraint::ValueConstraint;
use crate::mem_verifier::symbolic_value::{SymbolicValue, MAX_LOAD_DEPTH};
use crate::mem_verifier::trunc_i64_to_width;
use crate::mem_verifier::verifier::{ConstraintEnv, DefMap, Error, MemAccessVerifier, VerifierCtx};
use log::debug;
use regalloc2::VReg;
use std::collections::VecDeque;
use std::prelude::v1::{String, Vec};

fn get_inst_name(inst: &Inst) -> &'static str {
    match inst {
        Inst::Nop { .. } => "Nop",
        Inst::AluRmiR { .. } => "AluRmiR",
        Inst::AluRM { .. } => "AluRM",
        Inst::AluRmRVex { .. } => "AluRmRVex",
        Inst::AluConstOp { .. } => "AluConstOp",
        Inst::UnaryRmR { .. } => "UnaryRmR",
        Inst::UnaryRmRVex { .. } => "UnaryRmRVex",
        Inst::Not { .. } => "Not",
        Inst::Neg { .. } => "Neg",
        Inst::Div { .. } => "Div",
        Inst::Div8 { .. } => "Div8",
        Inst::MulHi { .. } => "MulHi",
        Inst::UMulLo { .. } => "UMulLo",
        Inst::CheckedSRemSeq { .. } => "CheckedSRemSeq",
        Inst::CheckedSRemSeq8 { .. } => "CheckedSRemSeq8",
        Inst::SignExtendData { .. } => "SignExtendData",
        Inst::Imm { .. } => "Imm",
        Inst::MovRR { .. } => "MovRR",
        Inst::MovFromPReg { .. } => "MovFromPReg",
        Inst::MovToPReg { .. } => "MovToPReg",
        Inst::MovzxRmR { .. } => "MovzxRmR",
        Inst::Mov64MR { .. } => "Mov64MR",
        Inst::LoadEffectiveAddress { .. } => "LoadEffectiveAddress",
        Inst::MovsxRmR { .. } => "MovsxRmR",
        Inst::MovImmM { .. } => "MovImmM",
        Inst::MovRM { .. } => "MovRM",
        Inst::ShiftR { .. } => "ShiftR",
        Inst::XmmRmiReg { .. } => "XmmRmiReg",
        Inst::CmpRmiR { .. } => "CmpRmiR",
        Inst::Setcc { .. } => "Setcc",
        Inst::Bswap { .. } => "Bswap",
        Inst::Cmove { .. } => "Cmove",
        Inst::XmmCmove { .. } => "XmmCmove",
        Inst::Push64 { .. } => "Push64",
        Inst::Pop64 { .. } => "Pop64",
        Inst::StackProbeLoop { .. } => "StackProbeLoop",
        Inst::XmmRmR { .. } => "XmmRmR",
        Inst::XmmRmRUnaligned { .. } => "XmmRmRUnaligned",
        Inst::XmmRmRBlend { .. } => "XmmRmRBlend",
        Inst::XmmRmiRVex { .. } => "XmmRmiRVex",
        Inst::XmmRmRImmVex { .. } => "XmmRmRImmVex",
        Inst::XmmVexPinsr { .. } => "XmmVexPinsr",
        Inst::XmmRmRVex3 { .. } => "XmmRmRVex3",
        Inst::XmmRmRBlendVex { .. } => "XmmRmRBlendVex",
        Inst::XmmUnaryRmRVex { .. } => "XmmUnaryRmRVex",
        Inst::XmmUnaryRmRImmVex { .. } => "XmmUnaryRmRImmVex",
        Inst::XmmMovRMVex { .. } => "XmmMovRMVex",
        Inst::XmmMovRMImmVex { .. } => "XmmMovRMImmVex",
        Inst::XmmToGprImmVex { .. } => "XmmToGprImmVex",
        Inst::GprToXmmVex { .. } => "GprToXmmVex",
        Inst::XmmToGprVex { .. } => "XmmToGprVex",
        Inst::XmmRmREvex { .. } => "XmmRmREvex",
        Inst::XmmUnaryRmRImmEvex { .. } => "XmmUnaryRmRImmEvex",
        Inst::XmmRmREvex3 { .. } => "XmmRmREvex3",
        Inst::XmmUnaryRmR { .. } => "XmmUnaryRmR",
        Inst::XmmUnaryRmRUnaligned { .. } => "XmmUnaryRmRUnaligned",
        Inst::XmmUnaryRmRImm { .. } => "XmmUnaryRmRImm",
        Inst::XmmUnaryRmREvex { .. } => "XmmUnaryRmREvex",
        Inst::XmmMovRM { .. } => "XmmMovRM",
        Inst::XmmMovRMImm { .. } => "XmmMovRMImm",
        Inst::XmmToGpr { .. } => "XmmToGpr",
        Inst::XmmToGprImm { .. } => "XmmToGprImm",
        Inst::GprToXmm { .. } => "GprToXmm",
        Inst::CvtUint64ToFloatSeq { .. } => "CvtUint64ToFloatSeq",
        Inst::CvtFloatToSintSeq { .. } => "CvtFloatToSintSeq",
        Inst::CvtFloatToUintSeq { .. } => "CvtFloatToUintSeq",
        Inst::XmmMinMaxSeq { .. } => "XmmMinMaxSeq",
        Inst::XmmCmpRmR { .. } => "XmmCmpRmR",
        Inst::XmmRmRImm { .. } => "XmmRmRImm",
        Inst::CallKnown { .. } => "CallKnown",
        Inst::CallUnknown { .. } => "CallUnknown",
        Inst::ReturnCallKnown { .. } => "ReturnCallKnown",
        Inst::ReturnCallUnknown { .. } => "ReturnCallUnknown",
        Inst::Args { .. } => "Args",
        Inst::Ret { .. } => "Ret",
        Inst::JmpKnown { .. } => "JmpKnown",
        Inst::JmpIf { .. } => "JmpIf",
        Inst::JmpCond { .. } => "JmpCond",
        Inst::JmpTableSeq { .. } => "JmpTableSeq",
        Inst::JmpUnknown { .. } => "JmpUnknown",
        Inst::TrapIf { .. } => "TrapIf",
        Inst::TrapIfAnd { .. } => "TrapIfAnd",
        Inst::TrapIfOr { .. } => "TrapIfOr",
        Inst::Hlt => "Hlt",
        Inst::Ud2 { .. } => "Ud2",
        Inst::LoadExtName { .. } => "LoadExtName",
        Inst::LockCmpxchg { .. } => "LockCmpxchg",
        Inst::AtomicRmwSeq { .. } => "AtomicRmwSeq",
        Inst::Fence { .. } => "Fence",
        Inst::VirtualSPOffsetAdj { .. } => "VirtualSPOffsetAdj",
        Inst::XmmUninitializedValue { .. } => "XmmUninitializedValue",
        Inst::ElfTlsGetAddr { .. } => "ElfTlsGetAddr",
        Inst::MachOTlsGetAddr { .. } => "MachOTlsGetAddr",
        Inst::CoffTlsGetAddr { .. } => "CoffTlsGetAddr",
        Inst::Unwind { .. } => "Unwind",
        Inst::DummyUse { .. } => "DummyUse",
        Inst::UnaryRmRImmVex { .. } => "UnaryRmRImmVex",
        Inst::CvtIntToFloat { .. } => "CvtIntToFloat",
        Inst::CvtIntToFloatVex { .. } => "CvtIntToFloatVex",
        Inst::Rets { .. } => "Rets",
    }
}

fn sext_simm(val: i64, size: OperandSize) -> i64 {
    trunc_i64_to_width(val, size.to_bits().into())
}

struct X64SymbolicValueLifter<'a> {
    insts: &'a [Inst],
    def_map: &'a DefMap,
    vreg_aliases: &'a FxHashMap<VReg, VReg>,
    constants: &'a VCodeConstants,
}

impl<'a> X64SymbolicValueLifter<'a> {
    fn new(
        insts: &'a [Inst],
        def_map: &'a DefMap,
        vreg_aliases: &'a FxHashMap<VReg, VReg>,
        constants: &'a VCodeConstants,
    ) -> Self {
        Self {
            insts,
            def_map,
            vreg_aliases,
            constants,
        }
    }

    fn resolve_vreg_alias(&self, from: VReg) -> VReg {
        let mut vreg = from;

        while let Some(to) = self.vreg_aliases.get(&vreg) {
            vreg = *to;
        }

        vreg
    }

    fn amode_eq(&self, lhs: &Amode, rhs: &Amode) -> bool {
        match (lhs, rhs) {
            (
                Amode::ImmReg {
                    base,
                    simm32,
                    flags,
                },
                Amode::ImmReg {
                    base: base1,
                    simm32: simm1,
                    flags: flags1,
                },
            ) => self.reg_or_inst_eq(base.0, base1.0) && simm32 == simm1 && flags == flags1,
            (
                Amode::ImmRegRegShift {
                    base,
                    index,
                    simm32,
                    shift,
                    flags,
                },
                Amode::ImmRegRegShift {
                    base: base1,
                    index: index1,
                    simm32: simm1,
                    shift: shift1,
                    flags: flags1,
                },
            ) => {
                self.reg_or_inst_eq(base.0.into(), base1.0.into())
                    && self.reg_or_inst_eq(index.0.into(), index1.0.into())
                    && simm32 == simm1
                    && shift == shift1
                    && flags == flags1
            }
            (Amode::RipRelative { target }, Amode::RipRelative { target: target1 }) => {
                target == target1
            }
            _ => false,
        }
    }

    fn synthetic_amode_eq(&self, lhs: &SyntheticAmode, rhs: &SyntheticAmode) -> bool {
        match (lhs, rhs) {
            (SyntheticAmode::Real(amode1), SyntheticAmode::Real(amode2)) => {
                self.amode_eq(amode1, amode2)
            }
            (
                SyntheticAmode::NominalSPOffset { simm32: imm1 },
                SyntheticAmode::NominalSPOffset { simm32: imm2 },
            ) => imm1 == imm2,
            (
                SyntheticAmode::ConstantOffset(constant1),
                SyntheticAmode::ConstantOffset(constant2),
            ) => constant1 == constant2,
            _ => false,
        }
    }

    fn reg_mem_imm_eq(&self, lhs: &GprMemImm, rhs: &GprMemImm) -> bool {
        match (lhs.clone().to_reg_mem_imm(), rhs.clone().to_reg_mem_imm()) {
            (RegMemImm::Reg { reg: reg1 }, RegMemImm::Reg { reg: reg2 }) => reg1 == reg2,
            (RegMemImm::Imm { simm32: imm1 }, RegMemImm::Imm { simm32: imm2 }) => imm1 == imm2,
            (RegMemImm::Mem { addr: addr1 }, RegMemImm::Mem { addr: addr2 }) => {
                self.synthetic_amode_eq(&addr1, &addr2)
            }
            _ => false,
        }
    }

    fn reg_mem_eq(&self, lhs: &GprMem, rhs: &GprMem) -> bool {
        match (lhs.clone().to_reg_mem(), rhs.clone().to_reg_mem()) {
            (RegMem::Reg { reg: reg1 }, RegMem::Reg { reg: reg2 }) => reg1 == reg2,
            (RegMem::Mem { addr: addr1 }, RegMem::Mem { addr: addr2 }) => {
                self.synthetic_amode_eq(&addr1, &addr2)
            }
            _ => false,
        }
    }

    fn reg_or_inst_eq(&self, reg1: VReg, reg2: VReg) -> bool {
        let reg1 = self.resolve_vreg_alias(reg1);
        let reg2 = self.resolve_vreg_alias(reg2);
        if reg1 == reg2 {
            return true;
        }

        if let (Some(src1_inst), Some(src2_inst)) =
            (self.def_map.get(&reg1), self.def_map.get(&reg2))
        {
            let src1_inst = &self.insts[src1_inst.0 as usize];
            let src2_inst = &self.insts[src2_inst.0 as usize];
            self.is_same_inst(src1_inst, src2_inst)
        } else {
            false
        }
    }

    fn is_same_inst(&self, inst1: &Inst, inst2: &Inst) -> bool {
        // eprintln!(
        //     "is_same_inst:\n{inst1:?} ({})\n{inst2:?} ({})",
        //     get_inst_name(inst1),
        //     get_inst_name(inst2)
        // );
        match (inst1, inst2) {
            (
                Inst::AluRmiR {
                    op: op1,
                    src1: src1_1,
                    src2: src2_1,
                    size: size1,
                    ..
                },
                Inst::AluRmiR {
                    op: op2,
                    src1: src1_2,
                    src2: src2_2,
                    size: size2,
                    ..
                },
            ) => {
                self.reg_or_inst_eq(src1_1.0.into(), src1_2.0.into())
                    && op1 == op2
                    && size1 == size2
                    && self.reg_mem_imm_eq(src2_1, src2_2)
            }
            (
                Inst::AluRmRVex {
                    op: op1,
                    src1: src1_1,
                    src2: src2_1,
                    size: size1,
                    ..
                },
                Inst::AluRmRVex {
                    op: op2,
                    src1: src1_2,
                    src2: src2_2,
                    size: size2,
                    ..
                },
            ) => {
                op1 == op2
                    && self.reg_or_inst_eq(src1_1.to_reg().into(), src1_2.to_reg().into())
                    && self.reg_mem_eq(src2_1, src2_2)
                    && size1 == size2
            }
            (
                Inst::LoadEffectiveAddress {
                    addr: addr1,
                    size: size1,
                    ..
                },
                Inst::LoadEffectiveAddress {
                    addr: addr2,
                    size: size2,
                    ..
                },
            ) => size1 == size2 && self.synthetic_amode_eq(addr1, addr2),
            (
                Inst::Not {
                    size: size1,
                    src: src1,
                    ..
                },
                Inst::Not {
                    size: size2,
                    src: src2,
                    ..
                },
            ) => self.reg_or_inst_eq(src1.0.into(), src2.0.into()) && size1 == size2,
            (
                Inst::Imm {
                    simm64: imm1,
                    dst_size: size1,
                    ..
                },
                Inst::Imm {
                    simm64: imm2,
                    dst_size: size2,
                    ..
                },
            ) => imm1 == imm2 && size1 == size2,
            _ => false,
        }
    }

    fn constrain_value_with_operand_size(
        mut value: SymbolicValue,
        size: OperandSize,
    ) -> SymbolicValue {
        if let SymbolicValue::Const(_) = &value {
            // if the value is already fixed, we don't need to add a constraint
            return value;
        }

        let upper_bound = match size {
            OperandSize::Size8 => i64::from(u8::MAX),
            OperandSize::Size16 => i64::from(u16::MAX),
            OperandSize::Size32 => i64::from(u32::MAX),
            // Since 64 bits is the maximum anyway, we do not constrain the value
            OperandSize::Size64 => return value,
        };
        value.trunc_const_to_bit_width(size.to_bits().into());
        value.bound_upper_const(upper_bound)
    }

    /// Create a SymbolicValue from a value in a virtual register
    /// insts must contain all preceding instructions of the one we are currently trying to create a value from
    /// constraints are any optional known constraints
    /// def_map must contain all registers up to this point
    /// TODO: rewrite this doc comment a bit better
    fn build_from_vreg(
        &self,
        reg: VReg,
        constraints: &ConstraintEnv,
        depth: usize,
    ) -> Result<SymbolicValue, Error> {
        if depth > MAX_LOAD_DEPTH {
            return Ok(SymbolicValue::Unknown);
        }

        let reg = self.resolve_vreg_alias(reg);

        let Some(ins_index) = self.def_map.get(&reg) else {
            return Ok(constraints
                .get(&reg.into())
                .map(|c| c.apply(SymbolicValue::Unknown))
                .unwrap_or_else(|| SymbolicValue::Unknown));
        };
        let inst = &self.insts[ins_index.0 as usize];

        let val = match inst {
            Inst::Args { .. } => {
                // if this is the vmctx register, we should have it in our constraints, which will be resolved later
                Ok(SymbolicValue::Unknown)
            }
            Inst::Imm {
                simm64, dst_size, ..
            } => Ok(Self::constrain_value_with_operand_size(
                SymbolicValue::Const(*simm64 as i64),
                *dst_size,
            )),
            Inst::AluConstOp { .. } => Ok(SymbolicValue::Const(0)),
            Inst::AluRmiR {
                op,
                src1,
                src2,
                size,
                ..
            } => {
                match op {
                    AluRmiROpcode::Add => {
                        let val2 = match src2.clone().to_reg_mem_imm() {
                            RegMemImm::Reg { reg } => {
                                self.build_from_vreg(VReg::from(reg), constraints, depth)?
                            }
                            RegMemImm::Mem { addr } => {
                                let (addr, is_real_load) =
                                    self.build_from_synthetic_amode(&addr, constraints, depth)?;
                                if is_real_load {
                                    addr.load()
                                } else {
                                    addr
                                }
                            }
                            RegMemImm::Imm { simm32 } => Self::try_constrain_const_value(
                                SymbolicValue::Const(sext_simm(simm32.into(), *size)),
                                constraints,
                            ),
                        };

                        let val1 = self.build_from_vreg(
                            VReg::from(src1.clone().to_reg()),
                            constraints,
                            depth,
                        )?;

                        Ok(val1.offset(val2))
                    }
                    AluRmiROpcode::Mul => {
                        // We only handle multiplication if src2 is an immediate that fits into an u8
                        let value = if let RegMemImm::Imm { simm32 } = src2.clone().to_reg_mem_imm()
                        {
                            self.build_from_vreg(
                                VReg::from(src1.clone().to_reg()),
                                constraints,
                                depth,
                            )?
                            .scaled(simm32.into())
                        } else {
                            SymbolicValue::Unknown
                        };

                        Ok(value)
                    }
                    _ => Ok(SymbolicValue::Unknown),
                }
                .map(|val| Self::constrain_value_with_operand_size(val, *size))
            }
            Inst::Mov64MR { src, .. } => {
                let (addr, is_real_load) =
                    self.build_from_synthetic_amode(&src, constraints, depth)?;
                let val = if is_real_load { addr.load() } else { addr };
                Ok(val)
            }
            Inst::Cmove {
                cc,
                consequent,
                alternative,
                size,
                ..
            } => {
                let cc_writing_inst =
                    self.last_flag_writing_inst(*ins_index)
                        .ok_or(Error::new(format!(
                            "No instruction writing the flags register found"
                        )))?;

                let (cons_constraint, alt_constraint) =
                    self.infer_constraints_from_cmp_inst(cc_writing_inst, *cc, constraints, depth)?;

                // eprintln!("cons_constraint:\n{cons_constraint:#?}");
                // eprintln!("alt_constraint:\n{alt_constraint:#?}");

                let consequent = if let Some(cons_constraint) = cons_constraint {
                    match consequent.clone().to_reg_mem() {
                        RegMem::Reg { reg } => {
                            self.build_from_vreg(VReg::from(reg), &cons_constraint, depth)
                        }
                        RegMem::Mem { addr } => {
                            let (addr, is_real_load) =
                                self.build_from_synthetic_amode(&addr, &cons_constraint, depth)?;
                            let val = if is_real_load { addr.load() } else { addr };
                            Ok(val)
                        }
                    }?
                } else {
                    // unreachable, use bottom
                    SymbolicValue::Bottom
                };
                let alternative = if let Some(alt_constraint) = alt_constraint {
                    self.build_from_vreg(
                        VReg::from(alternative.clone().to_reg()),
                        &alt_constraint,
                        depth,
                    )?
                } else {
                    // unreachable, use bottom
                    SymbolicValue::Bottom
                };

                let value = Self::constrain_value_with_operand_size(
                    SymbolicValue::either(consequent, alternative),
                    *size,
                );
                Ok(value)
            }
            Inst::MovRR { src, size, .. } => self
                .build_from_vreg(VReg::from(src.to_reg()), constraints, depth)
                .map(|val| Self::constrain_value_with_operand_size(val, *size)),
            Inst::MovzxRmR { src, ext_mode, .. } => {
                let val = match src.clone().to_reg_mem() {
                    RegMem::Reg { reg } => self.build_from_vreg(reg.0, constraints, depth),
                    RegMem::Mem { addr } => {
                        let (addr, is_real_load) =
                            self.build_from_synthetic_amode(&addr, constraints, depth)?;
                        let val = if is_real_load { addr.load() } else { addr };
                        Ok(val)
                    }
                }?;
                let size = match ext_mode {
                    ExtMode::BL | ExtMode::BQ => OperandSize::Size8,
                    ExtMode::WL | ExtMode::WQ => OperandSize::Size16,
                    ExtMode::LQ => OperandSize::Size32,
                };

                // since we're zero extending, the resulting value is bound by the previous max value
                Ok(Self::constrain_value_with_operand_size(val, size))
            }
            Inst::LoadEffectiveAddress { addr, size, .. } => {
                let (value, _) = self.build_from_synthetic_amode(addr, constraints, depth)?;
                Ok(Self::constrain_value_with_operand_size(value, *size))
            }
            Inst::ShiftR {
                src,
                kind,
                size,
                num_bits,
                ..
            } => {
                let value = match (kind, num_bits.clone().to_imm8_reg()) {
                    (ShiftKind::ShiftLeft, Imm8Reg::Imm8 { imm }) => self
                        .build_from_vreg(VReg::from(src.to_reg()), constraints, depth)?
                        .shifted(imm),
                    _ => SymbolicValue::Unknown,
                };

                Ok(Self::constrain_value_with_operand_size(value, *size))
            }
            _ => Ok(SymbolicValue::Unknown),
        }
        .map(|val| val.simplify())
        .map(|mut val| {
            if let Some(constraint) = constraints.get(&reg.into()) {
                val = constraint.apply(val);
            } else {
                // We check if for any constraint register, the instruction matches exactly the one we are looking
                // at right now.
                // This is required for the following cases:
                // lor $1, %v3, %v1
                // cmpl %v2, %v1
                // jnb label_oob; j label1
                //
                // label1:
                // lor $1, %v3, %v4 ;; <- here we cnanot use the constraint inferred on %v1, even though they are equal

                // For now, we also only do this for AluRmiR and LoadEffectiveAddress instructions
                if matches!(
                    &self.insts[ins_index.0 as usize],
                    Inst::AluRmiR { .. }
                        | Inst::LoadEffectiveAddress { .. }
                        | Inst::AluRmRVex { .. }
                        | Inst::Not { .. }
                        | Inst::Imm { .. }
                ) {
                    for (reg, constraint) in constraints {
                        let RegOrConst::Reg(reg) = reg else {
                            continue;
                        };

                        let Some(inst2) = self.def_map.get(reg) else {
                            continue;
                        };

                        if self.is_same_inst(inst, &self.insts[inst2.0 as usize]) {
                            // we found a matching instruction
                            val = constraint.apply(val);
                            break;
                        }
                    }
                }
            }
            val = Self::try_constrain_const_value(val, constraints);
            val.simplify_load_from_val_or_null();

            val
        });

        // eprintln!("from_vreg: {reg}, constraints: {:?}", constraints);
        // eprintln!("{:?} ({})\n -> {:?}", inst, get_inst_name(inst), val);

        val
    }

    fn try_constrain_const_value(
        value: SymbolicValue,
        _constraints: &ConstraintEnv,
    ) -> SymbolicValue {
        // let mut worklist = VecDeque::new();
        // worklist.push_back(&mut value);
        //
        // while let Some(mut value) = worklist.pop_front() {
        //     match value {
        //         SymbolicValue::Unknown => {}
        //         SymbolicValue::VmCtx => {}
        //         SymbolicValue::RetAreaPtr => {}
        //         SymbolicValue::Bottom => {}
        //         SymbolicValue::Const(0) => {}
        //         SymbolicValue::Scale(a, _) | SymbolicValue::Load(a) => worklist.push_back(a),
        //         SymbolicValue::Offset(a, b)
        //         | SymbolicValue::OffsetNeg(a, b)
        //         | SymbolicValue::Bounded(a, b)
        //         | SymbolicValue::Either(a, b) => {
        //             worklist.push_back(&mut **a);
        //             worklist.push_back(&mut **b);
        //         }
        //         ref mut value @ SymbolicValue::Const(_) => {
        //             let c = match *value {
        //                 SymbolicValue::Const(c) => *c,
        //                 _ => unreachable!(),
        //             };
        //             // we continuously update value with any constraints we can find
        //             // First, we try some common scaling factors
        //             for scaling_factor in [1, 2, 4, 8] {
        //                 let c = c as u64;
        //                 if c % scaling_factor == 0 {
        //                     if let Some(constraint) =
        //                         constraints.get(&RegOrConst::Const((c / scaling_factor) as i64))
        //                     {
        //                         **value = constraint
        //                             .clone()
        //                             .scaled(scaling_factor.try_into().unwrap())
        //                             .apply((*value).clone());
        //                     }
        //                 }
        //             }
        //             // Then, offsets (load sizes)
        //             for offset in [16, 8, 4, 2, 1] {
        //                 if c == offset {
        //                     continue;
        //                 }
        //                 if let Some(val) = c.checked_sub(offset) {
        //                     if let Some(constraint) = constraints.get(&RegOrConst::Const(val)) {
        //                         **value = constraint
        //                             .clone()
        //                             .offset(SymbolicValue::Const(offset))
        //                             .apply((*value).clone());
        //                     }
        //                 }
        //                 if let Some(val) = c.checked_add(offset) {
        //                     if let Some(constraint) = constraints.get(&RegOrConst::Const(val)) {
        //                         **value = constraint
        //                             .clone()
        //                             .offset_neg(SymbolicValue::Const(offset))
        //                             .apply((*value).clone());
        //                     }
        //                 }
        //                 //
        //                 // // TODO: iterate over all constraints and check if any contain an offset
        //                 // for (key, constraint) in constraints {
        //                 //     let RegOrConst::Const(key) = key else {
        //                 //         continue;
        //                 //     };
        //                 //     if let Some((constraint, offset)) = constraint.extract_const_offset() {
        //                 //         eprintln!("checking {c} == {key} + {offset} (= {})", key.wrapping_sub(offset));
        //                 //         if c == key.wrapping_sub(offset) {
        //                 //             **value = constraint.apply((*value).clone());
        //                 //         }
        //                 //     }
        //                 // }
        //             }
        //         }
        //     }
        // }

        value
    }

    fn bubble_up_constraints(
        &self,
        vreg: VReg,
        constraints: &mut ConstraintEnv,
        depth: usize,
    ) -> Result<(), Error> {
        // example: constraint: v1 -> Bounded(Unknown..*(VmCtx+0x88))
        // inst: v1 = add v2, 4
        // we want:
        // constraint v2 -> Bounded(Unknown-4..*(VmCtx+0x88)-4)

        let mut worklist = VecDeque::new();
        worklist.push_back(vreg);

        while let Some(vreg) = worklist.pop_front() {
            let vreg = self.resolve_vreg_alias(vreg);
            let Some(constraint) = constraints.get(&vreg.into()) else {
                continue;
            };
            let constraint = constraint.clone();

            let Some(inst) = self.def_map.get(&vreg) else {
                // if we don't have an instruction for this register, it is outside of our current function
                continue;
            };

            let mut handle_reg = |reg, constraint, constraints: &mut ConstraintEnv| {
                let reg = self.resolve_vreg_alias(VReg::from(reg));
                let existing_constraint = constraints.get(&reg.into()).cloned();
                let constraint = existing_constraint
                    .map(|c| c.clamp(constraint))
                    .unwrap_or_else(|| constraint.clone());
                constraints.insert(reg.into(), constraint);
                worklist.push_back(reg);
            };

            match &self.insts[inst.0 as usize] {
                Inst::AluRmiR {
                    op: AluRmiROpcode::Add,
                    src1,
                    src2,
                    size,
                    ..
                } => {
                    // TODO: for now we only handle add
                    // is this a fixpoint iteration problem?
                    // we have to constrain src1 -> vreg - src2
                    // and                  src2 -> vreg - src1
                    // but doing one thing is going to change the value the other depends on
                    // sure seems like fixpoint iteration...
                    // for now we can assume that we only encounter src2 imm and fix this once we encounter a case.

                    /*
                    v1 = v2 + 4 // -> v2 - 4 < bound
                                // -> v2 < bound + 4
                    if v1 < bound:
                        // do something
                    end
                     */

                    let src2 = match src2.clone().to_reg_mem_imm() {
                        RegMemImm::Reg { .. } => {
                            return Err(Error::new(format!(
                                "not yet implemented: AluRmiR Reg {:?}",
                                self.insts[inst.0 as usize]
                            )))
                        }
                        RegMemImm::Mem { addr } => {
                            self.build_from_synthetic_amode(&addr, constraints, depth)?
                                .0
                        }
                        RegMemImm::Imm { simm32 } => {
                            let val = sext_simm(simm32.into(), *size);

                            // the following covers the edge case where an access is performed at a constant offset and
                            // the compiler uses an immediate for the alu operation, which is used to compare to the heap
                            // bound, but uses a constant placed in a different register for the actual memory access.
                            // See the following example:
                            //   Inst 1: movl    $437914382, %v231l ; register later used for memory access
                            //   Inst 2: movl    $2, %v204l
                            //   ; check is performed against the constant + access_size (here 2)
                            //   Inst 3: addq    %v204, $437914382, %v229
                            if let SymbolicValue::Const(src_val) = self.build_from_vreg(
                                src1.clone().to_reg().into(),
                                constraints,
                                depth,
                            )? {
                                constraints.insert(
                                    RegOrConst::Const(val),
                                    constraint.clone().offset_neg(SymbolicValue::Const(src_val)),
                                );
                            }

                            SymbolicValue::Const(val)
                        }
                    };

                    let constraint = constraint.clone().offset_neg(src2);

                    handle_reg(src1.to_reg(), &constraint, constraints);
                }
                Inst::MovRR { src, .. } => {
                    handle_reg(src.to_reg(), &constraint, constraints);
                }
                Inst::MovzxRmR { src, .. } => {
                    if let RegMem::Reg { reg } = src.clone().to_reg_mem() {
                        handle_reg(reg, &constraint, constraints);
                    }
                }
                Inst::Imm { simm64, .. } => {
                    constraints.insert(RegOrConst::Const(*simm64 as i64), constraint.clone());
                }
                Inst::LoadEffectiveAddress {
                    addr: SyntheticAmode::Real(amode),
                    ..
                } => {
                    // we only handle the basic case of reg + imm for the moment
                    match amode {
                        Amode::ImmReg { base, simm32, .. } => {
                            let simm32 = *simm32 as i64;
                            let constraint =
                                constraint.clone().offset_neg(SymbolicValue::Const(simm32));
                            handle_reg(*base, &constraint, constraints);
                        }
                        Amode::ImmRegRegShift { .. } | Amode::RipRelative { .. } => {}
                    }
                }
                // we ignore every other instruction, as we don't want to bubble up constraints through them
                _ => {}
            }
        }

        Ok(())
    }

    /// This function returns the bounds for values in the if and then branch for a compare instruction
    /// If a branch is inferred as unreachable with the given constraints, `None` is returned.
    /// This is the case for the given example code:
    ///
    /// if a > b {
    ///   // do something
    /// } else {
    ///   x = select a > b, c, d // c will never be selected
    /// }
    fn infer_constraints_from_cmp_inst(
        &self,
        inst: &Inst,
        cc: CC,
        constraints: &ConstraintEnv,
        depth: usize,
    ) -> Result<(Option<ConstraintEnv>, Option<ConstraintEnv>), Error> {
        let Inst::CmpRmiR {
            src,
            dst,
            opcode,
            size,
            ..
        } = inst
        else {
            return Ok((Some(constraints.clone()), Some(constraints.clone())));
        };

        let (src, src_val) = match src.clone().to_reg_mem_imm() {
            RegMemImm::Reg { reg } => {
                let src = self.resolve_vreg_alias(VReg::from(reg));

                (
                    RegOrConst::Reg(src),
                    self.build_from_vreg(src, constraints, depth)?,
                )
            }
            RegMemImm::Imm { simm32 } => (
                RegOrConst::Const(sext_simm(simm32.into(), *size)),
                SymbolicValue::Const(sext_simm(simm32.into(), *size)),
            ),
            RegMemImm::Mem { addr } => match addr {
                SyntheticAmode::ConstantOffset(c) => {
                    let value = trunc_i64_to_width(self.get_const_value(c)?, size.to_bits().into());
                    (RegOrConst::Const(value), SymbolicValue::Const(value))
                }
                _ => {
                    // If we are unable to handle the amode, just return the unmodified constraints.
                    return Ok((Some(constraints.clone()), Some(constraints.clone())));
                }
            },
        };
        let dst_reg = self.resolve_vreg_alias(VReg::from(dst.to_reg()));
        let dst_val = self.build_from_vreg(dst_reg, constraints, depth)?;
        let dst = RegOrConst::Reg(dst_reg);

        let src_val = Self::constrain_value_with_operand_size(src_val, *size);
        let dst_val = Self::constrain_value_with_operand_size(dst_val, *size);

        let mut cons_env = constraints.clone();
        let mut alt_env = constraints.clone();

        let src_constraint = constraints.get(&src).cloned().unwrap_or(Default::default());
        let dst_constraint = constraints.get(&dst).cloned().unwrap_or(Default::default());

        match opcode {
            CmpOpcode::Cmp => match cc {
                CC::NB => {
                    cons_env.insert(src, src_constraint.clone().lower_eq(dst_val.clone()));
                    cons_env.insert(dst, dst_constraint.clone().greater_eq(src_val.clone()));
                    alt_env.insert(
                        src,
                        src_constraint
                            .clone()
                            .greater_eq(dst_val.clone().offset_const(1)),
                    );
                    alt_env.insert(
                        dst,
                        dst_constraint.lower_eq(src_val.clone().offset_const_neg(1)),
                    );
                }
                CC::NBE => {
                    cons_env.insert(
                        src,
                        src_constraint
                            .clone()
                            .lower_eq(dst_val.clone().offset_const_neg(1)),
                    );
                    cons_env.insert(
                        dst,
                        dst_constraint
                            .clone()
                            .greater_eq(src_val.clone().offset_const(1)),
                    );
                    alt_env.insert(src, src_constraint.clone().greater_eq(dst_val.clone()));
                    alt_env.insert(dst, dst_constraint.lower_eq(src_val.clone()));
                }
                CC::B => {
                    cons_env.insert(
                        src,
                        src_constraint
                            .clone()
                            .greater_eq(dst_val.clone().offset_const_neg(1)),
                    );
                    cons_env.insert(
                        dst,
                        dst_constraint
                            .clone()
                            .lower_eq(src_val.clone().offset_const(1)),
                    );
                    alt_env.insert(src, src_constraint.clone().lower_eq(dst_val.clone()));
                    alt_env.insert(dst, dst_constraint.greater_eq(src_val.clone()));
                }
                CC::BE => {
                    cons_env.insert(src, src_constraint.clone().greater_eq(dst_val.clone()));
                    cons_env.insert(dst, dst_constraint.clone().lower_eq(src_val.clone()));
                    alt_env.insert(
                        src,
                        src_constraint
                            .clone()
                            .lower_eq(dst_val.clone().offset_const(1)),
                    );
                    alt_env.insert(
                        dst,
                        dst_constraint.greater_eq(src_val.clone().offset_const_neg(1)),
                    );
                }
                CC::Z => {
                    if src == dst {
                        alt_env.insert(src, ValueConstraint::eq(SymbolicValue::Bottom));
                    } else {
                        cons_env.insert(src, ValueConstraint::eq(dst_val.clone()));
                        cons_env.insert(dst, ValueConstraint::eq(src_val.clone()));
                        alt_env.insert(src, ValueConstraint::neq(dst_val.clone()));
                        alt_env.insert(dst, ValueConstraint::neq(src_val.clone()));
                    }
                }
                CC::NZ => {
                    if src == dst {
                        cons_env.insert(src, ValueConstraint::eq(SymbolicValue::Bottom));
                    } else {
                        cons_env.insert(src, ValueConstraint::neq(dst_val.clone()));
                        cons_env.insert(dst, ValueConstraint::neq(src_val.clone()));
                        alt_env.insert(src, ValueConstraint::eq(dst_val.clone()));
                        alt_env.insert(dst, ValueConstraint::eq(src_val.clone()));
                    }
                }
                _ => {}
            },
            CmpOpcode::Test => match cc {
                CC::Z => {
                    if src == dst {
                        cons_env.insert(
                            src,
                            ValueConstraint::eq(SymbolicValue::Const(0))
                                .clamp(&ValueConstraint::eq(src_val.clone())),
                        );
                    }
                    alt_env.insert(
                        src,
                        ValueConstraint::neq(SymbolicValue::Const(0))
                            .clamp(&ValueConstraint::eq(src_val.clone())),
                    );
                    alt_env.insert(
                        dst,
                        ValueConstraint::neq(SymbolicValue::Const(0))
                            .clamp(&ValueConstraint::eq(dst_val.clone())),
                    );
                }
                CC::NZ => {
                    if src == dst {
                        alt_env.insert(
                            src,
                            ValueConstraint::eq(SymbolicValue::Const(0))
                                .clamp(&ValueConstraint::eq(src_val.clone())),
                        );
                    }
                    cons_env.insert(
                        src,
                        ValueConstraint::neq(SymbolicValue::Const(0))
                            .clamp(&ValueConstraint::eq(src_val.clone())),
                    );
                    cons_env.insert(
                        dst,
                        ValueConstraint::neq(SymbolicValue::Const(0))
                            .clamp(&ValueConstraint::eq(dst_val.clone())),
                    );
                }
                // other tests should not be relevant for address computation
                _ => {}
            },
        }

        Ok((
            self.bubble_up_environment(cons_env, src, dst_reg, depth)?,
            self.bubble_up_environment(alt_env, src, dst_reg, depth)?,
        ))
    }

    fn bubble_up_environment(
        &self,
        mut env: ConstraintEnv,
        src: RegOrConst,
        dst: VReg,
        depth: usize,
    ) -> Result<Option<ConstraintEnv>, Error> {
        let constraint_matches_bottom = |constraint: Option<&ValueConstraint>| {
            constraint
                .map(|c| c.check_in_bounds(&SymbolicValue::Bottom))
                .unwrap_or(false)
        };

        if constraint_matches_bottom(env.get(&src))
            || constraint_matches_bottom(env.get(&RegOrConst::Reg(dst)))
        {
            return Ok(None);
        }

        if let RegOrConst::Reg(src) = src {
            self.bubble_up_constraints(src, &mut env, depth)?;
        }
        self.bubble_up_constraints(dst, &mut env, depth)?;
        for (_, constraint) in env.iter_mut() {
            constraint.simplify();
        }
        Self::legalize_const_constraints(&mut env);

        Ok(Some(env))
    }

    /// This function legalizes constraints of the form
    /// `RegOrConst::Const(c1) >= x + c2`
    /// to
    /// `RegOrConst::Const(c1 - c2) >= x`
    fn legalize_const_constraints(env: &mut ConstraintEnv) {
        let mut keys = Vec::new();

        for (key, constraint) in env.iter() {
            let RegOrConst::Const(_) = key else {
                continue;
            };
            if constraint.has_const_offset() {
                keys.push(*key);
            }
        }

        for key in keys {
            let RegOrConst::Const(c) = key else {
                unreachable!();
            };

            let constraint = env.remove(&key).unwrap();
            let (constraint, offset) = constraint.extract_const_offset().unwrap();
            let new_key = c.wrapping_sub(offset);
            env.insert(RegOrConst::Const(new_key), constraint);
        }
    }

    fn build_from_amode(
        &self,
        amode: &Amode,
        constraints: &ConstraintEnv,
        depth: usize,
    ) -> Result<SymbolicValue, Error> {
        match amode {
            Amode::ImmReg { base, simm32, .. } => {
                let ptr = self.build_from_vreg(base.0, constraints, depth + 1)?;
                let addr = if *simm32 < 0 {
                    ptr.offset_neg(Self::try_constrain_const_value(
                        SymbolicValue::Const(-i64::from(*simm32)),
                        constraints,
                    ))
                } else {
                    ptr.offset(Self::try_constrain_const_value(
                        SymbolicValue::Const(i64::from(*simm32)),
                        constraints,
                    ))
                };

                Ok(addr)
            }
            Amode::ImmRegRegShift {
                base,
                index,
                simm32,
                shift,
                ..
            } => {
                let base =
                    self.build_from_vreg(VReg::from(base.to_reg()), constraints, depth + 1)?;
                let index = self
                    .build_from_vreg(VReg::from(index.to_reg()), constraints, depth + 1)?
                    .shifted(*shift);
                let value = base.offset(index);

                let value = if *simm32 < 0 {
                    value.offset_neg(Self::try_constrain_const_value(
                        SymbolicValue::Const(-i64::from(*simm32)),
                        constraints,
                    ))
                } else {
                    value.offset(Self::try_constrain_const_value(
                        SymbolicValue::Const(i64::from(*simm32)),
                        constraints,
                    ))
                };

                Ok(value)
            }
            Amode::RipRelative { .. } => unimplemented!(),
        }
        .map(|mut val| {
            // simplify (0 | val) -> val
            val.simplify_either_or_null();

            val
        })
    }

    /// Returns a value and a bool indicating whether this was a real memory access
    fn build_from_synthetic_amode(
        &self,
        amode: &SyntheticAmode,
        constraints: &ConstraintEnv,
        depth: usize,
    ) -> Result<(SymbolicValue, bool), Error> {
        match amode {
            SyntheticAmode::Real(amode) => {
                Ok((self.build_from_amode(amode, constraints, depth)?, true))
            }
            SyntheticAmode::NominalSPOffset { .. } => unimplemented!(),
            SyntheticAmode::ConstantOffset(c) => {
                Ok((SymbolicValue::Const(self.get_const_value(*c)?), false))
            }
        }
    }

    fn get_const_value(&self, c: VCodeConstant) -> Result<i64, Error> {
        let bytes = self.constants.get(c).as_slice();
        let mut zext_bytes = [0u8; 8];

        for i in 0..usize::min(bytes.len(), 8) {
            zext_bytes[i] = bytes[i];
        }

        Ok(i64::from_le_bytes(zext_bytes))
    }

    fn last_flag_writing_inst(&self, index: regalloc2::Inst) -> Option<&Inst> {
        self.insts[..index.0 as usize]
            .iter()
            .rev()
            .find(|inst| writes_flags(inst))
    }

    fn get_amode_for_reg_mem_imm(reg_mem_imm: RegMemImm) -> Option<SyntheticAmode> {
        match reg_mem_imm {
            RegMemImm::Mem { addr } => Some(addr),
            _ => None,
        }
    }

    fn get_amode_for_reg_mem(reg_mem: RegMem) -> Option<SyntheticAmode> {
        match reg_mem {
            RegMem::Mem { addr } => Some(addr),
            _ => None,
        }
    }

    fn get_amode_for_gpr_mem_imm(gpr_mem_imm: &GprMemImm) -> Option<SyntheticAmode> {
        Self::get_amode_for_reg_mem_imm(gpr_mem_imm.clone().to_reg_mem_imm())
    }

    fn get_amode_for_gpr_mem(gpr_mem: &GprMem) -> Option<SyntheticAmode> {
        Self::get_amode_for_reg_mem(gpr_mem.clone().to_reg_mem())
    }

    fn get_amode_for_xmm_mem_aligned_imm(xmm: &XmmMemAlignedImm) -> Option<SyntheticAmode> {
        Self::get_amode_for_reg_mem_imm(xmm.clone().to_reg_mem_imm())
    }

    fn get_amode_for_xmm_mem_aligned(xmm: &XmmMemAligned) -> Option<SyntheticAmode> {
        Self::get_amode_for_reg_mem(xmm.clone().to_reg_mem())
    }

    fn get_amode_for_xmm_mem_imm(xmm: &XmmMemImm) -> Option<SyntheticAmode> {
        Self::get_amode_for_reg_mem_imm(xmm.clone().to_reg_mem_imm())
    }

    fn get_amode_for_xmm_mem(xmm: &XmmMem) -> Option<SyntheticAmode> {
        Self::get_amode_for_reg_mem(xmm.clone().to_reg_mem())
    }

    fn get_sse_access_size(op: SseOpcode) -> u8 {
        let Some(size) = op.mem_access_size() else {
            panic!("No access size for sse opcode {op}");
        };
        size
    }

    fn get_avx_access_size(op: AvxOpcode) -> u8 {
        let Some(size) = op.mem_access_size() else {
            panic!("No access size for avx opcode {op}");
        };
        size
    }

    fn get_avx_512_access_size(op: Avx512Opcode) -> u8 {
        let Some(size) = op.mem_access_size() else {
            panic!("No access size for avx512 opcode {op}");
        };
        size
    }

    /// Return the amode and access size for an instruction
    fn get_amode_for_inst(inst: &Inst) -> Option<(SyntheticAmode, u8)> {
        let result = match inst {
            MInst::AluRmiR { src2, size, .. } => {
                (Self::get_amode_for_gpr_mem_imm(src2)?, size.to_bytes())
            }
            MInst::AluRM { src1_dst, size, .. } => (src1_dst.clone(), size.to_bytes()),
            MInst::AluRmRVex { .. } => return None,
            MInst::UnaryRmR { src, size, .. } => {
                (Self::get_amode_for_gpr_mem(src)?, size.to_bytes())
            }
            MInst::UnaryRmRVex { src, size, .. } => {
                (Self::get_amode_for_gpr_mem(src)?, size.to_bytes())
            }
            MInst::MovzxRmR { src, ext_mode, .. } => (
                Self::get_amode_for_gpr_mem(src)?,
                ext_mode.src_size().into(),
            ),
            MInst::Mov64MR { src, .. } => (src.clone(), OperandSize::Size64.to_bytes()),
            MInst::MovsxRmR { src, ext_mode, .. } => (
                Self::get_amode_for_gpr_mem(src)?,
                ext_mode.src_size().into(),
            ),
            MInst::MovImmM { dst, size, .. } => (dst.clone(), size.to_bytes()),
            MInst::MovRM { dst, size, .. } => (dst.clone(), size.to_bytes()),
            MInst::CmpRmiR { src, size, .. } => {
                (Self::get_amode_for_gpr_mem_imm(src)?, size.to_bytes())
            }
            MInst::Cmove {
                consequent, size, ..
            } => (Self::get_amode_for_gpr_mem(consequent)?, size.to_bytes()),
            MInst::Push64 { src, .. } => (
                Self::get_amode_for_gpr_mem_imm(src)?,
                OperandSize::Size64.to_bytes(),
            ),
            MInst::Pop64 { .. } => return None,
            MInst::StackProbeLoop { .. } => return None,
            MInst::LockCmpxchg { mem, ty, .. } => (
                mem.clone(),
                ty.bytes()
                    .try_into()
                    .expect("Access size doesn't fit into u8"),
            ),
            MInst::AtomicRmwSeq { mem, ty, .. } => (
                mem.clone(),
                ty.bytes()
                    .try_into()
                    .expect("Access size doesn't fit into u8"),
            ),
            MInst::CvtUint64ToFloatSeq { .. } => return None,
            MInst::CvtFloatToSintSeq { .. } => return None,
            MInst::CvtFloatToUintSeq { .. } => return None,
            MInst::CallKnown { .. } => return None,
            MInst::CallUnknown { .. } => return None,
            MInst::ReturnCallKnown { .. } => return None,
            MInst::ReturnCallUnknown { .. } => return None,
            MInst::Args { .. } => return None,
            MInst::Ret { .. } => return None,
            MInst::JmpKnown { .. } => return None,
            MInst::JmpIf { .. } => return None,
            MInst::JmpCond { .. } => return None,
            MInst::JmpTableSeq { .. } => return None,
            MInst::JmpUnknown { .. } => return None,
            MInst::TrapIf { .. } => return None,
            MInst::TrapIfAnd { .. } => return None,
            MInst::TrapIfOr { .. } => return None,
            MInst::Hlt => return None,
            MInst::Ud2 { .. } => return None,
            MInst::LoadExtName { .. } => return None,
            MInst::Fence { .. } => return None,
            MInst::VirtualSPOffsetAdj { .. } => return None,
            MInst::ElfTlsGetAddr { .. } => return None,
            MInst::MachOTlsGetAddr { .. } => return None,
            MInst::CoffTlsGetAddr { .. } => return None,
            MInst::Unwind { .. } => return None,
            MInst::DummyUse { .. } => return None,
            MInst::Nop { .. } => return None,
            MInst::AluConstOp { .. } => return None,
            MInst::Not { .. } => return None,
            MInst::Neg { .. } => return None,
            MInst::Div { .. } => return None,
            MInst::Div8 { .. } => return None,
            MInst::MulHi { .. } => return None,
            MInst::UMulLo { .. } => return None,
            MInst::CheckedSRemSeq { .. } => return None,
            MInst::CheckedSRemSeq8 { .. } => return None,
            MInst::SignExtendData { .. } => return None,
            MInst::Imm { .. } => return None,
            MInst::MovRR { .. } => return None,
            MInst::MovFromPReg { .. } => return None,
            MInst::MovToPReg { .. } => return None,
            MInst::LoadEffectiveAddress { .. } => return None,
            MInst::ShiftR { .. } => return None,
            MInst::Setcc { .. } => return None,
            MInst::Bswap { .. } => return None,
            MInst::XmmRmiReg { src2, opcode, .. } => (
                Self::get_amode_for_xmm_mem_aligned_imm(src2)?,
                Self::get_sse_access_size(*opcode),
            ),
            MInst::XmmCmove { consequent, ty, .. } => (
                Self::get_amode_for_xmm_mem_aligned(consequent)?,
                ty.bytes().try_into().unwrap(),
            ),
            MInst::XmmRmR { src2, op, .. } => (
                Self::get_amode_for_xmm_mem_aligned(src2)?,
                Self::get_sse_access_size(*op),
            ),
            MInst::XmmRmRUnaligned { src2, op, .. } => (
                Self::get_amode_for_xmm_mem(src2)?,
                Self::get_sse_access_size(*op),
            ),
            MInst::XmmRmRBlend { src2, op, .. } => (
                Self::get_amode_for_xmm_mem_aligned(src2)?,
                Self::get_sse_access_size(*op),
            ),
            MInst::XmmRmiRVex { src2, op, .. } => (
                Self::get_amode_for_xmm_mem_imm(src2)?,
                Self::get_avx_access_size(*op),
            ),
            MInst::XmmRmRImmVex { src2, op, .. } => (
                Self::get_amode_for_xmm_mem(src2)?,
                Self::get_avx_access_size(*op),
            ),
            MInst::XmmVexPinsr { src2, op, .. } => (
                Self::get_amode_for_gpr_mem(src2)?,
                Self::get_avx_access_size(*op),
            ),
            MInst::XmmRmRVex3 { src3, op, .. } => (
                Self::get_amode_for_xmm_mem(src3)?,
                Self::get_avx_access_size(*op),
            ),
            MInst::XmmRmRBlendVex { src2, op, .. } => (
                Self::get_amode_for_xmm_mem(src2)?,
                Self::get_avx_access_size(*op),
            ),
            MInst::XmmUnaryRmRVex { src, op, .. } => (
                Self::get_amode_for_xmm_mem(src)?,
                Self::get_avx_access_size(*op),
            ),
            MInst::XmmUnaryRmRImmVex { src, op, .. } => (
                Self::get_amode_for_xmm_mem(src)?,
                Self::get_avx_access_size(*op),
            ),
            MInst::XmmMovRMVex { dst, op, .. } => (dst.clone(), Self::get_avx_access_size(*op)),
            MInst::XmmMovRMImmVex { dst, op, .. } => (dst.clone(), Self::get_avx_access_size(*op)),
            MInst::XmmToGprImmVex { .. } => return None,
            MInst::GprToXmmVex { src, src_size, .. } => {
                (Self::get_amode_for_gpr_mem(src)?, src_size.to_bytes())
            }
            MInst::XmmToGprVex { .. } => return None,
            MInst::XmmRmREvex { src2, op, .. } => (
                Self::get_amode_for_xmm_mem(src2)?,
                Self::get_avx_512_access_size(*op),
            ),
            MInst::XmmUnaryRmRImmEvex { src, op, .. } => (
                Self::get_amode_for_xmm_mem(src)?,
                Self::get_avx_512_access_size(*op),
            ),
            MInst::XmmRmREvex3 { src3, op, .. } => (
                Self::get_amode_for_xmm_mem(src3)?,
                Self::get_avx_512_access_size(*op),
            ),
            MInst::XmmUnaryRmR { src, op, .. } => (
                Self::get_amode_for_xmm_mem_aligned(src)?,
                Self::get_sse_access_size(*op),
            ),
            MInst::XmmUnaryRmRUnaligned { src, op, .. } => (
                Self::get_amode_for_xmm_mem(src)?,
                Self::get_sse_access_size(*op),
            ),
            MInst::XmmUnaryRmRImm { src, op, .. } => (
                Self::get_amode_for_xmm_mem_aligned(src)?,
                Self::get_sse_access_size(*op),
            ),
            MInst::XmmUnaryRmREvex { src, op, .. } => (
                Self::get_amode_for_xmm_mem(src)?,
                Self::get_avx_512_access_size(*op),
            ),
            MInst::XmmMovRM { dst, op, .. } => (dst.clone(), Self::get_sse_access_size(*op)),
            MInst::XmmMovRMImm { dst, op, .. } => (dst.clone(), Self::get_sse_access_size(*op)),
            MInst::XmmToGpr { .. } => return None,
            MInst::XmmToGprImm { .. } => return None,
            MInst::GprToXmm { src, src_size, .. } => {
                (Self::get_amode_for_gpr_mem(src)?, src_size.to_bytes())
            }
            MInst::XmmMinMaxSeq { .. } => return None,
            MInst::XmmCmpRmR { src, op, .. } => (
                Self::get_amode_for_xmm_mem_aligned(src)?,
                Self::get_sse_access_size(*op),
            ),
            MInst::XmmRmRImm { src2, size, .. } => {
                (Self::get_amode_for_reg_mem(src2.clone())?, size.to_bytes())
            }
            MInst::XmmUninitializedValue { .. } => return None,
            MInst::UnaryRmRImmVex { src, size, .. } => {
                (Self::get_amode_for_gpr_mem(src)?, size.to_bytes())
            }
            MInst::CvtIntToFloat {
                src2, src2_size, ..
            } => (Self::get_amode_for_gpr_mem(src2)?, src2_size.to_bytes()),
            MInst::CvtIntToFloatVex {
                src2, src2_size, ..
            } => (Self::get_amode_for_gpr_mem(src2)?, src2_size.to_bytes()),
            MInst::Rets { .. } => return None,
        };

        Some(result)
    }

    fn is_rbp_rsp(reg: &machinst::Reg) -> bool {
        reg == &regs::rbp() || reg == &regs::rsp()
    }

    fn is_stack_access(amode: &SyntheticAmode) -> bool {
        match amode {
            SyntheticAmode::Real(amode) => match amode {
                Amode::ImmReg { base, .. } => Self::is_rbp_rsp(base),
                Amode::ImmRegRegShift { base, index, .. } => {
                    Self::is_rbp_rsp(base) || Self::is_rbp_rsp(index)
                }
                Amode::RipRelative { .. } => false,
            },
            SyntheticAmode::ConstantOffset(_) => false,
            SyntheticAmode::NominalSPOffset { .. } => true,
        }
    }
}

/// Verify memory accesses
pub struct X64MemAccessVerifier;

impl X64MemAccessVerifier {
    /// Create a new instance of the verifier
    pub fn new() -> Self {
        Self {}
    }
}

impl MemAccessVerifier<Inst> for X64MemAccessVerifier {
    fn verify_reg_assertion(
        &self,
        reg: VReg,
        assertion: &ValueAssertion,
        ctx: VerifierCtx<Inst>,
    ) -> Result<(), Error> {
        let lifter =
            X64SymbolicValueLifter::new(ctx.insts, ctx.def_map, ctx.vreg_aliases, ctx.constants);

        let value = lifter.build_from_vreg(reg, ctx.verified_constraints, 0)?;

        if let SymbolicValue::Bottom = value {
            // bottom means this value is unreachable
            return Ok(());
        }

        if !assertion.constraint.check_in_bounds(&value) {
            return Err(Error::new(format!(
                "Error verifying annotation:\n{}\nValue does not match:\n{}\nconstraints:{:?}\n",
                assertion.display(&reg),
                value,
                ctx.verified_constraints,
            )));
        } else {
            debug!(
                "Successfully verified value match:\n{} {}",
                value, assertion.constraint
            );
        }

        Ok(())
    }

    fn verify_memory_access(
        &self,
        inst: &Inst,
        capabilities: &[MemoryAccessCapability],
        ctx: VerifierCtx<Inst>,
    ) -> Result<(), Error> {
        // eprintln!("checking inst {:?}", inst);
        let Some((amode, access_size)) = X64SymbolicValueLifter::get_amode_for_inst(inst) else {
            // no memory access, so we return success
            return Ok(());
        };

        if X64SymbolicValueLifter::is_stack_access(&amode) {
            // stack access, which we don't verify at the moment
            // eprintln!("Ignoring stack access");
            return Ok(());
        }

        let lifter =
            X64SymbolicValueLifter::new(ctx.insts, ctx.def_map, ctx.vreg_aliases, ctx.constants);
        let (value, is_real_load) =
            lifter.build_from_synthetic_amode(&amode, ctx.verified_constraints, 0)?;

        if !is_real_load {
            return Ok(());
        }
        let value = value.simplify();

        let mut worklist = VecDeque::new();
        worklist.push_back(value);

        'outer: while let Some(value) = worklist.pop_front() {
            if let SymbolicValue::Either(a, b) = value {
                worklist.push_back((*a).clone());
                worklist.push_back((*b).clone());
                continue;
            }

            // Allow the access in two cases:
            // 1. If the symbolic value is the bottom value, this instruction is unreachable and will not be executed.
            // 2. If the value points to null, allow the access, as it will trap.
            if matches!(value, SymbolicValue::Bottom) || matches!(value, SymbolicValue::Const(0)) {
                return Ok(());
            }

            for capability in capabilities {
                let access_size = if let Some(min_size) = capability.min_size {
                    access_size.saturating_sub(min_size)
                } else {
                    access_size
                };

                // we try each capability until we find one that matches
                let constraint = ValueConstraint::from(capability.clone());
                if constraint.check_in_bounds_with_access_size(&value, access_size) {
                    debug!(
                        "Instruction {:?} matches capablity {} (value: {}, access size: 0x{access_size:x})",
                        inst, capability, value
                    );
                    break 'outer;
                }
            }

            let mut capabilites_str = String::new();
            for capability in capabilities {
                capabilites_str.push_str(&format!("{}\n", capability));
            }

            eprintln!("{:?}", ctx.verified_constraints);
            return Err(Error::new(format!(
                "Error verifying memory access:\n\
                    {inst:?} ({})\n\
                    Address does not match any capability:\n\
                    {value} (access size: 0x{access_size:x})\n\
                    Capabilites available:\n\
                    {capabilites_str}\n\
                    constraints:\n\
                    {:#?}
                    ",
                get_inst_name(inst),
                ctx.verified_constraints,
            )));
        }

        Ok(())
    }

    fn get_outgoing_constraints(
        &self,
        terminator: regalloc2::Inst,
        ctx: VerifierCtx<Inst>,
    ) -> Result<Vec<FxHashMap<RegOrConst, ValueConstraint>>, Error> {
        match &ctx.insts[terminator.0 as usize] {
            MInst::JmpCond { cc, .. } | MInst::JmpIf { cc, .. } => {
                let lifter = X64SymbolicValueLifter::new(
                    ctx.insts,
                    ctx.def_map,
                    ctx.vreg_aliases,
                    ctx.constants,
                );
                let Some(last_flag_writing_inst) = lifter.last_flag_writing_inst(terminator) else {
                    return Ok(vec![Default::default(); 2]);
                };

                let (c1, c2) = lifter.infer_constraints_from_cmp_inst(
                    last_flag_writing_inst,
                    *cc,
                    ctx.verified_constraints,
                    0,
                )?;

                Ok(vec![c1.unwrap_or_default(), c2.unwrap_or_default()])
            }
            MInst::JmpTableSeq { targets, .. } => Ok(vec![
                Default::default();
                targets.len() + /*default target*/ 1
            ]),
            // single successor, but no inferred constraints
            MInst::JmpKnown { .. } => Ok(vec![Default::default()]),
            // Terminator instructions that should not have a successor or unconditionally continue
            MInst::ReturnCallKnown { .. } => Ok(Default::default()),
            MInst::ReturnCallUnknown { .. } => Ok(Default::default()),
            MInst::Ret { .. } => Ok(Default::default()),
            MInst::Rets { .. } => Ok(Default::default()),
            MInst::JmpUnknown { .. } => Ok(Default::default()),
            MInst::Hlt => Ok(Default::default()),
            MInst::Ud2 { .. } => Ok(Default::default()),
            inst => unreachable!("Not a terminator instruction: {:?}", inst),
        }
    }
}

/// Returns true if the instruction affects the flag register
fn writes_flags(inst: &Inst) -> bool {
    match inst {
        Inst::AluRmiR { .. } => true,
        Inst::AluRM { .. } => true,
        Inst::AluRmRVex { .. } => true,
        Inst::AluConstOp { .. } => true,
        Inst::UnaryRmR { .. } => true,
        Inst::UnaryRmRVex { .. } => true,
        Inst::Neg { .. } => true,
        Inst::Div { .. } => true,  // flags -> undefined
        Inst::Div8 { .. } => true, // flags -> undefined
        Inst::MulHi { .. } => true,
        Inst::UMulLo { .. } => true,
        Inst::ShiftR { .. } => true,
        Inst::CmpRmiR { .. } => true,
        _ => false,
    }
}
