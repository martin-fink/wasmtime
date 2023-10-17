//! Compilation backend pipeline: optimized IR to VCode / binemit.

use crate::dominator_tree::DominatorTree;
use crate::ir::Function;
use crate::isa::TargetIsa;
use crate::machinst::*;
use crate::timing;
use crate::trace;

use crate::mem_verifier::verifier::MemAccessVerifier;
use regalloc2::RegallocOptions;

/// Compile the given function down to VCode with allocated registers, ready
/// for binary emission.
pub fn compile<B: LowerBackend + TargetIsa>(
    f: &Function,
    domtree: &DominatorTree,
    b: &B,
    abi: Callee<<<B as LowerBackend>::MInst as MachInst>::ABIMachineSpec>,
    emit_info: <B::MInst as MachInstEmit>::Info,
    sigs: SigSet,
    ctrl_plane: &mut ControlPlane,
    mem_verifier: &dyn MemAccessVerifier<<B as LowerBackend>::MInst>,
) -> CodegenResult<(VCode<B::MInst>, regalloc2::Output)> {
    // Compute lowered block order.
    let block_order = BlockLoweringOrder::new(f, domtree, ctrl_plane);

    // Build the lowering context.
    let lower = crate::machinst::Lower::new(f, abi, emit_info, block_order, sigs)?;

    // Lower the IR.
    let vcode = {
        log::debug!(
            "Number of CLIF instructions to lower: {}",
            f.dfg.num_insts()
        );
        log::debug!("Number of CLIF blocks to lower: {}", f.dfg.num_blocks());

        let _tt = timing::vcode_lower();
        lower.lower(b, ctrl_plane, domtree)?
    };

    log::debug!(
        "Number of lowered vcode instructions: {}",
        vcode.num_insts()
    );
    log::debug!("Number of lowered vcode blocks: {}", vcode.num_blocks());
    trace!("vcode from lowering: \n{:?}", vcode);

    if b.flags().enable_mem_verifier() && f.mem_verifier.enabled {
        let _tt = timing::mem_verifier();
        // Validate here before doing regalloc
        // eprintln!("{:?}", vcode);
        vcode
            .verify_memory_accesses(mem_verifier, &f.mem_verifier.capabilities)
            .map_err(|err| {
                log::error!(
                    "Memory access validation error: {}\nVCode:\n{:?}\nCLIF for error:\n{:?}",
                    err,
                    vcode,
                    f,
                );
                err
            })
            .expect("memory access validation");
    }

    // Perform register allocation.
    let regalloc_result = {
        let _tt = timing::regalloc();
        let mut options = RegallocOptions::default();
        options.verbose_log = b.flags().regalloc_verbose_logs();

        if cfg!(debug_assertions) {
            options.validate_ssa = true;
        }

        regalloc2::run(&vcode, vcode.machine_env(), &options)
            .map_err(|err| {
                log::error!(
                    "Register allocation error for vcode\n{:?}\nError: {:?}\nCLIF for error:\n{:?}",
                    vcode,
                    err,
                    f,
                );
                err
            })
            .expect("register allocation")
    };

    // Run the regalloc checker, if requested.
    if b.flags().regalloc_checker() {
        let _tt = timing::regalloc_checker();
        let mut checker = regalloc2::checker::Checker::new(&vcode, vcode.machine_env());
        checker.prepare(&regalloc_result);
        checker
            .run()
            .map_err(|err| {
                log::error!(
                    "Register allocation checker errors:\n{:?}\nfor vcode:\n{:?}",
                    err,
                    vcode
                );
                err
            })
            .expect("register allocation checker");
    }

    Ok((vcode, regalloc_result))
}
