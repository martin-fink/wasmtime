//! Compile arbitrary bytes from the fuzzer as if they were Wasm, checking that
//! compilation is deterministic.
//!
//! Also use `wasm-mutate` to mutate the fuzz inputs.

#![no_main]

use libfuzzer_sys::{fuzz_mutator, fuzz_target};
use wasmtime::{Config, Engine, Module, Result};

fn create_engine() -> Engine {
    let mut config = Config::default();
    // Safety: the Cranelift option `enable_mem_verifier` does not alter
    // the generated code at all; it only does extra checking after
    // compilation.
    unsafe {
        config.cranelift_debug_verifier(false);
        config.cranelift_flag_enable("enable_mem_verifier");
    }
    Engine::new(&config).expect("Could not construct Engine")
}

fn compile_and_serialize(engine: &Engine, wasm: &[u8]) -> Result<Vec<u8>> {
    let module = Module::new(&engine, wasm)?;
    module.serialize()
}

fuzz_target!(|data: &[u8]| {
    let engine = create_engine();
    wasmtime_fuzzing::oracles::log_wasm(data);

    let _ = compile_and_serialize(&engine, data);
});

fuzz_mutator!(|data: &mut [u8], size: usize, max_size: usize, seed: u32| {
    // Half of the time use libfuzzer's built in mutators, and the other half of
    // the time use `wasm-mutate`.
    if seed.count_ones() % 2 == 0 {
        libfuzzer_sys::fuzzer_mutate(data, size, max_size)
    } else {
        wasmtime_fuzzing::mutators::wasm_mutate(
            data,
            size,
            max_size,
            seed,
            libfuzzer_sys::fuzzer_mutate,
        )
    }
});
