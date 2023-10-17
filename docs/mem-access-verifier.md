# Memory Access verifier

The memory access verifier provides a framework to verify that mid-end optimizations and instruction lowering do not
introduce sandbox escape bugs, such as [CVE-2023-26489].

On a high level, the verifier relies on cranelift-wasm to provide knowledge about the sandbox, such as which memory
areas are allowed to be accessed. This not only includes the `vmctx` struct or the linear memory, but also return area
pointers, tables, and function references.

The actual verification is done just before register allocation on the VCode. This has the advantage that the VCode is
still in SSA form, which makes verification easier, as we don't need to track registers at program points.
Since the register allocator already has its own verifier, we do not put this component in the trusted computing base.

## Usage

The verifier is enabled with the `--enable-cranelift-mem-verifier` flag. If it encounters a memory access violation,
it will panic and print the error.

```shell
wasmtime compile --enable-cranelift-mem-verifier file.wasm
```

## Abstract interpretation

To verify memory accesses, we use abstract interpretation to overapproximate values and reason about their bounds. This
is helped by the fact that we don't need to be very precise here and can ignore many instructions and cases, as we only
care about a subset of the code that is generated; about the code containing bounds checks and address computation.
For this, we have defined a small expression language, which is described below. We lift VCode to this representation
to check if no sandbox escapes have been introduced.

### Symbolic Values

The `SymbolicValue` struct is the heart of the memory access verifier. It supports the following values and operators,
which are enough to describe the address computation emitted by cranelift:

- `unknown` the default value
- `vmctx` the special vmctx value
- `ret_area_ptr` the pointer to the return area
- `bottom` an unreachable value
- `i64` constants
- `symbolic + symbolic` offsets
- `symbolic - symbolic` negative offsets (TODO: remove, insert `neg` value?)
- `symbolic * u32` scale
- `bounded(symbolic, symbolic)` represents a value between two bounds
- `symbolic | symbolic` either of two values
- `*symbolic` load

We have defined a number of simplification rules to bring arbitrary expressions into a canonical form, as well as a
partial order over this structure. This allows comparing values (if they are comparable) to see if they are equal or
contain each other.

These expressions can be arbitrarily combined and nested, which becomes a problem when comparing them to other values,
as the runtime rises exponentially with the nesting depth. To combat this, we truncate values at a given load depth, and
replace the expression tree below the limit with a single `unknown` value.
Additionally, we implemented a few optimizations, which truncate large trees and insert `unknown` values for patterns
we discovered, which are not required to check for correct bounds checking. This greatly reduced the runtime, and did
not introduce uncertainty, as the bounds checks are represented in the outer levels of the expression tree.

#### Lifting from VCode

We lift at a moment where the VCode is in almost final form, just missing stack spills and register allocation. If the
lifter is given the following VCode, it will infer the following values for the address operand of the mov instruction:

```s
;; assume v192 = vmctx
;; assume v192 = unknown

movq    96(%v192), %v201
;; v201 = *(vmctx + 96)
movl    %v194l, %v200l
;; v200 = bounded(unknown, u32::MAX)
movl    0(%v201,%v200,1), %v199l
;; 0(%v201,%v200,1) = bounded(*(vmctx + 96) + unknown, *(vmctx + 96) + u32::MAX)
;; v199 = bounded(bounded(*(vmctx + 96) + unknown, *(vmctx + 96) + u32::MAX), u32::MAX)
```

The above example is the code generated for the wasm program loading an `i32` from a memory location with no dynamic
bounds checks and a static memory with guard pages covering the whole 4 GiB address space a `i32` can address. The heap
base is stored in the vmctx field at offset `96`. We see that the memory access lies in the range
`*(vmctx+96)[0...u32::MAX]`.
When checking the VCode, however, we do not know if this is correct. The program might have been compiled with less than
4 GiB of guard pages and should insert dynamic memory checks, for example. To verify this, we need some information
about the environment.

### Capabilties

Capabilities are attached to functions and generated on demand, i.e. a function that does not access memory or does not
access function references does not contain the respective capabilities. Capabilities consist of two symbolic values,
a base and a length.

Every function contains at least one base capability for accessing the `vmctx` struct, which is implicitly passed to
every function as its first argument. The capability for the `vmctx` struct looks like this: `allow vmctx[0...128]`.
The size of the struct depends on the compilation context, target, and module. Other capabilities may depend on other
capabilities, e.g. the capability for accessing the heap. If the heap base is stored at address `vmctx + 80` and the
heap size is stored at address `vmctx + 88`, the capability for the heap will look like this:
`allow *(vmctx + 80)[0...*(vmctx + 88)]`.


Below you can find an example for a function that does not access memory, but calls a function through a function 
reference table. This also requires looking up and checking the functions signature, so multiple different capabilities
are required.

```
#[verify_memory_accesses]
function u0:0(i64 vmctx, i64) fast {
    allow *umin(*(vmctx + 72), (*(vmctx + 72) + ((*(vmctx + 80) * 8) - 8)))[0...64] ;; func_ref_table_elem
    allow *(vmctx + 72)[0...(*(vmctx + 80) * 8)] ;; table
    allow vmctx[0...128] ;; vmctx
    allow (vmctx + 72)[0...16] ;; table_ptr
    allow (*(vmctx + 56) + 72)[0...8] ;; builtin_func_addr
    allow *(vmctx + 64)[0...24] ;; signature_ids_ptr
    allow *(vmctx + 56)[0...8] ;; builtin_func_array
}
```

### Block assertions/assumptions

To optimize the verification process and to pass information about special parameters, such as `vmctx` to the verifier,
we define assertions and assumptions on blocks.
Assertions and assumptions are both used in a block to determine values. Assertions need to be checked by predecessor
blocks, while assumptions are assertions and assumptions forwarded to successor blocks, if the current block dominates 
the successor.
This domination check is required, as can be seen in the following example:

```
               ┌─────── block0 ───────┐
               │ cmp v0 v1            │
               │ jl block1; j block2  │
               └──────────────────────┘
                     ╱            ╲
  ┌─────── block1 ───────┐    ┌─────── block2 ───────┐
  │ j block4             │    │ j block3             │
  └──────────────────────┘    └──────────────────────┘
              ╲                           │
               ╲              ┌─────── block2 ───────┐
                ╲             │ j block4             │
                 ╲            └──────────────────────┘
                  ╲              ╱
               ┌─────── block4 ───────┐
               │                      │
               └──────────────────────┘
```

In `block1`, the assertions `v0 < v1` and `v1 > v0` hold, while in `block2` and `block3` the assertions `v0 >= v1` and
`v1 <= v0` hold. In `block4` neither holds.

## Verifying memory accesses

The actual verification happens just before register allocation and is done separately for each basic block of a 
function.
To gather information about value ranges influenced by checks and conditional branches, we need to look at predecessor
blocks before we start checking memory accesses.

- If a block has a single predecessor, we check if the predecessor is terminated by a conditional branch; if yes, we
  try to infer constraints from the condition on which the block branches to the current or to another block.
- We recursively walk back predecessor blocks, to try to assume value ranges from them. If a predecessor block dominates
  the current block, we assume all its assertions/assumptions. Since the computational complexity of this rises
  exponentially with the number of blocks in a function, we limit the depth of blocks visited. In our tests and in 
  fuzzing we did not see any issues with this.

After we have gathered assumptions, we can iterate over all instructions in the current block. If the instruction
accesses memory, we check that the address matches one of the capabilities defined on the current function. If no
capability matches, we print an error and abort the compilation.

After we are done verifying all memory accesses, we need to check that all assertions defined on successor blocks hold.

Verifying all blocks on a function can be parallelized, but isn't done at the moment, as functions are already compiled
in parallel, and the performance gain is therefore potentially not too high.

The memory access verifier is able to detect all bounds checks cranelift-wasm currently emits:
- Static memories with guard pages
- Dynamic bounds checks
- Dynamic bounds checks with spectre guards
- Lazily initialized tables, spectre guarded

We do not verify stack accesses, as no stack accesses exist before regalloc, with one exception. If a function has more
parameters than can be passed in registers, the remaining arguments are passed on the stack. Cranelift inserts loads
into virtual registers in the entry block of the function. Checking that only arguments and nothing beyond that is
accessed can be implemented at a later stage. For this, a new special SymbolicValue (stack frame base) needs to be
introduced, and a new capability needs to be added to the function, allowing only the access to the arguments passed on
the stack.

## Performance

Running the fuzzer is, depending on the compiled module, relatively expensive. Its overhead ranges from 2-4x and might
potentially be higher for some edge cases. The memory usage is also quite high, as all symbolic values are allocated on
the heap. There might be room for future optimizations there, but it is not clear how high that improvmement can be.

## Fuzzing

The memory access verifier is currently being used in the fuzzing infrastructure to try to find bugs during optimization
or instruction lowering. If [CVE-2023-26489] is manually reintroduced, the fuzzer finds the issue after a few hours of fuzzing.

[CVE-2023-26489]: https://github.com/bytecodealliance/wasmtime/security/advisories/GHSA-ff4p-7xrq-q5r8 (CVE-2023-26489)
