//! Module containing the code to verify memory accesses remain in the sandbox.

/// Module containing types for value assertions
pub mod assertions;
/// Module containing capabilities attached to functions
pub mod capability;
/// Contains constraints on value
pub mod constraint;
/// Module containing the symbolic value
pub mod symbolic_value;
/// Module containing the verifier at the VCode level
pub mod verifier;

/// Truncate integers to a smaller representation
pub fn trunc_i64_to_width(val: i64, width: u32) -> i64 {
    match width {
        8 => val as i8 as u8 as i64,
        16 => val as i16 as u16 as i64,
        32 => val as i32 as u32 as i64,
        64 => val,
        width => unimplemented!("cannot truncate to width {width}"),
    }
}
