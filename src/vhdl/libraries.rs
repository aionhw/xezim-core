//! The VHDL standard packages built into xezim: `std` (STANDARD, TEXTIO,
//! ENV) and `ieee` (STD_LOGIC_1164, NUMERIC_STD, …), the IEEE P1076 Working
//! Group sources vendored unmodified under `libraries/` (Apache-2.0; see
//! `libraries/README.md`).

/// One vendored source file and the design library it is analysed into.
pub struct LibSource {
    pub library: &'static str,
    pub file: &'static str,
    pub text: &'static [u8],
}

pub static SOURCES: &[LibSource] = &[
    LibSource {
        library: "std",
        file: "env.vhdl",
        text: include_bytes!("libraries/std/env.vhdl"),
    },
    LibSource {
        library: "std",
        file: "standard.vhdl",
        text: include_bytes!("libraries/std/standard.vhdl"),
    },
    LibSource {
        library: "std",
        file: "textio.vhdl",
        text: include_bytes!("libraries/std/textio.vhdl"),
    },
    LibSource {
        library: "ieee",
        file: "fixed_float_types.vhdl",
        text: include_bytes!("libraries/ieee/fixed_float_types.vhdl"),
    },
    LibSource {
        library: "ieee",
        file: "fixed_generic_pkg-body.vhdl",
        text: include_bytes!("libraries/ieee/fixed_generic_pkg-body.vhdl"),
    },
    LibSource {
        library: "ieee",
        file: "fixed_generic_pkg.vhdl",
        text: include_bytes!("libraries/ieee/fixed_generic_pkg.vhdl"),
    },
    LibSource {
        library: "ieee",
        file: "fixed_pkg.vhdl",
        text: include_bytes!("libraries/ieee/fixed_pkg.vhdl"),
    },
    LibSource {
        library: "ieee",
        file: "float_generic_pkg-body.vhdl",
        text: include_bytes!("libraries/ieee/float_generic_pkg-body.vhdl"),
    },
    LibSource {
        library: "ieee",
        file: "float_generic_pkg.vhdl",
        text: include_bytes!("libraries/ieee/float_generic_pkg.vhdl"),
    },
    LibSource {
        library: "ieee",
        file: "float_pkg.vhdl",
        text: include_bytes!("libraries/ieee/float_pkg.vhdl"),
    },
    LibSource {
        library: "ieee",
        file: "ieee_bit_context.vhdl",
        text: include_bytes!("libraries/ieee/ieee_bit_context.vhdl"),
    },
    LibSource {
        library: "ieee",
        file: "ieee_std_context.vhdl",
        text: include_bytes!("libraries/ieee/ieee_std_context.vhdl"),
    },
    LibSource {
        library: "ieee",
        file: "math_complex-body.vhdl",
        text: include_bytes!("libraries/ieee/math_complex-body.vhdl"),
    },
    LibSource {
        library: "ieee",
        file: "math_complex.vhdl",
        text: include_bytes!("libraries/ieee/math_complex.vhdl"),
    },
    LibSource {
        library: "ieee",
        file: "math_real-body.vhdl",
        text: include_bytes!("libraries/ieee/math_real-body.vhdl"),
    },
    LibSource {
        library: "ieee",
        file: "math_real.vhdl",
        text: include_bytes!("libraries/ieee/math_real.vhdl"),
    },
    LibSource {
        library: "ieee",
        file: "numeric_bit-body.vhdl",
        text: include_bytes!("libraries/ieee/numeric_bit-body.vhdl"),
    },
    LibSource {
        library: "ieee",
        file: "numeric_bit.vhdl",
        text: include_bytes!("libraries/ieee/numeric_bit.vhdl"),
    },
    LibSource {
        library: "ieee",
        file: "numeric_bit_unsigned-body.vhdl",
        text: include_bytes!("libraries/ieee/numeric_bit_unsigned-body.vhdl"),
    },
    LibSource {
        library: "ieee",
        file: "numeric_bit_unsigned.vhdl",
        text: include_bytes!("libraries/ieee/numeric_bit_unsigned.vhdl"),
    },
    LibSource {
        library: "ieee",
        file: "numeric_std-body.vhdl",
        text: include_bytes!("libraries/ieee/numeric_std-body.vhdl"),
    },
    LibSource {
        library: "ieee",
        file: "numeric_std.vhdl",
        text: include_bytes!("libraries/ieee/numeric_std.vhdl"),
    },
    LibSource {
        library: "ieee",
        file: "numeric_std_unsigned-body.vhdl",
        text: include_bytes!("libraries/ieee/numeric_std_unsigned-body.vhdl"),
    },
    LibSource {
        library: "ieee",
        file: "numeric_std_unsigned.vhdl",
        text: include_bytes!("libraries/ieee/numeric_std_unsigned.vhdl"),
    },
    LibSource {
        library: "ieee",
        file: "std_logic_1164-body.vhdl",
        text: include_bytes!("libraries/ieee/std_logic_1164-body.vhdl"),
    },
    LibSource {
        library: "ieee",
        file: "std_logic_1164.vhdl",
        text: include_bytes!("libraries/ieee/std_logic_1164.vhdl"),
    },
    LibSource {
        library: "ieee",
        file: "std_logic_textio.vhdl",
        text: include_bytes!("libraries/ieee/std_logic_textio.vhdl"),
    },
];
