# Vendored VHDL standard packages

The `ieee/` and `std/` sources are the IEEE 1076 packages published by the
IEEE P1076 Working Group (<https://opensource.ieee.org/vasg/Packages>,
branch `release`, commit `dc691c8cf8a7365dd1d60895818631320996e983`),
copied unmodified. They are licensed under the Apache License 2.0
(`LICENSE`); the copyright holders are listed in `AUTHORS.md`.

`std/standard.vhdl`, `std/textio.vhdl` and `std/env.vhdl` declare the
packages only; their bodies are implementation-defined and are provided
natively by xezim, except for `std/env-body.vhdl`, written for xezim: the
calendar and time conversions of ENV in VHDL. The 2019-only `std.reflection` package is not included.

`ieee/ieee_std_context.vhdl` and `ieee/ieee_bit_context.vhdl` (the IEEE
1076-2008 context declarations) are not in that repository and were written
for xezim from IEEE Std 1076-2008 §16.8.

`synopsys/` holds the Synopsys packages that GHDL (with `-fsynopsys`),
Questa and most other simulators put in library `ieee`: STD_LOGIC_ARITH,
STD_LOGIC_UNSIGNED and STD_LOGIC_SIGNED, and STD_LOGIC_MISC in the
VHDL-2008 form GHDL ships (`synopsys/v08/`, the declarations that VHDL-2008
makes homographs commented out). They are copied unmodified from GHDL 4.1's
`src/synopsys`. Synopsys' notice in each file permits use and distribution
without restriction provided that the copyright statement is kept.
