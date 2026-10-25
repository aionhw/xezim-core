//! Mixed-language designs: VHDL entities instantiated from SystemVerilog
//! modules and SV modules instantiated as VHDL components. The language
//! standards leave the boundary to the tool; values cross it as Questa and
//! the other mixed-language simulators pass them (std_ulogic ↔ 4-state
//! logic, bit and boolean ↔ 2-state, integer ↔ 32-bit, real ↔ real).

use std::collections::BTreeMap;

use super::Design;
use super::hir::*;
use crate::vhdl::ast::Dir;

/// What the SystemVerilog side of the design gives the VHDL analysis.
#[derive(Clone, Debug, Default)]
pub struct Mixed {
    /// VHDL entities that SV modules instantiate, one per distinct
    /// parameter binding.
    pub roots: Vec<RootReq>,
    /// The SV modules by lower-case name.
    pub sv_modules: BTreeMap<String, SvModule>,
}

/// An SV module VHDL components may name: its name, port names and
/// parameter names as declared.
#[derive(Clone, Debug, Default)]
pub struct SvModule {
    pub name: String,
    pub ports: Vec<String>,
    pub params: Vec<String>,
}

/// A VHDL entity instantiated from SV, with the instance's parameter
/// overrides (by generic name, or by position).
#[derive(Clone, Debug, PartialEq)]
pub struct RootReq {
    pub entity: String,
    pub generics: Vec<(Option<String>, SvConst)>,
    /// The SV module instantiating it (for diagnostics).
    pub from: String,
}

/// A constant SV parameter value.
#[derive(Clone, Debug, PartialEq)]
pub enum SvConst {
    /// Bits, most significant first (`0 1 x z`), and signedness.
    Bits(String, bool),
    Real(f64),
    Str(String),
}

impl SvConst {
    pub fn as_i64(&self) -> Option<i64> {
        match self {
            SvConst::Bits(b, signed) => {
                if b.chars().any(|c| c != '0' && c != '1') || b.is_empty() {
                    return None;
                }
                let w = b.len();
                let tail = if w > 64 { &b[w - 64..] } else { b.as_str() };
                let mut v = u64::from_str_radix(tail, 2).ok()?;
                if *signed && w < 64 && b.starts_with('1') {
                    v |= !0u64 << w;
                }
                Some(v as i64)
            }
            SvConst::Real(r) => Some(r.round() as i64),
            SvConst::Str(_) => None,
        }
    }

    /// The bits, most significant first (a string: 8 bits a character).
    fn bits(&self) -> Option<String> {
        match self {
            SvConst::Bits(b, _) => Some(b.clone()),
            SvConst::Str(s) => Some(s.bytes().map(|c| format!("{:08b}", c)).collect()),
            SvConst::Real(_) => None,
        }
    }
}

impl Design {
    /// The VHDL value of an SV parameter value given to a generic of type
    /// `ty`, or `None` when the boundary does not carry it.
    pub fn foreign_value(&self, ty: TypeId, v: &SvConst) -> Option<Value> {
        let b = self.base(ty);
        match &self.types[b].kind {
            TypeKind::Integer | TypeKind::UniversalInteger => Some(Value::Int(v.as_i64()?)),
            TypeKind::Real | TypeKind::UniversalReal => Some(Value::Real(match v {
                SvConst::Real(r) => *r,
                _ => v.as_i64()? as f64,
            })),
            TypeKind::Enum(lits) => {
                if b == self.std.character {
                    return match v {
                        SvConst::Str(s) if s.len() == 1 => {
                            Some(Value::Enum(s.as_bytes()[0] as u32))
                        }
                        _ => None,
                    };
                }
                if self.is_logic_enum(b) {
                    let c = v.bits()?.chars().last()?;
                    return self.bit_value(b, c);
                }
                let n = v.as_i64()?;
                (n >= 0 && (n as usize) < lits.len()).then_some(Value::Enum(n as u32))
            }
            TypeKind::Array { index, elem } if index.len() == 1 => {
                let e = self.base(*elem);
                let range = self
                    .array_index_ranges(ty)
                    .and_then(|r| r.first().cloned().flatten());
                if e == self.std.character {
                    let SvConst::Str(s) = v else { return None };
                    let n = s.len() as i64;
                    let (l, dir) = match &range {
                        Some(r) if r.length() == n => (r.left.as_i64()?, r.dir),
                        Some(_) => return None,
                        None => (1, Dir::To),
                    };
                    let elems = s.bytes().map(|c| Value::Enum(c as u32)).collect();
                    return Some(array_value(l, dir, n, elems));
                }
                if !self.is_logic_enum(e) {
                    return None;
                }
                let mut bits = v.bits()?;
                let (l, dir, n) = match &range {
                    Some(r) => (r.left.as_i64()?, r.dir, r.length()),
                    None => (bits.len() as i64 - 1, Dir::Downto, bits.len() as i64),
                };
                // Right-aligned, zero-extended or truncated (IEEE 1800 §6.24).
                let n_us = n.max(0) as usize;
                if bits.len() > n_us {
                    bits = bits[bits.len() - n_us..].to_string();
                } else {
                    bits = "0".repeat(n_us - bits.len()) + &bits;
                }
                let elems = bits
                    .chars()
                    .map(|c| self.bit_value(e, c))
                    .collect::<Option<Vec<_>>>()?;
                Some(array_value(l, dir, n, elems))
            }
            _ => None,
        }
    }

    /// std_ulogic (and its subtypes), bit and boolean: the element types
    /// that cross the boundary as SV bits.
    pub fn is_logic_enum(&self, t: TypeId) -> bool {
        let b = self.base(t);
        b == self.std.bit || b == self.std.boolean || Some(b) == self.std.std_ulogic
    }

    /// The value of SV bit `c` (`0 1 x z`) as an element of type `t`.
    fn bit_value(&self, t: TypeId, c: char) -> Option<Value> {
        let b = self.base(t);
        if Some(b) == self.std.std_ulogic {
            // U X 0 1 Z W L H -
            return Some(Value::Enum(match c {
                '0' => 2,
                '1' => 3,
                'z' => 4,
                _ => 1,
            }));
        }
        match c {
            '0' => Some(Value::Enum(0)),
            '1' => Some(Value::Enum(1)),
            _ => None,
        }
    }
}

fn array_value(left: i64, dir: Dir, n: i64, elems: Vec<Value>) -> Value {
    let right = match dir {
        Dir::To => left + n - 1,
        Dir::Downto => left - n + 1,
    };
    Value::Array(Box::new(ArrayValue {
        left,
        dir,
        right,
        elems,
    }))
}
