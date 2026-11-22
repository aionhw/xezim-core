use super::*;

/// Stringify one `extends Base #(arg)` positional argument for
/// `ElaboratedClass.extends_type_args`. Type args become their bare type or
/// type-parameter name (e.g. `this_type`, `T`, a concrete class name); value
/// args become their expression text (a bare identifier or an integer
/// literal). Anything we cannot render simply becomes "<unknown>", which the
/// specialization-chain resolver treats as "give up on this arg".
pub(super) fn param_value_to_arg_string(pv: &ParamValue) -> String {
    match pv {
        ParamValue::Type(dt) => {
            data_type_to_spec_fragment(dt).unwrap_or_else(|| "<unknown>".to_string())
        }
        ParamValue::Expr(ex) => expr_to_arg_string(ex),
    }
}

/// Render a `DataType` (the default of a `type T = <dt>` parameter) to the
/// textual fragment used in specialization-signature canonicalization. Only
/// the shapes that can legally be a type-parameter default are handled
/// (class/type-reference and simple built-ins); anything else yields None so
/// the caller leaves that param position un-padded.
pub fn data_type_to_spec_fragment(dt: &DataType) -> Option<String> {
    use crate::ast::types::{IntegerAtomType, IntegerVectorType, RealType};
    match dt {
        DataType::TypeReference { name, .. } => Some(name.name.name.clone()),
        DataType::Simple { kind, .. } => Some(format!("{:?}", kind).to_lowercase()),
        // Built-in types are just as valid a DEFAULT for a type parameter as a
        // named one (`class C #(type T = int);`). Without these arms the
        // default was dropped, so `T` was left unbound on an unspecialized
        // instance and a property declared `T p;` had no type to clamp to.
        DataType::IntegerAtom { kind, signing, .. } => {
            let mut out = match kind {
                IntegerAtomType::Byte => "byte",
                IntegerAtomType::ShortInt => "shortint",
                IntegerAtomType::Int => "int",
                IntegerAtomType::LongInt => "longint",
                IntegerAtomType::Integer => "integer",
                IntegerAtomType::Time => "time",
            }
            .to_string();
            // §6.11 / §8.25: explicit non-default signing is type identity.
            match (kind, signing) {
                (IntegerAtomType::Time, Some(crate::ast::types::Signing::Signed)) => {
                    out.push_str(" signed")
                }
                (IntegerAtomType::Time, _) => {}
                (_, Some(crate::ast::types::Signing::Unsigned)) => out.push_str(" unsigned"),
                _ => {}
            }
            Some(out)
        }
        // The packed range is intentionally not rendered: a type ARGUMENT
        // loses its range at parse time too, so keeping the bare keyword here
        // matches what an explicit `#(logic [63:0])` produces.
        // Dimensions and signing are part of the type's identity:
        // `P#(bit[7:0])` is not `P#(bit)`. Literal bounds render inline;
        // a bound that is not a plain integer literal cannot be named here
        // and declines, so the caller falls back rather than aliasing.
        DataType::IntegerVector {
            kind,
            signing,
            dimensions,
            ..
        } => {
            let mut out = match kind {
                IntegerVectorType::Bit => "bit",
                IntegerVectorType::Logic => "logic",
                IntegerVectorType::Reg => "reg",
            }
            .to_string();
            if matches!(signing, Some(crate::ast::types::Signing::Signed)) {
                out.push_str(" signed");
            }
            for d in dimensions {
                match d {
                    crate::ast::types::PackedDimension::Range { left, right, .. } => {
                        let lit = |e: &crate::ast::expr::Expression| match &e.kind {
                            crate::ast::expr::ExprKind::Number(
                                crate::ast::expr::NumberLiteral::Integer { value, .. },
                            ) => Some(value.clone()),
                            _ => None,
                        };
                        let (l, r) = (lit(left)?, lit(right)?);
                        out.push_str(&format!("[{}:{}]", l, r));
                    }
                    crate::ast::types::PackedDimension::Unsized(_) => return None,
                }
            }
            Some(out)
        }
        DataType::Real { kind, .. } => Some(
            match kind {
                RealType::Real => "real",
                RealType::ShortReal => "shortreal",
                RealType::RealTime => "realtime",
            }
            .to_string(),
        ),
        // §25.9: a virtual-interface type, spelled as the simulator's
        // specialization keys spell it (`virtual I#(a,b).mp`).
        DataType::Interface {
            name,
            modport,
            type_args,
            ..
        } => {
            let mut out = format!("virtual {}", name.name);
            if !type_args.is_empty() {
                let args: Vec<String> = type_args.iter().map(expr_to_arg_string).collect();
                if args.iter().any(|a| a.contains("<unknown>")) {
                    return None;
                }
                out.push_str(&format!("#({})", args.join(",")));
            }
            if let Some(mp) = modport {
                out.push('.');
                out.push_str(&mp.name);
            }
            Some(out)
        }
        _ => None,
    }
}

/// Render the small set of expression shapes that appear as class parameter
/// arguments: a (possibly hierarchical) identifier and an integer literal.
pub(super) fn expr_to_arg_string(ex: &Expression) -> String {
    use crate::ast::expr::{ExprKind, NumberLiteral};
    match &ex.kind {
        ExprKind::Ident(h) => {
            if h.path.len() == 1 && h.root.is_none() {
                h.path[0].name.name.clone()
            } else {
                let mut parts: Vec<String> = h.root.iter().cloned().collect();
                parts.extend(h.path.iter().map(|seg| seg.name.name.clone()));
                parts.join("::")
            }
        }
        ExprKind::TypeLiteral(dt) => match dt.as_ref() {
            DataType::TypeReference { name, .. } => name.name.name.clone(),
            // §25.9: `extends B#(virtual I#(T))`.
            DataType::Interface { .. } => {
                data_type_to_spec_fragment(dt).unwrap_or_else(|| "<unknown>".to_string())
            }
            _ => "<unknown>".to_string(),
        },
        ExprKind::Number(NumberLiteral::Integer { value, .. }) => value.clone(),
        // §8.25 named argument `.NAME(value)`: keep the name, so the
        // simulator can move the value to NAME's slot in the base's list.
        ExprKind::NamedArg {
            name,
            expr: Some(x),
        } => {
            let v = match &x.kind {
                ExprKind::TypeLiteral(dt) => {
                    data_type_to_spec_fragment(dt).unwrap_or_else(|| "<unknown>".to_string())
                }
                _ => expr_to_arg_string(x),
            };
            format!(".{}({})", name.name, v)
        }
        // Nested parameterized type arg in an `extends` clause, e.g.
        // `class X extends Y#(Z#(T))`. Per-specialization keying relies on
        // the rendered arg matching the specialization text used elsewhere.
        ExprKind::Specialization {
            base,
            type_args_text,
            ..
        } => {
            if let ExprKind::Ident(h) = &base.kind {
                if let Some(last) = h.path.last() {
                    return format!("{}#({})", last.name.name, type_args_text);
                }
            }
            "<unknown>".to_string()
        }
        ExprKind::StringLiteral(s) => format!("\"{}\"", s),
        _ => "<unknown>".to_string(),
    }
}

pub(super) fn data_type_kind_name(dt: &DataType) -> String {
    match dt {
        DataType::Void(_) => "void".to_string(),
        DataType::IntegerAtom { kind, signing, .. } => format!("atom:{:?}:{:?}", kind, signing),
        DataType::IntegerVector {
            kind,
            signing,
            dimensions,
            ..
        } => format!("vec:{:?}:{:?}:{}", kind, signing, dimensions.len()),
        DataType::Real { kind, .. } => format!("real:{:?}", kind),
        DataType::Simple { kind, .. } => format!("simple:{:?}", kind),
        DataType::TypeReference { name, .. } => format!("tref:{}", name.name.name),
        DataType::Interface { name, .. } => format!("iface:{}", name.name),
        DataType::Struct(_) => "struct".to_string(),
        DataType::Enum(_) => "enum".to_string(),
        DataType::Implicit { .. } => "implicit".to_string(),
    }
}
