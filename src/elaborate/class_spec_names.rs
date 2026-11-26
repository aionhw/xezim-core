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

/// Canonicalize a built-in scalar/vector/real type fragment per IEEE 1800-2023 §6.22.1
/// so matching built-in types share one specialization signature:
/// - `bit signed[31:0]` <-> `int`, `bit[31:0]` <-> `int unsigned`
/// - `bit signed[7:0]` <-> `byte`, `bit[7:0]` <-> `byte unsigned`
/// - `bit signed[15:0]` <-> `shortint`, `bit[15:0]` <-> `shortint unsigned`
/// - `bit signed[63:0]` <-> `longint`, `bit[63:0]` <-> `longint unsigned`
/// - `logic signed[31:0]` <-> `integer`, `logic[31:0]` <-> `integer unsigned`
/// - `logic[63:0]` <-> `time`, `logic signed[63:0]` <-> `time signed`
/// - `reg` <-> `logic`, `realtime` <-> `real`, `bit unsigned` <-> `bit`
/// Preserves packed bounds (`[0:0]` != scalar `bit`, `[3:0]` != `[4:1]` != `[0:3]`).
pub fn canonicalize_builtin_type_fragment(frag: &str) -> Option<String> {
    let s = frag.trim();
    let kw_end = s
        .find(|c: char| !c.is_ascii_alphabetic())
        .unwrap_or(s.len());
    let kw = &s[..kw_end];
    let mut rest = s[kw_end..].trim_start();
    match kw {
        "real" | "realtime" => return rest.is_empty().then(|| "real".to_string()),
        "shortreal" => return rest.is_empty().then(|| "shortreal".to_string()),
        _ => {}
    }
    let (is_4state, default_signed, atom_range): (bool, bool, Option<(i64, i64)>) = match kw {
        "byte" => (false, true, Some((7, 0))),
        "shortint" => (false, true, Some((15, 0))),
        "int" => (false, true, Some((31, 0))),
        "longint" => (false, true, Some((63, 0))),
        "integer" => (true, true, Some((31, 0))),
        "time" => (true, false, Some((63, 0))),
        "bit" => (false, false, None),
        "logic" | "reg" => (true, false, None),
        _ => return None,
    };
    let mut signing: Option<bool> = None;
    if let Some(after) = rest.strip_prefix("signed")
        && after
            .chars()
            .next()
            .is_none_or(|c| c.is_ascii_whitespace() || c == '[')
    {
        signing = Some(true);
        rest = after.trim_start();
    } else if let Some(after) = rest.strip_prefix("unsigned")
        && after
            .chars()
            .next()
            .is_none_or(|c| c.is_ascii_whitespace() || c == '[')
    {
        signing = Some(false);
        rest = after.trim_start();
    }
    let is_signed = signing.unwrap_or(default_signed);
    let mut dims: Vec<(i64, i64)> = Vec::new();
    while let Some(after_open) = rest.strip_prefix('[') {
        let close = after_open.find(']')?;
        let (l, r) = after_open[..close].split_once(':')?;
        let l = l.trim().parse::<i64>().ok()?;
        let r = r.trim().parse::<i64>().ok()?;
        dims.push((l, r));
        rest = after_open[close + 1..].trim_start();
    }
    if !rest.is_empty() {
        return None;
    }
    if let Some(ar) = atom_range {
        if !dims.is_empty() {
            return None;
        }
        dims.push(ar);
    }
    if dims.is_empty() {
        return Some(
            match (is_4state, is_signed) {
                (false, false) => "bit",
                (false, true) => "bit signed",
                (true, false) => "logic",
                (true, true) => "logic signed",
            }
            .to_string(),
        );
    }
    Some(match (is_4state, is_signed, dims.as_slice()) {
        (false, true, [(7, 0)]) => "byte".to_string(),
        (false, true, [(15, 0)]) => "shortint".to_string(),
        (false, true, [(31, 0)]) => "int".to_string(),
        (false, true, [(63, 0)]) => "longint".to_string(),
        (true, true, [(31, 0)]) => "integer".to_string(),
        (true, false, [(63, 0)]) => "time".to_string(),
        _ => {
            let mut out = if is_4state {
                "logic".to_string()
            } else {
                "bit".to_string()
            };
            if is_signed {
                out.push_str(" signed");
            }
            for (l, r) in dims {
                out.push_str(&format!("[{}:{}]", l, r));
            }
            out
        }
    })
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
            match signing {
                Some(crate::ast::types::Signing::Signed) => out.push_str(" signed"),
                Some(crate::ast::types::Signing::Unsigned) => out.push_str(" unsigned"),
                None => {}
            }
            Some(canonicalize_builtin_type_fragment(&out).unwrap_or(out))
        }
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
            Some(canonicalize_builtin_type_fragment(&out).unwrap_or(out))
        }
        DataType::Real { kind, .. } => Some(
            match kind {
                RealType::Real | RealType::RealTime => "real",
                RealType::ShortReal => "shortreal",
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
                let mut parts: Vec<String> = h.root.iter().map(|r| r.as_str().to_string()).collect();
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

#[cfg(test)]
mod tests {
    use super::canonicalize_builtin_type_fragment;

    fn canon(s: &str) -> String {
        canonicalize_builtin_type_fragment(s).unwrap_or_else(|| s.to_string())
    }

    #[test]
    fn matching_builtin_specialization_fragments_agree() {
        assert_eq!(canon("int"), canon("bit signed[31:0]"));
        assert_eq!(canon("int signed"), canon("int"));
        assert_eq!(canon("int unsigned"), canon("bit[31:0]"));
        assert_eq!(canon("bit unsigned[31:0]"), canon("bit[31:0]"));

        assert_eq!(canon("byte"), canon("bit signed[7:0]"));
        assert_eq!(canon("byte unsigned"), canon("bit[7:0]"));

        assert_eq!(canon("shortint"), canon("bit signed[15:0]"));
        assert_eq!(canon("shortint unsigned"), canon("bit[15:0]"));

        assert_eq!(canon("longint"), canon("bit signed[63:0]"));
        assert_eq!(canon("longint unsigned"), canon("bit[63:0]"));

        assert_eq!(canon("integer"), canon("logic signed[31:0]"));
        assert_eq!(canon("integer unsigned"), canon("logic[31:0]"));

        assert_eq!(canon("time"), canon("logic[63:0]"));
        assert_eq!(canon("time signed"), canon("logic signed[63:0]"));
        assert_eq!(canon("reg signed[63:0]"), canon("time signed"));

        assert_eq!(canon("reg"), canon("logic"));
        assert_eq!(canon("realtime"), canon("real"));
        assert_eq!(canon("bit unsigned"), canon("bit"));
        assert_eq!(canon("reg[0:0]"), canon("logic[0:0]"));
    }

    #[test]
    fn non_matching_builtin_specialization_fragments_stay_distinct() {
        assert_ne!(canon("bit[0:0]"), canon("bit"));
        assert_ne!(canon("logic[0:0]"), canon("logic"));
        assert_ne!(canon("logic[3:0]"), canon("logic[4:1]"));
        assert_ne!(canon("logic[4:1]"), canon("logic[0:3]"));
        assert_ne!(canon("shortreal"), canon("real"));
    }
}
