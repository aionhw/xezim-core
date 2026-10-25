//! The SystemVerilog side of a mixed-language design: SV instances of
//! VHDL entities (found before the VHDL analysis, rewritten to the lowered
//! modules after it) and the SV modules VHDL components may name.

use std::collections::{BTreeMap, BTreeSet};

use crate::ast::Description;
use crate::ast::decl::{
    ModuleInstantiation, ModuleItem, ParamConnection, ParamValue, ParameterKind, PortConnection,
};
use crate::ast::expr::{BinaryOp, ExprKind, Expression, NumberBase, NumberLiteral, UnaryOp};
use crate::ast::module::PortList;

use super::sema::{RootReq, SvConst, SvModule};

/// The SV modules (also interfaces and programs), by lower-case name.
pub fn sv_modules(descs: &[Description]) -> BTreeMap<String, SvModule> {
    let mut out = BTreeMap::new();
    for d in descs {
        let (name, params, ports, items) = match d {
            Description::Module(m) => (&m.name.name, &m.params, &m.ports, &m.items),
            Description::Interface(i) => (&i.name.name, &i.params, &i.ports, &i.items),
            Description::Program(p) => (&p.name.name, &p.params, &p.ports, &p.items),
            _ => continue,
        };
        let mut m = SvModule {
            name: name.clone(),
            ..Default::default()
        };
        match ports {
            PortList::Ansi(ps) => m.ports.extend(ps.iter().map(|p| p.name.name.clone())),
            PortList::NonAnsi(ps) => m.ports.extend(ps.iter().map(|p| p.name.clone())),
            PortList::Empty => {}
        }
        let body = items.iter().filter_map(|i| match i {
            ModuleItem::ParameterDeclaration(p) => Some(p),
            _ => None,
        });
        for p in params.iter().chain(body) {
            if let ParameterKind::Data { assignments, .. } = &p.kind
                && !p.local
            {
                m.params
                    .extend(assignments.iter().map(|a| a.name.name.clone()));
            }
        }
        out.insert(name.to_ascii_lowercase(), m);
    }
    out
}

/// The SV instances of VHDL entities (`entities`: lower-case names): one
/// request per distinct entity and parameter binding.
pub fn root_requests(
    descs: &[Description],
    entities: &BTreeSet<String>,
) -> Result<Vec<RootReq>, String> {
    let defined: BTreeSet<String> = descs
        .iter()
        .filter_map(|d| match d {
            Description::Module(m) => Some(m.name.name.clone()),
            Description::Interface(i) => Some(i.name.name.clone()),
            Description::Program(p) => Some(p.name.name.clone()),
            _ => None,
        })
        .collect();
    let mut reqs: Vec<RootReq> = Vec::new();
    let mut err = None;
    for d in descs {
        let Description::Module(m) = d else { continue };
        let from = m.name.name.clone();
        let scope = param_scope(m);
        visit(&m.items, &mut |mi| {
            if let Some(r) = request(mi, &defined, entities, &from, &scope, &mut err)
                && !reqs.iter().any(|x| same(x, &r))
            {
                reqs.push(r);
            }
        });
    }
    match err {
        Some(e) => Err(e),
        None => Ok(reqs),
    }
}

fn same(a: &RootReq, b: &RootReq) -> bool {
    a.entity == b.entity && a.generics == b.generics
}

fn request(
    mi: &ModuleInstantiation,
    defined: &BTreeSet<String>,
    entities: &BTreeSet<String>,
    from: &str,
    scope: &Scope,
    err: &mut Option<String>,
) -> Option<RootReq> {
    if defined.contains(&mi.module_name.name) {
        return None;
    }
    let entity = mi.module_name.name.to_ascii_lowercase();
    if !entities.contains(&entity) {
        return None;
    }
    let mut generics = Vec::new();
    for pc in mi.params.iter().flatten() {
        let (name, v) = match pc {
            ParamConnection::Ordered(v) => (None, v),
            ParamConnection::Named { name, value } => (Some(name.name.to_ascii_lowercase()), value),
        };
        let Some(ParamValue::Expr(e)) = v else {
            continue;
        };
        match sv_const(e, scope, 0) {
            Some(c) => generics.push((name, c)),
            None => {
                err.get_or_insert_with(|| {
                    format!(
                        "VHDL: the parameter values of module '{}''s instance of VHDL entity '{}' must be constant expressions of literals and parameters",
                        from, entity
                    )
                });
                return None;
            }
        }
    }
    Some(RootReq {
        entity,
        generics,
        from: from.to_string(),
    })
}

/// Point the SV instances of VHDL entities at the lowered modules
/// (`names`, by request), without parameter overrides (the module is
/// lowered for them) and with the port names VHDL gives (lower case).
pub fn rewrite(descs: &mut [Description], reqs: &[RootReq], names: &[String]) {
    let defined: BTreeSet<String> = sv_modules(descs).into_values().map(|m| m.name).collect();
    let entities: BTreeSet<String> = reqs.iter().map(|r| r.entity.clone()).collect();
    for d in descs.iter_mut() {
        let Description::Module(m) = d else { continue };
        let from = m.name.name.clone();
        let scope = param_scope(m);
        visit_mut(&mut m.items, &mut |mi| {
            let mut err = None;
            let Some(r) = request(mi, &defined, &entities, &from, &scope, &mut err) else {
                return;
            };
            let Some(k) = reqs.iter().position(|x| same(x, &r)) else {
                return;
            };
            mi.module_name.name = names[k].clone();
            mi.params = None;
            for inst in &mut mi.instances {
                for c in &mut inst.connections {
                    if let PortConnection::Named { name, .. } = c {
                        name.name = super::lower_ident(&name.name);
                    }
                }
            }
        });
    }
}

fn visit(items: &[ModuleItem], f: &mut dyn FnMut(&ModuleInstantiation)) {
    for item in items {
        match item {
            ModuleItem::ModuleInstantiation(mi) => f(mi),
            ModuleItem::GenerateIf(gi) => {
                for (_, items) in &gi.branches {
                    visit(items, f);
                }
            }
            ModuleItem::GenerateFor(gf) => visit(&gf.items, f),
            ModuleItem::GenerateRegion(gr) => visit(&gr.items, f),
            ModuleItem::GenerateCase(gc) => {
                for arm in &gc.arms {
                    visit(&arm.items, f);
                }
            }
            _ => {}
        }
    }
}

fn visit_mut(items: &mut [ModuleItem], f: &mut dyn FnMut(&mut ModuleInstantiation)) {
    for item in items {
        match item {
            ModuleItem::ModuleInstantiation(mi) => f(mi),
            ModuleItem::GenerateIf(gi) => {
                for (_, items) in &mut gi.branches {
                    visit_mut(items, f);
                }
            }
            ModuleItem::GenerateFor(gf) => visit_mut(&mut gf.items, f),
            ModuleItem::GenerateRegion(gr) => visit_mut(&mut gr.items, f),
            ModuleItem::GenerateCase(gc) => {
                for arm in &mut gc.arms {
                    visit_mut(&mut arm.items, f);
                }
            }
            _ => {}
        }
    }
}

/// The parameters (and local parameters) of a module with their default
/// values: the scope parameter values are evaluated in.
type Scope = BTreeMap<String, Expression>;

fn param_scope(m: &crate::ast::module::ModuleDeclaration) -> Scope {
    let mut out = Scope::new();
    let body = m.items.iter().filter_map(|i| match i {
        ModuleItem::ParameterDeclaration(p) | ModuleItem::LocalparamDeclaration(p) => Some(p),
        _ => None,
    });
    for p in m.params.iter().chain(body) {
        if let ParameterKind::Data { assignments, .. } = &p.kind {
            for a in assignments {
                if let Some(e) = &a.init {
                    out.insert(a.name.name.clone(), e.clone());
                }
            }
        }
    }
    out
}

/// A constant parameter value: literals, the module's parameters and
/// integer arithmetic on them.
fn sv_const(e: &Expression, scope: &Scope, depth: u32) -> Option<SvConst> {
    if depth > 32 {
        return None;
    }
    let int = |v: i64| Some(SvConst::Bits(format!("{:032b}", v as u32), true));
    match &e.kind {
        ExprKind::Paren(x) => sv_const(x, scope, depth + 1),
        ExprKind::Ident(h)
            if h.root.is_none() && h.path.len() == 1 && h.path[0].selects.is_empty() =>
        {
            sv_const(scope.get(&h.path[0].name.name)?, scope, depth + 1)
        }
        ExprKind::Binary { op, left, right } => {
            let l = sv_const(left, scope, depth + 1)?;
            let r = sv_const(right, scope, depth + 1)?;
            if let (SvConst::Real(_), _) | (_, SvConst::Real(_)) = (&l, &r) {
                let f = |c: &SvConst| match c {
                    SvConst::Real(x) => Some(*x),
                    c => c.as_i64().map(|v| v as f64),
                };
                let (a, b) = (f(&l)?, f(&r)?);
                return Some(SvConst::Real(match op {
                    BinaryOp::Add => a + b,
                    BinaryOp::Sub => a - b,
                    BinaryOp::Mul => a * b,
                    BinaryOp::Div => a / b,
                    BinaryOp::Power => a.powf(b),
                    _ => return None,
                }));
            }
            let (a, b) = (l.as_i64()?, r.as_i64()?);
            let v = match op {
                BinaryOp::Add => a.checked_add(b)?,
                BinaryOp::Sub => a.checked_sub(b)?,
                BinaryOp::Mul => a.checked_mul(b)?,
                BinaryOp::Div => a.checked_div(b)?,
                BinaryOp::Mod => a.checked_rem(b)?,
                BinaryOp::Power => a.checked_pow(u32::try_from(b).ok()?)?,
                BinaryOp::ShiftLeft | BinaryOp::ArithShiftLeft => {
                    a.checked_shl(u32::try_from(b).ok()?)?
                }
                BinaryOp::ShiftRight => ((a as u64) >> u32::try_from(b).ok()?.min(63)) as i64,
                BinaryOp::ArithShiftRight => a >> u32::try_from(b).ok()?.min(63),
                BinaryOp::BitAnd => a & b,
                BinaryOp::BitOr => a | b,
                BinaryOp::BitXor => a ^ b,
                BinaryOp::Eq => (a == b) as i64,
                BinaryOp::Neq => (a != b) as i64,
                BinaryOp::Lt => (a < b) as i64,
                BinaryOp::Leq => (a <= b) as i64,
                BinaryOp::Gt => (a > b) as i64,
                BinaryOp::Geq => (a >= b) as i64,
                BinaryOp::LogAnd => (a != 0 && b != 0) as i64,
                BinaryOp::LogOr => (a != 0 || b != 0) as i64,
                _ => return None,
            };
            int(v)
        }
        ExprKind::Conditional {
            condition,
            then_expr,
            else_expr,
        } => {
            if sv_const(condition, scope, depth + 1)?.as_i64()? != 0 {
                sv_const(then_expr, scope, depth + 1)
            } else {
                sv_const(else_expr, scope, depth + 1)
            }
        }
        ExprKind::SystemCall { name, args } if name == "$clog2" && args.len() == 1 => {
            let v = sv_const(&args[0], scope, depth + 1)?.as_i64()?;
            let mut n = 0;
            while (1i64 << n) < v {
                n += 1;
            }
            int(n)
        }
        ExprKind::Number(NumberLiteral::Integer {
            size,
            signed,
            base,
            value,
            ..
        }) => {
            let digits: String = value.chars().filter(|c| *c != '_').collect();
            let per = match base {
                NumberBase::Binary => 1,
                NumberBase::Octal => 3,
                NumberBase::Hex => 4,
                NumberBase::Decimal => 0,
            };
            let mut bits = String::new();
            if per == 0 {
                let lc = digits.to_ascii_lowercase();
                if lc.chars().all(|c| c == 'x' || c == 'z' || c == '?') && !lc.is_empty() {
                    let c = if lc.starts_with('x') { 'x' } else { 'z' };
                    bits = c.to_string().repeat(size.unwrap_or(32) as usize);
                } else {
                    let v: u128 = digits.parse().ok()?;
                    bits = format!("{:b}", v);
                }
            } else {
                for c in digits.chars() {
                    let c = c.to_ascii_lowercase();
                    match c {
                        'x' | 'z' | '?' => {
                            let b = if c == 'x' { 'x' } else { 'z' };
                            bits.extend(std::iter::repeat_n(b, per));
                        }
                        _ => {
                            let v = c.to_digit(16)?;
                            bits.push_str(&format!("{:0w$b}", v, w = per));
                        }
                    }
                }
            }
            // Unsized: 32 bits; extended with zeros (x or z when the most
            // significant digit is one, IEEE 1800 §5.7.1).
            let w = size.unwrap_or(32) as usize;
            let fill = match bits.chars().next() {
                Some(c @ ('x' | 'z')) => c,
                _ => '0',
            };
            if bits.len() > w {
                bits = bits[bits.len() - w..].to_string();
            } else {
                bits = fill.to_string().repeat(w - bits.len()) + &bits;
            }
            Some(SvConst::Bits(bits, *signed || size.is_none() && per == 0))
        }
        ExprKind::Number(NumberLiteral::Real(r)) => Some(SvConst::Real(*r)),
        ExprKind::Number(NumberLiteral::UnbasedUnsized(c)) => {
            Some(SvConst::Bits(c.to_ascii_lowercase().to_string(), false))
        }
        ExprKind::StringLiteral(s) => Some(SvConst::Str(s.clone())),
        ExprKind::Unary {
            op: UnaryOp::Minus,
            operand,
        } => match sv_const(operand, scope, depth + 1)? {
            SvConst::Real(r) => Some(SvConst::Real(-r)),
            c => {
                let v = c.as_i64()?.checked_neg()?;
                Some(SvConst::Bits(format!("{:032b}", v as u32), true))
            }
        },
        ExprKind::Unary {
            op: UnaryOp::Plus,
            operand,
        } => sv_const(operand, scope, depth + 1),
        _ => None,
    }
}
