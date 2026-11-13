//! IEEE 1800-2023 §11.8.2: type constant operands before applying operators.
//!
//! The cache belongs to one expression and one immutable parameter scope.
//! Self-determined leaves evaluated to discover their type are consumed once;
//! nested casts/selects must not multiply evaluation work at each boundary.
use super::*;

#[derive(Clone, Copy)]
pub(super) struct Type {
    pub width: u32,
    pub signed: bool,
    pub integral: bool,
    pub real: bool,
}
impl Type {
    fn integer(width: u32, signed: bool) -> Self {
        Self {
            width,
            signed,
            integral: true,
            real: false,
        }
    }
    fn of(value: &Value) -> Self {
        Self {
            width: value.width,
            signed: value.is_signed,
            integral: !value.is_real,
            real: value.is_real,
        }
    }
    fn common(self, other: Self) -> Self {
        Self {
            width: self.width.max(other.width),
            signed: self.signed && other.signed,
            integral: self.integral && other.integral,
            real: self.real || other.real,
        }
    }
}

struct Entry {
    ty: Type,
    value: Option<Value>,
}
#[derive(Default)]
pub(super) struct Types(HashMap<usize, Entry>);
impl Types {
    pub fn take_value(&mut self, expr: &Expression) -> Option<Value> {
        self.0.get_mut(&(expr as *const _ as usize))?.value.take()
    }
}

pub(super) fn infer(expr: &Expression, params: &HashMap<String, Value>, types: &mut Types) -> Type {
    let key = expr as *const _ as usize;
    if let Some(entry) = types.0.get(&key) {
        return entry.ty;
    }
    let mut cached = None;
    let ty = match &expr.kind {
        ExprKind::Number(NumberLiteral::Integer { size, signed, .. }) => {
            Type::integer(size.unwrap_or(32), *signed)
        }
        ExprKind::Number(NumberLiteral::UnbasedUnsized(_)) => Type::integer(1, false),
        ExprKind::Number(NumberLiteral::Real(_)) => Type {
            width: 64,
            signed: false,
            integral: false,
            real: true,
        },
        ExprKind::StringLiteral(text) => Type {
            width: text.len() as u32 * 8,
            signed: false,
            integral: false,
            real: false,
        },
        ExprKind::Paren(inner) => infer(inner, params, types),
        ExprKind::Binary { op, left, right } if is_context_operator(expr) => {
            let left = infer(left, params, types);
            if matches!(
                op,
                BinaryOp::ShiftLeft
                    | BinaryOp::ShiftRight
                    | BinaryOp::ArithShiftLeft
                    | BinaryOp::ArithShiftRight
                    | BinaryOp::Power
            ) {
                left
            } else {
                left.common(infer(right, params, types))
            }
        }
        ExprKind::Binary { op, .. }
            if is_comparison(*op)
                || matches!(
                    op,
                    BinaryOp::LogAnd | BinaryOp::LogOr | BinaryOp::LogImplies | BinaryOp::LogEquiv
                ) =>
        {
            Type::integer(1, false)
        }
        ExprKind::Unary { op, operand } => {
            if matches!(op, UnaryOp::Plus | UnaryOp::Minus | UnaryOp::BitNot) {
                infer(operand, params, types)
            } else {
                Type::integer(1, false)
            }
        }
        ExprKind::Conditional {
            then_expr,
            else_expr,
            ..
        } => infer(then_expr, params, types).common(infer(else_expr, params, types)),
        ExprKind::Concatenation(parts) => {
            let mut ty = Type::integer(0, false);
            for part in parts {
                let child = infer(part, params, types);
                ty.width = ty.width.saturating_add(child.width);
                ty.integral &= child.integral;
            }
            ty
        }
        ExprKind::Replication { count, exprs } => {
            let count = eval_const_expr_val_inner(count, params, types)
                .to_u64()
                .unwrap_or(0);
            let width: u32 = exprs
                .iter()
                .map(|part| infer(part, params, types).width)
                .fold(0, u32::saturating_add);
            Type::integer(
                (width as u64).saturating_mul(count).min(u32::MAX as u64) as u32,
                false,
            )
        }
        ExprKind::SystemCall { name, .. }
            if const_real_math_arity(name).is_some()
                || matches!(name.as_str(), "$itor" | "$bitstoreal" | "$bitstoshortreal") =>
        {
            Type {
                width: 64,
                signed: false,
                integral: false,
                real: true,
            }
        }
        ExprKind::Call { func, .. } => match function_type(func, params) {
            Some(ty) => ty,
            None => {
                let value = eval_const_expr_val_inner(expr, params, types);
                let ty = Type::of(&value);
                cached = Some(value);
                ty
            }
        },
        _ => {
            let value = eval_const_expr_val_inner(expr, params, types);
            let mut ty = Type::of(&value);
            if let ExprKind::Ident(h) = &expr.kind {
                ty.integral &= !h
                    .path
                    .last()
                    .is_some_and(|part| tls_is_string_param(&part.name.name));
            }
            cached = Some(value);
            ty
        }
    };
    types.0.insert(key, Entry { ty, value: cached });
    ty
}

fn function_type(func: &Expression, params: &HashMap<String, Value>) -> Option<Type> {
    let (name, scoped) = const_fn_call_name(func)?;
    let declared = FUNCS_TLS.with(|f| {
        let funcs = f.borrow();
        let funcs = funcs.as_ref()?;
        scoped
            .as_deref()
            .and_then(|key| funcs.get(key))
            .or_else(|| funcs.get(&name))
            .map(|fd| fd.return_type.clone())
    })?;
    let resolved = TYPEDEF_TYPES_TLS
        .with(|t| {
            t.borrow()
                .as_ref()
                .map(|t| resolve_typedef_chain(&declared, t).clone())
        })
        .unwrap_or(declared);
    let real = is_type_real(&resolved);
    let text = is_string_data_type(&resolved);
    let width = if real {
        64
    } else {
        typedefs_snapshot(|td| resolve_type_width(&resolved, Some(params), td))
    };
    (width > 0 || text).then_some(Type {
        width,
        signed: is_type_signed(&resolved),
        integral: !real && !text,
        real,
    })
}

pub(super) fn is_comparison(op: BinaryOp) -> bool {
    matches!(
        op,
        BinaryOp::Eq
            | BinaryOp::Neq
            | BinaryOp::CaseEq
            | BinaryOp::CaseNeq
            | BinaryOp::WildcardEq
            | BinaryOp::WildcardNeq
            | BinaryOp::Lt
            | BinaryOp::Leq
            | BinaryOp::Gt
            | BinaryOp::Geq
    )
}

