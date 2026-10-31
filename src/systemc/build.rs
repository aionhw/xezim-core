//! Constructors for the SystemVerilog AST nodes the SystemC lowering emits.
//!
//! Every node gets its own synthetic span above [`SPAN_BASE`]: the
//! simulator keys several caches by span offsets, so synthesized nodes must
//! not share one, and an offset past every source text makes location
//! lookups report "no location" instead of pointing into a real file. The
//! node shapes mirror what the SystemVerilog parser produces for the same
//! source, which is what elaboration expects.

use std::cell::{Cell, OnceCell};
use std::sync::atomic::{AtomicUsize, Ordering};

use crate::ast::Identifier;
use crate::ast::Span;
use crate::ast::decl::*;
use crate::ast::expr::*;
use crate::ast::module::*;
use crate::ast::stmt::*;
use crate::ast::types::*;

/// Synthetic spans start here, far above any source text length.
pub const SPAN_BASE: usize = 1 << 40;

static NEXT_SPAN: AtomicUsize = AtomicUsize::new(SPAN_BASE);

/// A fresh one-byte span.
pub fn sp() -> Span {
    let s = NEXT_SPAN.fetch_add(2, Ordering::Relaxed);
    Span::new(s, s + 1)
}

/// Reserve `len` span offsets (for a parsed text whose token spans are
/// shifted into the synthetic range); returns the base offset.
pub fn reserve(len: usize) -> usize {
    NEXT_SPAN.fetch_add(len + 2, Ordering::Relaxed)
}

pub fn id(name: &str) -> Identifier {
    Identifier {
        name: name.to_string(),
        span: sp(),
    }
}

// ---- expressions -----------------------------------------------------------

pub fn ex(kind: ExprKind) -> Expression {
    Expression::new(kind, sp())
}

pub fn ident(name: &str) -> Expression {
    ex(ExprKind::Ident(HierarchicalIdentifier {
        root: None,
        path: vec![HierPathSegment {
            name: id(name),
            selects: Vec::new(),
        }],
        span: sp(),
        cached_signal_id: Cell::new(None),
        cached_resolved_name: OnceCell::new(),
    }))
}

/// `process::self()` (§9.7): the running process.
pub fn process_self() -> Expression {
    let seg = |n: &str| HierPathSegment {
        name: id(n),
        selects: Vec::new(),
    };
    let callee = ex(ExprKind::Ident(HierarchicalIdentifier {
        root: None,
        path: vec![seg("process"), seg("self")],
        span: sp(),
        cached_signal_id: Cell::new(None),
        cached_resolved_name: OnceCell::new(),
    }));
    call(callee, Vec::new())
}

pub fn member(base: Expression, name: &str) -> Expression {
    ex(ExprKind::MemberAccess {
        expr: Box::new(base),
        member: id(name),
    })
}

fn integer(size: Option<u32>, signed: bool, value: String) -> Expression {
    ex(ExprKind::Number(NumberLiteral::Integer {
        size,
        signed,
        base: NumberBase::Decimal,
        value,
        cached_val: Cell::new(None),
    }))
}

/// A sized unsigned literal in base 2 or 16 (`digits` may hold x/z).
pub fn based_lit(width: u32, base: NumberBase, digits: String) -> Expression {
    ex(ExprKind::Number(NumberLiteral::Integer {
        size: Some(width),
        signed: false,
        base,
        value: digits,
        cached_val: Cell::new(None),
    }))
}

/// A signed 32-bit decimal literal (negative values as unary minus).
pub fn int(v: i64) -> Expression {
    if v < 0 {
        return unary(
            UnaryOp::Minus,
            integer(None, true, v.unsigned_abs().to_string()),
        );
    }
    integer(None, true, v.to_string())
}

/// An unsigned 64-bit literal (`64'd…`).
pub fn u64_lit(v: u64) -> Expression {
    integer(Some(64), false, v.to_string())
}

/// A sized unsigned literal of `width` bits.
pub fn sized(width: u32, v: u64) -> Expression {
    integer(Some(width), false, v.to_string())
}

pub fn real(v: f64) -> Expression {
    ex(ExprKind::Number(NumberLiteral::Real(v)))
}

pub fn string(s: &str) -> Expression {
    ex(ExprKind::StringLiteral(s.to_string()))
}

pub fn unary(op: UnaryOp, operand: Expression) -> Expression {
    ex(ExprKind::Unary {
        op,
        operand: Box::new(operand),
    })
}

pub fn bin(op: BinaryOp, left: Expression, right: Expression) -> Expression {
    ex(ExprKind::Binary {
        op,
        left: Box::new(left),
        right: Box::new(right),
    })
}

pub fn cond(c: Expression, t: Expression, f: Expression) -> Expression {
    ex(ExprKind::Conditional {
        condition: Box::new(c),
        then_expr: Box::new(t),
        else_expr: Box::new(f),
    })
}

pub fn concat(parts: Vec<Expression>) -> Expression {
    ex(ExprKind::Concatenation(parts))
}

pub fn index(base: Expression, i: Expression) -> Expression {
    ex(ExprKind::Index {
        expr: Box::new(base),
        index: Box::new(i),
    })
}

/// A stable text for a simple lvalue (`a`, `a.b`, `a[2]`): a key for the
/// object it names (spans are synthetic, so `{:?}` differs per build).
pub fn expr_key(e: &Expression) -> String {
    match &e.kind {
        ExprKind::Ident(h) => h
            .path
            .iter()
            .map(|s| s.name.name.clone())
            .collect::<Vec<_>>()
            .join("."),
        ExprKind::MemberAccess { expr, member } => format!("{}.{}", expr_key(expr), member.name),
        ExprKind::Index { expr, index } => format!("{}[{}]", expr_key(expr), expr_key(index)),
        ExprKind::Number(NumberLiteral::Integer { value, .. }) => format!("{}", value),
        _ => "?".to_string(),
    }
}

/// `base[left:right]`.
pub fn range(base: Expression, left: Expression, right: Expression) -> Expression {
    ex(ExprKind::RangeSelect {
        expr: Box::new(base),
        kind: RangeKind::Constant,
        left: Box::new(left),
        right: Box::new(right),
    })
}

pub fn call(func: Expression, args: Vec<Expression>) -> Expression {
    ex(ExprKind::Call {
        func: Box::new(func),
        args,
    })
}

pub fn call_fn(name: &str, args: Vec<Expression>) -> Expression {
    call(ident(name), args)
}

pub fn method(obj: Expression, name: &str, args: Vec<Expression>) -> Expression {
    call(member(obj, name), args)
}

pub fn sys(name: &str, args: Vec<Expression>) -> Expression {
    ex(ExprKind::SystemCall {
        name: name.to_string(),
        args,
    })
}

pub fn paren(e: Expression) -> Expression {
    ex(ExprKind::Paren(Box::new(e)))
}

pub fn null() -> Expression {
    ex(ExprKind::Null)
}

/// `new(args)`; `new` alone when `args` is `None`.
pub fn new_obj(args: Option<Vec<Expression>>) -> Expression {
    match args {
        Some(a) => call_fn("new", a),
        None => ident("new"),
    }
}

/// `type'(e)`.
pub fn type_cast(dt: DataType, e: Expression) -> Expression {
    sys(
        "$__xz_type_cast",
        vec![ex(ExprKind::TypeLiteral(Box::new(dt))), e],
    )
}

/// `N'(e)`.
pub fn size_cast(width: u32, e: Expression) -> Expression {
    sys("$__xz_size_cast", vec![int(width as i64), e])
}

// ---- statements ------------------------------------------------------------

pub fn st(kind: StatementKind) -> Statement {
    Statement::new(kind, sp())
}

pub fn null_stmt() -> Statement {
    st(StatementKind::Null)
}

pub fn block(stmts: Vec<Statement>) -> Statement {
    st(StatementKind::SeqBlock { name: None, stmts })
}

pub fn assign(lvalue: Expression, rvalue: Expression) -> Statement {
    st(StatementKind::BlockingAssign { lvalue, rvalue })
}

pub fn nba(lvalue: Expression, rvalue: Expression) -> Statement {
    st(StatementKind::NonblockingAssign {
        lvalue,
        delay: None,
        rvalue,
    })
}

pub fn expr_stmt(e: Expression) -> Statement {
    st(StatementKind::Expr(e))
}

pub fn if_(c: Expression, t: Statement, f: Option<Statement>) -> Statement {
    st(StatementKind::If {
        unique_priority: None,
        condition: c,
        then_stmt: Box::new(t),
        else_stmt: f.map(Box::new),
    })
}

/// `#d stmt` (`#d;` with a null statement).
pub fn delay(d: Expression, s: Statement) -> Statement {
    st(StatementKind::TimingControl {
        control: TimingControl::Delay(d),
        stmt: Box::new(s),
    })
}

pub fn event_expr(edge: Option<Edge>, e: Expression) -> EventExpr {
    EventExpr {
        edge,
        expr: e,
        iff: None,
        span: sp(),
    }
}

/// `@(e1 or e2 …) stmt`.
pub fn at(events: Vec<EventExpr>, s: Statement) -> Statement {
    st(StatementKind::TimingControl {
        control: TimingControl::Event(EventControl::EventExpr(events)),
        stmt: Box::new(s),
    })
}

/// `wait (c);`
pub fn wait(c: Expression) -> Statement {
    st(StatementKind::Wait {
        condition: c,
        stmt: Box::new(null_stmt()),
    })
}

pub fn forever(s: Statement) -> Statement {
    st(StatementKind::Forever { body: Box::new(s) })
}

pub fn repeat(n: Expression, s: Statement) -> Statement {
    st(StatementKind::Repeat {
        count: n,
        body: Box::new(s),
    })
}

pub fn while_(c: Expression, s: Statement) -> Statement {
    st(StatementKind::While {
        condition: c,
        body: Box::new(s),
    })
}

pub fn do_while(s: Statement, c: Expression) -> Statement {
    st(StatementKind::DoWhile {
        body: Box::new(s),
        condition: c,
    })
}

pub fn fork(join: JoinType, stmts: Vec<Statement>) -> Statement {
    st(StatementKind::ParBlock {
        name: None,
        join_type: join,
        stmts,
    })
}

pub fn disable_fork() -> Statement {
    st(StatementKind::DisableFork)
}

pub fn ret(e: Option<Expression>) -> Statement {
    st(StatementKind::Return(e))
}

pub fn trigger(name: &str) -> Statement {
    st(StatementKind::EventTrigger {
        nonblocking: false,
        name: id(name),
        target: Some(Box::new(ident(name))),
        span: sp(),
    })
}

/// `->> name;` (the trigger happens in the NBA region).
pub fn trigger_nb(name: &str) -> Statement {
    st(StatementKind::EventTrigger {
        nonblocking: true,
        name: id(name),
        target: Some(Box::new(ident(name))),
        span: sp(),
    })
}

pub fn var_decl(dt: DataType, name: &str, init: Option<Expression>) -> Statement {
    st(StatementKind::VarDecl {
        data_type: dt,
        lifetime: None,
        declarators: vec![var_declarator(name, Vec::new(), init)],
    })
}

pub fn var_declarator(
    name: &str,
    dims: Vec<UnpackedDimension>,
    init: Option<Expression>,
) -> VarDeclarator {
    VarDeclarator {
        name: id(name),
        dimensions: dims,
        init,
        span: sp(),
    }
}

// ---- types -----------------------------------------------------------------

fn vector(kind: IntegerVectorType, width: u32, signed: bool) -> DataType {
    DataType::IntegerVector {
        kind,
        signing: signed.then_some(Signing::Signed),
        dimensions: if width > 1 || signed {
            vec![PackedDimension::Range {
                left: Box::new(int(width as i64 - 1)),
                right: Box::new(int(0)),
                span: sp(),
            }]
        } else {
            Vec::new()
        },
        span: sp(),
    }
}

pub fn bit_t(width: u32, signed: bool) -> DataType {
    vector(IntegerVectorType::Bit, width, signed)
}

pub fn atom_t(kind: IntegerAtomType, unsigned: bool) -> DataType {
    DataType::IntegerAtom {
        kind,
        signing: unsigned.then_some(Signing::Unsigned),
        span: sp(),
    }
}

pub fn real_t(kind: RealType) -> DataType {
    DataType::Real { kind, span: sp() }
}

pub fn simple_t(kind: SimpleType) -> DataType {
    DataType::Simple { kind, span: sp() }
}

pub fn void_t() -> DataType {
    DataType::Void(sp())
}

pub fn type_name(name: &str) -> TypeName {
    TypeName {
        scopes: Vec::new(),
        name: id(name),
        span: sp(),
    }
}

/// A named (class or typedef) type, with `#(…)` type arguments.
pub fn named_t(name: &str, type_args: Vec<Expression>) -> DataType {
    DataType::TypeReference {
        name: type_name(name),
        dimensions: Vec::new(),
        type_args,
        span: sp(),
    }
}

/// A type as a `#(…)` argument: keyword types as the parser spells them
/// (an identifier), anything else as a type literal.
pub fn type_arg(dt: &DataType) -> Expression {
    match dt {
        DataType::IntegerAtom {
            kind,
            signing: None,
            ..
        } => ident(match kind {
            IntegerAtomType::Byte => "byte",
            IntegerAtomType::ShortInt => "shortint",
            IntegerAtomType::Int => "int",
            IntegerAtomType::LongInt => "longint",
            IntegerAtomType::Integer => "integer",
            IntegerAtomType::Time => "time",
        }),
        DataType::Simple {
            kind: SimpleType::String,
            ..
        } => ident("string"),
        DataType::TypeReference {
            name, type_args, ..
        } if type_args.is_empty() => ident(&name.name.name),
        other => ex(ExprKind::TypeLiteral(Box::new(other.clone()))),
    }
}

pub fn unpacked(n: Expression) -> UnpackedDimension {
    UnpackedDimension::Expression {
        expr: Box::new(n),
        span: sp(),
    }
}

// ---- declarations and module items -----------------------------------------

pub fn data_decl(
    dt: DataType,
    name: &str,
    dims: Vec<UnpackedDimension>,
    init: Option<Expression>,
) -> ModuleItem {
    ModuleItem::DataDeclaration(DataDeclaration {
        const_kw: false,
        var_kw: false,
        lifetime: None,
        data_type: dt,
        declarators: vec![var_declarator(name, dims, init)],
        span: sp(),
    })
}

pub fn initial(s: Statement) -> ModuleItem {
    ModuleItem::InitialConstruct(InitialConstruct {
        stmt: s,
        span: sp(),
        gen_scope: String::new(),
    })
}

pub fn import_all(pkg: &str) -> ModuleItem {
    ModuleItem::ImportDeclaration(ImportDeclaration {
        items: vec![ImportItem {
            package: id(pkg),
            item: None,
            span: sp(),
        }],
        span: sp(),
    })
}

/// `timeunit 1ps; timeprecision 1ps;` — SystemC's default resolution.
pub fn timeunits_ps() -> ModuleItem {
    ModuleItem::TimeunitsDecl(TimeunitsDeclaration {
        unit: Some("1ps".to_string()),
        precision: Some("1ps".to_string()),
        span: sp(),
    })
}

pub fn fport(dir: PortDirection, dt: DataType, name: &str) -> FunctionPort {
    FunctionPort {
        direction: dir,
        var_kw: false,
        data_type: dt,
        name: id(name),
        dimensions: Vec::new(),
        default: None,
        span: sp(),
    }
}

/// A subroutine port of a type with unpacked dimensions (a queue, an array).
pub fn fport_dims(
    dir: PortDirection,
    (dt, dims): (DataType, Vec<UnpackedDimension>),
    name: &str,
) -> FunctionPort {
    FunctionPort {
        dimensions: dims,
        ..fport(dir, dt, name)
    }
}

pub fn task_decl(name: &str, ports: Vec<FunctionPort>, body: Vec<Statement>) -> TaskDeclaration {
    TaskDeclaration {
        lifetime: Some(Lifetime::Automatic),
        specifier: None,
        name: type_name(name),
        ports,
        items: body,
        endlabel: None,
        strict_body_ports: Vec::new(),
        span: sp(),
    }
}

/// `assign lhs = rhs;`
pub fn cont_assign(lhs: Expression, rhs: Expression) -> ModuleItem {
    ModuleItem::ContinuousAssign(ContinuousAssign {
        strength: None,
        delay: None,
        delay_fall: None,
        delay_off: None,
        assignments: vec![(lhs, rhs)],
        span: sp(),
    })
}

/// `case (e) k0: s0; k1: s1; … default: d; endcase`
pub fn case_(e: Expression, arms: Vec<(Expression, Statement)>, default: Option<Statement>) -> Statement {
    let mut items: Vec<CaseItem> = arms
        .into_iter()
        .map(|(k, s)| CaseItem {
            patterns: vec![k],
            is_default: false,
            stmt: s,
            span: sp(),
            pattern: None,
            guard: None,
        })
        .collect();
    if let Some(d) = default {
        items.push(CaseItem {
            patterns: Vec::new(),
            is_default: true,
            stmt: d,
            span: sp(),
            pattern: None,
            guard: None,
        });
    }
    st(StatementKind::Case {
        unique_priority: None,
        kind: CaseKind::Case,
        expr: e,
        items,
    })
}

pub fn function_decl(
    name: &str,
    ret: DataType,
    ports: Vec<FunctionPort>,
    body: Vec<Statement>,
) -> FunctionDeclaration {
    FunctionDeclaration {
        lifetime: Some(Lifetime::Automatic),
        specifier: None,
        return_type: ret,
        name: type_name(name),
        ports,
        items: body,
        endlabel: None,
        strict_body_ports: Vec::new(),
        span: sp(),
    }
}

pub fn ansi_port(
    dir: PortDirection,
    dt: DataType,
    name: &str,
    dims: Vec<UnpackedDimension>,
) -> AnsiPort {
    AnsiPort {
        attrs: Vec::new(),
        direction: Some(dir),
        net_type: None,
        var_kw: false,
        data_type: Some(dt),
        name: id(name),
        dimensions: dims,
        default: None,
        span: sp(),
    }
}

pub fn param_decl(dt: DataType, name: &str, init: Expression) -> ParameterDeclaration {
    ParameterDeclaration {
        local: false,
        specparam: false,
        kind: ParameterKind::Data {
            data_type: dt,
            assignments: vec![ParamAssignment {
                name: id(name),
                dimensions: Vec::new(),
                init: Some(init),
                span: sp(),
            }],
        },
        span: sp(),
    }
}

pub fn instance(
    module: &str,
    name: &str,
    params: Vec<(String, Expression)>,
    conns: Vec<(String, Expression)>,
) -> ModuleItem {
    ModuleItem::ModuleInstantiation(ModuleInstantiation {
        module_name: id(module),
        params: if params.is_empty() {
            None
        } else {
            Some(
                params
                    .into_iter()
                    .map(|(n, v)| ParamConnection::Named {
                        name: id(&n),
                        value: Some(ParamValue::Expr(v)),
                    })
                    .collect(),
            )
        },
        instances: vec![HierarchicalInstance {
            name: id(name),
            dimensions: Vec::new(),
            connections: conns
                .into_iter()
                .map(|(n, e)| PortConnection::Named {
                    name: id(&n),
                    expr: Some(e),
                    implicit: false,
                })
                .collect(),
            span: sp(),
        }],
        span: sp(),
    })
}

pub fn module(
    name: &str,
    params: Vec<ParameterDeclaration>,
    ports: Vec<AnsiPort>,
    items: Vec<ModuleItem>,
) -> ModuleDeclaration {
    ModuleDeclaration {
        attrs: Vec::new(),
        kind: ModuleKind::Module,
        lifetime: None,
        name: id(name),
        params,
        ports: if ports.is_empty() {
            PortList::Empty
        } else {
            PortList::Ansi(ports)
        },
        items,
        endlabel: None,
        span: sp(),
    }
}

/// `class name extends base; <virtual tasks/functions> endclass`.
pub fn class_decl(name: &str, extends: Option<&str>, items: Vec<ClassItem>) -> ClassDeclaration {
    ClassDeclaration {
        virtual_kw: false,
        is_interface: false,
        is_final: false,
        name: id(name),
        params: Vec::new(),
        extends: extends.map(|b| ClassExtends {
            name: id(b),
            args: Vec::new(),
            span: sp(),
            scopes: Vec::new(),
        }),
        implements: Vec::new(),
        items,
        endlabel: None,
        span: sp(),
    }
}

pub fn class_task(t: TaskDeclaration, is_virtual: bool) -> ClassItem {
    ClassItem::Method(ClassMethod {
        qualifiers: if is_virtual {
            vec![ClassQualifier::Virtual]
        } else {
            Vec::new()
        },
        kind: ClassMethodKind::Task(t),
        span: sp(),
    })
}

pub fn class_function(f: FunctionDeclaration, is_virtual: bool) -> ClassItem {
    ClassItem::Method(ClassMethod {
        qualifiers: if is_virtual {
            vec![ClassQualifier::Virtual]
        } else {
            Vec::new()
        },
        kind: ClassMethodKind::Function(f),
        span: sp(),
    })
}
