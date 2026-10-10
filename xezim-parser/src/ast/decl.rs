//! SystemVerilog declarations (IEEE 1800-2017 §A.2)

use super::expr::Expression;
use super::stmt::{Statement, VarDeclarator};
use super::types::*;
use super::{Identifier, Span};

/// IEEE 1800-2017 §29 User-Defined Primitive declaration.
/// `primitive name(out, in..); ... table ... endtable endprimitive`
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct UdpDecl {
    pub name: Identifier,
    /// Port names in declaration order; `ports[0]` is the single output.
    pub ports: Vec<Identifier>,
    /// `reg out;` (or ANSI `output reg`) ⇒ sequential UDP.
    pub is_sequential: bool,
    /// §29.6 `initial out = 1'bX;` — start state ('0','1','x'); default 'x'.
    pub init: Option<char>,
    pub rows: Vec<UdpTableRow>,
    pub span: Span,
}

/// One row of a UDP truth table.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct UdpTableRow {
    /// One symbol per input port, declaration order. For edge-sequential rows
    /// exactly one entry is an `Edge`/`EdgeShort`.
    pub inputs: Vec<UdpSym>,
    /// Sequential middle field (current state); `None` for combinational rows.
    pub state: Option<UdpSym>,
    /// Output field.
    pub output: UdpOut,
    pub span: Span,
}

/// A UDP table input/state symbol (IEEE 1800-2017 Table 29-1/29-2).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum UdpSym {
    /// Level `0` `1` `x` (input `z` normalized to `x`).
    Level(char),
    /// `?` — matches 0, 1, or x (no edge).
    AnyQ,
    /// `b` — matches 0 or 1.
    B,
    /// Explicit edge `(vw)`, v,w ∈ {0,1,x,?} (`?` expands over levels).
    Edge { from: char, to: char },
    /// Edge shorthand: 'r'=(01), 'f'=(10), 'p'=(01)(0x)(x1),
    /// 'n'=(10)(1x)(x0), '*'=(??)=any change.
    EdgeShort(char),
}

/// A UDP output-field symbol.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum UdpOut {
    Level(char), // '0' '1' 'x'
    NoChange,    // '-' (sequential hold)
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ModuleItem {
    PortDeclaration(PortDeclaration),
    NetDeclaration(NetDeclaration),
    DataDeclaration(DataDeclaration),
    ParameterDeclaration(ParameterDeclaration),
    LocalparamDeclaration(ParameterDeclaration),
    TypedefDeclaration(TypedefDeclaration),
    AlwaysConstruct(AlwaysConstruct),
    InitialConstruct(InitialConstruct),
    FinalConstruct(FinalConstruct),
    ContinuousAssign(ContinuousAssign),
    ModuleInstantiation(ModuleInstantiation),
    GateInstantiation(GateInstantiation),
    GenerateRegion(GenerateRegion),
    /// Generate-if: condition + then-items, and a chain of (condition, items) for else-if/else
    GenerateIf(GenerateIf),
    GenerateFor(GenerateFor),
    /// Generate-case: case (constant_expr) values: items ... endcase
    /// Each arm matches one or more case values; an arm with empty `values`
    /// is the `default` arm. Used to pick between alternative module
    /// instantiations based on a parameter / genvar.
    GenerateCase(GenerateCase),
    GenvarDeclaration(GenvarDeclaration),
    FunctionDeclaration(FunctionDeclaration),
    TaskDeclaration(TaskDeclaration),
    ImportDeclaration(ImportDeclaration),
    TimeunitsDecl(TimeunitsDeclaration),
    ClassDeclaration(ClassDeclaration),
    AssertionItem(super::stmt::AssertionStatement),
    ModportDeclaration(ModportDeclaration),
    PropertyDeclaration(PropertyDeclaration),
    SequenceDeclaration(SequenceDeclaration),
    CovergroupDeclaration(CovergroupDeclaration),
    ClockingDeclaration(ClockingDeclaration),
    CheckerDeclaration(CheckerDeclaration),
    LetDeclaration(LetDeclaration),
    NettypeDeclaration(NettypeDeclaration),
    SpecifyBlock(SpecifyBlock),
    DPIImport(DPIImport),
    DPIExport(DPIExport),
    /// Out-of-class constraint definition: `constraint ClassName::cname { ... }`.
    /// Only the qualified name is tracked; body is not modeled.
    /// §18.5.1 `constraint Class::name { ... }` — the BODY is carried so the
    /// class's extern-constraint prototype can be filled in at elaboration
    /// (it used to be brace-skipped and discarded, so the constraints simply
    /// did not exist at solve time).
    OutOfClassConstraint {
        class_name: String,
        constraint_name: String,
        items: Vec<crate::ast::decl::ConstraintItem>,
    },
    /// `bind <target> <module> <inst>(<ports>);` appearing as a module item
    /// (rather than at compilation-unit scope). Treated by elaboration the
    /// same way as a top-level bind: the wrapped instantiation is appended
    /// to every instance of `target`.
    Bind(BindDirective),
    /// Deprecated hierarchical parameter override `defparam path.p = e, ...;`
    /// (LRM §23.10.1). Each entry is `(target_path, value)`; the target path's
    /// LAST segment is the parameter name and the leading segments are the
    /// instance path relative to the enclosing scope.
    Defparam(Vec<(Expression, Expression)>),
    Null,
    /// §23.4 NESTED module declaration. The top-level pipeline hoists these
    /// into the definitions map before elaboration (the nested module's
    /// access to the enclosing scope's names is NOT modeled — self-contained
    /// nested modules only). Appended last for bincode index stability.
    NestedModule(Box<crate::ast::module::ModuleDeclaration>),
    /// §10.11 `alias a = b [= c ...];` — the named nets are ONE net.
    /// Elaboration resolves the terms to flat names and the simulator maps
    /// them onto a single signal slot (true unification — an alias is NOT a
    /// pair of continuous assigns; a hand-written assign cycle reads x).
    AliasDecl(Vec<Expression>),
}

/// IEEE 1800-2023 §23.11 — `bind` directive. A lightweight, top-level form
/// is supported: `bind <target_module> <bind_module> <inst_name>(.<port>(<expr>), ...);`
/// is desugared by elaboration into a `ModuleInstantiation` appended to
/// `target_module`'s item list, so every instance of `target_module` gets
/// the bound module attached (typically a covergroup / assertion / monitor
/// holder).
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct BindDirective {
    /// Identifier of the module type the bind attaches to.
    pub target_module: Identifier,
    /// §23.11 bind_target_instance: when the target is written as a
    /// HIERARCHICAL instance path (`bind top.a.b.inst mod m ();`), the full
    /// dotted path (first segment = a top-level module name). Empty for the
    /// plain by-module-name form; `target_module` then holds the module.
    #[cfg_attr(feature = "serde", serde(default))]
    pub target_path: Vec<Identifier>,
    /// §23.11 colon form `bind <mod> : <inst>, <inst>, ... <binder> ...`:
    /// additional target-instance paths beyond `target_path` (which holds
    /// the first). Empty otherwise.
    #[cfg_attr(feature = "serde", serde(default))]
    pub extra_paths: Vec<Vec<Identifier>>,
    /// The instantiation appended into every instance of `target_module`.
    pub instantiation: ModuleInstantiation,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct CheckerDeclaration {
    pub name: Identifier,
    pub ports: super::module::PortList,
    pub items: Vec<ModuleItem>,
    pub endlabel: Option<Identifier>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct LetDeclaration {
    pub name: Identifier,
    pub ports: super::module::PortList, // let parameters look like ports
    pub expr: Expression,
    pub span: Span,
}

impl LetDeclaration {
    /// The formal arguments: name, declared type (None when untyped) and
    /// default actual.
    pub fn formals(&self) -> Vec<(&Identifier, Option<&DataType>, Option<&Expression>)> {
        use super::module::PortList;
        match &self.ports {
            PortList::Empty => Vec::new(),
            PortList::NonAnsi(names) => names.iter().map(|n| (n, None, None)).collect(),
            PortList::Ansi(ports) => ports
                .iter()
                .map(|p| {
                    // `untyped` and a bare name leave the formal untyped.
                    let ty = p.data_type.as_ref().filter(|dt| {
                        !matches!(dt, DataType::Implicit { signing: None, dimensions, .. }
                            if dimensions.is_empty())
                    });
                    (&p.name, ty, p.default.as_ref())
                })
                .collect(),
        }
    }

    /// IEEE 1800-2023 §11.13: expand one let instance `name(args)`. The let
    /// body is the instance: each formal is replaced by its actual argument
    /// (positional or `.name(expr)`, a default when omitted), parenthesized
    /// so it binds as one operand. A typed formal casts its actual to the
    /// formal's type first. The whole body is parenthesized too, so it takes
    /// part in the context-determined width of the expression around the
    /// instance (a let instance is a primary). `span` is the instance's.
    pub fn expand(&self, args: &[Expression], span: Span) -> Result<Expression, String> {
        use super::expr::ExprKind;
        let formals = self.formals();
        let lname = &self.name.name;
        let mut bound: Vec<Option<Expression>> = vec![None; formals.len()];
        let mut pos = 0usize;
        for a in args {
            match &a.kind {
                ExprKind::NamedArg { name, expr } => {
                    let Some(i) = formals.iter().position(|f| f.0.name == name.name) else {
                        return Err(format!(
                            "let '{}' has no formal argument '{}'",
                            lname, name.name
                        ));
                    };
                    bound[i] = expr.as_deref().cloned();
                }
                // `f(a, , c)`: an empty positional actual takes the default.
                ExprKind::Empty => pos += 1,
                _ => {
                    if pos >= formals.len() {
                        return Err(format!(
                            "too many arguments to let '{}' ({} formal{})",
                            lname,
                            formals.len(),
                            if formals.len() == 1 { "" } else { "s" }
                        ));
                    }
                    bound[pos] = Some(a.clone());
                    pos += 1;
                }
            }
        }
        let mut map: std::collections::HashMap<String, Expression> =
            std::collections::HashMap::new();
        for (i, (name, ty, default)) in formals.iter().enumerate() {
            let Some(actual) = bound[i].take().or_else(|| default.cloned()) else {
                return Err(format!(
                    "missing argument for formal '{}' of let '{}'",
                    name.name, lname
                ));
            };
            let aspan = actual.span;
            let mut actual = Expression::new(ExprKind::Paren(Box::new(actual)), aspan);
            if let Some(dt) = ty {
                actual = Expression::new(
                    ExprKind::SystemCall {
                        name: "$__xz_type_cast".to_string(),
                        args: vec![
                            Expression::new(ExprKind::TypeLiteral(Box::new((*dt).clone())), aspan),
                            actual,
                        ],
                    },
                    aspan,
                );
            }
            map.insert(name.name.clone(), actual);
        }
        let mut body = self.expr.clone();
        if !map.is_empty() {
            let_subst(&mut body, &map);
        }
        Ok(Expression::new(ExprKind::Paren(Box::new(body)), span))
    }
}

/// Replace every reference to a let formal in `e` with its actual (§11.13).
/// A formal used with selects or member names (`a[3]`, `a.f`) keeps them,
/// applied to the actual.
fn let_subst(e: &mut Expression, map: &std::collections::HashMap<String, Expression>) {
    use super::expr::{AssignmentPatternItem, ExprKind};
    let span = e.span;
    match &mut e.kind {
        ExprKind::Ident(h) => {
            let hit = h.root.is_none()
                && h.path
                    .first()
                    .is_some_and(|s| map.contains_key(&s.name.name));
            if hit {
                let path = std::mem::take(&mut h.path);
                let mut out: Option<Expression> = None;
                for seg in path {
                    let mut cur = match out {
                        None => map[&seg.name.name].clone(),
                        Some(base) => Expression::new(
                            ExprKind::MemberAccess {
                                expr: Box::new(base),
                                member: seg.name,
                            },
                            span,
                        ),
                    };
                    for mut sel in seg.selects {
                        let_subst(&mut sel, map);
                        cur = match sel.kind {
                            ExprKind::Range(l, r) => Expression::new(
                                ExprKind::RangeSelect {
                                    expr: Box::new(cur),
                                    kind: super::expr::RangeKind::Constant,
                                    left: l,
                                    right: r,
                                },
                                span,
                            ),
                            _ => Expression::new(
                                ExprKind::Index {
                                    expr: Box::new(cur),
                                    index: Box::new(sel),
                                },
                                span,
                            ),
                        };
                    }
                    out = Some(cur);
                }
                if let Some(o) = out {
                    *e = o;
                }
                return;
            }
            for seg in &mut h.path {
                for sel in &mut seg.selects {
                    let_subst(sel, map);
                }
            }
        }
        ExprKind::Unary { operand, .. } => let_subst(operand, map),
        ExprKind::Binary { left, right, .. } => {
            let_subst(left, map);
            let_subst(right, map);
        }
        ExprKind::Conditional {
            condition,
            then_expr,
            else_expr,
        } => {
            let_subst(condition, map);
            let_subst(then_expr, map);
            let_subst(else_expr, map);
        }
        ExprKind::Concatenation(parts) => parts.iter_mut().for_each(|p| let_subst(p, map)),
        ExprKind::Replication { count, exprs } => {
            let_subst(count, map);
            exprs.iter_mut().for_each(|p| let_subst(p, map));
        }
        ExprKind::AssignmentPattern(items) => {
            for it in items {
                match it {
                    AssignmentPatternItem::Ordered(x)
                    | AssignmentPatternItem::Named(_, x)
                    | AssignmentPatternItem::Typed(_, x)
                    | AssignmentPatternItem::Default(x) => let_subst(x, map),
                    AssignmentPatternItem::Keyed(k, x) => {
                        let_subst(k, map);
                        let_subst(x, map);
                    }
                }
            }
        }
        ExprKind::Call { func, args } => {
            // A plain callee name is a subroutine, not a formal.
            if !matches!(&func.kind, ExprKind::Ident(h) if h.path.len() == 1) {
                let_subst(func, map);
            }
            args.iter_mut().for_each(|a| let_subst(a, map));
        }
        ExprKind::SystemCall { args, .. } => args.iter_mut().for_each(|a| let_subst(a, map)),
        ExprKind::NamedArg { expr, .. } => {
            if let Some(x) = expr {
                let_subst(x, map);
            }
        }
        ExprKind::Inside { expr, ranges } => {
            let_subst(expr, map);
            ranges.iter_mut().for_each(|r| let_subst(r, map));
        }
        ExprKind::Matches { expr, .. } => let_subst(expr, map),
        ExprKind::MemberAccess { expr, .. } => let_subst(expr, map),
        ExprKind::Specialization { base, .. } => let_subst(base, map),
        ExprKind::Index { expr, index } => {
            let_subst(expr, map);
            let_subst(index, map);
        }
        ExprKind::RangeSelect {
            expr, left, right, ..
        } => {
            let_subst(expr, map);
            let_subst(left, map);
            let_subst(right, map);
        }
        ExprKind::Range(l, r) => {
            let_subst(l, map);
            let_subst(r, map);
        }
        ExprKind::Paren(inner) => let_subst(inner, map),
        ExprKind::WithClause { expr, filter } => {
            let_subst(expr, map);
            let_subst(filter, map);
        }
        ExprKind::RandomizeWith { call, .. } => let_subst(call, map),
        ExprKind::AssignExpr { lvalue, rvalue } => {
            let_subst(lvalue, map);
            let_subst(rvalue, map);
        }
        ExprKind::StreamOp {
            slice_size, exprs, ..
        } => {
            if let Some(s) = slice_size {
                let_subst(s, map);
            }
            exprs.iter_mut().for_each(|x| let_subst(x, map));
        }
        ExprKind::Tagged { inner, .. } => {
            if let Some(x) = inner {
                let_subst(x, map);
            }
        }
        ExprKind::SvaClocked {
            clock, iff, body, ..
        } => {
            let_subst(clock, map);
            if let Some(x) = iff {
                let_subst(x, map);
            }
            let_subst(body, map);
        }
        ExprKind::ShallowCopy { source } => let_subst(source, map),
        ExprKind::Number(_)
        | ExprKind::StringLiteral(_)
        | ExprKind::TypeLiteral(_)
        | ExprKind::Dollar
        | ExprKind::Null
        | ExprKind::This
        | ExprKind::Empty => {}
    }
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct NettypeDeclaration {
    pub data_type: DataType,
    pub name: Identifier,
    pub resolver: Option<Identifier>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct SpecifyBlock {
    pub paths: Vec<SpecifyPath>,
    /// IEEE 1364 §15.6 negative-timing-check DELAYED nets: the trailing
    /// `delayed_reference`/`delayed_data` arguments of `$setuphold`/`$recrem`
    /// (etc.). Each entry is (delayed_net, source_signal). Vendor cells route
    /// their functional clock/data path through these nets, so a functional
    /// simulator that does not model the check must still drive them —
    /// zero-delay, i.e. `assign delayed_net = source_signal`. Without this the
    /// cell's clock is undriven (x) and its flops never evaluate.
    pub delayed_nets: Vec<(String, String)>,
    /// §31 timing checks (`$setup`, `$hold`, `$width`, ...), in source order.
    #[cfg_attr(feature = "serde", serde(default))]
    pub timing_checks: Vec<TimingCheck>,
    pub span: Span,
}

/// IEEE 1800-2017 §31 timing check: the system task name (`$setuphold`) and
/// its arguments in source order. An omitted argument (`, ,`) is `None`.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TimingCheck {
    pub name: String,
    pub args: Vec<Option<TimingCheckArg>>,
    pub span: Span,
}

/// One timing check argument. Event arguments may carry an edge control and
/// a `&&&` condition; limits, notifiers and flags are plain expressions.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TimingCheckArg {
    /// §31.5 edge control as a transition mask (see [`timing_edge_bit`]);
    /// `None` when the argument has no edge control (any value change).
    pub edges: Option<u16>,
    pub expr: Expression,
    pub cond: Option<Expression>,
    /// Source spelling (`posedge clk &&& en`), for diagnostics.
    pub text: String,
}

/// Bit of a [`TimingCheckArg::edges`] mask for the `from -> to` transition,
/// levels encoded 0, 1, 2. §31.5 treats z like x, so 2 stands for both.
pub const fn timing_edge_bit(from: u8, to: u8) -> u16 {
    1u16 << ((from as u16) * 3 + to as u16)
}

/// `posedge`: 0->1, 0->x, x->1 (§31.5, same set as §9.4.2).
pub const TIMING_POSEDGE: u16 =
    timing_edge_bit(0, 1) | timing_edge_bit(0, 2) | timing_edge_bit(2, 1);

/// `negedge`: 1->0, 1->x, x->0.
pub const TIMING_NEGEDGE: u16 =
    timing_edge_bit(1, 0) | timing_edge_bit(1, 2) | timing_edge_bit(2, 0);

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct SpecifyPath {
    /// Input terminals (base names; a bit/part select is not kept).
    pub srcs: Vec<Identifier>,
    /// Output terminals (base names).
    pub dsts: Vec<Identifier>,
    /// §30.4.4 `if (cond)` of a state-dependent path.
    pub cond: Option<Expression>,
    /// §30.4.4.3 `ifnone`.
    pub ifnone: bool,
    /// §30.5.1 delay list: 1, 2, 3, 6 or 12 values, each already the
    /// min/typ/max selection.
    pub delays: Vec<Expression>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct DPIImport {
    pub property: Option<DPIProperty>,
    pub c_name: Option<String>,
    pub proto: DPIProto,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct DPIExport {
    pub c_name: Option<String>,
    pub proto: DPIProto,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum DPIProto {
    Function(FunctionDeclaration),
    Task(TaskDeclaration),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum DPIProperty {
    Context,
    Pure,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ClockingDeclaration {
    pub name: Identifier,
    /// LRM §14.3: clock event (e.g. `@(posedge clk)`). The signal
    /// expression is captured so the simulator can snapshot input
    /// signals before each clock edge. None when the clocking block
    /// was declared without an event — implementation-defined behavior.
    #[cfg_attr(feature = "serde", serde(default))]
    pub clock_signal: Option<Identifier>,
    /// LRM §14.3: the clock event's EDGE (`posedge`/`negedge`/`edge`). `None`
    /// when unspecified — the simulator defaults to posedge. Without this the
    /// block would always sync on posedge even for `@(negedge clk)`.
    #[cfg_attr(feature = "serde", serde(default))]
    pub clock_edge: Option<super::stmt::Edge>,
    /// §14.4 `default input #d` skew expression, if declared.
    #[cfg_attr(feature = "serde", serde(default))]
    pub default_input_skew: Option<super::expr::Expression>,
    /// §14.4 `default output #d` skew expression, if declared.
    #[cfg_attr(feature = "serde", serde(default))]
    pub default_output_skew: Option<super::expr::Expression>,
    /// LRM §14.11: true when declared `default clocking ...` — the block
    /// that procedural cycle delays (`##N`) synchronize to.
    #[cfg_attr(feature = "serde", serde(default))]
    pub is_default: bool,
    pub signals: Vec<ClockingSignal>,
    pub items: Vec<super::stmt::Statement>, // Approximate clocking body as statements
    pub endlabel: Option<Identifier>,
    pub span: Span,
}

/// IEEE 1800-2023 §14.4: a `#1step` clocking skew is carried as an
/// identifier expression with this name (no real identifier starts with a
/// digit), so it stays distinct from an absent skew and from `#1`.
pub const CLOCKING_ONE_STEP: &str = "1step";

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ClockingSignal {
    pub direction: PortDirection,
    pub name: Identifier,
    /// §14.4 per-signal skew (`output #0 sig;`). None = use the block default.
    #[cfg_attr(feature = "serde", serde(default))]
    pub skew: Option<super::expr::Expression>,
    /// §14.3 signal RENAMING: `input alias = actual_expr;` binds the clocking
    /// name to a different signal. None = the clocking name IS the signal.
    #[cfg_attr(feature = "serde", serde(default))]
    pub bound_to: Option<super::expr::Expression>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct CovergroupDeclaration {
    pub name: Identifier,
    /// §19.3 constructor formals: `covergroup cg (int lo, int hi);` — bound
    /// at `new(...)` and visible to coverpoint bins and options.
    #[cfg_attr(feature = "serde", serde(default))]
    pub ports: Vec<FunctionPort>,
    /// §19.8.1 `with function sample(tf_port_list)` formals: bound at each
    /// `cg.sample(args)` call and visible to the coverpoint expressions.
    #[cfg_attr(feature = "serde", serde(default))]
    pub sample_ports: Vec<FunctionPort>,
    pub event: Option<super::stmt::EventControl>,
    pub items: Vec<CovergroupItem>,
    pub endlabel: Option<Identifier>,
    pub span: Span,
}

impl CovergroupDeclaration {
    /// Every expression of the body and sampling event that names a design
    /// object (not the constructor or sample formals' defaults): coverpoint
    /// expressions and guards, bin values, options and cross guards.
    pub fn for_each_expr_mut(&mut self, f: &mut dyn FnMut(&mut Expression)) {
        if let Some(ev) = &mut self.event {
            match ev {
                super::stmt::EventControl::HierIdentifier(e) => f(e),
                super::stmt::EventControl::EventExpr(list) => {
                    for ee in list {
                        f(&mut ee.expr);
                        if let Some(g) = &mut ee.iff {
                            f(g);
                        }
                    }
                }
                _ => {}
            }
        }
        for it in &mut self.items {
            match it {
                CovergroupItem::Coverpoint(cp) => {
                    f(&mut cp.expr);
                    if let Some(g) = &mut cp.iff_guard {
                        f(g);
                    }
                    for b in &mut cp.bins {
                        for r in &mut b.values {
                            r.for_each_expr_mut(f);
                        }
                        if let Some(n) = &mut b.array_size {
                            f(n);
                        }
                        for step in b.transitions.iter_mut().flatten() {
                            for r in &mut step.values {
                                r.for_each_expr_mut(f);
                            }
                            if let Some(rep) = &mut step.repeat {
                                f(&mut rep.lo);
                                if let Some(h) = &mut rep.hi {
                                    f(h);
                                }
                            }
                        }
                    }
                    for (_, v) in &mut cp.options {
                        f(v);
                    }
                }
                CovergroupItem::Cross(cr) => {
                    if let Some(g) = &mut cr.iff_guard {
                        f(g);
                    }
                    for b in &mut cr.bins {
                        b.select.for_each_expr_mut(f);
                        if let Some(g) = &mut b.iff_guard {
                            f(g);
                        }
                    }
                    for (_, v) in &mut cr.options {
                        f(v);
                    }
                }
                CovergroupItem::Option { val, .. } | CovergroupItem::TypeOption { val, .. } => {
                    f(val)
                }
            }
        }
    }
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum CovergroupItem {
    Coverpoint(Coverpoint),
    Cross(Cross),
    Option { name: String, val: Expression },
    TypeOption { name: String, val: Expression },
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Coverpoint {
    pub name: Option<Identifier>,
    pub expr: Expression,
    /// IEEE 1800-2023 §19.5 `coverpoint real <expr>` — the sampled expression
    /// is real-valued, so bins are ranges over reals rather than over integral
    /// values. False for an ordinary integral coverpoint.
    #[cfg_attr(feature = "serde", serde(default))]
    pub is_real: bool,
    /// LRM §19.5 `coverpoint x iff (guard)` — sample is skipped when the
    /// guard evaluates false. `None` means "always sample".
    #[cfg_attr(feature = "serde", serde(default))]
    pub iff_guard: Option<Expression>,
    /// LRM §19.5 explicit bins. Empty when the coverpoint uses the implicit
    /// "every distinct sampled value is its own bin" model.
    #[cfg_attr(feature = "serde", serde(default))]
    pub bins: Vec<CoverBin>,
    /// LRM §19.7 coverpoint-level options — `option.at_least = N`,
    /// `option.weight = W` declared inside the coverpoint body. Stored as
    /// (option_name, value_expr) pairs; empty when none.
    #[cfg_attr(feature = "serde", serde(default))]
    pub options: Vec<(String, Expression)>,
    pub span: Span,
}

/// LRM §19.5 bin declaration: `bins`, `ignore_bins`, `illegal_bins` or a
/// `default` bin, over a value list, a wildcard pattern list or a list of
/// transitions.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct CoverBin {
    pub name: Identifier,
    pub kind: CoverBinKind,
    pub values: Vec<ConstraintRange>,
    /// LRM §19.5.1 `bins name[]` (one bin per value) or `bins name[N]`.
    #[cfg_attr(feature = "serde", serde(default))]
    pub array_form: bool,
    /// The `N` of `bins name[N]`: the values are spread over N bins.
    #[cfg_attr(feature = "serde", serde(default))]
    pub array_size: Option<Expression>,
    /// LRM §19.5 `wildcard bins name = { pattern };` — bit-wise match
    /// where `x`/`z`/`?` bits in `pattern` are don't-cares. Sampler
    /// switches to per-bit compare honoring the value's xz_bits mask.
    #[cfg_attr(feature = "serde", serde(default))]
    pub is_wildcard: bool,
    /// LRM §19.5.2 transition bins, one entry per parenthesized
    /// `trans_set` of the list (`(1 => 2), (5 => 6)`); each is the chain
    /// of its `=>` steps.
    #[cfg_attr(feature = "serde", serde(default))]
    pub transitions: Vec<Vec<TransStep>>,
    pub span: Span,
}

/// One step of a §19.5.2 transition: a value set (`1, [3:4]`) with an
/// optional repetition (`[* n]`, `[-> n]`, `[= n]`, or an `n:m` range).
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TransStep {
    pub values: Vec<ConstraintRange>,
    pub repeat: Option<TransRepeat>,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TransRepeat {
    pub kind: TransRepeatKind,
    pub lo: Expression,
    /// The upper bound of `n:m` (`$` is unbounded); `None` repeats exactly `lo`.
    pub hi: Option<Expression>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum TransRepeatKind {
    /// `[* n]`: n consecutive matching samples.
    Consecutive,
    /// `[-> n]`: n matching samples, not necessarily consecutive, the last
    /// one ending the step.
    Goto,
    /// `[= n]`: like goto, but any non-matching samples may follow.
    NonConsecutive,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum CoverBinKind {
    Bins,
    Ignore,
    Illegal,
    Default,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Cross {
    pub name: Option<Identifier>,
    pub items: Vec<Identifier>,
    /// LRM §19.6 `cross x, y iff (guard)` — skip the cross sample when
    /// guard is false. Mirrors `Coverpoint.iff_guard`.
    #[cfg_attr(feature = "serde", serde(default))]
    pub iff_guard: Option<Expression>,
    /// LRM §19.6.1 bins, ignore_bins and illegal_bins of the cross body.
    #[cfg_attr(feature = "serde", serde(default))]
    pub bins: Vec<CrossBin>,
    /// §19.7 cross-level `option.NAME = expr;` items.
    #[cfg_attr(feature = "serde", serde(default))]
    pub options: Vec<(String, Expression)>,
    pub span: Span,
}

/// LRM §19.6.1 `bins NAME = select_expression [iff (expr)];` in a cross body.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct CrossBin {
    pub name: Identifier,
    pub kind: CoverBinKind,
    pub select: CrossSelect,
    pub iff_guard: Option<Expression>,
}

/// LRM §19.6.1 select_expression: a set of the cross's product bins.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum CrossSelect {
    /// `binsof(cp)` or `binsof(cp.bin)`, optionally `intersect {ranges}`:
    /// the product bins whose `cp` bin is that bin, or has a value in the
    /// ranges.
    Binsof {
        cp: Identifier,
        bin: Option<Identifier>,
        intersect: Option<Vec<ConstraintRange>>,
    },
    Not(Box<CrossSelect>),
    And(Box<CrossSelect>, Box<CrossSelect>),
    Or(Box<CrossSelect>, Box<CrossSelect>),
    /// `select with (expr)`: the product bins holding a value tuple for
    /// which `expr`, over the coverpoint names, is true.
    With(Box<CrossSelect>, Expression),
    /// The cross's own name: every product bin.
    All,
}

impl CrossSelect {
    pub fn for_each_expr_mut(&mut self, f: &mut dyn FnMut(&mut Expression)) {
        match self {
            CrossSelect::Binsof { intersect, .. } => {
                for r in intersect.iter_mut().flatten() {
                    r.for_each_expr_mut(f);
                }
            }
            CrossSelect::Not(a) => a.for_each_expr_mut(f),
            CrossSelect::And(a, b) | CrossSelect::Or(a, b) => {
                a.for_each_expr_mut(f);
                b.for_each_expr_mut(f);
            }
            // A `with` expression names the cross's coverpoints, not design
            // objects: left out.
            CrossSelect::With(a, _) => a.for_each_expr_mut(f),
            CrossSelect::All => {}
        }
    }
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct PropertyDeclaration {
    pub name: Identifier,
    /// §16.6 formal port names, in declaration order. Captured so
    /// `assert property (p(actuals))` can substitute formals→actuals.
    #[cfg_attr(feature = "serde", serde(default))]
    pub ports: Vec<Identifier>,
    pub items: Vec<super::stmt::Statement>, // Approximate property body as statements for parsing
    /// LRM §16.6 property body, captured when it matches the common
    /// `@(clk_event) <expr>` shape. Used by `assert property (p_name)`
    /// to inline the body without re-parsing. `None` for property
    /// bodies the parser couldn't structure as a single expression
    /// (those still parse — the items list is exhausted token-by-
    /// token — but the inline-substitution path is skipped).
    #[cfg_attr(feature = "serde", serde(default))]
    pub body: Option<super::expr::Expression>,
    pub endlabel: Option<Identifier>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct SequenceDeclaration {
    pub name: Identifier,
    /// §16.5 formal port names, in declaration order (see
    /// PropertyDeclaration::ports).
    #[cfg_attr(feature = "serde", serde(default))]
    pub ports: Vec<Identifier>,
    pub items: Vec<super::stmt::Statement>, // Approximate sequence body as statements
    /// LRM §16.5 — sequence body when it matches the common
    /// `@(clk) <expr>` shape (an `SvaClocked` wrapper). Used for
    /// `assert property (s)` style references.
    #[cfg_attr(feature = "serde", serde(default))]
    pub body: Option<super::expr::Expression>,
    pub endlabel: Option<Identifier>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ModportDeclaration {
    pub items: Vec<ModportItem>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ModportItem {
    pub name: Identifier,
    pub ports: Vec<ModportPort>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ModportPort {
    pub direction: PortDirection,
    pub name: Identifier,
    pub span: Span,
    /// §25.5.4 modport EXPRESSION: `.name(expr)` binds the modport member
    /// to an expression over the interface's signals instead of a signal.
    #[cfg_attr(feature = "serde", serde(default))]
    pub expr: Option<super::expr::Expression>,
}

/// Verilog gate-level primitive instantiation (IEEE 1800-2017 §28)
/// e.g., `and and0 (out, in1, in2);`  `not not0 (out, in);`
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct GateInstantiation {
    pub gate_type: GateType,
    /// `buf #(d) g(y, a);` — the gate's RISE delay (the first expression of
    /// the delay spec). Counts the enclosing module's timeunit until the
    /// elaborator pre-scales it to ticks.
    #[cfg_attr(feature = "serde", serde(default))]
    pub delay: Option<Expression>,
    /// §28.11 `#(rise, fall)` — the FALL delay (second expression), applied to
    /// 1→0 output transitions. `None` when the spec gave a single delay, in
    /// which case the rise value governs both edges. A third (turn-off) value
    /// is still skipped.
    #[cfg_attr(feature = "serde", serde(default))]
    pub delay_fall: Option<Expression>,
    pub instances: Vec<GateInstance>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct GateInstance {
    pub name: Option<Identifier>,
    /// First element is output, rest are inputs (for most gates).
    /// For buf/not: first is output, last is input.
    pub terminals: Vec<Expression>,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum GateType {
    And,
    Nand,
    Or,
    Nor,
    Xor,
    Xnor,
    Buf,
    Not,
    Bufif0,
    Bufif1,
    Notif0,
    Notif1,
    // §28 switch (MOS/bidirectional/pull) primitives
    Nmos,
    Pmos,
    Cmos,
    Rnmos,
    Rpmos,
    Rcmos,
    Tran,
    Rtran,
    Tranif0,
    Tranif1,
    Rtranif0,
    Rtranif1,
    Pullup,
    Pulldown,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct PortDeclaration {
    pub direction: PortDirection,
    pub net_type: Option<NetType>,
    pub data_type: DataType,
    pub declarators: Vec<VarDeclarator>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct NetDeclaration {
    pub net_type: NetType,
    pub strength: Option<String>,
    pub data_type: DataType,
    /// §6.7.1 net delay: `#d` / first of `#(rise, fall[, turnoff])`.
    pub delay: Option<Expression>,
    /// Second delay of the pair/triple form: applied to a transition to 0.
    #[cfg_attr(feature = "serde", serde(default))]
    pub delay_fall: Option<Expression>,
    /// Third delay: applied to a transition to z.
    #[cfg_attr(feature = "serde", serde(default))]
    pub delay_off: Option<Expression>,
    pub declarators: Vec<NetDeclarator>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct NetDeclarator {
    pub name: Identifier,
    pub dimensions: Vec<UnpackedDimension>,
    pub init: Option<Expression>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct DataDeclaration {
    pub const_kw: bool,
    pub var_kw: bool,
    pub lifetime: Option<Lifetime>,
    pub data_type: DataType,
    pub declarators: Vec<VarDeclarator>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ParameterDeclaration {
    pub local: bool,
    pub kind: ParameterKind,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ParameterKind {
    Data {
        data_type: DataType,
        assignments: Vec<ParamAssignment>,
    },
    Type {
        assignments: Vec<TypeParamAssignment>,
    },
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ParamAssignment {
    pub name: Identifier,
    pub dimensions: Vec<UnpackedDimension>,
    pub init: Option<Expression>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TypeParamAssignment {
    pub name: Identifier,
    /// IEEE 1800-2023 §6.20.2.1: optional `extends <Base>` constraint
    /// that restricts the type argument to a class derived from `Base`.
    pub extends: Option<Identifier>,
    pub init: Option<DataType>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TypedefDeclaration {
    pub data_type: DataType,
    pub name: Identifier,
    pub dimensions: Vec<UnpackedDimension>,
    pub span: Span,
    /// IEEE 1800-2017 §6.18: true for a bare forward type declaration
    /// `typedef name;` (no type body). Such a name must be resolved by a later
    /// full typedef in the same scope; elaboration errors otherwise.
    #[cfg_attr(feature = "serde", serde(default))]
    pub forward: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum AlwaysKind {
    Always,
    AlwaysComb,
    AlwaysFf,
    AlwaysLatch,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct AlwaysConstruct {
    pub kind: AlwaysKind,
    pub stmt: Statement,
    pub span: Span,
    /// §21.2.1.7: generate block scope prefix for %m hierarchy.
    #[cfg_attr(feature = "serde", serde(default))]
    pub gen_scope: String,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct InitialConstruct {
    pub stmt: Statement,
    pub span: Span,
    /// §21.2.1.7: generate block scope prefix for %m hierarchy.
    #[cfg_attr(feature = "serde", serde(default))]
    pub gen_scope: String,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct FinalConstruct {
    pub stmt: Statement,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ContinuousAssign {
    pub strength: Option<String>,
    /// `#d` / first of `#(rise, fall[, turnoff])` (§10.3.3).
    pub delay: Option<Expression>,
    /// Second delay of the pair/triple form: applied to a transition to 0.
    #[cfg_attr(feature = "serde", serde(default))]
    pub delay_fall: Option<Expression>,
    /// Third delay: applied to a transition to z.
    #[cfg_attr(feature = "serde", serde(default))]
    pub delay_off: Option<Expression>,
    pub assignments: Vec<(Expression, Expression)>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ModuleInstantiation {
    pub module_name: Identifier,
    pub params: Option<Vec<ParamConnection>>,
    pub instances: Vec<HierarchicalInstance>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ParamValue {
    Expr(Expression),
    Type(DataType),
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ParamConnection {
    Ordered(Option<ParamValue>),
    Named {
        name: Identifier,
        value: Option<ParamValue>,
    },
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct HierarchicalInstance {
    pub name: Identifier,
    pub dimensions: Vec<UnpackedDimension>,
    pub connections: Vec<PortConnection>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum PortConnection {
    Ordered(Option<Expression>),
    /// `.name(expr)`, `.name()` (explicitly unconnected) or `.name` (implicit
    /// connection to a same-named net). `implicit` is true only for the last,
    /// parenthesis-free form (§23.3.2.2), which requires a matching net; the
    /// `.name()` form is an explicit no-connect and imposes no such requirement.
    Named {
        name: Identifier,
        expr: Option<Expression>,
        implicit: bool,
    },
    Wildcard,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct GenerateRegion {
    pub items: Vec<ModuleItem>,
    pub span: Span,
}

/// A generate-if construct: if (cond) items [else if (cond) items]* [else items]
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct GenerateIf {
    /// Chain of (condition, items). Last entry may have None condition for `else`.
    pub branches: Vec<(Option<super::expr::Expression>, Vec<ModuleItem>)>,
    /// §27.6 `begin : label` block name per branch (parallel to `branches`).
    /// Empty (older cached ASTs) means all branches are unnamed.
    #[cfg_attr(feature = "serde", serde(default))]
    pub branch_labels: Vec<Option<String>>,
    pub span: Span,
}

/// A single arm of a generate-case construct.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct GenerateCaseArm {
    /// Constant expressions matched against the selector. Empty for the
    /// `default` arm.
    pub values: Vec<super::expr::Expression>,
    /// Generate items elaborated when this arm is selected.
    pub items: Vec<ModuleItem>,
    /// §27.6 `begin : label` block name for this arm.
    #[cfg_attr(feature = "serde", serde(default))]
    pub label: Option<String>,
}

/// A generate-case construct: case (selector) <arm>* endcase
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct GenerateCase {
    pub selector: super::expr::Expression,
    pub arms: Vec<GenerateCaseArm>,
    pub span: Span,
}

/// A generate-for loop: for (init; cond; incr) items
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct GenerateFor {
    /// Genvar name
    pub var: String,
    /// Initial value — the literal fold of `init` only (0 for any other
    /// initializer); elaboration folds `init` itself.
    pub init_val: i64,
    /// §27.4: the genvar initializer, a constant expression (`i = P`,
    /// `i = -2`, `i = $low(a)`).
    #[cfg_attr(feature = "serde", serde(default))]
    pub init: Option<super::expr::Expression>,
    /// Condition expression
    pub cond: super::expr::Expression,
    /// Increment expression (genvar update)
    pub incr: super::expr::Expression,
    /// Body items to replicate
    pub items: Vec<ModuleItem>,
    /// Optional `begin : <label>` block name. Used to namespace per-iteration
    /// declaration renames so two generate-for blocks that share a genvar name
    /// (e.g. black-parrot's many `for (genvar i …) begin : <label>` blocks)
    /// don't collide on `sig__gf_i_<n>_`.
    #[cfg_attr(feature = "serde", serde(default))]
    pub name: Option<String>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct GenvarDeclaration {
    pub names: Vec<Identifier>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct FunctionDeclaration {
    pub lifetime: Option<Lifetime>,
    /// IEEE 1800-2023 §8.20.5: `function :final/:extends/:initial`.
    #[cfg_attr(feature = "serde", serde(default))]
    pub specifier: Option<MethodSpecifier>,
    pub return_type: DataType,
    pub name: TypeName,
    pub ports: Vec<FunctionPort>,
    pub items: Vec<super::stmt::Statement>,
    pub endlabel: Option<Identifier>,
    /// Non-ANSI body port declarations (`function f; input int x; …`). The
    /// main parser otherwise discards these (they parse to a `Null` stmt);
    /// retained here only for the strict-check pass (duplicate-port detection).
    /// Not consumed by elaboration — behavior-neutral.
    #[cfg_attr(feature = "serde", serde(default))]
    pub strict_body_ports: Vec<Identifier>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TaskDeclaration {
    pub lifetime: Option<Lifetime>,
    /// IEEE 1800-2023 §8.20.5: `task :final/:extends/:initial`.
    #[cfg_attr(feature = "serde", serde(default))]
    pub specifier: Option<MethodSpecifier>,
    pub name: TypeName,
    pub ports: Vec<FunctionPort>,
    pub items: Vec<super::stmt::Statement>,
    pub endlabel: Option<Identifier>,
    /// Non-ANSI body port declarations (`task t; input int x; …`); retained
    /// only for the strict-check pass. Not consumed by elaboration.
    #[cfg_attr(feature = "serde", serde(default))]
    pub strict_body_ports: Vec<Identifier>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct FunctionPort {
    pub direction: PortDirection,
    pub var_kw: bool,
    pub data_type: DataType,
    pub name: Identifier,
    pub dimensions: Vec<UnpackedDimension>,
    pub default: Option<Expression>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ImportDeclaration {
    pub items: Vec<ImportItem>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ImportItem {
    pub package: Identifier,
    pub item: Option<Identifier>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TimeunitsDeclaration {
    pub unit: Option<String>,
    pub precision: Option<String>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ClassDeclaration {
    pub virtual_kw: bool,
    #[cfg_attr(feature = "serde", serde(default))]
    pub is_interface: bool,
    /// IEEE 1800-2023 §8.20.5: `class :final <name>` — class cannot
    /// be extended.
    #[cfg_attr(feature = "serde", serde(default))]
    pub is_final: bool,
    pub name: Identifier,
    pub params: Vec<ParameterDeclaration>,
    pub extends: Option<ClassExtends>,
    pub implements: Vec<Identifier>,
    pub items: Vec<ClassItem>,
    pub endlabel: Option<Identifier>,
    pub span: Span,
}

/// extends clause: `extends base_class [(args)]`
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ClassExtends {
    pub name: Identifier,
    pub args: Vec<ParamValue>,
    pub span: Span,
}

/// Items that can appear inside a class body.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ClassItem {
    /// Property: class member variable
    Property(ClassProperty),
    /// Method: function or task
    Method(ClassMethod),
    /// Constraint declaration
    Constraint(ClassConstraint),
    /// Typedef inside class
    Typedef(TypedefDeclaration),
    /// Parameter/localparam inside class
    Parameter(ParameterDeclaration),
    /// Class inside class (nested)
    Class(ClassDeclaration),
    /// Covergroup inside class
    Covergroup(CovergroupDeclaration),
    /// Import statement
    Import(ImportDeclaration),
    /// Empty item (stray semicolons)
    Empty,
}

/// Class property (member variable).
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ClassProperty {
    pub qualifiers: Vec<ClassQualifier>,
    pub data_type: super::types::DataType,
    pub declarators: Vec<VarDeclarator>,
    pub span: Span,
}

/// Class method (function/task).
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ClassMethod {
    pub qualifiers: Vec<ClassQualifier>,
    pub kind: ClassMethodKind,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ClassMethodKind {
    Function(FunctionDeclaration),
    Task(TaskDeclaration),
    /// Pure virtual prototype: `pure virtual function ...;`
    PureVirtual(FunctionDeclaration),
    /// extern method (body defined outside class)
    Extern(FunctionDeclaration),
}

/// Class constraint.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ClassConstraint {
    pub is_static: bool,
    #[cfg_attr(feature = "serde", serde(default))]
    pub is_extern: bool,
    #[cfg_attr(feature = "serde", serde(default))]
    pub has_body: bool,
    pub name: Identifier,
    pub items: Vec<ConstraintItem>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ConstraintItem {
    Expr(Expression),
    Inside {
        expr: Expression,
        range: Vec<ConstraintRange>,
        #[cfg_attr(feature = "serde", serde(default))]
        is_dist: bool,
        /// Parallel to `range`. Only populated when `is_dist`; absent entries
        /// (or all-`None` entries) mean "uniform weight 1 per LRM default".
        #[cfg_attr(feature = "serde", serde(default))]
        dist_weights: Vec<Option<DistWeight>>,
        span: Span,
    },
    Implication {
        condition: Expression,
        constraint: Box<ConstraintItem>,
        span: Span,
    },
    IfElse {
        condition: Expression,
        then_item: Box<ConstraintItem>,
        else_item: Option<Box<ConstraintItem>>,
        span: Span,
    },
    Foreach {
        array: Expression,
        vars: Vec<Option<Identifier>>,
        item: Box<ConstraintItem>,
        span: Span,
    },
    Solve {
        before: Vec<Identifier>,
        after: Vec<Identifier>,
        /// §18.5.10: each operand of `before` / `after` as written, a
        /// member or element path (`a.b.c`, `arr[i].f`), parallel to
        /// `before` / `after` (which keep the root identifier).
        #[cfg_attr(feature = "serde", serde(default))]
        before_paths: Vec<Expression>,
        #[cfg_attr(feature = "serde", serde(default))]
        after_paths: Vec<Expression>,
        span: Span,
    },
    Soft(Box<ConstraintItem>),
    Block(Vec<ConstraintItem>),
    /// LRM §18.5.5 `unique {expr_list}` where the list could not be fully
    /// desugared to pairwise `!=` at parse time — i.e. a single expression
    /// naming a whole array, whose element count is only known at solve
    /// time (`unique {gpr}` over `rand reg_t gpr[4]`). Multi-expression
    /// lists are still desugared by the parser and never reach this variant.
    Unique {
        exprs: Vec<Expression>,
        span: Span,
    },
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ConstraintRange {
    Value(Expression),
    Range { lo: Expression, hi: Expression },
}

impl ConstraintRange {
    pub fn for_each_expr_mut(&mut self, f: &mut dyn FnMut(&mut Expression)) {
        match self {
            ConstraintRange::Value(e) => f(e),
            ConstraintRange::Range { lo, hi } => {
                f(lo);
                f(hi);
            }
        }
    }
}

/// LRM §18.5.4 weight specifier in `dist { item := w, item :/ w }`.
/// `Each` (`:=`) — the weight applies independently to every value in the
/// range (so a range expands to N items each with weight w).
/// `Total` (`:/`) — the weight is split evenly across the values in the
/// range (so each individual value gets w/N).
/// Stored as a parallel `Vec<DistWeight>` on the `Inside { is_dist: true }`
/// variant, indexed parallel to `range: Vec<ConstraintRange>`. `None` means
/// "no explicit weight" (the LRM default of `:= 1`).
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum DistWeight {
    Each(Expression),
    Total(Expression),
}

/// Qualifiers for class properties and methods.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ClassQualifier {
    Static,
    Protected,
    Local,
    Rand,
    Randc,
    Virtual,
    Pure,
    Extern,
    Const,
}

/// IEEE 1800-2023 §8.20.5: colon-prefixed method specifier on
/// `function` / `task`. Three variants:
/// - `:final`   — locks the method against further override.
/// - `:extends` — explicit override marker (must be overriding).
/// - `:initial` — explicit non-override marker (must not be overriding).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum MethodSpecifier {
    Final,
    Extends,
    Initial,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum PackageItem {
    Parameter(ParameterDeclaration),
    Typedef(TypedefDeclaration),
    Function(FunctionDeclaration),
    Task(TaskDeclaration),
    Import(ImportDeclaration),
    DPIImport(DPIImport),
    DPIExport(DPIExport),
    Data(DataDeclaration),
    Class(ClassDeclaration),
    Checker(CheckerDeclaration),
    Let(LetDeclaration),
    Nettype(NettypeDeclaration),
    /// §26.2: package_item includes concurrent_assertion_item_declaration,
    /// so a package may declare named properties/sequences (hoisted into
    /// importing modules like package subroutines are).
    Property(PropertyDeclaration),
    Sequence(SequenceDeclaration),
    /// Placeholder for package items that the parser consumed but does not
    /// model (e.g. non-DPI `export pkg::*;` re-exports). Lets
    /// `parse_package_declaration`'s item loop consume them without falling
    /// through to its `else { self.bump(); }` recovery, which would otherwise
    /// eat the `endpackage` keyword and corrupt parsing.
    Null,
    /// §26.6 `export P::*;` / `export P::sym;` / `export *::*;` — reuses the
    /// import-declaration shape (package `*` spells the export-everything
    /// form). Appended last for bincode index stability.
    Export(ImportDeclaration),
    /// `timeunit`/`timeprecision` inside a package (LRM §3.14.2.2): the
    /// package's own time unit, overriding the file's `timescale for the
    /// delays in its classes, tasks and functions. Appended last for bincode
    /// index stability.
    TimeunitsDecl(crate::ast::decl::TimeunitsDeclaration),
    /// §19.3 a covergroup declared in a package, or at file scope (then
    /// carried as `Description::PackageItem`). Appended last for bincode
    /// index stability.
    Covergroup(CovergroupDeclaration),
}
