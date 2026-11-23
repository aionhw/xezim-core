use super::*;

pub(super) fn default_timeunit_exp() -> i32 {
    -9
}

/// Decode a SystemVerilog time literal (e.g. "10ns", "100ps") into a
/// log10-second exponent. Returns -9 (1ns) on unparseable input.
/// Seconds -> power-of-ten exponent (1e-6 -> -6). Rounds, so float drift in
/// the seconds value does not shift the exponent.
pub fn secs_to_exp(s: f64) -> i32 {
    if s <= 0.0 {
        return -9;
    }
    s.log10().round() as i32
}

/// Power-of-ten exponent -> seconds (-6 -> 1e-6).
pub fn exp_to_secs(e: i32) -> f64 {
    10f64.powi(e)
}

/// The powers of ten that are exact in an f64 (10^0 to 10^22).
const POW10_EXACT: [f64; 23] = [
    1e0, 1e1, 1e2, 1e3, 1e4, 1e5, 1e6, 1e7, 1e8, 1e9, 1e10, 1e11, 1e12, 1e13, 1e14, 1e15, 1e16,
    1e17, 1e18, 1e19, 1e20, 1e21, 1e22,
];

/// §5.8, §3.14.1: `x * 10^e`, correctly rounded. A time value changes units
/// by a power of ten; 10^n is exact in an f64 up to 10^22, so the product
/// (or, for a negative `e`, the quotient) is the nearest f64 to the exact
/// result. `x / 10f64.powi(-15)` is not: 1e-15 is not 10^-15, and
/// `9200.0 / 1e-15` is 9199999999999998000, so `9200s` under `1ns/1fs` was
/// 2048 fs short of 9200 s and never equal to the integer 9200000000000.
#[inline]
pub fn scale_pow10(x: f64, e: i32) -> f64 {
    match e {
        0 => x,
        1..=22 => x * POW10_EXACT[e as usize],
        -22..=-1 => x / POW10_EXACT[e.unsigned_abs() as usize],
        _ => x * 10f64.powi(e),
    }
}

/// §3.14.1, §6.12.1: round a time value counted in units of a precision to
/// the nearest whole unit, ties away from zero. A decimal half reaches here
/// a few ulps off after a change of unit (`2.5ps` as 2.4999999999999996
/// ps), so a value within four ulps below a half is taken as the half. The
/// slack applies below 2^30 only, where four ulps are under 2^-20; a larger
/// count is rounded as it is (every f64 of 2^52 or more is an integer
/// already). The relative nudge used before, `x * (1 + 1e-12)`, moved such
/// a count: 9.2e15 by 9200.
#[inline]
pub fn round_time_units(x: f64) -> f64 {
    let a = x.abs();
    if !(a < 1_073_741_824.0) {
        return x.round();
    }
    let f = a.floor();
    let r = if a - f >= 0.5 - 4.0 * f64::EPSILON * a.max(1.0) {
        f + 1.0
    } else {
        f
    };
    r.copysign(x)
}

/// §5.8: the value of a time literal of `secs` seconds in a scope whose time
/// unit is 10^`unit_exp` s and whose precision is 10^`prec_exp` s: rounded
/// to the precision (§3.14.1), then expressed in the unit. Both changes of
/// unit are by an exact power of ten (`scale_pow10`), so a literal that is a
/// whole number of precision ticks gives exactly that count whenever an f64
/// holds it (`9200s` under `1ns/1fs` is 9200000000000.0).
#[inline]
pub fn time_literal_in_units(secs: f64, unit_exp: i32, prec_exp: i32) -> f64 {
    scale_pow10(
        round_time_units(scale_pow10(secs, -prec_exp)),
        prec_exp - unit_exp,
    )
}

pub fn time_literal_to_exp(s: &str) -> i32 {
    let s = s.trim();
    let split = s.find(|c: char| c.is_alphabetic()).unwrap_or(s.len());
    let (digits, unit) = s.split_at(split);
    let mantissa: u32 = digits.trim().parse().unwrap_or(1);
    let mantissa_exp = match mantissa {
        1 => 0,
        10 => 1,
        100 => 2,
        _ => 0,
    };
    let unit_exp: i32 = match unit.trim() {
        "s" => 0,
        "ms" => -3,
        "us" => -6,
        "ns" => -9,
        "ps" => -12,
        "fs" => -15,
        _ => -9,
    };
    mantissa_exp + unit_exp
}

pub fn default_tick_s() -> f64 {
    1e-9
}

/// Public entry to pre-scale a module's delays from its timeunit to the global
/// tick (see `rewrite_module_item_delays`).
/// §3.14.2.3: rewrite the TIME SEMANTICS of a subroutine/class body declared
/// in a scope with its own timescale (compilation-unit `timeunit`, class or
/// package scope): delays become global-tick counts, VALUE-position time
/// literals become constants in the scope's unit (`delay = 5ns` under
/// 100ps/10ps is 50), and `$time`/`$stime`/`$realtime` become
/// `$__xz_time_at(unit_exp)` so the runtime reports the DECLARING scope's
/// unit regardless of the caller (ivtest br1003a-d).
pub fn rewrite_scope_time_semantics(
    stmts: &mut [crate::ast::stmt::Statement],
    unit_exp: i32,
    prec_exp: i32,
    tick_s: f64,
) {
    let unit_s = exp_to_secs(unit_exp);
    let prec_s = exp_to_secs(prec_exp);
    for s in stmts.iter_mut() {
        rewrite_stmt_delays(s, unit_s, prec_s, tick_s);
    }
    for s in stmts.iter_mut() {
        scope_time_stmt(s, unit_exp, prec_exp);
    }
}

/// Same rewrite over a whole class declaration (methods + nested classes).
pub fn rewrite_class_time_semantics(
    c: &mut crate::ast::decl::ClassDeclaration,
    unit_exp: i32,
    prec_exp: i32,
    tick_s: f64,
) {
    use crate::ast::decl::{ClassItem, ClassMethodKind};
    for item in &mut c.items {
        match item {
            ClassItem::Method(m) => match &mut m.kind {
                ClassMethodKind::Function(fd)
                | ClassMethodKind::PureVirtual(fd)
                | ClassMethodKind::Extern(fd) => {
                    rewrite_scope_time_semantics(&mut fd.items, unit_exp, prec_exp, tick_s)
                }
                ClassMethodKind::Task(td) => {
                    rewrite_scope_time_semantics(&mut td.items, unit_exp, prec_exp, tick_s)
                }
            },
            ClassItem::Class(nc) => rewrite_class_time_semantics(nc, unit_exp, prec_exp, tick_s),
            _ => {}
        }
    }
}

fn scope_time_stmt(stmt: &mut Statement, u: i32, p: i32) {
    // Expression fields first, then recurse into sub-statements.
    match &mut stmt.kind {
        StatementKind::TimingControl { stmt, .. } => scope_time_stmt(stmt, u, p),
        StatementKind::BlockingAssign { rvalue, .. }
        | StatementKind::NonblockingAssign { rvalue, .. } => scope_time_expr(rvalue, u, p),
        StatementKind::Return(Some(e)) => scope_time_expr(e, u, p),
        StatementKind::VarDecl { declarators, .. }
        | StatementKind::ParamDecl { declarators, .. } => {
            for d in declarators.iter_mut() {
                if let Some(init) = d.init.as_mut() {
                    scope_time_expr(init, u, p);
                }
            }
        }
        StatementKind::Expr(e) => scope_time_expr(e, u, p),
        StatementKind::SeqBlock { stmts, .. } | StatementKind::ParBlock { stmts, .. } => {
            for s in stmts.iter_mut() {
                scope_time_stmt(s, u, p);
            }
        }
        StatementKind::If {
            condition,
            then_stmt,
            else_stmt,
            ..
        } => {
            scope_time_expr(condition, u, p);
            scope_time_stmt(then_stmt, u, p);
            if let Some(e) = else_stmt {
                scope_time_stmt(e, u, p);
            }
        }
        StatementKind::For { body, .. }
        | StatementKind::Foreach { body, .. }
        | StatementKind::While { body, .. }
        | StatementKind::DoWhile { body, .. }
        | StatementKind::Repeat { body, .. }
        | StatementKind::Forever { body, .. } => scope_time_stmt(body, u, p),
        StatementKind::Wait { stmt, .. } => scope_time_stmt(stmt, u, p),
        StatementKind::Case { items, .. } => {
            for it in items.iter_mut() {
                scope_time_stmt(&mut it.stmt, u, p);
            }
        }
        _ => {}
    }
}

fn scope_time_expr(e: &mut Expression, u: i32, p: i32) {
    use crate::ast::expr::NumberLiteral;
    match &mut e.kind {
        // VALUE-position time literal: absolute seconds, scaled to the
        // scope's unit rounded at its precision (§5.8).
        ExprKind::Number(NumberLiteral::Time(secs)) => {
            e.kind = ExprKind::Number(NumberLiteral::Real(time_literal_in_units(*secs, u, p)));
        }
        ExprKind::SystemCall { name, args } => {
            if args.is_empty() && matches!(name.as_str(), "$time" | "$stime" | "$realtime") {
                // §20.3.2: `$stime` keeps its own name, the 32-bit read.
                *name = match name.as_str() {
                    "$realtime" => "$__xz_realtime_at",
                    "$stime" => "$__xz_stime_at",
                    _ => "$__xz_time_at",
                }
                .to_string();
                args.push(Expression::new(
                    ExprKind::Number(NumberLiteral::Real(u as f64)),
                    e.span,
                ));
            } else {
                for a in args.iter_mut() {
                    scope_time_expr(a, u, p);
                }
            }
        }
        ExprKind::Binary { left, right, .. } => {
            scope_time_expr(left, u, p);
            scope_time_expr(right, u, p);
        }
        ExprKind::Unary { operand, .. } => scope_time_expr(operand, u, p),
        ExprKind::Paren(inner) => scope_time_expr(inner, u, p),
        ExprKind::Conditional {
            condition,
            then_expr,
            else_expr,
        } => {
            scope_time_expr(condition, u, p);
            scope_time_expr(then_expr, u, p);
            scope_time_expr(else_expr, u, p);
        }
        ExprKind::Call { args, .. } => {
            for a in args.iter_mut() {
                scope_time_expr(a, u, p);
            }
        }
        ExprKind::Concatenation(parts) => {
            for a in parts.iter_mut() {
                scope_time_expr(a, u, p);
            }
        }
        ExprKind::Index { expr, index } => {
            scope_time_expr(expr, u, p);
            scope_time_expr(index, u, p);
        }
        _ => {}
    }
}

thread_local! {
    /// §6.6.7: the nettype names a design element can see while its delays
    /// are rewritten: those of the compilation units and packages
    /// (`set_design_nettype_names`), then also its own, less the names its
    /// own typedefs and classes hide.
    static NETTYPE_NAMES: std::cell::RefCell<HashSet<String>> = std::cell::RefCell::default();
}

/// Record the nettype names the compilation units and packages of the design
/// declare, before its design elements' delays are rewritten.
pub fn set_design_nettype_names(names: HashSet<String>) {
    NETTYPE_NAMES.with(|n| *n.borrow_mut() = names);
}

pub fn rewrite_module_delays_pub(items: &mut [ModuleItem], unit_s: f64, prec_s: f64, tick_s: f64) {
    // §6.18, §26.5: the element's own nettypes are visible in it, and its own
    // typedefs and classes hide outer nettypes of the same name.
    let outer = NETTYPE_NAMES.with(|n| n.borrow().clone());
    let mut visible = outer.clone();
    for item in items.iter() {
        match item {
            ModuleItem::NettypeDeclaration(nd) => {
                visible.insert(nd.name.name.clone());
            }
            ModuleItem::TypedefDeclaration(td) if !td.forward => {
                visible.remove(&td.name.name);
            }
            ModuleItem::ClassDeclaration(cd) => {
                visible.remove(&cd.name.name);
            }
            _ => {}
        }
    }
    NETTYPE_NAMES.with(|n| *n.borrow_mut() = visible);
    rewrite_module_item_delays(items, unit_s, prec_s, tick_s);
    NETTYPE_NAMES.with(|n| *n.borrow_mut() = outer);
    scope_time_decl_inits(items, secs_to_exp(unit_s), secs_to_exp(prec_s));
}

/// §6.6.7 `net_declaration ::= nettype_identifier [delay_control] ...`: the
/// parser keeps a nettype net's delay (`rn #3 n = e;`) in the type's argument
/// list, since it cannot tell a nettype name from a class name there.
fn nettype_delay_args(dd: &mut crate::ast::decl::DataDeclaration) -> Option<&mut Vec<Expression>> {
    let DataType::TypeReference {
        name, type_args, ..
    } = &mut dd.data_type
    else {
        return None;
    };
    if type_args.is_empty() || type_args.len() > 3 {
        return None;
    }
    let key = match name.scopes.as_slice() {
        [] => name.name.name.clone(),
        [pkg] => format!("{}::{}", pkg.name.name, name.name.name),
        _ => return None,
    };
    NETTYPE_NAMES
        .with(|n| n.borrow().contains(&key))
        .then_some(type_args)
}

/// §5.8 for a VALUE-position time literal in a DECLARATION initialiser.
///
/// `rewrite_scope_time_semantics` already applies `scope_time_expr` to
/// procedural code, so `#100ns`, `x = 100ns` and an automatic-variable
/// initialiser were all scaled to the declaring scope's unit. Module ITEMS
/// were never walked, so a declaration initialiser kept its
/// `NumberLiteral::Time` and fell through to the fixed-1ns fallback in
/// `eval_expr` (`secs * 1e9`) — scaling to nanoseconds regardless of the
/// module's own unit. The two paths disagreed:
///
/// ```text
///                        `timescale 1fs/1fs, both meaning 100 ns
///   #100ns                            100000000   correct
///   localparam realtime T = 100ns           100   1e6 short
/// ```
///
/// The error is the ratio `1ns / unit`, so it was invisible at the default
/// 1 ns timeunit and grew as the timescale got finer. Worse than a scale
/// factor: a sub-nanosecond literal did not shrink, it VANISHED, because
/// the folded value rounded to zero at the module's precision
/// (`localparam realtime D = 300ps` under 1ps/1ps folded to 0.3, and the
/// delay it fed measured 0.000 ps).
///
/// Note this walks INITIALISERS only. Delay-position expressions keep going
/// through `rewrite_module_item_delays`, which converts to global ticks; the
/// two passes touch disjoint expressions.
pub fn scope_time_decl_inits(items: &mut [ModuleItem], unit_exp: i32, prec_exp: i32) {
    for item in items.iter_mut() {
        match item {
            ModuleItem::ParameterDeclaration(pd) | ModuleItem::LocalparamDeclaration(pd) => {
                scope_time_param_decl(pd, unit_exp, prec_exp);
            }
            ModuleItem::DataDeclaration(dd) => {
                for d in dd.declarators.iter_mut() {
                    if let Some(e) = d.init.as_mut() {
                        scope_time_expr(e, unit_exp, prec_exp);
                    }
                }
            }
            ModuleItem::NetDeclaration(nd) => {
                for d in nd.declarators.iter_mut() {
                    if let Some(e) = d.init.as_mut() {
                        scope_time_expr(e, unit_exp, prec_exp);
                    }
                }
            }
            // A parameter OVERRIDE at an instantiation (`m #(.P(50ns)) u();`)
            // and a `defparam` are written in THIS module's unit, so they
            // scale here too; otherwise a design that sets its timing
            // parameters from the instantiation saw the default scaled and
            // the override not.
            ModuleItem::ModuleInstantiation(inst) => {
                for conn in inst.instances.iter_mut().flat_map(|i| &mut i.connections) {
                    let actual = match conn {
                        PortConnection::Ordered(expr) | PortConnection::Named { expr, .. } => expr,
                        PortConnection::Wildcard => continue,
                    };
                    if let Some(actual) = actual {
                        let mut literal = &*actual;
                        while let ExprKind::Paren(inner) = &literal.kind {
                            literal = inner;
                        }
                        // §5.8: scale a time literal in the connecting scope
                        // before a port substitutes it into another scope.
                        if matches!(literal.kind, ExprKind::Number(NumberLiteral::Time(_))) {
                            scope_time_expr(actual, unit_exp, prec_exp);
                        }
                    }
                }
                if let Some(params) = inst.params.as_mut() {
                    for pc in params.iter_mut() {
                        let value = match pc {
                            crate::ast::decl::ParamConnection::Ordered(v) => v,
                            crate::ast::decl::ParamConnection::Named { value, .. } => value,
                        };
                        if let Some(crate::ast::decl::ParamValue::Expr(e)) = value.as_mut() {
                            scope_time_expr(e, unit_exp, prec_exp);
                        }
                    }
                }
            }
            ModuleItem::Defparam(list) => {
                for (_, e) in list.iter_mut() {
                    scope_time_expr(e, unit_exp, prec_exp);
                }
            }
            // §3.14.2.3, §20.3: `$time`, `$stime` and `$realtime` on the right
            // of a continuous assignment read in this module's unit, as in a
            // net declaration assignment above. The assignment runs from
            // whatever process changed its operands, so unscoped it reported
            // that process's unit (`assign t = a ? $time : 0;` in a 1 ps child
            // read 499 at 499 fs from a 1 fs parent).
            ModuleItem::ContinuousAssign(ca) => {
                for (_, rhs) in ca.assignments.iter_mut() {
                    scope_time_expr(rhs, unit_exp, prec_exp);
                }
            }
            // Generate scopes are the same module scope for timing purposes.
            ModuleItem::GenerateFor(gf) => scope_time_decl_inits(&mut gf.items, unit_exp, prec_exp),
            ModuleItem::GenerateIf(gi) => {
                for (_c, items) in gi.branches.iter_mut() {
                    scope_time_decl_inits(items, unit_exp, prec_exp);
                }
            }
            ModuleItem::GenerateRegion(gr) => {
                scope_time_decl_inits(&mut gr.items, unit_exp, prec_exp)
            }
            ModuleItem::GenerateCase(gc) => {
                for arm in gc.arms.iter_mut() {
                    scope_time_decl_inits(&mut arm.items, unit_exp, prec_exp);
                }
            }
            _ => {}
        }
    }
}

/// §5.8 over a declaration's parameter PORT list, which is not part of
/// `items` and so is not reached by `rewrite_module_delays_pub`.
pub fn scope_time_param_ports_pub(
    params: &mut [crate::ast::decl::ParameterDeclaration],
    unit_s: f64,
    prec_s: f64,
) {
    let (u, p) = (secs_to_exp(unit_s), secs_to_exp(prec_s));
    for pd in params.iter_mut() {
        scope_time_param_decl(pd, u, p);
    }
}

/// Same §5.8 scaling for a parameter declaration, including a parameter PORT
/// (`module m #(parameter realtime P = 100ns)`), which is not a `ModuleItem`
/// and so is reached from the declaration's own `params` list.
pub fn scope_time_param_decl(
    pd: &mut crate::ast::decl::ParameterDeclaration,
    unit_exp: i32,
    prec_exp: i32,
) {
    if let crate::ast::decl::ParameterKind::Data { assignments, .. } = &mut pd.kind {
        for a in assignments.iter_mut() {
            if let Some(e) = a.init.as_mut() {
                scope_time_expr(e, unit_exp, prec_exp);
            }
        }
    }
}

/// `rewrite_scope_time_semantics` over a package's subroutines and classes.
pub fn rewrite_package_time_semantics(
    items: &mut [crate::ast::decl::PackageItem],
    unit_exp: i32,
    prec_exp: i32,
    tick_s: f64,
) {
    use crate::ast::decl::PackageItem;
    for item in items.iter_mut() {
        match item {
            PackageItem::Class(cd) => rewrite_class_time_semantics(cd, unit_exp, prec_exp, tick_s),
            PackageItem::Task(td) => {
                rewrite_scope_time_semantics(&mut td.items, unit_exp, prec_exp, tick_s)
            }
            PackageItem::Function(f) => {
                rewrite_scope_time_semantics(&mut f.items, unit_exp, prec_exp, tick_s)
            }
            _ => {}
        }
    }
}

/// Rewrite every delay expression inside a module's items so it is expressed in
/// GLOBAL TICK units (`tick_s` seconds each), given the module's own timeunit
/// `unit_s`. A *bare* delay `#5` is a count of `unit_s`, so it scales by
/// `unit_s / tick_s`; a *time literal* `#10ns` is absolute seconds, so it
/// becomes `seconds / tick_s`. With no finer timescale anywhere (tick_s = unit_s
/// = 1 ns) both are identities, so behaviour is unchanged. LRM §22.7 / §3.14.
/// Scale every delay in a class's method bodies (and nested classes).
fn rewrite_class_delays(cd: &mut ClassDeclaration, unit_s: f64, prec_s: f64, tick_s: f64) {
    for item in cd.items.iter_mut() {
        match item {
            ClassItem::Method(m) => match &mut m.kind {
                ClassMethodKind::Task(td) => {
                    for st in td.items.iter_mut() {
                        rewrite_stmt_delays(st, unit_s, prec_s, tick_s);
                    }
                }
                // A function cannot consume time, but `#0` is legal inside one
                // and must still be tick-denominated for the executor.
                ClassMethodKind::Function(f) => {
                    for st in f.items.iter_mut() {
                        rewrite_stmt_delays(st, unit_s, prec_s, tick_s);
                    }
                }
                _ => {}
            },
            ClassItem::Class(inner) => rewrite_class_delays(inner, unit_s, prec_s, tick_s),
            _ => {}
        }
    }
}

fn rewrite_module_item_delays(items: &mut [ModuleItem], unit_s: f64, prec_s: f64, tick_s: f64) {
    for item in items.iter_mut() {
        match item {
            ModuleItem::AlwaysConstruct(ac) => {
                rewrite_stmt_delays(&mut ac.stmt, unit_s, prec_s, tick_s)
            }
            ModuleItem::InitialConstruct(ic) => {
                rewrite_stmt_delays(&mut ic.stmt, unit_s, prec_s, tick_s)
            }
            ModuleItem::FinalConstruct(fc) => {
                rewrite_stmt_delays(&mut fc.stmt, unit_s, prec_s, tick_s)
            }
            // Task bodies carry delays too (`task pulse; #1 clk = 1; ...`).
            // Without this a task-body `#1` stayed a raw 1-tick delay while
            // the caller's `#1` was unit-scaled — a 1ns/1ps module's task
            // delays silently ran 1000x too fast (§3.14.3).
            ModuleItem::TaskDeclaration(td) => {
                for s in td.items.iter_mut() {
                    rewrite_stmt_delays(s, unit_s, prec_s, tick_s);
                }
            }
            // `assign #5 y = a;` — the cont-assign delay counts module
            // timeunits like any other delay; unscaled it ran as raw ticks
            // (5 ps in a 1ns/1ps module instead of 5 ns).
            ModuleItem::ContinuousAssign(ca) => {
                for d in [&mut ca.delay, &mut ca.delay_fall, &mut ca.delay_off]
                    .into_iter()
                    .flatten()
                {
                    rewrite_delay_expr(d, unit_s, prec_s, tick_s);
                }
            }
            // `rn #2 n = a;` — a nettype net's delay likewise.
            ModuleItem::DataDeclaration(dd) => {
                if let Some(args) = nettype_delay_args(dd) {
                    for d in args.iter_mut() {
                        rewrite_delay_expr(d, unit_s, prec_s, tick_s);
                    }
                }
            }
            // `wire #2 w = a;` — a net declaration delay likewise.
            ModuleItem::NetDeclaration(nd) => {
                for d in [&mut nd.delay, &mut nd.delay_fall, &mut nd.delay_off]
                    .into_iter()
                    .flatten()
                {
                    rewrite_delay_expr(d, unit_s, prec_s, tick_s);
                }
            }
            // `buf #(4) g(y, a);` — gate delays likewise count timeunits.
            ModuleItem::GateInstantiation(gi) => {
                if let Some(d) = gi.delay.as_mut() {
                    rewrite_delay_expr(d, unit_s, prec_s, tick_s);
                }
                if let Some(d) = gi.delay_off.as_mut() {
                    rewrite_delay_expr(d, unit_s, prec_s, tick_s);
                }
                if let Some(d) = gi.delay_fall.as_mut() {
                    rewrite_delay_expr(d, unit_s, prec_s, tick_s);
                }
            }
            // A class METHOD body carries delays exactly like a task body, and
            // for the same reason (§3.14.3): a bare `#5` counts the enclosing
            // scope's timeunit. Classes were the one construct this pass never
            // walked, so a `#5` inside a class task stayed a raw 5-TICK delay
            // while the identical `#5` in a module task was unit-scaled — in a
            // 1ns/1ps scope the class delay ran 1000x too short. That is
            // invisible in a pure-RTL design and breaks every class-based
            // testbench that paces itself with `#`.
            ModuleItem::ClassDeclaration(cd) => rewrite_class_delays(cd, unit_s, prec_s, tick_s),
            // §30.4 module path delays and §31 timing check limits count
            // the module's time unit too. Unscaled, `(a => y) = 5;` in a
            // 1ns/1ps module delayed 5 ps instead of 5 ns.
            ModuleItem::SpecifyBlock(sb) => {
                for p in sb.paths.iter_mut() {
                    for d in p.delays.iter_mut() {
                        rewrite_delay_expr(d, unit_s, prec_s, tick_s);
                    }
                }
                for tc in sb.timing_checks.iter_mut() {
                    for &i in timing_check_limit_args(&tc.name) {
                        if let Some(Some(arg)) = tc.args.get_mut(i) {
                            rewrite_delay_expr(&mut arg.expr, unit_s, prec_s, tick_s);
                        }
                    }
                }
            }
            ModuleItem::GenerateFor(gf) => {
                rewrite_module_item_delays(&mut gf.items, unit_s, prec_s, tick_s)
            }
            ModuleItem::GenerateIf(gi) => {
                for (_c, items) in gi.branches.iter_mut() {
                    rewrite_module_item_delays(items, unit_s, prec_s, tick_s);
                }
            }
            ModuleItem::GenerateRegion(gr) => {
                rewrite_module_item_delays(&mut gr.items, unit_s, prec_s, tick_s)
            }
            ModuleItem::GenerateCase(gc) => {
                for arm in gc.arms.iter_mut() {
                    rewrite_module_item_delays(&mut arm.items, unit_s, prec_s, tick_s);
                }
            }
            _ => {}
        }
    }
}

/// Whether `items` (generate constructs included) hold an instance with
/// delays of a definition `is_udp` names.
pub fn instantiates_udp(items: &[ModuleItem], is_udp: &dyn Fn(&str) -> bool) -> bool {
    items.iter().any(|item| match item {
        ModuleItem::ModuleInstantiation(mi) => mi.params.is_some() && is_udp(&mi.module_name.name),
        ModuleItem::GenerateFor(gf) => instantiates_udp(&gf.items, is_udp),
        ModuleItem::GenerateIf(gi) => gi
            .branches
            .iter()
            .any(|(_c, items)| instantiates_udp(items, is_udp)),
        ModuleItem::GenerateRegion(gr) => instantiates_udp(&gr.items, is_udp),
        ModuleItem::GenerateCase(gc) => {
            gc.arms.iter().any(|arm| instantiates_udp(&arm.items, is_udp))
        }
        _ => false,
    })
}

/// §29.8, §28.16, §3.14.2: the delays of a UDP instance (`udp #(4) u(q, a);`,
/// `#(rise, fall)`) count the time unit of the module that holds the
/// instance, like the delays of a gate. A UDP instance is written as a module
/// instantiation, and which names are primitives is known only once every
/// definition is in hand, so `rewrite_module_item_delays` cannot take them;
/// this pass runs afterwards, once per holding definition.
pub fn rewrite_udp_instance_delays(
    items: &mut [ModuleItem],
    is_udp: &dyn Fn(&str) -> bool,
    unit_s: f64,
    prec_s: f64,
    tick_s: f64,
) {
    for item in items.iter_mut() {
        match item {
            ModuleItem::ModuleInstantiation(mi) if is_udp(&mi.module_name.name) => {
                for conn in mi.params.iter_mut().flatten() {
                    if let crate::ast::decl::ParamConnection::Ordered(Some(
                        crate::ast::decl::ParamValue::Expr(d),
                    )) = conn
                    {
                        rewrite_delay_expr(d, unit_s, prec_s, tick_s);
                    }
                }
            }
            ModuleItem::GenerateFor(gf) => {
                rewrite_udp_instance_delays(&mut gf.items, is_udp, unit_s, prec_s, tick_s)
            }
            ModuleItem::GenerateIf(gi) => {
                for (_c, items) in gi.branches.iter_mut() {
                    rewrite_udp_instance_delays(items, is_udp, unit_s, prec_s, tick_s);
                }
            }
            ModuleItem::GenerateRegion(gr) => {
                rewrite_udp_instance_delays(&mut gr.items, is_udp, unit_s, prec_s, tick_s)
            }
            ModuleItem::GenerateCase(gc) => {
                for arm in gc.arms.iter_mut() {
                    rewrite_udp_instance_delays(&mut arm.items, is_udp, unit_s, prec_s, tick_s);
                }
            }
            _ => {}
        }
    }
}

/// Replace a single delay expression with its tick-count equivalent.
/// The elaborated form of a `1step` delay value (§3.14.3): one global tick,
/// not rounded to the running scope's precision.
pub const ONE_STEP_DELAY: &str = "$__xz_one_step";

fn rewrite_delay_expr(d: &mut Expression, unit_s: f64, prec_s: f64, tick_s: f64) {
    use crate::ast::expr::NumberLiteral;
    // §3.14.3: a delay rounds to the DECLARING scope's time precision.
    // CONSTANT delays quantize here, where the declaring module is
    // unambiguous — the runtime fallback resolves the scope from execution
    // context and gets it wrong on some task-call paths (a `#0.002` in a
    // 1ns/1ns BFM kept a real 2 ps duration when called hierarchically
    // from a 1 ps-precision testbench, phase-shifting delay-paced loops
    // off the clock grid for the rest of the run).
    // Every change of unit is by an exact power of ten (`scale_pow10`): the
    // quotients of the unit, precision and tick in seconds are not exact
    // (`1e-6 / 1e-15` is 999999999.9999999), and neither was `9200s / 1e-15`.
    let (u, p, t) = (
        secs_to_exp(unit_s),
        secs_to_exp(prec_s),
        secs_to_exp(tick_s),
    );
    // A count of precision units, rounded to a whole one, in global ticks.
    let quant = |prec_units: f64| -> f64 { scale_pow10(round_time_units(prec_units), p - t) };
    match &d.kind {
        // §3.14.3 / A.2.2.3: `1step` is the global time precision, one tick,
        // whatever the scope's own unit and precision (#615).
        ExprKind::Ident(h)
            if h.path.len() == 1 && h.path[0].name.name == crate::ast::decl::CLOCKING_ONE_STEP =>
        {
            // The runtime rounds a delay to the running scope's precision;
            // a step is exempt, so it stays a marker the simulator reads as
            // one unrounded tick.
            *d = Expression::new(
                ExprKind::SystemCall {
                    name: ONE_STEP_DELAY.to_string(),
                    args: Vec::new(),
                },
                d.span,
            );
        }
        ExprKind::Number(NumberLiteral::Time(s)) => {
            // Absolute time literal → ticks, on the precision grid.
            let ticks = quant(scale_pow10(*s, -p));
            *d = Expression::new(ExprKind::Number(NumberLiteral::Real(ticks)), d.span);
        }
        // A FRACTIONAL bare delay is the only bare form the precision grid
        // can move (an integer count of timeunits is always on it): fold
        // and quantize now. Integer and non-constant delays keep the
        // multiply-by-scale form (+ runtime quantization).
        ExprKind::Number(NumberLiteral::Real(r)) => {
            let ticks = quant(scale_pow10(*r, u - p));
            *d = Expression::new(ExprKind::Number(NumberLiteral::Real(ticks)), d.span);
        }
        _ => {
            // Bare delay (count of the module timeunit) → ticks.
            let scale = scale_pow10(1.0, u - t);
            if (scale - 1.0).abs() > f64::EPSILON {
                let span = d.span;
                let inner = std::mem::replace(d, Expression::new(ExprKind::Null, span));
                *d = Expression::new(
                    ExprKind::Binary {
                        op: BinaryOp::Mul,
                        left: Box::new(inner),
                        right: Box::new(Expression::new(
                            ExprKind::Number(NumberLiteral::Real(scale)),
                            span,
                        )),
                    },
                    span,
                );
            }
        }
    }
}

/// §10.3.1 / §10.3.3: a net declaration assignment with a delay
/// (`wire #2 w = a;`, `wire #(1,3) w = a;`) drives the net through that
/// delay, like `assign #2 w = a;`: (rise, fall, turn-off) ticks.
/// §10.3.1 / §28.12: declaration assignments carry the declared drive
/// strength through resolution, just like an explicit continuous assignment.
pub(super) fn net_declaration_driver(
    nd: &crate::ast::decl::NetDeclaration,
    name: &str,
    init: &Expression,
    elab: &mut ElaboratedModule,
) -> Expression {
    let Some(strength) = &nd.strength else {
        return init.clone();
    };
    let mut s1 = String::new();
    let mut s0 = String::new();
    for token in strength.split(',').map(str::trim) {
        if token.ends_with('1') {
            s1 = token.to_string();
        }
        if token.ends_with('0') {
            s0 = token.to_string();
        }
    }
    elab.net_strengths.insert(name.to_string(), (s1, s0));
    match strength_marker(strength) {
        Some((marker, code)) => make_syscall(
            marker,
            vec![init.clone(), strength_code_literal(code, init.span)],
            init.span,
        ),
        None => init.clone(),
    }
}

/// A dynamic delay uses the ordinary delayed-driver path even when its
/// current value is zero. Preserve every specified operand so transition
/// selection can use their values at the instant the RHS changes.
pub(super) fn cont_assign_delays(
    operands: [Option<&Expression>; 3],
    params: &HashMap<String, Value>,
) -> (u64, Option<u64>, Option<u64>, Option<DelayExpressions>) {
    if operands.iter().flatten().any(|e| !is_const_expr(e, params)) {
        return (1, None, None, Some(Box::new(operands.map(|e| e.cloned()))));
    }
    let [rise, fall, off] = operands.map(|e| e.map(|e| eval_const_expr(e, params)));
    (rise.unwrap_or(0), fall, off, None)
}

pub(super) fn net_decl_assign_delay(
    nd: &crate::ast::decl::NetDeclaration,
    params: &HashMap<String, Value>,
) -> (u64, Option<u64>, Option<u64>, Option<DelayExpressions>) {
    cont_assign_delays([nd.delay.as_deref(), nd.delay_fall.as_deref(), nd.delay_off.as_deref()], params)
}

/// §6.7.1 / §10.3.3: the NET delay of `decl` (declared by `nd`) as (rise,
/// fall, turn-off) ticks, evaluated in the declaring scope (`params`).
///
/// A net delay delays EVERY driver of the net — a separate `assign`, a port
/// connection, a gate — so the callers record it in `net_delays` for
/// `apply_net_delays`. §10.3.3: "when there is a continuous assignment in a
/// declaration, the delay is part of the continuous assignment and is not a
/// net delay", so a declarator with an initializer has none (its delay rides
/// on that assignment; see `net_decl_assign_delay`). None as well for an
/// all-zero delay and for an array of nets.
pub(super) fn net_delay_of(
    decl: &crate::ast::decl::NetDeclarator,
    nd: &crate::ast::decl::NetDeclaration,
    params: &HashMap<String, Value>,
) -> Option<(u64, Option<u64>, Option<u64>, Option<DelayExpressions>)> {
    nd.delay.as_ref()?;
    if decl.init.is_some() || !decl.dimensions.is_empty() {
        return None;
    }
    let (rise, fall, off, exprs) = net_decl_assign_delay(nd, params);
    (rise != 0 || fall.unwrap_or(0) != 0 || off.unwrap_or(0) != 0).then_some((rise, fall, off, exprs))
}

/// §9.4.5 intra-assignment delays are canonicalized pre-parse into
/// `$__xz_intra_delay(d, rhs)` marker calls (see xezim's intra_delay pass);
/// their first arg is a delay in module timeunits and must be scaled like
/// any other delay.
fn rewrite_intra_marker_delay(e: &mut Expression, unit_s: f64, prec_s: f64, tick_s: f64) {
    if let ExprKind::SystemCall { name, args } = &mut e.kind {
        if name == "$__xz_intra_delay" && args.len() == 2 {
            rewrite_delay_expr(&mut args[0], unit_s, prec_s, tick_s);
        }
    }
}

fn rewrite_stmt_delays(stmt: &mut Statement, unit_s: f64, prec_s: f64, tick_s: f64) {
    match &mut stmt.kind {
        StatementKind::TimingControl { control, stmt } => {
            if let TimingControl::Delay(d) = control {
                rewrite_delay_expr(d, unit_s, prec_s, tick_s);
            }
            rewrite_stmt_delays(stmt, unit_s, prec_s, tick_s);
        }
        StatementKind::BlockingAssign { rvalue, .. } => {
            rewrite_intra_marker_delay(rvalue, unit_s, prec_s, tick_s);
        }
        StatementKind::NonblockingAssign {
            delay: Some(d),
            rvalue,
            ..
        } => {
            rewrite_delay_expr(d, unit_s, prec_s, tick_s);
            rewrite_intra_marker_delay(rvalue, unit_s, prec_s, tick_s);
        }
        StatementKind::NonblockingAssign { rvalue, .. } => {
            rewrite_intra_marker_delay(rvalue, unit_s, prec_s, tick_s);
        }
        StatementKind::SeqBlock { stmts, .. } | StatementKind::ParBlock { stmts, .. } => {
            for s in stmts.iter_mut() {
                rewrite_stmt_delays(s, unit_s, prec_s, tick_s);
            }
        }
        StatementKind::If {
            then_stmt,
            else_stmt,
            ..
        } => {
            rewrite_stmt_delays(then_stmt, unit_s, prec_s, tick_s);
            if let Some(e) = else_stmt {
                rewrite_stmt_delays(e, unit_s, prec_s, tick_s);
            }
        }
        StatementKind::For { body, .. }
        | StatementKind::Foreach { body, .. }
        | StatementKind::While { body, .. }
        | StatementKind::DoWhile { body, .. }
        | StatementKind::Repeat { body, .. }
        | StatementKind::Forever { body, .. } => rewrite_stmt_delays(body, unit_s, prec_s, tick_s),
        StatementKind::Wait { stmt, .. } => rewrite_stmt_delays(stmt, unit_s, prec_s, tick_s),
        StatementKind::Case { items, .. } => {
            for it in items.iter_mut() {
                rewrite_stmt_delays(&mut it.stmt, unit_s, prec_s, tick_s);
            }
        }
        _ => {}
    }
}
