//! IEEE 1800-2017 §26.3: package-scoped TYPE names.
//!
//! The elaborator and the simulator keep one flat, string-keyed table per
//! design for typedef widths, typedef targets, struct layouts, enum members
//! and classes. A type name declared by two packages (or by a package and by
//! `$unit` or a module) collapsed onto one entry there: the later declaration
//! overwrote the earlier, so a class in the first package got the second
//! package's type, and even `$bits(pkg_one::T)` read the other `T` (#300).
//! Two same-named classes collapsed the same way (`pa::C` ran `pb::C`'s
//! methods).
//!
//! This pass runs on the parsed design, before elaboration. A package typedef
//! or class whose name is ALSO declared elsewhere is renamed to its qualified
//! spelling `pkg::name` (not a legal identifier, so it cannot clash with a
//! user name, and it is the key the qualified lookups already try first), and
//! every reference that resolves to it is rewritten to that spelling, by the
//! §26.3 rules:
//!  * inside package P, P's own declaration wins;
//!  * a local declaration of the scope shadows any import;
//!  * then the scope's explicit imports (`import Q::name;`);
//!  * then its wildcard imports (`import Q::*;`) — when two of them provide
//!    different declarations the name is not visible, an error where it is
//!    used as a type;
//!  * then the enclosing scopes, out to `$unit`;
//!  * `Q::name` always means the declaration Q holds or exports.
//!
//! Enum members (§6.19) get the same treatment without the renaming: a bare
//! run-time reference to a member that two packages (or a package and
//! `$unit` / a module) declare is spelled `pkg::NAME` after the same rules,
//! since all packages' members share one flat table too. Constant contexts
//! (types, parameters, generate conditions) keep the bare name; the
//! elaborator evaluates those while it is still registering the packages.
//!
//! Names declared in one place only are left alone, so a design without
//! such a collision is not touched at all.

use std::collections::BTreeSet;

use crate::hasher::{HashMap, HashSet};

use crate::ast::Description;
use crate::ast::decl::*;
use crate::ast::expr::{
    AssignmentPatternItem, ExprKind, Expression, HierPathSegment, HierarchicalIdentifier,
};
use crate::ast::module::PortList;
use crate::ast::stmt::*;
use crate::ast::types::*;

thread_local! {
    /// Enum member names this pass disambiguates (see `member_is_qualified`).
    static QUALIFIED_MEMBERS: std::cell::RefCell<HashSet<String>> =
        std::cell::RefCell::new(HashSet::default());
}

/// True when `name` is an enum member declared by a package and somewhere
/// else, whose bare run-time references this pass already spelled `pkg::name`
/// for the current design — the flat member table's "later definition wins"
/// then decides nothing those references read.
pub fn member_is_qualified(name: &str) -> bool {
    QUALIFIED_MEMBERS.with(|m| m.borrow().contains(name))
}

/// What a package declares and imports, for owner lookups.
#[derive(Default)]
struct PkgInfo {
    /// Typedef and class names declared directly in the package.
    types: HashSet<String>,
    /// Members of the package's own enum typedefs.
    members: HashSet<String>,
    /// Value names declared directly in the package: functions, tasks,
    /// parameters, variables and `let`s.
    values: HashSet<String>,
    /// Variable names declared directly in the package (a subset of
    /// `values`).
    vars: HashSet<String>,
    /// `import Q::name;` as (Q, name).
    explicit: Vec<(String, String)>,
    /// `import Q::*;`
    wild: Vec<String>,
    /// `export Q::name;` / `export Q::*;` / `export *::*;` as (Q or "*", name).
    exports: Vec<(String, Option<String>)>,
}

struct Info {
    pkgs: HashMap<String, PkgInfo>,
    /// Type names declared by a package AND somewhere else.
    colliding: HashSet<String>,
    /// Enum member names declared by a package AND somewhere else.
    colliding_members: HashSet<String>,
    /// Value names (subroutines, parameters, variables, `let`s) declared by
    /// more than one package, or by a package and `$unit`.
    colliding_values: HashSet<String>,
    /// Package VARIABLE names that two or more packages declare. Every
    /// package's variables share one design-wide bare namespace at run
    /// time, so each such variable is renamed to `pkg::name` and every
    /// reference resolving to it rewritten to that spelling, exactly like a
    /// colliding type name.
    mangled_vars: HashSet<String>,
    /// Type names (typedefs, nested classes) a class declares that are also
    /// declared in another class or any other scope (§8.3, §6.18).
    class_colliding: HashSet<String>,
    /// §23.9: module-local classes whose names another lexical scope owns.
    hiding: HashSet<String>,
    repeated_module_classes: HashSet<String>,
    /// Every class by the name it carries after this pass: its own type
    /// names and the base class name as written.
    classes: HashMap<String, ClassInfo>,
    /// Bare class name -> the names it carries after this pass.
    class_by_bare: HashMap<String, Vec<String>>,
}

/// A class's own type names (typedefs and nested classes) and its base.
#[derive(Default)]
struct ClassInfo {
    types: HashSet<String>,
    base: Option<String>,
    /// Every typedef the class declares (class-naming ones included).
    typedefs: HashSet<String>,
    /// The header parameters in declaration order.
    params: Vec<HeaderParam>,
    /// The base specialization's arguments (`extends B #(args)`).
    ext_args: Vec<ParamValue>,
    /// §8.25/§6.18: typedefs whose type depends on a TYPE parameter of the
    /// class (`typedef T payload_t;`), by name, with earlier such typedefs
    /// expanded, and the unpacked dimensions it declares (`typedef T
    /// ua_t[3];`). Every reference is replaced by this type (see
    /// `inline_type`, `splice_unpacked`).
    inline: HashMap<String, (DataType, Vec<UnpackedDimension>)>,
}

/// One `#(...)` header parameter of a class.
struct HeaderParam {
    name: String,
    /// A type parameter, with its default type; else a value parameter.
    kind: HeaderParamKind,
}

enum HeaderParamKind {
    Type(Option<DataType>),
    Value(Option<Expression>),
}

/// A class typedef this pass may rename: a real declaration of a data
/// type. A typedef naming a class (`typedef C#(T) this_type;`, every UVM
/// `type_id`) only aliases a handle type, which the simulator already
/// resolves in its class context.
fn class_typedef_renamable(td: &TypedefDeclaration, class_names: &HashSet<String>) -> bool {
    if td.forward {
        return false;
    }
    match &td.data_type {
        DataType::TypeReference {
            name, type_args, ..
        } => {
            type_args.is_empty()
                && name.scopes.iter().all(|s| s.type_args.is_empty())
                && !class_names.contains(&name.name.name)
        }
        _ => true,
    }
}

/// Every class name of the design, nested ones included.
fn class_names_of(c: &ClassDeclaration, out: &mut HashSet<String>) {
    out.insert(c.name.name.clone());
    for it in &c.items {
        if let ClassItem::Class(nc) = it {
            class_names_of(nc, out);
        }
    }
}

/// Count the type names every class (nested ones included) declares.
fn count_class_types(
    c: &ClassDeclaration,
    class_names: &HashSet<String>,
    count: &mut HashMap<String, u32>,
) {
    for it in &c.items {
        match it {
            ClassItem::Typedef(td) if class_typedef_renamable(td, class_names) => {
                *count.entry(td.name.name.clone()).or_default() += 1;
            }
            ClassItem::Class(nc) => {
                *count.entry(nc.name.name.clone()).or_default() += 1;
                count_class_types(nc, class_names, count);
            }
            _ => {}
        }
    }
}

/// Record class `c`, which carries the name `named` after this pass, and its
/// nested classes (a colliding nested class becomes `Outer::Inner`).
fn record_class(
    c: &ClassDeclaration,
    named: String,
    cc: &HashSet<String>,
    class_names: &HashSet<String>,
    classes: &mut HashMap<String, ClassInfo>,
    by_bare: &mut HashMap<String, Vec<String>>,
) {
    let mut ci = ClassInfo {
        base: c.extends.as_ref().map(|e| e.name.name.clone()),
        ext_args: c
            .extends
            .as_ref()
            .map(|e| e.args.clone())
            .unwrap_or_default(),
        ..ClassInfo::default()
    };
    class_param_typedefs(c, class_names, &mut ci);
    for it in &c.items {
        match it {
            ClassItem::Typedef(td) if class_typedef_renamable(td, class_names) => {
                ci.types.insert(td.name.name.clone());
            }
            ClassItem::Class(nc) => {
                ci.types.insert(nc.name.name.clone());
                let m = if cc.contains(&nc.name.name) {
                    mangle(&named, &nc.name.name)
                } else {
                    nc.name.name.clone()
                };
                record_class(nc, m, cc, class_names, classes, by_bare);
            }
            _ => {}
        }
    }
    by_bare
        .entry(c.name.name.clone())
        .or_default()
        .push(named.clone());
    classes.insert(named, ci);
}

/// §8.25/§6.18: record class `c`'s header parameters and the typedefs whose
/// type depends on one of its TYPE parameters. The design keeps one flat
/// typedef table, where such a typedef is sized once, by the parameter
/// defaults; every reference is instead replaced by the typedef's type (see
/// `Rw::inline_type`), which the simulator already resolves against each
/// specialization's own bindings, like a member declared `T d;`.
fn class_param_typedefs(c: &ClassDeclaration, class_names: &HashSet<String>, ci: &mut ClassInfo) {
    for pd in &c.params {
        match &pd.kind {
            ParameterKind::Type { assignments } => {
                for a in assignments {
                    ci.params.push(HeaderParam {
                        name: a.name.name.clone(),
                        kind: HeaderParamKind::Type(a.init.clone()),
                    });
                }
            }
            ParameterKind::Data { assignments, .. } => {
                for a in assignments {
                    ci.params.push(HeaderParam {
                        name: a.name.name.clone(),
                        kind: HeaderParamKind::Value(a.init.clone()),
                    });
                }
            }
        }
    }
    let type_params: HashSet<String> = ci
        .params
        .iter()
        .filter(|p| matches!(p.kind, HeaderParamKind::Type(_)))
        .map(|p| p.name.clone())
        .collect();
    for it in &c.items {
        let ClassItem::Typedef(td) = it else { continue };
        ci.typedefs.insert(td.name.name.clone());
        // A typedef naming a class (`typedef C#(T) this_type;`) stays: the
        // simulator resolves class handles in their class context.
        if type_params.is_empty()
            || !class_typedef_renamable(td, class_names)
            || type_has_args(&td.data_type)
        {
            continue;
        }
        // Earlier packed ones expand in place; an unpacked one cannot be
        // used as the element type of another typedef here.
        let tmap: HashMap<String, Option<DataType>> = ci
            .inline
            .iter()
            .map(|(n, (t, u))| (n.clone(), u.is_empty().then(|| t.clone())))
            .collect();
        let Some(dt) = subst_type(&td.data_type, &tmap, &HashMap::default()) else {
            continue;
        };
        if type_mentions(&dt, &type_params) {
            ci.inline
                .insert(td.name.name.clone(), (dt, td.dimensions.clone()));
        }
    }
}

/// Whether a type reference in `dt` carries a parameter list or a scope
/// (`C#(T)`, `pkg::t`): such a typedef is left to the simulator.
fn type_has_args(dt: &DataType) -> bool {
    match dt {
        DataType::TypeReference {
            name, type_args, ..
        } => !type_args.is_empty() || !name.scopes.is_empty(),
        DataType::Struct(su) => su.members.iter().any(|m| type_has_args(&m.data_type)),
        DataType::Enum(et) => et.base_type.as_deref().is_some_and(type_has_args),
        DataType::Interface { .. } => true,
        _ => false,
    }
}

/// Whether `dt` names one of `names` as a (bare) type.
fn type_mentions(dt: &DataType, names: &HashSet<String>) -> bool {
    match dt {
        DataType::TypeReference { name, .. } => {
            name.scopes.is_empty() && names.contains(&name.name.name)
        }
        DataType::Struct(su) => su
            .members
            .iter()
            .any(|m| type_mentions(&m.data_type, names)),
        DataType::Enum(et) => et
            .base_type
            .as_deref()
            .is_some_and(|b| type_mentions(b, names)),
        _ => false,
    }
}

/// `dt` with every bare type name in `tmap` replaced by its type (packed
/// dimensions of the reference outermost), and every bare value name in
/// `vmap` replaced in its dimension expressions. `None` when a name maps to
/// nothing usable or the dimensions cannot be merged.
fn subst_type(
    dt: &DataType,
    tmap: &HashMap<String, Option<DataType>>,
    vmap: &HashMap<String, Expression>,
) -> Option<DataType> {
    let mut out = dt.clone();
    match &mut out {
        DataType::TypeReference {
            name, dimensions, ..
        } => {
            subst_dims(dimensions, vmap);
            if name.scopes.is_empty() {
                if let Some(rep) = tmap.get(&name.name.name) {
                    return merge_packed(rep.clone()?, std::mem::take(dimensions));
                }
            }
        }
        DataType::IntegerVector { dimensions, .. } | DataType::Implicit { dimensions, .. } => {
            subst_dims(dimensions, vmap)
        }
        DataType::Struct(su) => {
            for m in &mut su.members {
                m.data_type = subst_type(&m.data_type, tmap, vmap)?;
            }
            subst_dims(&mut su.dimensions, vmap);
        }
        DataType::Enum(et) => {
            if let Some(b) = &mut et.base_type {
                **b = subst_type(b, tmap, vmap)?;
            }
            subst_dims(&mut et.dimensions, vmap);
        }
        _ => {}
    }
    Some(out)
}

/// `rep` used with the packed dimensions `outer` (`payload_t [3:0] x`):
/// the outer dimensions come first.
fn merge_packed(mut rep: DataType, mut outer: Vec<PackedDimension>) -> Option<DataType> {
    if outer.is_empty() {
        return Some(rep);
    }
    let inner = match &mut rep {
        DataType::IntegerVector { dimensions, .. }
        | DataType::Implicit { dimensions, .. }
        | DataType::TypeReference { dimensions, .. } => dimensions,
        DataType::Struct(su) if su.packed => &mut su.dimensions,
        DataType::Enum(et) => &mut et.dimensions,
        // §7.4.1: a packed array of an integer atom (`byte [2:0]` through a
        // typedef) is a packed array of the atom's bit vector.
        DataType::IntegerAtom { kind, span, .. } => {
            let (vk, w) = match kind {
                IntegerAtomType::Byte => (IntegerVectorType::Bit, 8),
                IntegerAtomType::ShortInt => (IntegerVectorType::Bit, 16),
                IntegerAtomType::Int => (IntegerVectorType::Bit, 32),
                IntegerAtomType::LongInt => (IntegerVectorType::Bit, 64),
                IntegerAtomType::Integer => (IntegerVectorType::Logic, 32),
                IntegerAtomType::Time => (IntegerVectorType::Logic, 64),
            };
            let span = *span;
            let num = |v: u32| {
                Box::new(Expression::new(
                    ExprKind::Number(crate::ast::expr::NumberLiteral::Integer {
                        size: None,
                        signed: false,
                        base: crate::ast::expr::NumberBase::Decimal,
                        value: v.to_string(),
                        cached_val: crate::ast::cache::LiteralCache::new(None),
                    }),
                    span,
                ))
            };
            outer.push(PackedDimension::Range {
                left: num(w - 1),
                right: num(0),
                span,
            });
            return Some(DataType::IntegerVector {
                kind: vk,
                signing: None,
                dimensions: outer,
                span,
            });
        }
        _ => return None,
    };
    outer.append(inner);
    *inner = outer;
    Some(rep)
}

fn subst_dims(dims: &mut [PackedDimension], vmap: &HashMap<String, Expression>) {
    if vmap.is_empty() {
        return;
    }
    for d in dims {
        if let PackedDimension::Range { left, right, .. } = d {
            subst_expr(left, vmap);
            subst_expr(right, vmap);
        }
    }
}

fn subst_udims(dims: &mut [UnpackedDimension], vmap: &HashMap<String, Expression>) {
    if vmap.is_empty() {
        return;
    }
    for d in dims {
        match d {
            UnpackedDimension::Range { left, right, .. } => {
                subst_expr(left, vmap);
                subst_expr(right, vmap);
            }
            UnpackedDimension::Expression { expr, .. } => subst_expr(expr, vmap),
            _ => {}
        }
    }
}

/// Replace bare value names in a constant expression.
fn subst_expr(e: &mut Expression, vmap: &HashMap<String, Expression>) {
    match &mut e.kind {
        ExprKind::Ident(_) => {
            if let Some(r) = plain_ident(e).and_then(|n| vmap.get(n)) {
                let span = e.span;
                *e = Expression::new(ExprKind::Paren(Box::new(r.clone())), span);
            }
        }
        ExprKind::Unary { operand, .. } => subst_expr(operand, vmap),
        ExprKind::Binary { left, right, .. } => {
            subst_expr(left, vmap);
            subst_expr(right, vmap);
        }
        ExprKind::Conditional {
            condition,
            then_expr,
            else_expr,
        } => {
            subst_expr(condition, vmap);
            subst_expr(then_expr, vmap);
            subst_expr(else_expr, vmap);
        }
        ExprKind::Paren(x) => subst_expr(x, vmap),
        ExprKind::SystemCall { args, .. } | ExprKind::Call { args, .. } => {
            args.iter_mut().for_each(|a| subst_expr(a, vmap))
        }
        _ => {}
    }
}

/// A type argument as a data type: `byte`, `T`, `logic [7:0]`.
fn arg_type(e: &Expression) -> Option<DataType> {
    match &e.kind {
        ExprKind::TypeLiteral(dt) => Some((**dt).clone()),
        ExprKind::Paren(x) => arg_type(x),
        _ => plain_ident(e).map(|n| {
            keyword_type(n, e.span).unwrap_or_else(|| DataType::TypeReference {
                name: TypeName {
                    scopes: Vec::new(),
                    name: crate::ast::Identifier {
                        name: n.to_string(),
                        span: e.span,
                    },
                    span: e.span,
                    bound: Default::default(),
                },
                dimensions: Vec::new(),
                type_args: Vec::new(),
                span: e.span,
            })
        }),
    }
}

/// The built-in type a type-argument keyword names (`#(byte)` reaches the
/// AST as the identifier `byte`).
fn keyword_type(n: &str, span: crate::ast::Span) -> Option<DataType> {
    let atom = |kind| DataType::IntegerAtom {
        kind,
        signing: None,
        span,
    };
    let vector = |kind| DataType::IntegerVector {
        kind,
        signing: None,
        dimensions: Vec::new(),
        span,
    };
    Some(match n {
        "byte" => atom(IntegerAtomType::Byte),
        "shortint" => atom(IntegerAtomType::ShortInt),
        "int" => atom(IntegerAtomType::Int),
        "longint" => atom(IntegerAtomType::LongInt),
        "integer" => atom(IntegerAtomType::Integer),
        "time" => atom(IntegerAtomType::Time),
        "bit" => vector(IntegerVectorType::Bit),
        "logic" => vector(IntegerVectorType::Logic),
        "reg" => vector(IntegerVectorType::Reg),
        "real" => DataType::Real {
            kind: RealType::Real,
            span,
        },
        "shortreal" => DataType::Real {
            kind: RealType::ShortReal,
            span,
        },
        "realtime" => DataType::Real {
            kind: RealType::RealTime,
            span,
        },
        "string" => DataType::Simple {
            kind: SimpleType::String,
            span,
        },
        _ => return None,
    })
}

/// Bind the header parameters `params` of a class to a specialization's
/// arguments (positional or named, §8.25), defaults filling the rest.
fn bind_params(
    params: &[HeaderParam],
    args: &[ParamValue],
) -> (
    HashMap<String, Option<DataType>>,
    HashMap<String, Expression>,
) {
    let mut given: HashMap<String, &ParamValue> = HashMap::default();
    let mut named: Vec<(String, ParamValue)> = Vec::new();
    for (i, a) in args.iter().enumerate() {
        if let ParamValue::Expr(Expression {
            kind: ExprKind::NamedArg { name, expr },
            ..
        }) = a
        {
            if let Some(x) = expr {
                named.push((name.name.clone(), ParamValue::Expr((**x).clone())));
            }
        } else if let Some(p) = params.get(i) {
            given.insert(p.name.clone(), a);
        }
    }
    for (n, v) in &named {
        given.insert(n.clone(), v);
    }
    let mut tmap: HashMap<String, Option<DataType>> = HashMap::default();
    let mut vmap: HashMap<String, Expression> = HashMap::default();
    for p in params {
        match (&p.kind, given.get(&p.name)) {
            (HeaderParamKind::Type(_), Some(ParamValue::Type(t))) => {
                tmap.insert(p.name.clone(), Some(t.clone()));
            }
            (HeaderParamKind::Type(_), Some(ParamValue::Expr(x))) => {
                tmap.insert(p.name.clone(), arg_type(x));
            }
            (HeaderParamKind::Type(d), None) => {
                // A default may name an earlier parameter (`type RSP = REQ`).
                let d = d.as_ref().and_then(|d| subst_type(d, &tmap, &vmap));
                tmap.insert(p.name.clone(), d);
            }
            (HeaderParamKind::Value(_), Some(ParamValue::Expr(x))) => {
                vmap.insert(p.name.clone(), x.clone());
            }
            (HeaderParamKind::Value(d), _) => {
                if let Some(d) = d {
                    vmap.insert(p.name.clone(), d.clone());
                }
            }
        }
    }
    (tmap, vmap)
}

/// Every class declaration of the design with the package (if any) it is
/// declared in.
#[derive(Clone, Copy)]
enum ClassScope<'a> {
    Unit,
    Package(&'a str),
    Module(&'a str),
}

fn design_classes(descs: &[Description]) -> Vec<(ClassScope<'_>, &ClassDeclaration)> {
    fn module_classes<'a>(
        items: &'a [ModuleItem],
        owner: &'a str,
        out: &mut Vec<(ClassScope<'a>, &'a ClassDeclaration)>,
    ) {
        for it in items {
            match it {
                ModuleItem::ClassDeclaration(c) => out.push((ClassScope::Module(owner), c)),
                ModuleItem::GenerateRegion(g) => module_classes(&g.items, owner, out),
                ModuleItem::GenerateIf(g) => {
                    for (_, b) in &g.branches {
                        module_classes(b, owner, out);
                    }
                }
                ModuleItem::GenerateFor(g) => module_classes(&g.items, owner, out),
                ModuleItem::GenerateCase(g) => {
                    for a in &g.arms {
                        module_classes(&a.items, owner, out);
                    }
                }
                _ => {}
            }
        }
    }
    let mut out = Vec::new();
    for d in descs {
        match d {
            Description::Package(p) => {
                for it in &p.items {
                    if let PackageItem::Class(c) = it {
                        out.push((ClassScope::Package(p.name.name.as_str()), c));
                    }
                }
            }
            Description::Class(c) | Description::PackageItem(PackageItem::Class(c)) => {
                out.push((ClassScope::Unit, c))
            }
            Description::Module(m) => module_classes(&m.items, &m.name.name, &mut out),
            Description::Interface(m) => module_classes(&m.items, &m.name.name, &mut out),
            Description::Program(m) => module_classes(&m.items, &m.name.name, &mut out),
            _ => {}
        }
    }
    out
}

impl Info {
    fn module_class_name(&self, owner: &str, c: &ClassDeclaration) -> String {
        let named = mangle(owner, &c.name.name);
        if self.repeated_module_classes.contains(&named) {
            mangle(
                &format!("{owner}::__scope{}", c.name.span.start),
                &c.name.name,
            )
        } else {
            named
        }
    }
    /// The package whose declaration `Q::name` denotes: Q itself when it
    /// declares `name`, else the package it re-exports `name` from (§26.6).
    fn owner(&self, q: &str, name: &str, depth: u32) -> Option<String> {
        self.owner_in(q, name, depth, |pi| &pi.types)
    }

    /// `owner` for an enum member name.
    fn member_owner(&self, q: &str, name: &str, depth: u32) -> Option<String> {
        self.owner_in(q, name, depth, |pi| &pi.members)
    }

    /// `owner` for a value name (subroutine, parameter, variable, `let`).
    fn value_owner(&self, q: &str, name: &str, depth: u32) -> Option<String> {
        self.owner_in(q, name, depth, |pi| &pi.values)
    }

    fn owner_in(
        &self,
        q: &str,
        name: &str,
        depth: u32,
        decls: fn(&PkgInfo) -> &HashSet<String>,
    ) -> Option<String> {
        if depth > 8 {
            return None;
        }
        let pi = self.pkgs.get(q)?;
        if decls(pi).contains(name) {
            return Some(q.to_string());
        }
        for (ep, en) in &pi.exports {
            if en.as_deref().is_some_and(|x| x != name) {
                continue;
            }
            for (ip, iname) in &pi.explicit {
                if iname == name && (ep == "*" || ep == ip) {
                    if let Some(o) = self.owner_in(ip, name, depth + 1, decls) {
                        return Some(o);
                    }
                }
            }
            for ip in &pi.wild {
                if ep == "*" || ep == ip {
                    if let Some(o) = self.owner_in(ip, name, depth + 1, decls) {
                        return Some(o);
                    }
                }
            }
            // `export Q::name;` also imports it (§26.6).
            if ep != "*" && en.is_some() {
                if let Some(o) = self.owner_in(ep, name, depth + 1, decls) {
                    return Some(o);
                }
            }
        }
        None
    }
}

fn mangle(pkg: &str, name: &str) -> String {
    format!("{}::{}", pkg, name)
}

/// One lexical scope's names, innermost last on the walker's stack.
#[derive(Default)]
struct Frame {
    /// Set on a package's own frame: its declarations resolve to `pkg::name`.
    pkg: Option<String>,
    /// The enclosing module and the class bindings this lexical body owns.
    module: Option<String>,
    module_classes: HashMap<String, String>,
    /// Type names declared here (they shadow imports and outer scopes).
    types: HashSet<String>,
    /// Value names declared here — an identifier naming one of these is not
    /// a type reference.
    values: HashSet<String>,
    /// `import Q::name;` as name -> Q.
    explicit: HashMap<String, String>,
    /// `import Q::*;`
    wild: Vec<String>,
    /// §26.3: a name a reference found through exactly one wildcard import
    /// here, with that import's package. The name is then locally visible,
    /// so a later reference takes it like an explicit import, whatever
    /// wildcard import of another package follows (#620).
    bound: std::cell::RefCell<HashMap<String, String>>,
    /// A class scope with a base class: names it inherits are not tracked
    /// here, so value names are not resolved past it.
    inherits: bool,
    /// Set on a class's own frame: the name the class carries after this
    /// pass, and its base classes' (nearest first).
    cls: Option<String>,
    bases: Vec<String>,
}

impl Frame {
    fn add_imports(&mut self, imp: &ImportDeclaration) {
        for ii in &imp.items {
            match &ii.item {
                Some(n) => {
                    self.explicit
                        .insert(n.name.clone(), ii.package.name.clone());
                }
                None => self.wild.push(ii.package.name.clone()),
            }
        }
    }
}

enum Res {
    Keep,
    To(String),
    Ambiguous(Vec<String>),
}

struct Rw<'a> {
    info: &'a Info,
    frames: Vec<Frame>,
    errors: Vec<String>,
    /// Inside a constant context (a data type, a parameter, a generate
    /// condition): enum member references stay bare there, since they are
    /// evaluated while the elaborator is still registering the packages.
    in_const: u32,
    /// Nesting of `inline_type` replacements being walked (a guard).
    inline_depth: u32,
}

/// A name looked up in a class and its bases.
enum ClassLookup {
    /// Declared there: its inlined type and unpacked dimensions, if it is
    /// one `inline_lookup` replaces.
    Found(Option<(DataType, Vec<UnpackedDimension>)>),
    Missing,
}

/// Rename colliding package type names to `pkg::name` and rewrite their
/// references (see the module docs). Errors when a type reference is made
/// ambiguous by two wildcard imports.
/// §6.21: a subroutine of a module, interface, program or package declared
/// `automatic` is automatic unless it says otherwise. Record that on the
/// subroutine itself, so a later stage telling a static subroutine (whose
/// variables keep their values between calls) from an automatic one needs
/// only the subroutine's own lifetime.
pub fn stamp_automatic_subroutines(descs: &mut [Description]) {
    use crate::ast::types::Lifetime;
    fn stamp(l: &mut Option<Lifetime>) {
        if l.is_none() {
            *l = Some(Lifetime::Automatic);
        }
    }
    for d in descs.iter_mut() {
        let items = match d {
            Description::Module(m) if m.lifetime == Some(Lifetime::Automatic) => &mut m.items,
            Description::Interface(m) if m.lifetime == Some(Lifetime::Automatic) => &mut m.items,
            Description::Program(m) if m.lifetime == Some(Lifetime::Automatic) => &mut m.items,
            Description::Package(p) if p.lifetime == Some(Lifetime::Automatic) => {
                for it in p.items.iter_mut() {
                    match it {
                        PackageItem::Function(fd) => stamp(&mut fd.lifetime),
                        PackageItem::Task(td) => stamp(&mut td.lifetime),
                        _ => {}
                    }
                }
                continue;
            }
            _ => continue,
        };
        for it in items.iter_mut() {
            match it {
                ModuleItem::FunctionDeclaration(fd) => stamp(&mut fd.lifetime),
                ModuleItem::TaskDeclaration(td) => stamp(&mut td.lifetime),
                _ => {}
            }
        }
    }
}

pub fn qualify_colliding_package_types(descs: &mut [Description]) -> Result<(), String> {
    QUALIFIED_MEMBERS.with(|m| m.borrow_mut().clear());

    let Some(info) = collect(descs) else {
        return Ok(());
    };

    QUALIFIED_MEMBERS.with(|m| {
        m.borrow_mut()
            .extend(info.colliding_members.iter().cloned())
    });
    let mut rw = Rw {
        info: &info,
        frames: Vec::new(),
        errors: Vec::new(),
        in_const: 0,
        inline_depth: 0,
    };
    let unit = unit_frame(descs);
    rw.frames.push(unit);
    for d in descs.iter_mut() {
        rw.description(d);
    }
    match rw.errors.into_iter().next() {
        Some(e) => Err(e),
        None => Ok(()),
    }
}

/// Gather every package's type names and imports; `None` when no type name
/// is declared by a package and anywhere else (nothing to do).
fn collect(descs: &[Description]) -> Option<Info> {
    let mut pkgs: HashMap<String, PkgInfo> = HashMap::default();
    let mut other: HashSet<String> = HashSet::default();
    let mut other_members: HashSet<String> = HashSet::default();
    let mut other_values: HashSet<String> = HashSet::default();
    for d in descs {
        match d {
            Description::Package(p) => {
                let pi = pkgs.entry(p.name.name.clone()).or_default();
                for it in &p.items {
                    package_item_values(it, &mut pi.values);
                    if let PackageItem::Data(dd) = it {
                        pi.vars
                            .extend(dd.declarators.iter().map(|v| v.name.name.clone()));
                    }
                    match it {
                        PackageItem::Typedef(td) => {
                            pi.types.insert(td.name.name.clone());
                            enum_members(&td.data_type, &mut pi.members);
                        }
                        PackageItem::Class(c) => {
                            pi.types.insert(c.name.name.clone());
                        }
                        // §19.3: a covergroup declaration is a type.
                        PackageItem::Covergroup(cg) => {
                            pi.types.insert(cg.name.name.clone());
                        }
                        PackageItem::Import(imp) => {
                            for ii in &imp.items {
                                match &ii.item {
                                    Some(n) => {
                                        pi.explicit.push((ii.package.name.clone(), n.name.clone()))
                                    }
                                    None => pi.wild.push(ii.package.name.clone()),
                                }
                            }
                        }
                        PackageItem::Export(imp) => {
                            for ii in &imp.items {
                                pi.exports.push((
                                    ii.package.name.clone(),
                                    ii.item.as_ref().map(|n| n.name.clone()),
                                ));
                            }
                        }
                        _ => {}
                    }
                }
            }
            Description::TypedefDecl(td) | Description::PackageItem(PackageItem::Typedef(td)) => {
                other.insert(td.name.name.clone());
                enum_members(&td.data_type, &mut other_members);
            }
            Description::Class(c) | Description::PackageItem(PackageItem::Class(c)) => {
                other.insert(c.name.name.clone());
            }
            Description::PackageItem(PackageItem::Covergroup(cg)) => {
                other.insert(cg.name.name.clone());
            }
            Description::PackageItem(pi) => package_item_values(pi, &mut other_values),
            Description::DPIImport(di) => {
                other_values.insert(match &di.proto {
                    DPIProto::Function(f) => f.name.name.name.clone(),
                    DPIProto::Task(t) => t.name.name.name.clone(),
                });
            }
            Description::Module(m) => {
                module_level_types(&m.items, &mut other, &mut other_members);
                module_dpi_names(&m.items, &mut other_values);
            }
            Description::Interface(m) => {
                module_level_types(&m.items, &mut other, &mut other_members);
                module_dpi_names(&m.items, &mut other_values);
            }
            Description::Program(m) => {
                module_level_types(&m.items, &mut other, &mut other_members);
                module_dpi_names(&m.items, &mut other_values);
            }
            _ => {}
        }
    }
    let clash = |decls: fn(&PkgInfo) -> &HashSet<String>, other: &HashSet<String>| {
        let mut count: HashMap<&str, u32> = HashMap::default();
        for pi in pkgs.values() {
            for n in decls(pi) {
                *count.entry(n.as_str()).or_default() += 1;
            }
        }
        count
            .into_iter()
            .filter(|(n, c)| *c > 1 || other.contains(*n))
            .map(|(n, _)| n.to_string())
            .collect::<HashSet<String>>()
    };
    let colliding = clash(|pi| &pi.types, &other);
    let colliding_members = clash(|pi| &pi.members, &other_members);
    let colliding_values = clash(|pi| &pi.values, &other_values);
    // A name some `import Q::n;` / `export Q::n;` spells out keeps its
    // declared name: the import and export checks look it up by that name.
    let mut explicit_named: HashSet<String> = HashSet::default();
    for pi in pkgs.values() {
        explicit_named.extend(pi.explicit.iter().map(|(_, n)| n.clone()));
        explicit_named.extend(pi.exports.iter().filter_map(|(_, n)| n.clone()));
    }
    for d in descs {
        let items = match d {
            Description::Module(m) => &m.items,
            Description::Interface(m) => &m.items,
            Description::Program(m) => &m.items,
            Description::PackageItem(PackageItem::Import(imp)) => {
                explicit_named.extend(
                    imp.items
                        .iter()
                        .filter_map(|ii| ii.item.as_ref())
                        .map(|n| n.name.clone()),
                );
                continue;
            }
            _ => continue,
        };
        for it in items {
            if let ModuleItem::ImportDeclaration(imp) = it {
                explicit_named.extend(
                    imp.items
                        .iter()
                        .filter_map(|ii| ii.item.as_ref())
                        .map(|n| n.name.clone()),
                );
            }
        }
    }
    let mangled_vars: HashSet<String> = {
        let mut count: HashMap<&str, u32> = HashMap::default();
        for pi in pkgs.values() {
            for n in &pi.vars {
                *count.entry(n.as_str()).or_default() += 1;
            }
        }
        count
            .into_iter()
            .filter(|(n, c)| *c > 1 && !other_values.contains(*n) && !explicit_named.contains(*n))
            .map(|(n, _)| n.to_string())
            .collect()
    };
    // §8.3: a class is a scope of its own; a type name a class declares
    // collides when it is declared anywhere else as well.
    let all_classes = design_classes(descs);
    let mut lexical_counts: HashMap<&str, usize> = HashMap::default();
    for (scope, c) in &all_classes {
        if !matches!(scope, ClassScope::Package(_)) {
            *lexical_counts.entry(c.name.name.as_str()).or_default() += 1;
        }
    }
    let hiding: HashSet<String> = all_classes
        .iter()
        .filter(|(s, c)| {
            matches!(s, ClassScope::Module(_))
                && lexical_counts
                    .get(c.name.name.as_str())
                    .is_some_and(|count| *count > 1)
        })
        .map(|(_, c)| c.name.name.clone())
        .collect();
    let mut module_counts: HashMap<String, usize> = HashMap::default();
    for (scope, c) in &all_classes {
        if let ClassScope::Module(owner) = scope
            && hiding.contains(&c.name.name)
        {
            *module_counts
                .entry(mangle(owner, &c.name.name))
                .or_default() += 1;
        }
    }
    let repeated_module_classes: HashSet<String> = module_counts
        .into_iter()
        .filter_map(|(n, count)| (count > 1).then_some(n))
        .collect();
    let mut class_names: HashSet<String> = HashSet::default();
    for (_, c) in &all_classes {
        class_names_of(c, &mut class_names);
    }
    let mut class_count: HashMap<String, u32> = HashMap::default();
    for (_, c) in &all_classes {
        count_class_types(c, &class_names, &mut class_count);
    }
    let class_colliding: HashSet<String> = class_count
        .iter()
        .filter(|(n, c)| {
            **c > 1 || other.contains(*n) || pkgs.values().any(|pi| pi.types.contains(*n))
        })
        .map(|(n, _)| n.clone())
        .collect();
    let mut classes: HashMap<String, ClassInfo> = HashMap::default();
    let mut class_by_bare: HashMap<String, Vec<String>> = HashMap::default();
    for (scope, c) in &all_classes {
        let named = match scope {
            ClassScope::Package(p) if colliding.contains(&c.name.name) => mangle(p, &c.name.name),
            ClassScope::Module(m) if hiding.contains(&c.name.name) => {
                let owner = if repeated_module_classes.contains(&mangle(m, &c.name.name)) {
                    format!("{m}::__scope{}", c.name.span.start)
                } else {
                    m.to_string()
                };
                mangle(&owner, &c.name.name)
            }
            _ => c.name.name.clone(),
        };
        record_class(
            c,
            named,
            &class_colliding,
            &class_names,
            &mut classes,
            &mut class_by_bare,
        );
    }
    if colliding.is_empty()
        && colliding_members.is_empty()
        && colliding_values.is_empty()
        && class_colliding.is_empty()
        && hiding.is_empty()
        && classes.values().all(|ci| ci.inline.is_empty())
    {
        return None;
    }
    Some(Info {
        pkgs,
        colliding,
        colliding_members,
        colliding_values,
        mangled_vars,
        class_colliding,
        hiding,
        repeated_module_classes,
        classes,
        class_by_bare,
    })
}

/// Typedef and class names a module/interface/program declares at its own
/// level (generate blocks included).
fn module_level_types(
    items: &[ModuleItem],
    out: &mut HashSet<String>,
    members: &mut HashSet<String>,
) {
    for it in items {
        match it {
            ModuleItem::TypedefDeclaration(td) => {
                out.insert(td.name.name.clone());
                enum_members(&td.data_type, members);
            }
            ModuleItem::DataDeclaration(d) => enum_members(&d.data_type, members),
            ModuleItem::ClassDeclaration(c) => {
                out.insert(c.name.name.clone());
            }
            ModuleItem::GenerateRegion(g) => module_level_types(&g.items, out, members),
            ModuleItem::GenerateIf(g) => {
                for (_, b) in &g.branches {
                    module_level_types(b, out, members);
                }
            }
            ModuleItem::GenerateFor(g) => module_level_types(&g.items, out, members),
            ModuleItem::GenerateCase(g) => {
                for a in &g.arms {
                    module_level_types(&a.items, out, members);
                }
            }
            _ => {}
        }
    }
}

/// Module DPI declarations also shadow imported package subroutines.
fn module_dpi_names(items: &[ModuleItem], out: &mut HashSet<String>) {
    for item in items {
        match item {
            ModuleItem::DPIImport(di) => {
                out.insert(match &di.proto {
                    DPIProto::Function(f) => f.name.name.name.clone(),
                    DPIProto::Task(t) => t.name.name.name.clone(),
                });
            }
            ModuleItem::GenerateRegion(g) => module_dpi_names(&g.items, out),
            ModuleItem::GenerateIf(g) => {
                for (_, items) in &g.branches { module_dpi_names(items, out); }
            }
            ModuleItem::GenerateFor(g) => module_dpi_names(&g.items, out),
            ModuleItem::GenerateCase(g) => {
                for arm in &g.arms { module_dpi_names(&arm.items, out); }
            }
            _ => {}
        }
    }
}

/// The member names an enum type declares (`enum {A, B}`); empty for any
/// other type. A ranged member (`A[2]`) declares generated names, left out.
fn enum_members(dt: &DataType, out: &mut HashSet<String>) {
    if let DataType::Enum(et) = dt {
        out.extend(
            et.members
                .iter()
                .filter(|m| m.range.is_none())
                .map(|m| m.name.name.clone()),
        );
    }
}

/// The compilation-unit (`$unit`) scope: its declarations and imports.
fn unit_frame(descs: &[Description]) -> Frame {
    let mut f = Frame::default();
    for d in descs {
        match d {
            Description::TypedefDecl(td) | Description::PackageItem(PackageItem::Typedef(td)) => {
                f.types.insert(td.name.name.clone());
                enum_members(&td.data_type, &mut f.values);
            }
            Description::Class(c) | Description::PackageItem(PackageItem::Class(c)) => {
                f.types.insert(c.name.name.clone());
            }
            // §26.3: a `$unit` import counts from where it appears; the walk
            // adds it then (`Rw::description`).
            Description::ImportDecl(_) | Description::PackageItem(PackageItem::Import(_)) => {}
            Description::PackageItem(pi) => package_item_values(pi, &mut f.values),
            Description::DPIImport(di) => {
                f.values.insert(match &di.proto {
                    DPIProto::Function(fd) => fd.name.name.name.clone(),
                    DPIProto::Task(td) => td.name.name.name.clone(),
                });
            }
            _ => {}
        }
    }
    f
}

fn param_names(
    pd: &ParameterDeclaration,
    types: &mut HashSet<String>,
    values: &mut HashSet<String>,
) {
    match &pd.kind {
        ParameterKind::Data { assignments, .. } => {
            values.extend(assignments.iter().map(|a| a.name.name.clone()))
        }
        ParameterKind::Type { assignments } => {
            types.extend(assignments.iter().map(|a| a.name.name.clone()))
        }
    }
}

fn package_item_values(pi: &PackageItem, out: &mut HashSet<String>) {
    let mut sink = HashSet::default();
    match pi {
        PackageItem::Parameter(pd) => param_names(pd, &mut sink, out),
        PackageItem::Data(dd) => out.extend(dd.declarators.iter().map(|v| v.name.name.clone())),
        // An out-of-block class method (`function C::f`) is not a package
        // value.
        PackageItem::Function(f) if f.name.scopes.is_empty() => {
            out.insert(f.name.name.name.clone());
        }
        PackageItem::Task(t) if t.name.scopes.is_empty() => {
            out.insert(t.name.name.name.clone());
        }
        PackageItem::DPIImport(di) => {
            out.insert(match &di.proto {
                DPIProto::Function(f) => f.name.name.name.clone(),
                DPIProto::Task(t) => t.name.name.name.clone(),
            });
        }
        PackageItem::Let(l) => {
            out.insert(l.name.name.clone());
        }
        _ => {}
    }
}

/// Declarations belonging directly to one procedural scope (§23.9).
/// Descendant blocks and loop indices get their own frames: hoisting them
/// here would suppress qualification of an outer package import.
fn stmt_locals(s: &Statement, f: &mut Frame) {
    match &s.kind {
        StatementKind::VarDecl {
            data_type,
            declarators,
            ..
        } => {
            f.values
                .extend(declarators.iter().map(|d| d.name.name.clone()));
            enum_members(data_type, &mut f.values);
        }
        StatementKind::Typedef(td) => {
            f.types.insert(td.name.name.clone());
            enum_members(&td.data_type, &mut f.values);
        }
        _ => {}
    }
}

fn ident_expr(name: String, span: crate::ast::Span) -> Expression {
    Expression::new(
        ExprKind::Ident(HierarchicalIdentifier {
            root: None,
            path: vec![HierPathSegment {
                name: crate::ast::Identifier { name, span },
                selects: Vec::new(),
            }],
            span,
            cached_signal_id: crate::ast::cache::SignalCache::new(None),
            cached_resolved_name: crate::ast::cache::NameCache::new(),
            bound: crate::ast::binding::Bound::UNSET,
        }),
        span,
    )
}

/// The names of a `A::B` chain of plain identifiers.
fn scope_chain(e: &Expression) -> Option<Vec<String>> {
    match &e.kind {
        ExprKind::Ident(h) if h.root.is_none() && h.path.iter().all(|s| s.selects.is_empty()) => {
            Some(h.path.iter().map(|s| s.name.name.clone()).collect())
        }
        ExprKind::MemberAccess { expr, member } => {
            let mut v = scope_chain(expr)?;
            v.push(member.name.clone());
            Some(v)
        }
        _ => None,
    }
}

fn plain_ident(e: &Expression) -> Option<&str> {
    match &e.kind {
        ExprKind::Ident(h)
            if h.root.is_none() && h.path.len() == 1 && h.path[0].selects.is_empty() =>
        {
            Some(h.path[0].name.name.as_str())
        }
        _ => None,
    }
}

impl Rw<'_> {
    /// Record that a reference found `n` through the one wildcard import of
    /// `f` whose package declares it (see `Frame::bound`).
    fn bind_wild(f: &Frame, n: &str, declares: impl Fn(&str) -> bool) {
        if let Some(q) = f.wild.iter().find(|q| declares(q)) {
            f.bound
                .borrow_mut()
                .entry(n.to_string())
                .or_insert_with(|| q.clone());
        }
    }

    fn resolve(&self, n: &str) -> Res {
        let pkg_col = self.info.colliding.contains(n);
        let cls_col = self.info.class_colliding.contains(n);
        if !pkg_col && !cls_col && !self.info.hiding.contains(n) {
            return Res::Keep;
        }
        for f in self.frames.iter().rev() {
            if let Some(named) = f.module_classes.get(n) {
                return Res::To(named.clone());
            }
            // §8.3/§8.13: a class's own type names, then its base classes'.
            if let Some(c) = &f.cls {
                for k in std::iter::once(c).chain(f.bases.iter()) {
                    if self
                        .info
                        .classes
                        .get(k)
                        .is_some_and(|ci| ci.types.contains(n))
                    {
                        return if cls_col {
                            Res::To(mangle(k, n))
                        } else {
                            Res::Keep
                        };
                    }
                }
            }
            if !pkg_col {
                if f.types.contains(n) {
                    return Res::Keep;
                }
                continue;
            }
            if let Some(p) = &f.pkg {
                if self.info.pkgs.get(p).is_some_and(|pi| pi.types.contains(n)) {
                    return Res::To(mangle(p, n));
                }
            }
            if f.types.contains(n) {
                return Res::Keep;
            }
            if let Some(q) = f.explicit.get(n).or(f.bound.borrow().get(n)) {
                return match self.info.owner(q, n, 0) {
                    Some(o) => Res::To(mangle(&o, n)),
                    None => Res::Keep,
                };
            }
            let cands: BTreeSet<String> = f
                .wild
                .iter()
                .filter_map(|q| self.info.owner(q, n, 0))
                .collect();
            if cands.len() == 1 {
                Self::bind_wild(f, n, |q| self.info.owner(q, n, 0).is_some());
            }
            match cands.len() {
                0 => {}
                1 => return Res::To(mangle(cands.first().unwrap(), n)),
                _ => return Res::Ambiguous(cands.into_iter().collect()),
            }
        }
        Res::Keep
    }

    /// The package whose enum member a bare `n` denotes, when that is not
    /// the one the flat namespace would pick on its own (see `resolve`).
    fn resolve_member(&self, n: &str) -> Option<String> {
        if !self.info.colliding_members.contains(n) {
            return None;
        }
        for f in self.frames.iter().rev() {
            if let Some(p) = &f.pkg {
                if self
                    .info
                    .pkgs
                    .get(p)
                    .is_some_and(|pi| pi.members.contains(n))
                {
                    return Some(p.clone());
                }
            }
            if f.values.contains(n) {
                return None;
            }
            if let Some(q) = f.explicit.get(n).or(f.bound.borrow().get(n)) {
                return self.info.member_owner(q, n, 0);
            }
            let cands: BTreeSet<String> = f
                .wild
                .iter()
                .filter_map(|q| self.info.member_owner(q, n, 0))
                .collect();
            if cands.len() == 1 {
                Self::bind_wild(f, n, |q| self.info.member_owner(q, n, 0).is_some());
            }
            match cands.len() {
                0 => {}
                1 => return cands.into_iter().next(),
                // Not visible (§26.3); left to the existing diagnostics.
                _ => return None,
            }
        }
        None
    }

    /// The package whose subroutine, parameter, variable or `let` a bare `n`
    /// denotes, by the §26.3 rules, when two packages (or a package and
    /// `$unit`) declare it. All of them share one flat table keyed by the
    /// bare name, where the last package registered wins, so the reference
    /// is spelled `pkg::n`, the qualified lookup.
    fn resolve_value(&self, n: &str) -> Option<String> {
        if !self.info.colliding_values.contains(n) {
            return None;
        }
        for f in self.frames.iter().rev() {
            if let Some(p) = &f.pkg {
                if self
                    .info
                    .pkgs
                    .get(p)
                    .is_some_and(|pi| pi.values.contains(n))
                {
                    // The package's own declaration: its subroutines and
                    // initializers already read their own package's entry
                    // (including constant evaluation while it registers),
                    // so the reference stays as written.
                    return None;
                }
            }
            if f.values.contains(n) || f.inherits {
                return None;
            }
            if let Some(q) = f.explicit.get(n).or(f.bound.borrow().get(n)) {
                return self.info.value_owner(q, n, 0);
            }
            let cands: BTreeSet<String> = f
                .wild
                .iter()
                .filter_map(|q| self.info.value_owner(q, n, 0))
                .collect();
            if cands.len() == 1 {
                Self::bind_wild(f, n, |q| self.info.value_owner(q, n, 0).is_some());
            }
            match cands.len() {
                0 => {}
                1 => return cands.into_iter().next(),
                _ => return None,
            }
        }
        None
    }

    /// The renamed storage `pkg::n` of the package variable a bare `n`
    /// names here, when `n` is one of `mangled_vars` (see `resolve_value`
    /// for the scope rules; inside its own package it is that package's).
    fn mangled_var(&self, n: &str) -> Option<String> {
        if !self.info.mangled_vars.contains(n) {
            return None;
        }
        let declares = |p: &str| self.info.pkgs.get(p).is_some_and(|pi| pi.vars.contains(n));
        for f in self.frames.iter().rev() {
            if let Some(p) = &f.pkg {
                if declares(p) {
                    return Some(mangle(p, n));
                }
                if self
                    .info
                    .pkgs
                    .get(p)
                    .is_some_and(|pi| pi.values.contains(n))
                {
                    return None;
                }
            }
            if f.values.contains(n) || f.inherits {
                return None;
            }
            if let Some(q) = f.explicit.get(n).or(f.bound.borrow().get(n)) {
                return self
                    .info
                    .value_owner(q, n, 0)
                    .filter(|o| declares(o))
                    .map(|o| mangle(&o, n));
            }
            let cands: BTreeSet<String> = f
                .wild
                .iter()
                .filter_map(|q| self.info.value_owner(q, n, 0))
                .collect();
            if cands.len() == 1 {
                Self::bind_wild(f, n, |q| self.info.value_owner(q, n, 0).is_some());
            }
            match cands.len() {
                0 => {}
                1 => {
                    return cands
                        .into_iter()
                        .next()
                        .filter(|o| declares(o))
                        .map(|o| mangle(&o, n));
                }
                _ => return None,
            }
        }
        None
    }

    /// `Q::n` naming a renamed package variable: its storage name.
    fn mangled_qualified(&self, q: &str, n: &str) -> Option<String> {
        if !self.info.mangled_vars.contains(n) || !self.is_package(q) {
            return None;
        }
        let o = self.info.value_owner(q, n, 0)?;
        self.info
            .pkgs
            .get(&o)
            .is_some_and(|pi| pi.vars.contains(n))
            .then(|| mangle(&o, n))
    }

    /// `n` (a bare identifier) rewritten to `pkg::n` when it names a
    /// colliding package value (see `resolve_value`).
    fn qualify_value(&self, e: &mut Expression) -> bool {
        let Some(n) = plain_ident(e) else {
            return false;
        };
        let Some(p) = self.resolve_value(n) else {
            return false;
        };
        let span = e.span;
        let ExprKind::Ident(h) = &e.kind else {
            return false;
        };
        let member = h.path[0].name.clone();
        *e = Expression::new(
            ExprKind::MemberAccess {
                expr: Box::new(ident_expr(p, span)),
                member,
            },
            span,
        );
        true
    }

    /// The name class `n` (as written in scope) carries after this pass.
    fn class_named(&self, n: &str) -> Option<String> {
        if let Res::To(m) = self.resolve(n) {
            if self.info.classes.contains_key(&m) {
                return Some(m);
            }
        }
        if self.info.classes.contains_key(n) {
            return Some(n.to_string());
        }
        match self.info.class_by_bare.get(n).map(|v| v.as_slice()) {
            Some([one]) => Some(one.clone()),
            _ => None,
        }
    }

    /// `C` / `Outer::Inner` naming a class: the name it carries after this
    /// pass. A segment that names a value (or a package) is not a class.
    fn class_path(&self, segs: &[String]) -> Option<String> {
        let (first, mut rest) = segs.split_first()?;
        if self.value_shadowed(first) {
            return None;
        }
        let mut cur = if self.info.pkgs.contains_key(first) {
            // `pkg::C::...`: the class package `pkg` holds.
            let (c, more) = rest.split_first()?;
            rest = more;
            let q = mangle(first, c);
            if self.info.classes.contains_key(&q) {
                q
            } else if self.info.classes.contains_key(c) {
                c.clone()
            } else {
                return None;
            }
        } else {
            self.class_named(first)?
        };
        for s in rest {
            let ci = self.info.classes.get(&cur)?;
            if !ci.types.contains(s) {
                return None;
            }
            cur = if self.info.class_colliding.contains(s) {
                mangle(&cur, s)
            } else {
                s.clone()
            };
            if !self.info.classes.contains_key(&cur) {
                return None;
            }
        }
        Some(cur)
    }

    /// `C::name` (`Outer::Inner::name`) naming a type of class C that this
    /// pass renamed: the new spelling.
    fn class_scoped_type(&self, segs: &[String], name: &str) -> Option<String> {
        if !self.info.class_colliding.contains(name) {
            return None;
        }
        let c = self.class_path(segs)?;
        self.info
            .classes
            .get(&c)
            .is_some_and(|ci| ci.types.contains(name))
            .then(|| mangle(&c, name))
    }

    /// §8.25/§6.18: the type a bare type name `n` stands for when it is a
    /// class typedef depending on a type parameter (`typedef T payload_t;`),
    /// seen from the current scope: declared by an enclosing class, or
    /// inherited from a base, its type with the base's parameters bound to
    /// the `extends` arguments (`extends G#(shortint)` -> `shortint`).
    fn inline_type(&self, n: &str) -> Option<DataType> {
        self.inline_lookup(n)
            .and_then(|(t, u)| u.is_empty().then_some(t))
    }

    /// `inline_type` for a typedef that declares unpacked dimensions
    /// (`typedef T ua_t[3];`): its element type and those dimensions.
    fn inline_unpacked(&self, n: &str) -> Option<(DataType, Vec<UnpackedDimension>)> {
        self.inline_lookup(n).filter(|(_, u)| !u.is_empty())
    }

    fn inline_lookup(&self, n: &str) -> Option<(DataType, Vec<UnpackedDimension>)> {
        if self.inline_depth > 8 {
            return None;
        }
        for f in self.frames.iter().rev() {
            if let Some(c) = &f.cls {
                // §8.23: a name a nested class does not declare is looked
                // up in its enclosing class, whose parameters the nested
                // class carries per specialization (see the elaborator's
                // `with_enclosing_params`).
                match self.class_chain_type(c, n) {
                    ClassLookup::Found(t) => return t,
                    ClassLookup::Missing => continue,
                }
            }
            if f.types.contains(n) {
                return None;
            }
        }
        None
    }

    fn class_chain_type(&self, c: &str, n: &str) -> ClassLookup {
        let mut cur = c.to_string();
        let mut maps = Vec::new();
        for _ in 0..64 {
            let Some(ci) = self.info.classes.get(&cur) else {
                return ClassLookup::Missing;
            };
            if let Some((dt, ud)) = ci.inline.get(n) {
                let mut dt = Some(dt.clone());
                let mut ud = ud.clone();
                for (t, v) in maps.iter().rev() {
                    dt = dt.and_then(|d| subst_type(&d, t, v));
                    subst_udims(&mut ud, v);
                }
                return ClassLookup::Found(dt.map(|d| (d, ud)));
            }
            if ci.typedefs.contains(n)
                || ci.types.contains(n)
                || ci.params.iter().any(|p| p.name == n)
            {
                return ClassLookup::Found(None);
            }
            let Some(b) = ci.base.as_ref().and_then(|b| self.class_named(b)) else {
                return ClassLookup::Missing;
            };
            let Some(bci) = self.info.classes.get(&b) else {
                return ClassLookup::Missing;
            };
            maps.push(bind_params(&bci.params, &ci.ext_args));
            cur = b;
        }
        ClassLookup::Missing
    }

    /// The replacement for a type reference: a bare name `inline_type`
    /// knows, or `C#(args)::name` naming such a typedef of class C.
    fn inline_ref(&self, dt: &DataType) -> Option<DataType> {
        let DataType::TypeReference {
            name,
            dimensions,
            type_args,
            ..
        } = dt
        else {
            return None;
        };
        if !type_args.is_empty() {
            return None;
        }
        let rep = match name.scopes.as_slice() {
            [] => self.inline_type(&name.name.name)?,
            [s] if !s.type_args.is_empty() => {
                let c = self.class_named(&s.name.name)?;
                let ci = self.info.classes.get(&c)?;
                let (dt, ud) = ci.inline.get(&name.name.name)?;
                if !ud.is_empty() {
                    return None;
                }
                let args: Vec<ParamValue> =
                    s.type_args.iter().cloned().map(ParamValue::Expr).collect();
                let (t, v) = bind_params(&ci.params, &args);
                subst_type(dt, &t, &v)?
            }
            _ => return None,
        };
        merge_packed(rep, dimensions.clone())
    }

    fn value_shadowed(&self, n: &str) -> bool {
        self.frames.iter().any(|f| f.values.contains(n))
    }

    fn is_package(&self, n: &str) -> bool {
        self.info.pkgs.contains_key(n) && !self.value_shadowed(n)
    }

    fn ambiguous(&mut self, n: &str, pkgs: &[String]) {
        let list: Vec<String> = pkgs.iter().map(|p| format!("'{}'", p)).collect();
        self.errors.push(format!(
            "type '{}' is declared by more than one wildcard-imported package ({}), so it \
             is not visible here; import it explicitly or qualify it (`{}::{}`) \
             (IEEE 1800-2017 §26.3)",
            n,
            list.join(", "),
            pkgs[0],
            n
        ));
    }

    /// A bare type name in a type position.
    fn type_ident(&mut self, id: &mut crate::ast::Identifier) {
        match self.resolve(&id.name) {
            Res::Keep => {}
            Res::To(m) => id.name = m,
            Res::Ambiguous(c) => {
                let n = id.name.clone();
                self.ambiguous(&n, &c);
            }
        }
    }

    fn type_name(&mut self, tn: &mut TypeName) {
        for s in &mut tn.scopes {
            for a in &mut s.type_args {
                self.expr(a);
            }
        }
        if tn.scopes.is_empty() {
            self.type_ident(&mut tn.name);
            return;
        }
        // `C::t` (`Outer::Inner::t`, `pkg::C::t`) naming a renamed class-scoped type.
        if tn.scopes.iter().all(|s| s.type_args.is_empty()) {
            let segs: Vec<String> = tn.scopes.iter().map(|s| s.name.name.clone()).collect();
            if let Some(m) = self.class_scoped_type(&segs, &tn.name.name) {
                tn.scopes.clear();
                tn.name.name = m;
                return;
            }
        }
        let first = tn.scopes[0].name.name.clone();
        if self.is_package(&first) {
            let next = if tn.scopes.len() > 1 {
                tn.scopes[1].name.name.clone()
            } else {
                tn.name.name.clone()
            };
            if self.info.colliding.contains(&next) {
                if let Some(o) = self.info.owner(&first, &next, 0) {
                    let m = mangle(&o, &next);
                    if tn.scopes.len() > 1 {
                        tn.scopes.remove(0);
                        tn.scopes[0].name.name = m;
                    } else {
                        tn.scopes.clear();
                        tn.name.name = m;
                    }
                }
            }
            return;
        }
        // `C::t` / `C#(..)::t` with C itself a colliding class name.
        self.type_ident(&mut tn.scopes[0].name);
    }

    fn dtype(&mut self, dt: &mut DataType) {
        self.in_const += 1;
        self.dtype_inner(dt);
        self.in_const -= 1;
    }

    fn dtype_inner(&mut self, dt: &mut DataType) {
        if let Some(rep) = self.inline_ref(dt) {
            *dt = rep;
            self.inline_depth += 1;
            self.dtype_inner(dt);
            self.inline_depth -= 1;
            return;
        }
        match dt {
            DataType::IntegerVector { dimensions, .. } | DataType::Implicit { dimensions, .. } => {
                self.packed(dimensions)
            }
            DataType::TypeReference {
                name,
                dimensions,
                type_args,
                ..
            } => {
                self.type_name(name);
                self.packed(dimensions);
                type_args.iter_mut().for_each(|a| self.expr(a));
            }
            DataType::Struct(su) => {
                for m in &mut su.members {
                    self.dtype(&mut m.data_type);
                    for d in &mut m.declarators {
                        self.unpacked(&mut d.dimensions);
                        if let Some(i) = &mut d.init {
                            self.expr(i);
                        }
                    }
                }
                self.packed(&mut su.dimensions);
            }
            DataType::Enum(et) => {
                if let Some(b) = &mut et.base_type {
                    self.dtype(b);
                }
                for m in &mut et.members {
                    if let Some((a, b)) = &mut m.range {
                        self.expr(a);
                        self.expr(b);
                    }
                    if let Some(i) = &mut m.init {
                        self.expr(i);
                    }
                }
                self.packed(&mut et.dimensions);
            }
            DataType::Interface { type_args, .. } => {
                type_args.iter_mut().for_each(|a| self.expr(a))
            }
            DataType::IntegerAtom { .. }
            | DataType::Real { .. }
            | DataType::Simple { .. }
            | DataType::Void(_) => {}
        }
    }

    fn packed(&mut self, dims: &mut [PackedDimension]) {
        for d in dims {
            if let PackedDimension::Range { left, right, .. } = d {
                self.expr(left);
                self.expr(right);
            }
        }
    }

    fn unpacked(&mut self, dims: &mut [UnpackedDimension]) {
        self.in_const += 1;
        self.unpacked_inner(dims);
        self.in_const -= 1;
    }

    fn unpacked_inner(&mut self, dims: &mut [UnpackedDimension]) {
        for d in dims {
            match d {
                UnpackedDimension::Range { left, right, .. } => {
                    self.expr(left);
                    self.expr(right);
                }
                UnpackedDimension::Expression { expr, .. } => {
                    // `T arr[key_t]` parses the key type as an expression.
                    self.expr(expr)
                }
                UnpackedDimension::Queue { max_size, .. } => {
                    if let Some(m) = max_size {
                        self.expr(m);
                    }
                }
                UnpackedDimension::Associative { data_type, span } => {
                    if let Some(t) = data_type {
                        if let Some(size) = self.contested_size_name(t, *span) {
                            *d = UnpackedDimension::Expression {
                                expr: Box::new(size),
                                span: *span,
                            };
                            continue;
                        }
                        self.dtype(t);
                    }
                }
                UnpackedDimension::Unsized(_) => {}
            }
        }
    }

    /// §7.4.2 / §26.3: `x[N]` with a bare `N` parses as an associative
    /// dimension keyed by the type `N`, and is a fixed size when `N` names a
    /// constant. When two packages (or a package and `$unit`) declare the
    /// value `N`, the one this scope sees is found by the §26.3 rules, like
    /// any other reference to it: the explicit import `import q::N;` of a
    /// module wins over the compilation unit's `import r::*;`. The size is
    /// then spelled `q::N`, the qualified lookup — the elaborator's own
    /// resolution of a bare size name read the flat table, where the
    /// compilation unit's wildcard import had registered `r::N` (#895).
    fn contested_size_name(&mut self, t: &DataType, span: crate::ast::Span) -> Option<Expression> {
        let DataType::TypeReference {
            name,
            dimensions,
            type_args,
            ..
        } = t
        else {
            return None;
        };
        if !name.scopes.is_empty() || !dimensions.is_empty() || !type_args.is_empty() {
            return None;
        }
        let n = name.name.name.as_str();
        // A type of that name in scope keeps the associative reading.
        if !matches!(self.resolve(n), Res::Keep)
            || self.frames.iter().any(|f| f.types.contains(n))
            || !self.info.colliding_values.contains(n)
        {
            return None;
        }
        let pkg = self.resolve_value(n)?;
        let member = crate::ast::Identifier {
            name: n.to_string(),
            span: name.name.span,
        };
        Some(Expression::new(
            ExprKind::MemberAccess {
                expr: Box::new(ident_expr(pkg, span)),
                member,
            },
            span,
        ))
    }

    fn opt(&mut self, e: &mut Option<Expression>) {
        if let Some(e) = e {
            self.expr(e);
        }
    }

    fn opt_box(&mut self, e: &mut Option<Box<Expression>>) {
        if let Some(e) = e {
            self.expr(e);
        }
    }

    fn expr(&mut self, e: &mut Expression) {
        match &mut e.kind {
            ExprKind::MemberAccess { expr, member } => {
                // `Q::v` naming a renamed package variable.
                if let Some(q) = plain_ident(expr) {
                    if let Some(m) = self.mangled_qualified(q, &member.name) {
                        let span = e.span;
                        *e = ident_expr(m, span);
                        return;
                    }
                }
                // `C::t` / `Outer::Inner::t` naming a renamed class type.
                if self.info.class_colliding.contains(&member.name) {
                    if let Some(segs) = scope_chain(expr) {
                        if let Some(m) = self.class_scoped_type(&segs, &member.name) {
                            let span = e.span;
                            *e = ident_expr(m, span);
                            return;
                        }
                    }
                }
                // `Q::name` with Q a package: the declaration Q holds.
                if let Some(q) = plain_ident(expr) {
                    if self.info.colliding.contains(&member.name) && self.is_package(q) {
                        if let Some(o) = self.info.owner(q, &member.name, 0) {
                            let m = mangle(&o, &member.name);
                            let span = e.span;
                            *e = ident_expr(m, span);
                            return;
                        }
                    }
                    // §26.6: a value Q re-exports is the one its owner holds.
                    if self.info.colliding_values.contains(&member.name) && self.is_package(q) {
                        if let Some(o) = self.info.value_owner(q, &member.name, 0) {
                            if o != q {
                                let span = expr.span;
                                **expr = ident_expr(o, span);
                            }
                            return;
                        }
                    }
                }
                self.expr(expr);
            }
            ExprKind::Ident(h) => {
                if h.root.is_none() && h.path.len() > 1 {
                    let n = &h.path[0].name.name;
                    if self.info.hiding.contains(n)
                        && !self.value_shadowed(n)
                        && let Res::To(named) = self.resolve(n)
                    {
                        h.path[0].name.name = named;
                    }
                }
                // A renamed package variable (see `mangled_vars`), as
                // `Q::v...` or bare: spell it by its storage name and keep the
                // selects and member path.
                if h.root.is_none() && !self.info.mangled_vars.is_empty() {
                    let qualified = h.path.len() >= 2
                        && h.path[0].selects.is_empty()
                        && self.info.mangled_vars.contains(&h.path[1].name.name);
                    let to = if qualified {
                        self.mangled_qualified(&h.path[0].name.name, &h.path[1].name.name)
                    } else {
                        None
                    };
                    if let Some(m) = to {
                        h.path.remove(0);
                        h.path[0].name.name = m;
                    } else if let Some(m) = self.mangled_var(&h.path[0].name.name) {
                        h.path[0].name.name = m;
                    }
                }
                if h.root.is_none() && h.path.len() == 1 && h.path[0].selects.is_empty() {
                    let n = &h.path[0].name.name;
                    // A typedef `inline_type` replaces, used as an operand
                    // (`$bits(payload_t)`, `payload_t'(v)`).
                    if !self.value_shadowed(n) {
                        if let Some(rep) = self.inline_type(n) {
                            match &rep {
                                DataType::TypeReference {
                                    name,
                                    dimensions,
                                    type_args,
                                    ..
                                } if name.scopes.is_empty()
                                    && dimensions.is_empty()
                                    && type_args.is_empty() =>
                                {
                                    h.path[0].name.name = name.name.name.clone();
                                }
                                _ => {
                                    let span = e.span;
                                    *e =
                                        Expression::new(ExprKind::TypeLiteral(Box::new(rep)), span);
                                    self.inline_depth += 1;
                                    self.expr(e);
                                    self.inline_depth -= 1;
                                }
                            }
                            return;
                        }
                    }
                    if (self.info.colliding.contains(n)
                        || self.info.class_colliding.contains(n)
                        || self.info.hiding.contains(n))
                        && !self.value_shadowed(n)
                    {
                        // Expression positions only rename; an ambiguous
                        // name may still be a value from somewhere this
                        // pass does not track.
                        if let Res::To(m) = self.resolve(n) {
                            h.path[0].name.name = m;
                        }
                    } else if self.info.colliding_values.contains(n) {
                        if let Some(p) = self.resolve_value(n) {
                            let span = e.span;
                            let member = h.path[0].name.clone();
                            *e = Expression::new(
                                ExprKind::MemberAccess {
                                    expr: Box::new(ident_expr(p, span)),
                                    member,
                                },
                                span,
                            );
                            return;
                        }
                    } else if self.in_const == 0 {
                        // §26.3 / §6.19: an enum member of a package, named
                        // bare where that package's declaration is the one in
                        // scope. All packages' members share one flat table,
                        // where the last package registered wins, so spell
                        // the reference `pkg::NAME` — the qualified lookup.
                        if let Some(p) = self.resolve_member(n) {
                            let span = e.span;
                            let member = h.path[0].name.clone();
                            *e = Expression::new(
                                ExprKind::MemberAccess {
                                    expr: Box::new(ident_expr(p, span)),
                                    member,
                                },
                                span,
                            );
                            return;
                        }
                    }
                }
                for seg in &mut h.path {
                    for s in &mut seg.selects {
                        self.expr(s);
                    }
                }
            }
            ExprKind::Call { func, args } => {
                if plain_ident(func).is_none() {
                    self.expr(func);
                } else {
                    self.qualify_value(func);
                }
                args.iter_mut().for_each(|a| self.expr(a));
            }
            ExprKind::TypeLiteral(dt) => self.dtype(dt),
            ExprKind::Unary { operand, .. } => self.expr(operand),
            ExprKind::Binary { left, right, .. } => {
                self.expr(left);
                self.expr(right);
            }
            ExprKind::Conditional {
                condition,
                then_expr,
                else_expr,
            } => {
                self.expr(condition);
                self.expr(then_expr);
                self.expr(else_expr);
            }
            ExprKind::Concatenation(v) => v.iter_mut().for_each(|x| self.expr(x)),
            ExprKind::Replication { count, exprs } => {
                self.expr(count);
                exprs.iter_mut().for_each(|x| self.expr(x));
            }
            ExprKind::AssignmentPattern(items) => {
                for it in items {
                    match it {
                        AssignmentPatternItem::Ordered(x)
                        | AssignmentPatternItem::Named(_, x)
                        | AssignmentPatternItem::Default(x) => self.expr(x),
                        AssignmentPatternItem::Typed(t, x) => {
                            self.dtype(t);
                            self.expr(x);
                        }
                        AssignmentPatternItem::Keyed(k, x) => {
                            self.expr(k);
                            self.expr(x);
                        }
                    }
                }
            }
            ExprKind::SystemCall { name, args } => {
                args.iter_mut().for_each(|a| self.expr(a));
                // `payload_t'(v)` whose typedef was replaced by a type.
                if name == "$__xz_named_cast"
                    && args
                        .first()
                        .is_some_and(|a| matches!(a.kind, ExprKind::TypeLiteral(_)))
                {
                    *name = "$__xz_type_cast".to_string();
                }
            }
            ExprKind::NamedArg { expr, .. } => self.opt_box(expr),
            ExprKind::Inside { expr, ranges } => {
                self.expr(expr);
                ranges.iter_mut().for_each(|r| self.expr(r));
            }
            ExprKind::Matches { expr, pattern } => {
                self.expr(expr);
                self.pattern(pattern);
            }
            ExprKind::Specialization {
                base,
                type_args_text: args_text,
            } => {
                self.expr(base);
                // §8.25: the parser retains specialization operands as
                // tokens. Qualify lexical class references there as well,
                // preserving strings, named formals and explicit scopes.
                if !self.info.hiding.is_empty() {
                    use crate::lexer::{Lexer, TokenKind};
                    let tokens = Lexer::new(args_text).tokenize();
                    let mut edits = Vec::new();
                    for (i, token) in tokens.iter().enumerate() {
                        if token.kind == TokenKind::Identifier
                            && self.info.hiding.contains(&token.text)
                            && !self.value_shadowed(&token.text)
                            && !i.checked_sub(1).is_some_and(|p| {
                                matches!(tokens[p].kind, TokenKind::Dot | TokenKind::DoubleColon)
                            })
                            && let Res::To(named) = self.resolve(&token.text)
                        {
                            edits.push((token.span, named));
                        }
                    }
                    for (span, named) in edits.into_iter().rev() {
                        args_text.replace_range(span.start..span.end, &named);
                    }
                }
            }
            ExprKind::Index { expr, index } => {
                self.expr(expr);
                self.expr(index);
            }
            ExprKind::RangeSelect {
                expr, left, right, ..
            } => {
                self.expr(expr);
                self.expr(left);
                self.expr(right);
            }
            ExprKind::Range(l, r) => {
                self.expr(l);
                self.expr(r);
            }
            ExprKind::Paren(x) => self.expr(x),
            ExprKind::WithClause { expr, filter } => {
                self.expr(expr);
                self.expr(filter);
            }
            ExprKind::RandomizeWith { call, constraints } => {
                self.expr(call);
                constraints.iter_mut().for_each(|c| self.constraint(c));
            }
            ExprKind::AssignExpr { lvalue, rvalue } => {
                self.expr(lvalue);
                self.expr(rvalue);
            }
            ExprKind::StreamOp {
                slice_size, exprs, ..
            } => {
                self.opt_box(slice_size);
                exprs.iter_mut().for_each(|x| self.expr(x));
            }
            ExprKind::Tagged { inner, .. } => self.opt_box(inner),
            ExprKind::SvaClocked { events, body } => {
                for event in events {
                    self.expr(&mut event.expr);
                    if let Some(g) = &mut event.iff {
                        self.expr(g);
                    }
                }
                self.expr(body);
            }
            ExprKind::ShallowCopy { source } => self.expr(source),
            ExprKind::TypedPattern { ty, pattern } => {
                self.dtype(ty);
                self.expr(pattern);
            }
            ExprKind::Number(_)
            | ExprKind::StringLiteral(_)
            | ExprKind::Dollar
            | ExprKind::Null
            | ExprKind::This
            | ExprKind::Empty => {}
        }
    }

    fn pattern(&mut self, p: &mut Pattern) {
        match p {
            Pattern::Expr(e) => self.expr(e),
            Pattern::Tagged { inner: Some(i), .. } => self.pattern(i),
            Pattern::Struct(v) => v.iter_mut().for_each(|(_, p)| self.pattern(p)),
            _ => {}
        }
    }

    fn constraint(&mut self, c: &mut ConstraintItem) {
        match c {
            ConstraintItem::Expr(e) => self.expr(e),
            ConstraintItem::Inside {
                expr,
                range,
                dist_weights,
                ..
            } => {
                self.expr(expr);
                range
                    .iter_mut()
                    .for_each(|r| r.for_each_expr_mut(&mut |x| self.expr(x)));
                for w in dist_weights.iter_mut().flatten() {
                    match w {
                        DistWeight::Each(x) | DistWeight::Total(x) => self.expr(x),
                    }
                }
            }
            ConstraintItem::Implication {
                condition,
                constraint,
                ..
            } => {
                self.expr(condition);
                self.constraint(constraint);
            }
            ConstraintItem::IfElse {
                condition,
                then_item,
                else_item,
                ..
            } => {
                self.expr(condition);
                self.constraint(then_item);
                if let Some(e) = else_item {
                    self.constraint(e);
                }
            }
            ConstraintItem::Foreach {
                array, vars, item, ..
            } => {
                self.expr(array);
                let mut f = Frame::default();
                f.values
                    .extend(vars.iter().flatten().map(|v| v.name.clone()));
                self.frames.push(f);
                self.constraint(item);
                self.frames.pop();
            }
            ConstraintItem::Solve {
                before_paths,
                after_paths,
                ..
            } => {
                before_paths.iter_mut().for_each(|x| self.expr(x));
                after_paths.iter_mut().for_each(|x| self.expr(x));
            }
            ConstraintItem::Soft(i) => self.constraint(i),
            ConstraintItem::Block(v) => v.iter_mut().for_each(|i| self.constraint(i)),
            ConstraintItem::Unique { exprs, .. } => exprs.iter_mut().for_each(|x| self.expr(x)),
        }
    }

    fn stmt(&mut self, s: &mut Statement) {
        match &mut s.kind {
            StatementKind::Expr(e)
            | StatementKind::Return(Some(e))
            | StatementKind::Coverpoint { expr: e, .. } => self.expr(e),
            StatementKind::BlockingAssign { lvalue, rvalue } => {
                self.expr(lvalue);
                self.expr(rvalue);
            }
            StatementKind::NonblockingAssign {
                lvalue,
                delay,
                rvalue,
            } => {
                self.expr(lvalue);
                self.opt(delay);
                self.expr(rvalue);
            }
            StatementKind::If {
                condition,
                then_stmt,
                else_stmt,
                ..
            } => {
                self.expr(condition);
                self.stmt(then_stmt);
                if let Some(e) = else_stmt {
                    self.stmt(e);
                }
            }
            StatementKind::Case { expr, items, .. } => {
                self.expr(expr);
                for it in items {
                    it.patterns.iter_mut().for_each(|p| self.expr(p));
                    if let Some(p) = &mut it.pattern {
                        self.pattern(p);
                    }
                    self.opt(&mut it.guard);
                    self.stmt(&mut it.stmt);
                }
            }
            StatementKind::For {
                init,
                condition,
                step,
                body,
            } => {
                let mut frame = Frame::default();
                for item in init.iter() {
                    if let ForInit::VarDecl { name, .. } = item {
                        frame.values.insert(name.name.clone());
                    }
                }
                self.frames.push(frame);
                for i in init {
                    match i {
                        ForInit::VarDecl {
                            data_type, init, ..
                        } => {
                            self.dtype(data_type);
                            self.expr(init);
                        }
                        ForInit::Assign { lvalue, rvalue } => {
                            self.expr(lvalue);
                            self.expr(rvalue);
                        }
                    }
                }
                self.opt(condition);
                step.iter_mut().for_each(|x| self.expr(x));
                self.stmt(body);
                self.frames.pop();
            }
            StatementKind::Foreach { array, vars, body } => {
                self.expr(array);
                let mut frame = Frame::default();
                frame
                    .values
                    .extend(vars.iter().flatten().map(|v| v.name.clone()));
                self.frames.push(frame);
                self.stmt(body);
                self.frames.pop();
            }
            StatementKind::While { condition, body }
            | StatementKind::DoWhile { body, condition } => {
                self.expr(condition);
                self.stmt(body);
            }
            StatementKind::Repeat { count, body } => {
                self.expr(count);
                self.stmt(body);
            }
            StatementKind::ForeachTail { body, .. }
            | StatementKind::Forever { body }
            | StatementKind::ForeverTail { body }
            | StatementKind::RsAction { body } => self.stmt(body),
            StatementKind::SeqBlock { stmts, .. } | StatementKind::ParBlock { stmts, .. } => {
                let mut frame = Frame::default();
                for stmt in stmts.iter() {
                    stmt_locals(stmt, &mut frame);
                }
                self.frames.push(frame);
                stmts.iter_mut().for_each(|x| self.stmt(x));
                self.frames.pop();
            }
            StatementKind::TimingControl { control, stmt } => {
                match control {
                    TimingControl::Delay(d) => self.expr(d),
                    TimingControl::Event(ev) => self.event(ev),
                }
                self.stmt(stmt);
            }
            StatementKind::EventTrigger { target, .. } => self.opt_box(target),
            StatementKind::Wait { condition, stmt } => {
                self.expr(condition);
                self.stmt(stmt);
            }
            StatementKind::Assertion(a) => self.assertion(a),
            StatementKind::ProceduralContinuous(pc) => match pc {
                ProceduralContinuous::Assign { lvalue, rvalue }
                | ProceduralContinuous::Force { lvalue, rvalue } => {
                    self.expr(lvalue);
                    self.expr(rvalue);
                }
                ProceduralContinuous::Deassign(e) | ProceduralContinuous::Release(e) => {
                    self.expr(e)
                }
            },
            StatementKind::VarDecl {
                data_type,
                declarators,
                ..
            } => {
                self.splice_unpacked(data_type, declarators);
                self.dtype(data_type);
                self.declarators(declarators);
            }
            StatementKind::RandCase { items } => {
                for (e, s) in items {
                    self.expr(e);
                    self.stmt(s);
                }
            }
            StatementKind::Typedef(td) => {
                self.dtype(&mut td.data_type);
                self.unpacked(&mut td.dimensions);
            }
            StatementKind::Cross { items, .. } => items.iter_mut().for_each(|x| self.expr(x)),
            StatementKind::WaitOrder { pass, fail, .. } => {
                if let Some(p) = pass {
                    self.stmt(p);
                }
                if let Some(f) = fail {
                    self.stmt(f);
                }
            }
            StatementKind::Null
            | StatementKind::ScopePop
            | StatementKind::LoopStep
            | StatementKind::DisableFork
            | StatementKind::Return(None)
            | StatementKind::WaitFork
            | StatementKind::Disable(_)
            | StatementKind::Break
            | StatementKind::Continue
            | StatementKind::RsReturn => {}
        }
    }

    fn event(&mut self, ev: &mut EventControl) {
        match ev {
            EventControl::HierIdentifier(e) => self.expr(e),
            EventControl::EventExpr(list) => {
                for ee in list {
                    self.expr(&mut ee.expr);
                    self.opt(&mut ee.iff);
                }
            }
            _ => {}
        }
    }

    fn assertion(&mut self, a: &mut AssertionStatement) {
        self.expr(&mut a.expr);
        if let Some(s) = &mut a.action {
            self.stmt(s);
        }
        if let Some(s) = &mut a.else_action {
            self.stmt(s);
        }
        if let Some(ee) = &mut a.inferred_clock {
            self.expr(&mut ee.expr);
            self.opt(&mut ee.iff);
        }
    }

    /// A declaration whose type is a typedef `inline_unpacked` replaces
    /// (`ua_t u;` with `typedef T ua_t[3];`) declares `T u[3]`: the
    /// typedef's dimensions follow the declarator's own (§7.4.2).
    fn splice_unpacked(&mut self, dt: &mut DataType, ds: &mut [VarDeclarator]) {
        let DataType::TypeReference {
            name,
            dimensions,
            type_args,
            ..
        } = dt
        else {
            return;
        };
        if name.has_scope() || !dimensions.is_empty() || !type_args.is_empty() || ds.is_empty() {
            return;
        }
        let Some((elem, ud)) = self.inline_unpacked(&name.name.name) else {
            return;
        };
        *dt = elem;
        for d in ds {
            d.dimensions.extend(ud.iter().cloned());
        }
    }

    fn declarators(&mut self, ds: &mut [VarDeclarator]) {
        for d in ds {
            self.unpacked(&mut d.dimensions);
            self.opt(&mut d.init);
        }
    }

    /// A procedural body in its own frame of local names.
    fn body(&mut self, s: &mut Statement) {
        let mut f = Frame::default();
        stmt_locals(s, &mut f);
        self.frames.push(f);
        self.stmt(s);
        self.frames.pop();
    }

    fn param_decl(&mut self, pd: &mut ParameterDeclaration) {
        self.in_const += 1;
        self.param_decl_inner(pd);
        self.in_const -= 1;
    }

    fn param_decl_inner(&mut self, pd: &mut ParameterDeclaration) {
        match &mut pd.kind {
            ParameterKind::Data {
                data_type,
                assignments,
            } => {
                self.dtype(data_type);
                for a in assignments {
                    self.unpacked(&mut a.dimensions);
                    self.opt(&mut a.init);
                }
            }
            ParameterKind::Type { assignments } => {
                for a in assignments {
                    if let Some(t) = &mut a.init {
                        self.dtype(t);
                    }
                }
            }
        }
    }

    fn param_value(&mut self, v: &mut ParamValue) {
        match v {
            ParamValue::Expr(e) => self.expr(e),
            ParamValue::Type(t) => self.dtype(t),
        }
    }

    /// `import Q::name;` naming a renamed declaration imports it by its new
    /// name, from the package that actually declares it.
    fn import_decl(&mut self, imp: &mut ImportDeclaration) {
        for ii in &mut imp.items {
            let Some(n) = &mut ii.item else { continue };
            if self.info.colliding_values.contains(&n.name) {
                // §26.6: `import Q::v;` of a value Q re-exports names the
                // owner's declaration.
                if let Some(o) = self.info.value_owner(&ii.package.name, &n.name, 0) {
                    ii.package.name = o;
                }
                continue;
            }
            if !self.info.colliding.contains(&n.name) {
                continue;
            }
            if let Some(o) = self.info.owner(&ii.package.name, &n.name, 0) {
                n.name = mangle(&o, &n.name);
                ii.package.name = o;
            }
        }
    }

    /// An out-of-block method name `C::f` — C is resolved like a type.
    fn subroutine_name(&mut self, tn: &mut TypeName) {
        if !tn.scopes.is_empty() {
            self.type_name_scope_only(tn);
        }
    }

    fn type_name_scope_only(&mut self, tn: &mut TypeName) {
        let first = tn.scopes[0].name.name.clone();
        if self.is_package(&first) && tn.scopes.len() > 1 {
            let next = tn.scopes[1].name.name.clone();
            if self.info.colliding.contains(&next) {
                if let Some(o) = self.info.owner(&first, &next, 0) {
                    tn.scopes.remove(0);
                    tn.scopes[0].name.name = mangle(&o, &next);
                }
            }
            return;
        }
        self.type_ident(&mut tn.scopes[0].name);
    }

    fn ports(&mut self, ports: &mut [FunctionPort]) {
        for p in ports {
            self.dtype(&mut p.data_type);
            self.unpacked(&mut p.dimensions);
            self.opt(&mut p.default);
        }
    }

    fn function(&mut self, f: &mut FunctionDeclaration) {
        let method = !f.name.scopes.is_empty();
        self.subroutine_name(&mut f.name);
        self.dtype(&mut f.return_type);
        let pushed = self.push_method_class(&f.name);
        self.subroutine_body(&mut f.ports, &mut f.items, method);
        if pushed {
            self.frames.pop();
        }
    }

    fn task(&mut self, t: &mut TaskDeclaration) {
        let method = !t.name.scopes.is_empty();
        self.subroutine_name(&mut t.name);
        let pushed = self.push_method_class(&t.name);
        self.subroutine_body(&mut t.ports, &mut t.items, method);
        if pushed {
            self.frames.pop();
        }
    }

    /// §8.24: the formals and body of an out-of-block method `C::f` are in
    /// the scope of class C — push its frame for the class's type names.
    fn push_method_class(&mut self, tn: &TypeName) -> bool {
        if tn.scopes.is_empty() {
            return false;
        }
        let segs: Vec<String> = tn.scopes.iter().map(|s| s.name.name.clone()).collect();
        let Some(c) = self.class_path(&segs) else {
            return false;
        };
        let bases = self.class_bases(&c);
        self.frames.push(Frame {
            inherits: true,
            cls: Some(c),
            bases,
            ..Frame::default()
        });
        true
    }

    /// The base classes of class `c` (by the names they carry after this
    /// pass), nearest first.
    fn class_bases(&self, c: &str) -> Vec<String> {
        let mut bases: Vec<String> = Vec::new();
        let mut cur = self
            .info
            .classes
            .get(c)
            .and_then(|ci| ci.base.clone())
            .and_then(|n| self.class_named(&n));
        while let Some(b) = cur {
            if bases.contains(&b) || bases.len() > 64 {
                break;
            }
            let next = self.info.classes.get(&b).and_then(|ci| ci.base.clone());
            bases.push(b);
            cur = next.and_then(|n| self.class_named(&n));
        }
        bases
    }

    /// `method`: the body of an out-of-block class method, which sees the
    /// class's members (not tracked here) before any import.
    fn subroutine_body(
        &mut self,
        ports: &mut [FunctionPort],
        items: &mut [Statement],
        method: bool,
    ) {
        self.ports(ports);
        let mut f = Frame {
            inherits: method,
            ..Frame::default()
        };
        f.values.extend(ports.iter().map(|p| p.name.name.clone()));
        for s in items.iter() {
            stmt_locals(s, &mut f);
        }
        self.frames.push(f);
        items.iter_mut().for_each(|s| self.stmt(s));
        self.frames.pop();
    }

    fn dpi(&mut self, p: &mut DPIProto) {
        match p {
            DPIProto::Function(f) => self.function(f),
            DPIProto::Task(t) => self.task(t),
        }
    }

    fn covergroup(&mut self, cg: &mut CovergroupDeclaration) {
        self.ports(&mut cg.ports);
        self.ports(&mut cg.sample_ports);
        cg.for_each_expr_mut(&mut |e| self.expr(e));
    }

    fn class(&mut self, c: &mut ClassDeclaration) {
        // The base and interface names resolve in the enclosing scope.
        if let Some(ext) = &mut c.extends {
            if let Some(first) = ext.scopes.first().map(|s| s.name.clone()) {
                if self.is_package(&first)
                    && ext.scopes.len() == 1
                    && self.info.colliding.contains(&ext.name.name)
                {
                    if let Some(o) = self.info.owner(&first, &ext.name.name, 0) {
                        ext.name.name = mangle(&o, &ext.name.name);
                        ext.scopes.clear();
                    }
                }
            } else {
                self.type_ident(&mut ext.name);
            }
        }
        for i in &mut c.implements {
            self.type_ident(i);
        }
        let named = c.name.name.clone();
        let mut bases = Vec::new();
        if let Some(ext) = &c.extends {
            let mut cur = self.class_named(&ext.name.name);
            while let Some(b) = cur {
                if bases.contains(&b) || bases.len() > 64 {
                    break;
                }
                let next = self.info.classes.get(&b).and_then(|ci| ci.base.clone());
                bases.push(b);
                cur = next.and_then(|n| self.class_named(&n));
            }
        }
        let mut f = Frame {
            inherits: c.extends.is_some(),
            cls: self
                .info
                .classes
                .contains_key(&named)
                .then(|| named.clone()),
            bases,
            ..Frame::default()
        };
        for p in &c.params {
            param_names(p, &mut f.types, &mut f.values);
        }
        for it in &c.items {
            match it {
                ClassItem::Property(p) => {
                    f.values
                        .extend(p.declarators.iter().map(|d| d.name.name.clone()));
                    enum_members(&p.data_type, &mut f.values);
                }
                ClassItem::Method(m) => {
                    let n = match &m.kind {
                        ClassMethodKind::Function(fd)
                        | ClassMethodKind::PureVirtual(fd)
                        | ClassMethodKind::Extern(fd) => &fd.name.name.name,
                        ClassMethodKind::Task(td) => &td.name.name.name,
                    };
                    f.values.insert(n.clone());
                }
                ClassItem::Typedef(td) => {
                    f.types.insert(td.name.name.clone());
                    enum_members(&td.data_type, &mut f.values);
                }
                ClassItem::Parameter(pd) => param_names(pd, &mut f.types, &mut f.values),
                ClassItem::Class(nc) => {
                    f.types.insert(nc.name.name.clone());
                }
                ClassItem::Import(imp) => f.add_imports(imp),
                _ => {}
            }
        }
        self.frames.push(f);
        if let Some(ext) = &mut c.extends {
            ext.args.iter_mut().for_each(|a| self.param_value(a));
        }
        c.params.iter_mut().for_each(|p| self.param_decl(p));
        for it in &mut c.items {
            match it {
                ClassItem::Property(p) => {
                    self.splice_unpacked(&mut p.data_type, &mut p.declarators);
                    self.dtype(&mut p.data_type);
                    self.declarators(&mut p.declarators);
                }
                ClassItem::Method(m) => match &mut m.kind {
                    ClassMethodKind::Function(fd)
                    | ClassMethodKind::PureVirtual(fd)
                    | ClassMethodKind::Extern(fd) => self.function(fd),
                    ClassMethodKind::Task(td) => self.task(td),
                },
                ClassItem::Constraint(cc) => cc.items.iter_mut().for_each(|i| self.constraint(i)),
                ClassItem::Typedef(td) => {
                    // §8.3/§6.18: a class typedef whose name is declared
                    // elsewhere too is renamed to its class-qualified spelling.
                    if self.info.class_colliding.contains(&td.name.name)
                        && self
                            .info
                            .classes
                            .get(&named)
                            .is_some_and(|ci| ci.types.contains(&td.name.name))
                    {
                        td.name.name = mangle(&named, &td.name.name);
                    }
                    self.dtype(&mut td.data_type);
                    self.unpacked(&mut td.dimensions);
                }
                ClassItem::Parameter(pd) => self.param_decl(pd),
                ClassItem::Class(nc) => {
                    if self.info.class_colliding.contains(&nc.name.name) {
                        let m = mangle(&named, &nc.name.name);
                        if let Some(l) = &mut nc.endlabel {
                            l.name = m.clone();
                        }
                        nc.name.name = m;
                    }
                    self.class(nc)
                }
                ClassItem::Covergroup(cg) => self.covergroup(cg),
                ClassItem::Import(imp) => self.import_decl(imp),
                ClassItem::Empty => {}
            }
        }
        self.frames.pop();
    }

    fn instantiation(&mut self, mi: &mut ModuleInstantiation) {
        if let Some(ps) = &mut mi.params {
            self.in_const += 1;
            for p in ps {
                match p {
                    ParamConnection::Ordered(Some(v))
                    | ParamConnection::Named { value: Some(v), .. } => self.param_value(v),
                    _ => {}
                }
            }
            self.in_const -= 1;
        }
        for inst in &mut mi.instances {
            self.unpacked(&mut inst.dimensions);
            for c in &mut inst.connections {
                match c {
                    PortConnection::Ordered(e) | PortConnection::Named { expr: e, .. } => {
                        self.opt(e)
                    }
                    PortConnection::Wildcard => {}
                }
            }
        }
    }

    fn module_frame(
        params: &[ParameterDeclaration],
        ports: &PortList,
        items: &[ModuleItem],
    ) -> Frame {
        let mut f = Frame::default();
        for p in params {
            param_names(p, &mut f.types, &mut f.values);
        }
        match ports {
            PortList::Ansi(v) => f.values.extend(v.iter().map(|p| p.name.name.clone())),
            PortList::NonAnsi(v) => f.values.extend(v.iter().map(|p| p.name.clone())),
            PortList::Empty => {}
        }
        module_item_names(items, &mut f);
        f
    }

    fn module_body(
        &mut self,
        name: &str,
        params: &mut [ParameterDeclaration],
        ports: &mut PortList,
        items: &mut [ModuleItem],
    ) {
        // §23.2/§6.5: body classes are not visible in header defaults.
        let mut f = Self::module_frame(params, ports, &[]);
        f.module = Some(name.to_string());
        for it in items.iter() {
            if let ModuleItem::ImportDeclaration(imp) = it {
                f.add_imports(imp);
            }
        }
        self.frames.push(f);
        params.iter_mut().for_each(|p| self.param_decl(p));
        if let PortList::Ansi(v) = ports {
            for p in v {
                if let Some(t) = &mut p.data_type {
                    self.dtype(t);
                }
                self.unpacked(&mut p.dimensions);
                self.opt(&mut p.default);
            }
        }
        let mut body = Frame::default();
        self.module_class_bindings(items, &mut body);
        module_item_names(items, &mut body);
        self.frames.push(body);
        items.iter_mut().for_each(|i| self.module_item(i));
        self.frames.pop();
        self.frames.pop();
    }

    fn module_item(&mut self, it: &mut ModuleItem) {
        match it {
            ModuleItem::PortDeclaration(p) => {
                self.dtype(&mut p.data_type);
                self.declarators(&mut p.declarators);
            }
            ModuleItem::NetDeclaration(n) => {
                self.dtype(&mut n.data_type);
                self.opt(&mut n.delay);
                self.opt(&mut n.delay_fall);
                self.opt(&mut n.delay_off);
                for d in &mut n.declarators {
                    self.unpacked(&mut d.dimensions);
                    self.opt(&mut d.init);
                }
            }
            ModuleItem::DataDeclaration(d) => {
                self.dtype(&mut d.data_type);
                self.declarators(&mut d.declarators);
            }
            ModuleItem::ParameterDeclaration(p) | ModuleItem::LocalparamDeclaration(p) => {
                self.param_decl(p)
            }
            ModuleItem::TypedefDeclaration(td) => {
                if (td.forward || matches!(td.data_type, DataType::Void(_)))
                    && self.info.hiding.contains(&td.name.name)
                    && let Res::To(named) = self.resolve(&td.name.name)
                {
                    td.name.name = named;
                }
                self.dtype(&mut td.data_type);
                self.unpacked(&mut td.dimensions);
            }
            ModuleItem::AlwaysConstruct(a) => self.body(&mut a.stmt),
            ModuleItem::InitialConstruct(i) => self.body(&mut i.stmt),
            ModuleItem::FinalConstruct(f) => self.body(&mut f.stmt),
            ModuleItem::ContinuousAssign(ca) => {
                self.opt(&mut ca.delay);
                self.opt(&mut ca.delay_fall);
                self.opt(&mut ca.delay_off);
                for (l, r) in &mut ca.assignments {
                    self.expr(l);
                    self.expr(r);
                }
            }
            ModuleItem::ModuleInstantiation(mi) => self.instantiation(mi),
            ModuleItem::GateInstantiation(g) => {
                self.opt(&mut g.delay);
                self.opt(&mut g.delay_fall);
                for i in &mut g.instances {
                    i.terminals.iter_mut().for_each(|t| self.expr(t));
                }
            }
            ModuleItem::GenerateRegion(g) => g.items.iter_mut().for_each(|i| self.module_item(i)),
            ModuleItem::GenerateIf(g) => {
                for (c, items) in &mut g.branches {
                    self.in_const += 1;
                    self.opt(c);
                    self.in_const -= 1;
                    self.generate_body(items);
                }
            }
            ModuleItem::GenerateFor(g) => {
                let mut frame = Frame::default();
                frame.values.insert(g.var.clone());
                self.frames.push(frame);
                self.in_const += 1;
                self.opt(&mut g.init);
                self.expr(&mut g.cond);
                self.expr(&mut g.incr);
                self.in_const -= 1;
                self.generate_body(&mut g.items);
                self.frames.pop();
            }
            ModuleItem::GenerateCase(g) => {
                self.in_const += 1;
                self.expr(&mut g.selector);
                for a in &mut g.arms {
                    a.values.iter_mut().for_each(|v| self.expr(v));
                }
                self.in_const -= 1;
                for a in &mut g.arms {
                    self.generate_body(&mut a.items);
                }
            }
            ModuleItem::FunctionDeclaration(f) => self.function(f),
            ModuleItem::TaskDeclaration(t) => self.task(t),
            ModuleItem::ImportDeclaration(imp) => self.import_decl(imp),
            ModuleItem::ClassDeclaration(c) => {
                if self.info.hiding.contains(&c.name.name)
                    && let Res::To(named) = self.resolve(&c.name.name)
                {
                    c.name.name = named.clone();
                    if let Some(end) = &mut c.endlabel {
                        end.name = named;
                    }
                }
                self.class(c)
            }
            ModuleItem::AssertionItem(a) => self.assertion(a),
            ModuleItem::PropertyDeclaration(p) => {
                p.items.iter_mut().for_each(|s| self.stmt(s));
                self.opt(&mut p.body);
            }
            ModuleItem::SequenceDeclaration(p) => {
                p.items.iter_mut().for_each(|s| self.stmt(s));
                self.opt(&mut p.body);
            }
            ModuleItem::CovergroupDeclaration(cg) => self.covergroup(cg),
            ModuleItem::ClockingDeclaration(cd) => {
                self.opt(&mut cd.default_input_skew);
                self.opt(&mut cd.default_output_skew);
                for s in &mut cd.signals {
                    self.opt(&mut s.skew);
                    self.opt(&mut s.bound_to);
                }
                cd.items.iter_mut().for_each(|s| self.stmt(s));
            }
            ModuleItem::CheckerDeclaration(cd) => {
                let mut f = Frame::default();
                module_item_names(&cd.items, &mut f);
                self.frames.push(f);
                cd.items.iter_mut().for_each(|i| self.module_item(i));
                self.frames.pop();
            }
            ModuleItem::LetDeclaration(l) => self.expr(&mut l.expr),
            ModuleItem::NettypeDeclaration(n) => self.dtype(&mut n.data_type),
            ModuleItem::DPIImport(d) => self.dpi(&mut d.proto),
            ModuleItem::DPIExport(d) => self.dpi(&mut d.proto),
            ModuleItem::OutOfClassConstraint {
                class_name, items, ..
            } => {
                self.class_name_string(class_name);
                items.iter_mut().for_each(|i| self.constraint(i));
            }
            ModuleItem::Bind(b) => self.instantiation(&mut b.instantiation),
            ModuleItem::Defparam(v) => {
                for (a, b) in v {
                    self.expr(a);
                    self.expr(b);
                }
            }
            ModuleItem::NestedModule(m) => {
                let m = &mut **m;
                self.module_body(&m.name.name, &mut m.params, &mut m.ports, &mut m.items);
            }
            ModuleItem::AliasDecl(v) => v.iter_mut().for_each(|x| self.expr(x)),
            ModuleItem::GenvarDeclaration(_)
            | ModuleItem::TimeunitsDecl(_)
            | ModuleItem::ModportDeclaration(_)
            | ModuleItem::SpecifyBlock(_)
            | ModuleItem::Null => {}
        }
    }

    /// §27: each generate block owns its declarations, not its parent.
    fn generate_body(&mut self, items: &mut [ModuleItem]) {
        let mut frame = Frame::default();
        self.module_class_bindings(items, &mut frame);
        module_item_names(items, &mut frame);
        self.frames.push(frame);
        items.iter_mut().for_each(|item| self.module_item(item));
        self.frames.pop();
    }

    fn module_class_bindings(&self, items: &[ModuleItem], frame: &mut Frame) {
        let Some(owner) = self.frames.iter().rev().find_map(|f| f.module.as_deref()) else {
            return;
        };
        for item in items {
            if let ModuleItem::ClassDeclaration(c) = item
                && self.info.hiding.contains(&c.name.name)
            {
                frame
                    .module_classes
                    .insert(c.name.name.clone(), self.info.module_class_name(owner, c));
            }
        }
    }

    fn class_name_string(&mut self, s: &mut String) {
        let mut id = crate::ast::Identifier {
            name: std::mem::take(s),
            span: crate::ast::Span { start: 0, end: 0 },
        };
        self.type_ident(&mut id);
        *s = id.name;
    }

    /// A package item; `pkg` is the enclosing package (None at `$unit`).
    fn package_item(&mut self, pkg: Option<&str>, it: &mut PackageItem) {
        let renamed = |n: &str| -> Option<String> {
            let p = pkg?;
            self.info.colliding.contains(n).then(|| mangle(p, n))
        };
        match it {
            PackageItem::Parameter(pd) => self.param_decl(pd),
            PackageItem::Typedef(td) => {
                if let Some(m) = renamed(&td.name.name) {
                    td.name.name = m;
                }
                self.dtype(&mut td.data_type);
                self.unpacked(&mut td.dimensions);
            }
            PackageItem::Function(f) => self.function(f),
            PackageItem::Task(t) => self.task(t),
            PackageItem::Import(imp) | PackageItem::Export(imp) => self.import_decl(imp),
            PackageItem::DPIImport(d) => self.dpi(&mut d.proto),
            PackageItem::DPIExport(d) => self.dpi(&mut d.proto),
            PackageItem::Data(dd) => {
                self.dtype(&mut dd.data_type);
                self.declarators(&mut dd.declarators);
                if let Some(p) = pkg {
                    for d in &mut dd.declarators {
                        if self.info.mangled_vars.contains(&d.name.name) {
                            d.name.name = mangle(p, &d.name.name);
                        }
                    }
                }
            }
            PackageItem::Net(nd) => {
                self.dtype(&mut nd.data_type);
                for d in &mut nd.declarators {
                    self.unpacked(&mut d.dimensions);
                    self.opt(&mut d.init);
                    if let Some(p) = pkg {
                        if self.info.mangled_vars.contains(&d.name.name) {
                            d.name.name = mangle(p, &d.name.name);
                        }
                    }
                }
            }
            PackageItem::Class(c) => {
                if let Some(m) = renamed(&c.name.name) {
                    if let Some(l) = &mut c.endlabel {
                        l.name = m.clone();
                    }
                    c.name.name = m;
                }
                self.class(c);
            }
            PackageItem::Checker(cd) => {
                let mut f = Frame::default();
                module_item_names(&cd.items, &mut f);
                self.frames.push(f);
                cd.items.iter_mut().for_each(|i| self.module_item(i));
                self.frames.pop();
            }
            PackageItem::Let(l) => self.expr(&mut l.expr),
            PackageItem::Nettype(n) => self.dtype(&mut n.data_type),
            PackageItem::Property(p) => {
                p.items.iter_mut().for_each(|s| self.stmt(s));
                self.opt(&mut p.body);
            }
            PackageItem::Sequence(p) => {
                p.items.iter_mut().for_each(|s| self.stmt(s));
                self.opt(&mut p.body);
            }
            PackageItem::Covergroup(cg) => {
                if let Some(m) = renamed(&cg.name.name) {
                    cg.name.name = m;
                }
                self.covergroup(cg)
            }
            PackageItem::Null | PackageItem::TimeunitsDecl(_) => {}
        }
    }

    /// A `$unit` import, added to the compilation-unit frame where the walk
    /// reaches it.
    fn unit_import(&mut self, imp: &ImportDeclaration) {
        if let Some(unit) = self.frames.first_mut() {
            unit.add_imports(imp);
        }
    }

    fn description(&mut self, d: &mut Description) {
        match d {
            Description::Module(m) => {
                self.module_body(&m.name.name, &mut m.params, &mut m.ports, &mut m.items)
            }
            Description::Interface(m) => {
                self.module_body(&m.name.name, &mut m.params, &mut m.ports, &mut m.items)
            }
            Description::Program(m) => {
                self.module_body(&m.name.name, &mut m.params, &mut m.ports, &mut m.items)
            }
            Description::Package(p) => {
                // A package sees its own declarations and imports, not the
                // compilation unit's imports.
                let saved = std::mem::take(&mut self.frames);
                let mut f = Frame {
                    pkg: Some(p.name.name.clone()),
                    ..Frame::default()
                };
                for it in &p.items {
                    if let PackageItem::Import(imp) = it {
                        f.add_imports(imp);
                    }
                    package_item_values(it, &mut f.values);
                }
                self.frames.push(f);
                let pn = p.name.name.clone();
                p.items
                    .iter_mut()
                    .for_each(|it| self.package_item(Some(&pn), it));
                self.frames = saved;
            }
            Description::Class(c) => self.class(c),
            Description::TypedefDecl(td) => {
                self.dtype(&mut td.data_type);
                self.unpacked(&mut td.dimensions);
            }
            Description::ImportDecl(imp) => {
                self.import_decl(imp);
                self.unit_import(imp);
            }
            Description::PackageItem(pi) => {
                self.package_item(None, pi);
                if let PackageItem::Import(imp) = pi {
                    self.unit_import(imp);
                }
            }
            Description::DPIImport(di) => self.dpi(&mut di.proto),
            Description::DPIExport(de) => self.dpi(&mut de.proto),
            Description::Bind(b) => self.instantiation(&mut b.instantiation),
            Description::OutOfClassConstraint {
                class_name, items, ..
            } => {
                self.class_name_string(class_name);
                items.iter_mut().for_each(|i| self.constraint(i));
            }
            Description::TimeunitsDecl(_) | Description::Udp(_) => {}
        }
    }
}

/// Names a module-like scope declares: types (typedefs, classes, type
/// parameters) and values (everything else that can be named in an
/// expression), plus its imports.
fn module_item_names(items: &[ModuleItem], f: &mut Frame) {
    for it in items {
        match it {
            ModuleItem::PortDeclaration(p) => f
                .values
                .extend(p.declarators.iter().map(|d| d.name.name.clone())),
            ModuleItem::NetDeclaration(n) => f
                .values
                .extend(n.declarators.iter().map(|d| d.name.name.clone())),
            ModuleItem::DataDeclaration(d) => {
                f.values
                    .extend(d.declarators.iter().map(|d| d.name.name.clone()));
                enum_members(&d.data_type, &mut f.values);
            }
            ModuleItem::ParameterDeclaration(p) | ModuleItem::LocalparamDeclaration(p) => {
                param_names(p, &mut f.types, &mut f.values)
            }
            ModuleItem::TypedefDeclaration(td) => {
                f.types.insert(td.name.name.clone());
                enum_members(&td.data_type, &mut f.values);
            }
            ModuleItem::ClassDeclaration(c) => {
                f.types.insert(c.name.name.clone());
            }
            ModuleItem::ModuleInstantiation(mi) => f
                .values
                .extend(mi.instances.iter().map(|i| i.name.name.clone())),
            ModuleItem::GenvarDeclaration(g) => {
                f.values.extend(g.names.iter().map(|n| n.name.clone()))
            }
            ModuleItem::FunctionDeclaration(fd) => {
                f.values.insert(fd.name.name.name.clone());
            }
            ModuleItem::TaskDeclaration(td) => {
                f.values.insert(td.name.name.name.clone());
            }
            ModuleItem::DPIImport(di) => {
                f.values.insert(match &di.proto {
                    DPIProto::Function(fd) => fd.name.name.name.clone(),
                    DPIProto::Task(td) => td.name.name.name.clone(),
                });
            }
            ModuleItem::LetDeclaration(l) => {
                f.values.insert(l.name.name.clone());
            }
            ModuleItem::ImportDeclaration(imp) => f.add_imports(imp),
            ModuleItem::GenerateRegion(g) => module_item_names(&g.items, f),
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn module_items(source: &str) -> Vec<ModuleItem> {
        let mut parsed = crate::parse(source);
        assert!(parsed.errors.is_empty(), "{:?}", parsed.errors);
        qualify_colliding_package_types(&mut parsed.source.descriptions).unwrap();
        parsed
            .source
            .descriptions
            .into_iter()
            .find_map(|d| match d {
                Description::Module(m) => Some(m.items),
                _ => None,
            })
            .unwrap()
    }

    fn declared_type(stmt: &Statement) -> &str {
        let StatementKind::VarDecl {
            data_type: DataType::TypeReference { name, .. },
            ..
        } = &stmt.kind
        else {
            panic!("expected a named-type variable declaration: {stmt:?}");
        };
        &name.name.name
    }

    /// §23.9/§26.3: a child block's typedef cannot hide an outer import.
    #[test]
    fn child_typedef_does_not_shadow_enclosing_or_sibling_statements() {
        let items = module_items(
            r#"
package copper; typedef bit [3:0] word_t; endpackage
package silver; typedef bit [7:0] word_t; endpackage
module scope_probe;
  import copper::*;
  initial begin
    word_t first;
    begin
      typedef bit [1:0] word_t;
      word_t inner;
    end
    begin word_t sibling; end
  end
  function void report();
    word_t first;
    begin typedef bit [1:0] word_t; word_t inner; end
    begin word_t sibling; end
  endfunction
endmodule
"#,
        );
        for item in items {
            let stmts = match item {
                ModuleItem::InitialConstruct(i) => match i.stmt.kind {
                    StatementKind::SeqBlock { stmts, .. } => stmts,
                    _ => panic!("expected a block"),
                },
                ModuleItem::FunctionDeclaration(f) => f.items.into_vec(),
                _ => continue,
            };
            assert_eq!(declared_type(&stmts[0]), "copper::word_t");
            let StatementKind::SeqBlock { stmts: inner, .. } = &stmts[1].kind else {
                panic!("expected a child block");
            };
            assert_eq!(declared_type(&inner[1]), "word_t");
            let StatementKind::SeqBlock { stmts: sibling, .. } = &stmts[2].kind else {
                panic!("expected a sibling block");
            };
            assert_eq!(declared_type(&sibling[0]), "copper::word_t");
        }
    }

    /// §27/§26.3: generate-local typedefs must not hide a parent import.
    #[test]
    fn generate_declarations_stay_in_their_own_scope() {
        let items = module_items(
            r#"
package copper; typedef bit [3:0] word_t; endpackage
package silver; typedef bit [7:0] word_t; endpackage
module scope_probe;
  import copper::*;
  word_t outer_word;
  if (1) begin : local_bank
    typedef bit [1:0] word_t;
    word_t inner_word;
  end
  if (1) begin : imported_bank
    word_t sibling_word;
  end
  for (genvar index = 0; index < $bits(word_t); index++) begin : loop_bank
    typedef bit [1:0] word_t;
    word_t loop_word;
  end
  case (1) 1: begin : chosen_bank word_t case_word; end endcase
endmodule
"#,
        );
        fn declarations(items: &[ModuleItem], out: &mut Vec<(String, String)>) {
            for item in items {
                match item {
                    ModuleItem::DataDeclaration(d) => {
                        let DataType::TypeReference { name, .. } = &d.data_type else {
                            continue;
                        };
                        for decl in &d.declarators {
                            out.push((decl.name.name.clone(), name.name.name.clone()));
                        }
                    }
                    ModuleItem::GenerateRegion(g) => declarations(&g.items, out),
                    ModuleItem::GenerateIf(g) => {
                        for (_, items) in &g.branches {
                            declarations(items, out);
                        }
                    }
                    ModuleItem::GenerateFor(g) => {
                        let ExprKind::Binary { right, .. } = &g.cond.kind else {
                            panic!("expected a loop bound");
                        };
                        let ExprKind::SystemCall { args, .. } = &right.kind else {
                            panic!("expected a type query");
                        };
                        assert_eq!(plain_ident(&args[0]), Some("copper::word_t"));
                        declarations(&g.items, out);
                    }
                    ModuleItem::GenerateCase(g) => {
                        for arm in &g.arms {
                            declarations(&arm.items, out);
                        }
                    }
                    _ => {}
                }
            }
        }
        let mut got = Vec::new();
        declarations(&items, &mut got);
        let expected = [
            ("outer_word", "copper::word_t"),
            ("inner_word", "word_t"),
            ("sibling_word", "copper::word_t"),
            ("loop_word", "word_t"),
            ("case_word", "copper::word_t"),
        ];
        assert_eq!(
            got,
            expected.map(|(name, ty)| (name.to_string(), ty.to_string()))
        );
    }

    /// The packages each module's `mode_t` resolves to, in module order.
    fn module_mode_owners(source: &str) -> Result<Vec<String>, String> {
        let mut parsed = crate::parse(source);
        assert!(parsed.errors.is_empty(), "{:?}", parsed.errors);
        qualify_colliding_package_types(&mut parsed.source.descriptions)?;
        Ok(parsed
            .source
            .descriptions
            .iter()
            .filter_map(|d| match d {
                Description::Module(m) => {
                    let text = format!("{:?}", m.items);
                    Some(
                        ["pkg_one", "pkg_two"]
                            .into_iter()
                            .find(|p| text.contains(&format!("\"{p}::mode_t\"")))
                            .unwrap_or("none")
                            .to_string(),
                    )
                }
                _ => None,
            })
            .collect())
    }

    const MODE_PKGS: &str = "package pkg_one; typedef enum logic [1:0] { A1 } mode_t; endpackage\n\
                             package pkg_two; typedef enum logic [3:0] { B1 } mode_t; endpackage\n";

    /// §26.3 (#620): a `$unit` wildcard import counts from where it appears,
    /// and the first reference that finds a name through one makes it locally
    /// visible: a later wildcard import of another package declaring it does
    /// not change it, and the order of the imports decides.
    #[test]
    fn unit_wildcard_binds_at_the_first_reference() {
        let a = "import pkg_one::*;\nmodule probe_a; mode_t m; endmodule\n";
        let b = "import pkg_two::*;\nmodule probe_b; mode_t m; endmodule\n";
        let c = "module probe_c; mode_t m; endmodule\n";
        assert_eq!(
            module_mode_owners(&format!("{MODE_PKGS}{a}{b}{c}")).unwrap(),
            ["pkg_one", "pkg_one", "pkg_one"]
        );
        assert_eq!(
            module_mode_owners(&format!("{MODE_PKGS}{b}{a}{c}")).unwrap(),
            ["pkg_two", "pkg_two", "pkg_two"]
        );
    }

    /// §26.3: both wildcard imports before the first reference, in `$unit`
    /// or in the module, still make the name ambiguous.
    #[test]
    fn two_wildcard_imports_before_a_reference_conflict() {
        for src in [
            "import pkg_one::*;\nimport pkg_two::*;\nmodule t; mode_t m; endmodule\n",
            "module t; import pkg_one::*; import pkg_two::*; mode_t m; endmodule\n",
        ] {
            let err = module_mode_owners(&format!("{MODE_PKGS}{src}")).unwrap_err();
            assert!(err.contains("more than one wildcard-imported package"), "{err}");
        }
    }

}
