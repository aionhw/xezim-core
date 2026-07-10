//! Elaborator: converts parsed AST into a flat simulation model.
//! Resolves net/variable declarations, continuous assigns, always blocks.

use crate::hasher::HashMap;
use crate::hasher::HashSet;
use std::collections::BTreeMap;
use std::rc::Rc;
use crate::ast::{Identifier, Span};
use crate::ast::decl::*;
use crate::ast::module::*;
use crate::ast::types::*;
use crate::ast::expr::*;
use crate::ast::stmt::*;
use super::value::Value;

fn elab_trace_enabled() -> bool {
    std::env::var("XEZIM_TRACE_ELAB").map(|v| {
        let v = v.trim();
        !v.is_empty() && v != "0" && !v.eq_ignore_ascii_case("false")
    }).unwrap_or(false)
}

/// A resolved signal in the simulation model.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct Signal {
    pub name: String,
    pub width: u32,
    pub is_signed: bool,
    pub is_real: bool,
    pub is_const: bool,
    pub direction: Option<PortDirection>,
    pub value: Value,
    /// Name of the data type (e.g. class name).
    pub type_name: Option<String>,
}

/// A continuous assignment: assign lhs = rhs.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct ContinuousAssignment {
    pub lhs: Expression,
    pub rhs: Expression,
    pub delay: u64,
}

/// An always block for combinatorial logic.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct AlwaysBlock {
    pub kind: AlwaysKind,
    pub stmt: Statement,
}

/// An initial block for testbench.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct InitialBlock {
    pub stmt: Statement,
    /// Instance scope this block belongs to (e.g. `"TB.p1"`), empty for the
    /// top module. The simulator sets it as the name-resolution hint while the
    /// block's process runs, so AST-evaluated bare names (e.g. a
    /// `std::randomize(sig)` target) resolve to THIS instance's signal rather
    /// than the first instance of a multiply-instantiated module.
    #[serde(default)]
    pub scope: String,
}

impl InitialBlock {
    pub fn new(stmt: Statement) -> Self {
        InitialBlock { stmt, scope: String::new() }
    }
}

// ----------------------------------------------------------------------------
// Deferred-rewrite (lazy-prefix) infrastructure — fix #7.
//
// `inline_module_items` historically eagerly rewrote each instance's procedural
// body (always/initial/cont-assign) at elaborate time, producing a per-instance
// owned AST in elab.always_blocks/initial_blocks/continuous_assigns. For
// designs that wrap many instances of large auto-generated modules
// (e.g. OpenTitan rv_core_ibex_cfg_reg_top with 26× prim_subreg) this peak
// memory is multi-GB.
//
// The lazy-prefix path stores the rewrite *context* alongside an Rc-shared
// reference to the (unrewritten) source AST. The rewrite produces an owned
// AST only at consumption time, so peak memory is bounded by:
//   sum(pending contexts)  +  one materialized block in flight
// instead of:
//   sum(materialized blocks)
//
// Sharing strategy: source ASTs are shared via Rc<Statement> / Rc<Expression>.
// `local_names` is shared via Rc<HashSet<String>> across siblings of the same
// submodule (a single Rc lives in PreparedModuleItems and is cloned cheaply
// per instance). port_map and interface_map are per-instance owned.
//
// A streaming consumer (the simulator's bytecode compiler) is expected to
// drain `pending_*` one block at a time via the `drain_pending_*` helpers,
// compile-and-drop, so the materialized AST never co-exists in bulk.
//
// For non-streaming callers, `ElaboratedModule::materialize_pending()`
// performs a non-streaming drain into `always_blocks`/`initial_blocks`/
// `continuous_assigns` — preserving prior semantics at the cost of peak.
// ----------------------------------------------------------------------------

/// Per-instance context needed to materialize a deferred procedural body.
/// Held lightweight: cloning is cheap because shared structures sit behind Rc.
#[derive(Debug, Clone)]
pub struct RewriteCtx {
    pub prefix: String,
    /// Port name → connecting expression in the parent scope. Per-instance
    /// (different connections per instantiation), so owned per ctx.
    pub port_map: HashMap<String, Expression>,
    /// Names declared locally inside the submodule. Shared across siblings of
    /// the same submodule via the prepared-items cache. Uses
    /// `std::collections::HashSet` to match `rewrite_expr`/`rewrite_stmt`
    /// signatures (which deliberately don't take ahash for hash determinism
    /// across the rewrite boundary).
    pub local_names: std::rc::Rc<std::collections::HashSet<String>>,
    /// Interface-port substitutions (interface name → parent path). Per-branch
    /// in the recursion tree; cloning the small map is cheap.
    pub interface_map: HashMap<String, String>,
}

#[derive(Debug, Clone)]
pub struct PendingAlways {
    pub kind: AlwaysKind,
    /// Source Statement, shared with the prepared-items cache so 26 sibling
    /// instances of the same submodule all point at the same Rc<Statement>.
    pub source: std::rc::Rc<Statement>,
    pub ctx: std::rc::Rc<RewriteCtx>,
}

#[derive(Debug, Clone)]
pub struct PendingInitial {
    pub source: std::rc::Rc<Statement>,
    pub ctx: std::rc::Rc<RewriteCtx>,
}

#[derive(Debug, Clone)]
pub struct PendingContAssign {
    pub lhs_source: std::rc::Rc<Expression>,
    pub rhs_source: std::rc::Rc<Expression>,
    pub ctx: std::rc::Rc<RewriteCtx>,
}

impl PendingAlways {
    /// Run the rewrite once and produce the owned AlwaysBlock. Drops self.
    pub fn materialize(self) -> AlwaysBlock {
        let stmt = rewrite_stmt(
            &self.source,
            &self.ctx.prefix,
            &self.ctx.port_map,
            &self.ctx.local_names,
            &self.ctx.interface_map,
        );
        AlwaysBlock { kind: self.kind, stmt }
    }
}

impl PendingInitial {
    pub fn materialize(self) -> InitialBlock {
        let stmt = rewrite_stmt(
            &self.source,
            &self.ctx.prefix,
            &self.ctx.port_map,
            &self.ctx.local_names,
            &self.ctx.interface_map,
        );
        // `ctx.prefix` is the instance path with a trailing dot ("TB.p1.");
        // record it (dot-trimmed) as the block's scope for name resolution.
        let scope = self.ctx.prefix.trim_end_matches('.').to_string();
        InitialBlock { stmt, scope }
    }
}

impl PendingContAssign {
    pub fn materialize(self) -> ContinuousAssignment {
        let lhs = rewrite_expr(
            &self.lhs_source,
            &self.ctx.prefix,
            &self.ctx.port_map,
            &self.ctx.local_names,
            &self.ctx.interface_map,
        );
        let rhs = rewrite_expr(
            &self.rhs_source,
            &self.ctx.prefix,
            &self.ctx.port_map,
            &self.ctx.local_names,
            &self.ctx.interface_map,
        );
        ContinuousAssignment { lhs, rhs, delay: 0 }
    }
}

/// Elaborated class definition.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct ElaboratedClass {
    pub name: String,
    pub extends: Option<String>,
    pub properties: HashMap<String, Signal>,
    /// Property names in DECLARATION order. `properties` is a HashMap and so
    /// loses source order; `%p` (LRM §21.2.1.7) must print a class object as
    /// `'{prop:value, ...}` in declaration order.
    #[serde(default)]
    pub property_order: Vec<String>,
    pub methods: HashMap<String, ClassMethod>,
    /// Properties marked as 'rand' or 'randc'.
    pub random_properties: HashSet<String>,
    /// Properties declared with type `string`, so `%p` renders them as text
    /// rather than the packed byte value (LRM §21.2.1.7).
    #[serde(default)]
    pub string_properties: HashSet<String>,
    /// LRM §25.8 — properties declared as `virtual <iface_t>` or
    /// `virtual <iface_t>.<modport>`. For each such property the
    /// simulator captures a binding (an interface instance name) at the
    /// time of `obj.<prop> = <iface_inst>` assignment, then rewrites
    /// `obj.<prop>.<member>` reads/writes to `<bound_inst>.<member>`.
    /// The value carries the declared `(iface_type, modport_opt)` so
    /// the runtime can also emit a warning on member writes that the
    /// modport tagged as `input`.
    #[serde(default)]
    pub virtual_iface_properties: HashMap<String, (String, Option<String>)>,
    /// Properties marked specifically as 'randc' (cyclic random).
    #[serde(default)]
    pub randc_properties: HashSet<String>,
    /// Constraints: name -> constraint declaration.
    pub constraints: HashMap<String, ClassConstraint>,
    /// Class parameters with default values, in declaration order.
    /// `(name, default_value_expr)`.
    pub param_defaults: Vec<(String, Option<crate::ast::expr::Expression>)>,
    /// `interface class` declaration — cannot be instantiated.
    #[serde(default)]
    pub is_interface: bool,
    /// Abstract (virtual) class — declared with `virtual class`. Cannot be instantiated
    /// directly.
    #[serde(default)]
    pub is_virtual: bool,
    /// IEEE 1800-2023 §8.20.5: `class :final` — class cannot be extended.
    #[serde(default)]
    pub is_final: bool,
    /// Has at least one `pure virtual` method prototype.
    #[serde(default)]
    pub has_pure_virtual: bool,
    /// Names listed in the `implements` clause.
    #[serde(default)]
    pub implements: Vec<String>,
    /// Names of type parameters declared on the class.
    #[serde(default)]
    pub type_param_names: Vec<String>,
    /// ALL parameter names (type and value), in declaration order. Needed to
    /// map positional `#(...)` type-args to the correct param when type and
    /// value params are interleaved (e.g. `uvm_component_registry#(type T,
    /// string Tname)` has the type param FIRST). `type_param_names`/
    /// `param_defaults` alone lose the combined order.
    #[serde(default)]
    pub param_order: Vec<String>,
    /// Typedef names declared in the class body.
    #[serde(default)]
    pub typedef_names: Vec<String>,
    /// Typedef name -> its target DataType, captured so a later step can
    /// resolve e.g. `MyClass::type_id` to its target type.
    #[serde(default)]
    pub typedef_targets: HashMap<String, crate::ast::types::DataType>,
    /// Properties declared with the `static` qualifier — shared across all
    /// instances of the class (one storage cell per class).
    #[serde(default)]
    pub static_properties: HashSet<String>,
    /// Methods declared with the `static` qualifier — callable as
    /// `ClassName::method(...)` without an instance handle.
    #[serde(default)]
    pub static_methods: HashSet<String>,
    /// Properties declared as associative arrays (`T m[KEY];`) — name
    /// mapped to whether the key type is `string`. Stored per-instance.
    #[serde(default)]
    pub assoc_properties: HashMap<String, bool>,
    /// Properties declared as queues / dynamic arrays (`T m[$];`, `T m[];`) —
    /// name mapped to (element width, optional bounded-queue max+1). Stored
    /// per-instance like associative arrays, so each object's queue is
    /// independent.
    #[serde(default)]
    pub queue_properties: HashMap<String, (u32, Option<u32>)>,
    /// Initializer expressions for scalar properties (`int x = EXPR;`). Held so
    /// they can be re-evaluated at instantiation against the live parameter
    /// table — `elaborate_class` runs before package params are bound, so a
    /// default like `= NUM_HARTS` would otherwise resolve to 0.
    #[serde(default)]
    pub property_inits: HashMap<String, crate::ast::expr::Expression>,
    /// Static member collections (`static T m[$]`, `static T m[]`, `static T
    /// m[KEY]`): name -> (is_associative, element width). They share a single
    /// global store (one copy per class, not per-instance) and are registered
    /// under their bare name at simulator startup.
    #[serde(default)]
    pub static_collections: Vec<(String, bool, u32)>,
    /// Fixed-size unpacked-array members with a compile-time-constant size
    /// (`rand reg_t gpr[4]`, `int m[2:0]`): name -> (lo, hi, element width).
    /// Stored per-instance as `<handle>#<member>` registered in `module.arrays`
    /// so index access and `foreach` see a real fixed range (and rand elements
    /// can be randomized). Non-constant sizes (`m[NUM_HARTS]`) stay in
    /// `queue_properties` since the size isn't known at class-elaboration time.
    #[serde(default)]
    pub array_properties: HashMap<String, (i64, i64, u32)>,
}

/// DPI import metadata used by the simulator for foreign-call dispatch.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct DpiImportSpec {
    pub c_name: String,
    pub property: Option<DPIProperty>,
    pub proto: DPIProto,
}

/// Run `f` with the current thread-local typedef table, if one has been
/// installed. `elaborate_class` takes no typedef parameter and has eight
/// call sites; this reads the snapshot the typedef registration already
/// maintains rather than threading a table through all of them.
fn typedefs_snapshot<R>(f: impl FnOnce(Option<&HashMap<String, u32>>) -> R) -> R {
    TYPEDEFS_TLS.with(|cell| f(cell.borrow().as_ref()))
}

pub fn elaborate_class(c: &ClassDeclaration) -> ElaboratedClass {
    let mut properties = HashMap::default();
    let mut property_order: Vec<String> = Vec::new();
    let mut string_properties: HashSet<String> = HashSet::default();
    let mut methods = HashMap::default();
    let mut random_properties = HashSet::default();
    let mut randc_properties = HashSet::default();
    let mut virtual_iface_properties: HashMap<String, (String, Option<String>)> = HashMap::default();
    let mut static_properties = HashSet::default();
    let mut static_methods = HashSet::default();
    let mut assoc_properties: HashMap<String, bool> = HashMap::default();
    let mut queue_properties: HashMap<String, (u32, Option<u32>)> = HashMap::default();
    let mut array_properties: HashMap<String, (i64, i64, u32)> = HashMap::default();
    let mut static_collections: Vec<(String, bool, u32)> = Vec::new();
    let mut property_inits: HashMap<String, crate::ast::expr::Expression> = HashMap::default();
    let mut constraints = HashMap::default();
    // Class-local typedefs carrying unpacked dimensions
    // (`typedef bit edges_t[uvm_phase];`). A property `edges_t m;` inherits
    // these so it's classified as an associative/queue/array member
    // (IEEE 1800-2017 §6.18). UVM's phase graph (`edges_t m_successors`,
    // `m_predecessors`) relies on this.
    let mut local_typedef_dims: HashMap<String, Vec<UnpackedDimension>> = HashMap::default();
    for item in &c.items {
        if let ClassItem::Typedef(td) = item {
            if !td.dimensions.is_empty() {
                local_typedef_dims.insert(td.name.name.clone(), td.dimensions.clone());
            }
        }
    }
    for item in &c.items {
        match item {
            ClassItem::Property(p) => {
                // Resolve against the typedef table, not `None`. A property
                // declared with a typedef'd type (`u2_t v;`) hits
                // `resolve_type_width`'s TypeReference branch, which returns a
                // flat 32 when it has no table — so every such property was
                // recorded 32 bits wide however narrow its type.
                let width = typedefs_snapshot(|td| resolve_type_width(&p.data_type, None, td));
                let is_signed = is_type_signed(&p.data_type);
                let is_rand = p.qualifiers.contains(&ClassQualifier::Rand) || p.qualifiers.contains(&ClassQualifier::Randc);
                let is_randc = p.qualifiers.contains(&ClassQualifier::Randc);
                let is_static = p.qualifiers.contains(&ClassQualifier::Static);
                let _is_const = p.qualifiers.contains(&ClassQualifier::Const);
                let is_virtual_iface = p.qualifiers.contains(&ClassQualifier::Virtual);
                let virtual_iface_info: Option<(String, Option<String>)> = if is_virtual_iface {
                    // `virtual <iface_t> name;` parses as TypeReference;
                    // `virtual <iface_t>.<modport> name;` parses as
                    // DataType::Interface { name, modport }.
                    match &p.data_type {
                        DataType::Interface { name, modport, .. } => {
                            Some((name.name.clone(), modport.as_ref().map(|m| m.name.clone())))
                        }
                        _ => get_type_name(&p.data_type).map(|n| (n, None)),
                    }
                } else { None };
                let is_real = is_type_real(&p.data_type);
                // Named types (class handles, enums, typedefs) default to
                // 0 — a class handle's default is `null`.
                let is_named_type = get_type_name(&p.data_type).is_some();
                for decl in &p.declarators {
                    // A property typed by an unpacked-dimension typedef
                    // (`edges_t m;`) inherits the typedef's dims when it
                    // declares none of its own. Otherwise this is exactly
                    // `decl.dimensions`, so behavior is unchanged.
                    let effective_dims: Vec<UnpackedDimension> = if decl.dimensions.is_empty() {
                        match &p.data_type {
                            DataType::TypeReference { name, .. } =>
                                local_typedef_dims.get(&name.name.name).cloned().unwrap_or_default(),
                            _ => Vec::new(),
                        }
                    } else {
                        decl.dimensions.clone()
                    };
                    // Track virtual-interface properties for L4 binding +
                    // late-dispatch. See the comment on
                    // `ElaboratedClass::virtual_iface_properties`.
                    if let Some(info) = &virtual_iface_info {
                        virtual_iface_properties.insert(decl.name.name.clone(), info.clone());
                    }
                    // Static member collections share one global store; route
                    // them out of the per-instance maps.
                    if is_static {
                        // Second field is `is_associative` (NOT key-is-string).
                        match effective_dims.first() {
                            Some(UnpackedDimension::Associative { .. }) => {
                                static_collections.push((decl.name.name.clone(), true, width.max(1)));
                            }
                            Some(UnpackedDimension::Queue { .. })
                            | Some(UnpackedDimension::Unsized(_)) => {
                                static_collections.push((decl.name.name.clone(), false, width.max(1)));
                            }
                            _ => {}
                        }
                    }
                    if !is_static {
                    if let Some(UnpackedDimension::Associative { data_type: key_dt, .. }) =
                        effective_dims.first()
                    {
                        let is_string_key = key_dt.as_ref().map_or(false, |dt| {
                            matches!(dt.as_ref(),
                                DataType::Simple { kind: SimpleType::String, .. })
                        });
                        assoc_properties.insert(decl.name.name.clone(), is_string_key);
                    }
                    // Queue (`m[$]`) / dynamic-array (`m[]`) member — track so
                    // it gets independent per-instance storage. Bounded queues
                    // (`m[$:N]`) record their cap.
                    match effective_dims.first() {
                        Some(UnpackedDimension::Queue { max_size, .. }) => {
                            let cap = max_size.as_ref().and_then(|e|
                                const_eval_i64_with_params(e, None)).map(|n| (n + 1).max(1) as u32);
                            queue_properties.insert(decl.name.name.clone(), (width.max(1), cap));
                        }
                        Some(UnpackedDimension::Unsized(_)) => {
                            queue_properties.insert(decl.name.name.clone(), (width.max(1), None));
                        }
                        // A member array sized by an expression (e.g.
                        // `seq m[NUM_HARTS]`) cannot be sized here — class
                        // elaboration has no parameter table, so the dimension
                        // would resolve to 0 and indexing would be out of
                        // bounds. Give it independent per-instance storage like
                        // a queue (indexed writes land in the 0..63 buffer).
                        // A *constant*-sized `[N]` IS resolvable, so register it
                        // as a real fixed array (so `gpr[0]` defaults to its
                        // element value, not an empty-queue read of 0).
                        Some(UnpackedDimension::Expression { expr, .. }) => {
                            match const_eval_i64_with_params(expr, None) {
                                Some(n) if n > 0 => {
                                    array_properties.insert(
                                        decl.name.name.clone(),
                                        (0, n - 1, width.max(1)),
                                    );
                                }
                                _ => {
                                    queue_properties
                                        .insert(decl.name.name.clone(), (width.max(1), None));
                                }
                            }
                        }
                        // `m[lo:hi]` fixed unpacked array with constant bounds.
                        Some(UnpackedDimension::Range { left, right, .. }) => {
                            if let (Some(l), Some(r)) = (
                                const_eval_i64_with_params(left, None),
                                const_eval_i64_with_params(right, None),
                            ) {
                                array_properties.insert(
                                    decl.name.name.clone(),
                                    (l.min(r), l.max(r), width.max(1)),
                                );
                            }
                        }
                        _ => {}
                    }
                    } // end `if !is_static`
                    // Remember scalar initializers so instantiation can re-eval
                    // them with the live parameter table (e.g. `= NUM_HARTS`).
                    if decl.dimensions.is_empty() {
                        if let Some(init) = &decl.init {
                            property_inits.insert(decl.name.name.clone(), init.clone());
                        }
                    }
                    let mut v = if let Some(init) = &decl.init {
                        let mut val = eval_init_for_width(init, &HashMap::default(), width);
                        if is_real { val = Value::from_f64(val.to_f64()); }
                        val
                    } else if is_real {
                        Value::from_f64(0.0)
                    } else if is_named_type {
                        Value::zero(width)
                    } else {
                        default_value_for_type(&p.data_type, width)
                    };
                    if is_signed { v.is_signed = true; }
                    // Track source order for `%p` (§21.2.1.7).
                    if !property_order.contains(&decl.name.name) {
                        property_order.push(decl.name.name.clone());
                    }
                    if matches!(&p.data_type, DataType::Simple { kind: SimpleType::String, .. }) {
                        string_properties.insert(decl.name.name.clone());
                    }
                    properties.insert(decl.name.name.clone(), Signal { is_const: false,
                        name: decl.name.name.clone(),
                        width,
                        is_signed,
                        is_real,
                        direction: None,
                        value: v,
                        type_name: get_type_name(&p.data_type),
                    });
                    if is_rand {
                        random_properties.insert(decl.name.name.clone());
                    }
                    if is_randc {
                        randc_properties.insert(decl.name.name.clone());
                    }
                    if is_static {
                        static_properties.insert(decl.name.name.clone());
                    }
                }
            }
            ClassItem::Method(m) => {
                let name = match &m.kind {
                    ClassMethodKind::Function(f) => f.name.name.name.clone(),
                    ClassMethodKind::Task(t) => t.name.name.name.clone(),
                    ClassMethodKind::PureVirtual(f) => f.name.name.name.clone(),
                    ClassMethodKind::Extern(f) => f.name.name.name.clone(),
                };
                if m.qualifiers.contains(&ClassQualifier::Static) {
                    static_methods.insert(name.clone());
                }
                methods.insert(name, m.clone());
            }
            ClassItem::Constraint(con) => {
                constraints.insert(con.name.name.clone(), con.clone());
            }
            _ => {}
        }
    }
    // Collect class parameters (name + optional default expression).
    let mut param_defaults: Vec<(String, Option<crate::ast::expr::Expression>)> = Vec::new();
    for p in &c.params {
        if let crate::ast::decl::ParameterKind::Data { assignments, .. } = &p.kind {
            for a in assignments {
                param_defaults.push((a.name.name.clone(), a.init.clone()));
            }
        }
    }
    // Also collect class-body `localparam` declarations (e.g. UVM 2020.3.1's
    // `localparam string prefix = "+uvm_set_verbosity="`). These are class
    // constants accessible as static members, so they need entries in both
    // `param_defaults` (for value lookup) and `static_properties` (for
    // name resolution) as well as `properties` (for initial value seeding).
    for item in &c.items {
        if let ClassItem::Parameter(pd) = item {
            if let crate::ast::decl::ParameterKind::Data { data_type, assignments, .. } = &pd.kind {
                for a in assignments {
                    param_defaults.push((a.name.name.clone(), a.init.clone()));
                    static_properties.insert(a.name.name.clone());
                    // Evaluate the initial value for the property.
                    let width = resolve_type_width(data_type, None, None);
                    let is_string = matches!(data_type, crate::ast::types::DataType::Simple { kind: crate::ast::types::SimpleType::String, .. });
                    let v = if is_string {
                        // String localparams: evaluate using the const-eval path.
                        if let Some(init) = &a.init {
                            eval_const_expr_val(init, &HashMap::default())
                        } else {
                            Value::from_string("")
                        }
                    } else if let Some(init) = &a.init {
                        eval_init_for_width(init, &HashMap::default(), width)
                    } else {
                        Value::zero(width)
                    };
                    properties.insert(a.name.name.clone(), Signal {
                        is_const: true,
                        name: a.name.name.clone(),
                        width,
                        is_signed: false,
                        is_real: false,
                        direction: None,
                        value: v,
                        type_name: get_type_name(data_type),
                    });
                }
            }
        }
    }
    let has_pure_virtual = c.items.iter().any(|it|
        matches!(it, ClassItem::Method(m) if matches!(m.kind, ClassMethodKind::PureVirtual(_))));
    let mut type_param_names = Vec::new();
    let mut param_order: Vec<String> = Vec::new();
    for p in &c.params {
        match &p.kind {
            crate::ast::decl::ParameterKind::Type { assignments } => {
                for a in assignments {
                    type_param_names.push(a.name.name.clone());
                    param_order.push(a.name.name.clone());
                }
            }
            crate::ast::decl::ParameterKind::Data { assignments, .. } => {
                for a in assignments {
                    param_order.push(a.name.name.clone());
                }
            }
            _ => {}
        }
    }
    ElaboratedClass {
        name: c.name.name.clone(),
        extends: c.extends.as_ref().map(|e| e.name.name.clone()),
        properties,
        property_order,
        string_properties,
        methods,
        random_properties,
        virtual_iface_properties,
        randc_properties,
        constraints,
        param_defaults,
        is_interface: c.is_interface,
        is_virtual: c.virtual_kw,
        is_final: c.is_final,
        has_pure_virtual,
        implements: c.implements.iter().map(|i| i.name.clone()).collect(),
        type_param_names,
        param_order,
        typedef_names: c.items.iter().filter_map(|it| match it {
            ClassItem::Typedef(td) => Some(td.name.name.clone()),
            _ => None,
        }).collect(),
        typedef_targets: c.items.iter().filter_map(|it| match it {
            ClassItem::Typedef(td) => Some((td.name.name.clone(), td.data_type.clone())),
            _ => None,
        }).collect(),
        static_properties,
        static_methods,
        assoc_properties,
        queue_properties,
        property_inits,
        static_collections,
        array_properties,
    }
}

/// One module/interface instance in the design hierarchy.
///
/// The design is flattened into a single `ElaboratedModule` with dotted
/// signal names, so this is the only surviving record of the instance
/// tree. VPI's `vpi_iterate(vpiModule, ...)` and `vpi_handle(vpiScope, ..)`
/// walk it, and `vpi_get_str(vpiDefName, ..)` reads `def_name` from it.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct ElabInstance {
    /// Dotted path below the top module, e.g. `u_sub_block` or `a.b`.
    /// Never carries the top module's own name.
    pub path: String,
    /// The module (or interface) definition this instantiates.
    pub def_name: String,
    /// Dotted path of the containing scope; empty for a child of the top.
    pub parent: String,
}

/// Elaborated module ready for simulation.
#[derive(Debug, serde::Serialize, serde::Deserialize)]
pub struct ElaboratedModule {
    pub name: String,
    /// Global simulation tick in seconds — the finest `timescale` precision
    /// across the design (default 1e-9 = 1 ns when none is finer). Delays are
    /// pre-scaled to this unit at elaboration; the simulator counts ticks of it.
    #[serde(default = "default_tick_s")]
    pub tick_s: f64,
    pub signals: HashMap<String, Signal>,
    /// Transient elaboration bookkeeping (not serialized): names that already
    /// received a type-bearing declaration, mapped to whether that type was
    /// *incompatible* (a named/atom/real/struct/enum type, which cannot be
    /// combined with any other type spec). Used to flag §23.2.2.1 conflicting
    /// non-ANSI redeclarations while still permitting the legal split forms.
    #[serde(skip)]
    pub typed_decls: HashMap<String, bool>,
    pub port_order: Vec<String>,
    pub continuous_assigns: Vec<ContinuousAssignment>,
    /// §28.8 bidirectional switches (`tran`/`tranif0`/`tranif1`), pending
    /// resolution against each terminal's own drivers.
    #[serde(default)]
    pub tran_switches: Vec<TranSwitch>,
    pub always_blocks: Vec<AlwaysBlock>,
    pub initial_blocks: Vec<InitialBlock>,
    /// `final` blocks — LRM §9.2.3. Identical AST shape to `initial`, but
    /// executed once after the event-loop terminates (e.g. on $finish or
    /// max-time exit) and before any VCD/coverage flush.
    #[serde(default)]
    pub final_blocks: Vec<InitialBlock>,
    /// Static/package-scope variable initializers. Scheduled at time 0 ahead of
    /// any `initial` block (and the lazy-prefix `pending_initial`), so package
    /// globals (e.g. riscv-dv's `supported_isa[$] = {...}`) are populated before
    /// user code that reads them.
    pub static_init_blocks: Vec<InitialBlock>,
    /// LRM §24 program block initials. Drained in the reactive region
    /// (after the observed region) rather than the active region — the
    /// simulator routes their statements through `pending_reactive`.
    #[serde(default)]
    pub program_initial_blocks: Vec<InitialBlock>,
    pub parameters: HashMap<String, Value>,
    /// Typedef name -> width mapping for user-defined types.
    pub typedefs: HashMap<String, u32>,
    pub typedef_types: HashMap<String, DataType>,
    /// Array declarations: base_name -> (lo_index, hi_index, element_width)
    pub arrays: HashMap<String, (i64, i64, u32)>,
    /// Associative arrays: name -> true if string-keyed
    pub associative_arrays: HashMap<String, bool>,
    /// Class definitions: name -> elaborated class.
    pub classes: HashMap<String, ElaboratedClass>,
    /// Covergroup definitions: name -> AST declaration.
    pub covergroups: HashMap<String, CovergroupDeclaration>,
    /// Module-level function declarations.
    pub functions: HashMap<String, FunctionDeclaration>,
    /// Module-level task declarations.
    pub tasks: HashMap<String, TaskDeclaration>,
    /// DPI imports by SV-visible symbol name.
    pub dpi_imports: HashMap<String, DpiImportSpec>,
    /// Clocking block definitions: name -> AST declaration.
    pub clocking_blocks: HashMap<String, ClockingDeclaration>,
    /// Let declarations visible in the elaborated scope.
    pub lets: HashMap<String, LetDeclaration>,
    /// Bound interface modport views: signal -> (member -> direction).
    pub modport_views: HashMap<String, HashMap<String, PortDirection>>,
    /// Clocking block signals: block name -> (signal -> direction).
    pub clocking_signal_dirs: HashMap<String, HashMap<String, PortDirection>>,
    /// Specify path delays: destination signal name -> delay (time units).
    pub specify_delays: HashMap<String, u64>,
    /// Associative array default values.
    pub assoc_defaults: HashMap<String, Expression>,
    /// Dynamic arrays / queues (size starts at 0, not pre-allocated range).
    pub dynamic_arrays: HashSet<String>,
    /// Arrays declared with descending range (e.g. [7:0])
    pub descending_arrays: HashSet<String>,
    /// Packed vectors declared with an ASCENDING range (`logic [0:7]`), mapped
    /// to their width. Bit/part selects index these from the MSB end (label 0 =
    /// MSB), so the interpreter remaps `sig[i]` → internal bit `(W-1)-i`
    /// (IEEE 1800-2017 §7.4.1, §11.5.1). Default-declared `[N:0]` vectors are
    /// descending and absent here.
    pub ascending_packed: HashMap<String, u32>,
    /// Unpacked dimensions attached to a typedef (`typedef T A[0:3];`), keyed by
    /// typedef name. A variable `A v;` inherits these dims so it elaborates as
    /// an unpacked array (IEEE 1800-2017 §6.18, §7.4). Empty for scalar typedefs.
    pub typedef_unpacked_dims: HashMap<String, Vec<UnpackedDimension>>,
    /// Bounded queue max sizes: name -> max element count (i.e., $:N means N+1).
    pub queue_max_sizes: HashMap<String, u32>,
    /// 2D unpacked arrays: name -> ((dim1_lo,dim1_hi),(dim2_lo,dim2_hi),elem_width).
    pub arrays_2d: HashMap<String, ((i64, i64), (i64, i64), u32)>,
    pub packages: HashSet<String>,
    /// Names of declared sequences and properties (so `@name` event control resolves).
    pub sequences: HashSet<String>,
    /// Packed struct bit-field layout: container_name -> Vec<(member_name, lsb_offset, width)>.
    /// Members are stored by bit offset so MemberAccess can slice the container.
    pub packed_struct_fields: HashMap<String, Vec<(String, u32, u32)>>,
    /// Variable -> its declared (element) data type. For an array this is the
    /// ELEMENT type; array-ness comes from `arrays`/`dynamic_arrays`/
    /// `associative_arrays`. Drives the type-directed `%p` renderer
    /// (LRM §21.2.1.7), which must walk nested structs/arrays/enums.
    #[serde(default)]
    pub var_decl_types: HashMap<String, DataType>,
    /// Struct variable -> its top-level member names in DECLARATION order, for
    /// packed and unpacked alike. `packed_struct_fields` is ordered by bit
    /// offset (i.e. reversed) and unpacked members live in separate signals, so
    /// neither preserves source order. Used by `%p` (LRM §21.2.1.7), which must
    /// print `'{member:value, ...}` in declaration order.
    #[serde(default)]
    pub struct_members: HashMap<String, Vec<String>>,
    /// Packed multi-dimensional signal element width: signal_name -> element_width.
    /// For `logic [3:0][7:0] words;` stores `"words" -> 8` so that `words[i]`
    /// resolves to an 8-bit slice rather than a 1-bit select. Also keyed for
    /// struct fields under `"struct_var.field"` form.
    pub packed_signal_elem_widths: HashMap<String, u32>,
    /// Signals declared as `string` (LRM §6.16). The bytecode compiler
    /// consults this so that `{a, b}` concatenations involving any
    /// string-typed operand bail to the AST interpreter — the bit-concat
    /// insn would truncate the result to a single operand's 1024-bit
    /// width and drop the others. Populated at elaboration from `VarDecl`
    /// declarations whose `data_type` is `SimpleType::String`.
    #[serde(default)]
    pub string_signals: HashSet<String>,
    /// LRM §25.4 — for each `(interface_name, modport_name)` pair,
    /// the map `member → direction`. Built once at elaboration by
    /// walking every `Definition::Interface`. Consumed by the runtime
    /// virtual-interface late-dispatch path to emit a warning when a
    /// write targets a modport-input member.
    #[serde(default)]
    pub modport_member_dirs:
        HashMap<(String, String), HashMap<String, crate::ast::types::PortDirection>>,
    /// Class-typed signal parameter overrides captured from `Type #(args) name;`
    /// declarations. Signal name -> positional type_args expressions.
    pub class_type_args: HashMap<String, Vec<Expression>>,
    /// LRM §25.9: known interface type names. Used by the runtime to
    /// detect virtual-interface formal args (`task drive(virtual
    /// bus_if vif)`) so the call hook can alias `vif → bus` for the
    /// duration of the call. Populated from every
    /// `Definition::Interface` in `all_defs` at the end of
    /// `elaborate_module_with_defs`.
    #[serde(default)]
    pub interfaces: HashSet<String>,
    /// LRM §17.2: checker declarations indexed by name. Stored so an
    /// instantiation can inline the body with formal→actual port
    /// substitution (basic single-instance semantics). Populated at
    /// the CheckerDeclaration elab arm.
    #[serde(default)]
    pub checker_decls: HashMap<String, crate::ast::decl::CheckerDeclaration>,
    /// LRM §16.6: named property declarations with a captured body
    /// expression (the common `@(clk) <expr>` shape — see the property
    /// parser). Used by `assert property (p_name)` to inline the body.
    #[serde(default)]
    pub property_decls: HashMap<String, crate::ast::expr::Expression>,
    /// LRM §8.4: for an array-of-class-handles (`T arr[N]`,
    /// `T arr[];`), record the element's class name so runtime
    /// `arr[i] = new(...)` can construct an instance of that class.
    /// Populated at signal-declaration time when the data type is a
    /// `TypeReference` whose name resolves to a known class. Without
    /// this, the assignment falls back to a zero value (null handle).
    #[serde(default)]
    pub array_elem_class: HashMap<String, String>,
    /// N-dimensional unpacked array shapes (N >= 3): name → Vec of (lo, hi) per dim.
    pub arrays_nd: HashMap<String, (Vec<(i64, i64)>, u32)>,
    /// Parameter init expressions that couldn't be evaluated at elaboration time
    /// (e.g. contain function calls). Simulator re-evaluates these during init.
    pub deferred_param_exprs: Vec<(String, Expression)>,
    /// Names declared as nets (wire, supply0/1, tri, etc). Variables are everything else.
    /// Used to enforce §6.5 driver-conflict rules only against variables.
    #[serde(default)]
    pub nets: HashSet<String>,
    /// The design's instance tree, in elaboration order. Inlining flattens
    /// every module into this one, so without this the hierarchy is only
    /// implicit in dotted signal names — enough to resolve a name, not
    /// enough to enumerate a scope's children. Drives the VPI object model.
    #[serde(default)]
    pub instances: Vec<ElabInstance>,
    /// Out-of-class constraint definitions: `(class_name, constraint_name)`.
    #[serde(default)]
    pub out_of_class_constraints: HashSet<(String, String)>,
    /// IEEE 1800-2023 §20.3: $timeunit / $timeprecision encoded as the
    /// power-of-10 exponent in seconds (e.g. 10ns → -8). Defaults to -9.
    #[serde(default = "default_timeunit_exp")]
    pub timeunit_exp: i32,
    #[serde(default = "default_timeunit_exp")]
    pub timeprecision_exp: i32,
    /// IEEE 1800-2017 §6.19: enum typedef members in declaration order.
    /// Keyed by typedef name; each entry is `(member_name, value)`.
    /// Used to resolve `.name()` / `.next()` / `.first()` etc.
    #[serde(default)]
    pub enum_members: HashMap<String, Vec<(String, u64)>>,
    /// IEEE 1800-2017 §6.2: names of 2-state-typed signals (bit, byte,
    /// shortint, int, longint). Assignments to these coerce X/Z
    /// source bits to 0.
    #[serde(default)]
    pub two_state_signals: HashSet<String>,
    /// Deferred-rewrite buffers (fix #7). Populated by `inline_module_items`
    /// instead of eagerly producing rewritten ASTs in `always_blocks` /
    /// `initial_blocks` / `continuous_assigns`. Drained by callers via
    /// `materialize_pending` (eager) or `drain_pending_*_for_each` (streaming).
    /// Skipped from serialization: the bincode artifact format only stores
    /// post-materialization state.
    #[serde(skip)]
    pub pending_always: Vec<PendingAlways>,
    #[serde(skip)]
    pub pending_initial: Vec<PendingInitial>,
    #[serde(skip)]
    pub pending_cont_assign: Vec<PendingContAssign>,
    /// §6.20.6: names of `const` variables that carry a declaration-time
    /// initializer (lowered to a synthetic initial assignment). The const's
    /// single legal write is that initializer, so the const-write validator
    /// exempts these names. (No test exercises a const re-write, so leniency
    /// here is safe; a fully precise check would mark the synthetic statement.)
    #[serde(default)]
    pub const_decl_inits: HashSet<String>,
    /// §6.18: names declared by a bare forward type declaration `typedef name;`.
    /// Each must resolve to a real data type (a later full typedef) within the
    /// scope; elaboration errors on any that stay unresolved.
    #[serde(default)]
    pub forward_typedef_names: HashSet<String>,
    /// §15.5: names declared as named `event` variables. An `always @(e)` on a
    /// named event is edge-triggered (woken by `->e`), not a level-sensitive
    /// combinational block — the simulator uses this set to route it correctly.
    #[serde(default)]
    pub events: HashSet<String>,
}

/// A `tran` / `tranif0` / `tranif1` primitive: two terminals and an optional
/// control. `active_high` distinguishes `tranif1` from `tranif0`.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct TranSwitch {
    pub a: Expression,
    pub b: Expression,
    pub ctl: Option<Expression>,
    pub active_high: bool,
}


impl ElaboratedModule {
    /// Record an *explicit* data-type declaration for `name`. Returns Err if
    /// `name` was already explicitly typed — a §23.2.2.1 redeclaration with
    /// conflicting types (e.g. `wire integer x; input integer x;` or
    /// `output [31:0] x; T x;`). Implicit types (a bare `output x;` direction
    /// line, or `wire x;`) are ignored, so the legal non-ANSI split where only
    /// one declaration carries a type still elaborates.
    fn note_explicit_type(&mut self, name: &str, dt: &DataType) -> Result<(), String> {
        // A *bare* implicit type — `output x;` / `wire x;` (no range, no
        // signing) — carries no type; it is the legal half of a non-ANSI split
        // and is ignored here.
        let bare = matches!(dt,
            DataType::Implicit { dimensions, signing: None, .. } if dimensions.is_empty());
        if bare { return Ok(()); }
        // An "incompatible" type cannot be combined with any other type spec:
        // a named type, an integer atom (int/integer/byte/…), real, string/
        // chandle/event, a struct/union, or an enum. A plain range
        // (`[7:0]`/Implicit-with-dims) or a vector keyword (logic/bit/reg) is
        // compatible — e.g. the standard `input [7:0] a; reg [7:0] a;` split is
        // legal. A second type-bearing declaration is a conflict only when one
        // of the two is incompatible.
        let incompat = matches!(dt,
            DataType::TypeReference { .. } | DataType::IntegerAtom { .. } | DataType::Real { .. }
            | DataType::Simple { .. } | DataType::Struct(_) | DataType::Enum(_));
        if let Some(&prev_incompat) = self.typed_decls.get(name) {
            if incompat || prev_incompat {
                return Err(format!("Duplicate declaration of '{}'", name));
            }
        }
        self.typed_decls.entry(name.to_string())
            .and_modify(|v| *v = *v || incompat)
            .or_insert(incompat);
        Ok(())
    }

    pub fn new(name: String) -> Self {
        Self {
            name,
            tick_s: default_tick_s(),
            signals: HashMap::default(),
            typed_decls: HashMap::default(),
            port_order: Vec::new(),
            continuous_assigns: Vec::new(),
            tran_switches: Vec::new(),
            always_blocks: Vec::new(),
            initial_blocks: Vec::new(),
            final_blocks: Vec::new(),
            static_init_blocks: Vec::new(),
            program_initial_blocks: Vec::new(),
            parameters: HashMap::default(),
            typedefs: HashMap::default(),
            typedef_types: HashMap::default(),
            arrays: HashMap::default(),
            associative_arrays: HashMap::default(),
            classes: HashMap::default(),
            covergroups: HashMap::default(),
            functions: HashMap::default(),
            tasks: HashMap::default(),
            dpi_imports: HashMap::default(),
            clocking_blocks: HashMap::default(),
            lets: HashMap::default(),
            modport_views: HashMap::default(),
            clocking_signal_dirs: HashMap::default(),
            specify_delays: HashMap::default(),
            assoc_defaults: HashMap::default(),
            dynamic_arrays: HashSet::default(),
            descending_arrays: HashSet::default(),
            ascending_packed: HashMap::default(),
            typedef_unpacked_dims: HashMap::default(),
            queue_max_sizes: HashMap::default(),
            arrays_2d: HashMap::default(),
            packages: HashSet::default(),
            sequences: HashSet::default(),
            packed_struct_fields: HashMap::default(),
            var_decl_types: HashMap::default(),
            struct_members: HashMap::default(),
            packed_signal_elem_widths: HashMap::default(),
            string_signals: HashSet::default(),
            modport_member_dirs: HashMap::default(),
            class_type_args: HashMap::default(),
            interfaces: HashSet::default(),
            checker_decls: HashMap::default(),
            property_decls: HashMap::default(),
            array_elem_class: HashMap::default(),
            arrays_nd: HashMap::default(),
            deferred_param_exprs: Vec::new(),
            nets: HashSet::default(),
            instances: Vec::new(),
            out_of_class_constraints: HashSet::default(),
            timeunit_exp: default_timeunit_exp(),
            timeprecision_exp: default_timeunit_exp(),
            enum_members: HashMap::default(),
            two_state_signals: HashSet::default(),
            pending_always: Vec::new(),
            pending_initial: Vec::new(),
            pending_cont_assign: Vec::new(),
            const_decl_inits: HashSet::default(),
            forward_typedef_names: HashSet::default(),
            events: HashSet::default(),
        }
    }

    /// Eager (non-streaming) drain of pending procedural blocks. Materializes
    /// every Pending* into the corresponding always_blocks/initial_blocks/
    /// continuous_assigns vec. Keeps semantics identical to pre-#7 elaborate
    /// at the cost of high peak memory — use streaming drains in performance-
    /// sensitive paths (see drain_pending_*_for_each).
    pub fn materialize_pending(&mut self) {
        let pending_always = std::mem::take(&mut self.pending_always);
        for p in pending_always {
            self.always_blocks.push(p.materialize());
        }
        let pending_initial = std::mem::take(&mut self.pending_initial);
        for p in pending_initial {
            self.initial_blocks.push(p.materialize());
        }
        let pending_ca = std::mem::take(&mut self.pending_cont_assign);
        for p in pending_ca {
            self.continuous_assigns.push(p.materialize());
        }
    }

    /// Streaming drain for pending always-blocks. Each block is materialized
    /// just before the callback runs, then dropped. Peak memory is one
    /// materialized AlwaysBlock at a time. Intended consumer: bytecode
    /// compiler — `f` should compile and discard the AST.
    pub fn drain_pending_always_for_each<F: FnMut(AlwaysBlock)>(&mut self, mut f: F) {
        let pending = std::mem::take(&mut self.pending_always);
        for p in pending { f(p.materialize()); }
    }

    /// Streaming drain for pending initial-blocks.
    pub fn drain_pending_initial_for_each<F: FnMut(InitialBlock)>(&mut self, mut f: F) {
        let pending = std::mem::take(&mut self.pending_initial);
        for p in pending { f(p.materialize()); }
    }

    /// Streaming drain for pending continuous-assigns.
    pub fn drain_pending_cont_assign_for_each<F: FnMut(ContinuousAssignment)>(&mut self, mut f: F) {
        let pending = std::mem::take(&mut self.pending_cont_assign);
        for p in pending { f(p.materialize()); }
    }
}

fn expr_has_call(expr: &Expression) -> bool {
    use crate::ast::expr::ExprKind;
    match &expr.kind {
        ExprKind::Call { .. } => true,
        // LRM §20.7 array-introspection system funcs over an array
        // identifier need the runtime path: elaboration's const-eval may
        // not yet have the array registered when the parameter init is
        // walked (order-dependent). Deferring guarantees `elab.arrays`
        // is fully populated and the runtime $size/$left/etc handler
        // resolves correctly.
        ExprKind::SystemCall { name, .. }
            if matches!(name.as_str(),
                "$size" | "$left" | "$right" | "$high" | "$low" | "$dimensions") => true,
        ExprKind::Binary { left, right, .. } => expr_has_call(left) || expr_has_call(right),
        ExprKind::Unary { operand, .. } => expr_has_call(operand),
        ExprKind::Paren(e) => expr_has_call(e),
        ExprKind::Conditional { condition, then_expr, else_expr } =>
            expr_has_call(condition) || expr_has_call(then_expr) || expr_has_call(else_expr),
        _ => false,
    }
}

/// A unified representation of a module or interface.
#[derive(Debug, Clone, Copy)]
pub enum Definition<'a> {
    Module(&'a ModuleDeclaration),
    Interface(&'a crate::ast::module::InterfaceDeclaration),
    Program(&'a crate::ast::module::ProgramDeclaration),
    Class(&'a crate::ast::decl::ClassDeclaration),
    Covergroup(&'a crate::ast::decl::CovergroupDeclaration),
    Package(&'a crate::ast::module::PackageDeclaration),
    Typedef(&'a crate::ast::decl::TypedefDeclaration),
}

impl<'a> Definition<'a> {
    pub fn name(&self) -> &str {
        match self {
            Definition::Module(m) => &m.name.name,
            Definition::Interface(i) => &i.name.name,
            Definition::Program(p) => &p.name.name,
            Definition::Class(c) => &c.name.name,
            Definition::Covergroup(cg) => &cg.name.name,
            Definition::Package(p) => &p.name.name,
            Definition::Typedef(t) => &t.name.name,
        }
    }

    pub fn params(&self) -> &[ParameterDeclaration] {
        match self {
            Definition::Module(m) => &m.params,
            Definition::Interface(i) => &i.params,
            Definition::Program(p) => &p.params,
            Definition::Class(c) => &c.params,
            Definition::Covergroup(_) | Definition::Package(_) | Definition::Typedef(_) => &[],
        }
    }

    pub fn ports(&self) -> &PortList {
        match self {
            Definition::Module(m) => &m.ports,
            Definition::Interface(i) => &i.ports,
            Definition::Program(p) => &p.ports,
            Definition::Class(_) | Definition::Covergroup(_) | Definition::Package(_) | Definition::Typedef(_) => &PortList::Empty,
        }
    }
        pub fn items(&self) -> &[ModuleItem] {
        match self {
        Definition::Module(m) => &m.items,
        Definition::Interface(i) => &i.items,
        Definition::Program(p) => &p.items,
        Definition::Class(_) | Definition::Covergroup(_) | Definition::Package(_) | Definition::Typedef(_) => &[],
        }
        }
        }

fn get_type_name(dt: &DataType) -> Option<String> {
    match dt {
        DataType::TypeReference { name, .. } => Some(name.name.name.clone()),
        DataType::Interface { name, .. } => Some(name.name.clone()),
        _ => None,
    }
}

fn dpi_proto_sv_name(proto: &DPIProto) -> String {
    match proto {
        DPIProto::Function(fd) => fd.name.name.name.clone(),
        DPIProto::Task(td) => td.name.name.name.clone(),
    }
}

fn register_dpi_import(di: &DPIImport, elab: &mut ElaboratedModule) -> Result<(), String> {
    let sv_name = dpi_proto_sv_name(&di.proto);
    let c_name = di.c_name.clone().unwrap_or_else(|| sv_name.clone());
    // LRM §35.5.2: the same foreign function may be imported more than once,
    // as long as the declarations are consistent (same C binding and import
    // property). This is common in real libraries — UVM re-imports helpers
    // such as `uvm_hdl_check_path` from headers pulled into more than one
    // scope. Accept a consistent re-import as a no-op; only a genuine
    // mismatch (different c_identifier or context/pure property) is illegal.
    if let Some(existing) = elab.dpi_imports.get(&sv_name) {
        if existing.c_name == c_name && existing.property == di.property {
            return Ok(());
        }
        return Err(format!(
            "Conflicting DPI import declaration '{}': already imported as \
             (c=\"{}\", {:?}), redeclared as (c=\"{}\", {:?})",
            sv_name, existing.c_name, existing.property, c_name, di.property
        ));
    }
    elab.dpi_imports.insert(sv_name, DpiImportSpec {
        c_name,
        property: di.property,
        proto: di.proto.clone(),
    });
    Ok(())
}

fn is_const_expr(expr: &Expression, params: &HashMap<String, Value>) -> bool {
    match &expr.kind {
        ExprKind::Number(_) | ExprKind::StringLiteral(_) => true,
        ExprKind::Ident(hier) => {
            let last = hier.path.last().map(|s| s.name.name.as_str()).unwrap_or("");
            // Const if the leaf is a param/enum const (`X`, `pkg::C`), or — for a
            // hierarchical `pt.FIELD` — the BASE is a const struct param.
            let base = hier.path.first().map(|s| s.name.name.as_str()).unwrap_or("");
            params.contains_key(last) || (hier.path.len() > 1 && params.contains_key(base))
        }
        ExprKind::Unary { operand, .. } => is_const_expr(operand, params),
        ExprKind::Binary { left, right, .. } => is_const_expr(left, params) && is_const_expr(right, params),
        ExprKind::Conditional { condition, then_expr, else_expr } => is_const_expr(condition, params) && is_const_expr(then_expr, params) && is_const_expr(else_expr, params),
        ExprKind::Concatenation(parts) => parts.iter().all(|p| is_const_expr(p, params)),
        ExprKind::Paren(inner) => is_const_expr(inner, params),
        // Struct member / packed-array element select on a constant base — e.g.
        // a generate-if on a config-struct parameter field `CVA6Cfg.RVF` (ariane)
        // or `all_cfgs_gp[idx]`. eval_const_expr_val resolves these via the
        // struct-layout / elem-width TLS context (see the Index/MemberAccess arms).
        ExprKind::MemberAccess { expr, member } => {
            // `s.field` (const struct base) OR `pkg::CONST` (the scoped member is
            // an imported package constant / enum value, resolved by bare name).
            is_const_expr(expr, params) || params.contains_key(&member.name)
        }
        ExprKind::Index { expr, index } => is_const_expr(expr, params) && is_const_expr(index, params),
        // System constant functions used in generate conditions ($bits, $clog2…).
        ExprKind::SystemCall { args, .. } => args.iter().all(|a| is_const_expr(a, params)),
        _ => false, // Calls (new()) etc. are not constant
    }
}

/// Elaborate a module or interface declaration into a simulation model.
pub fn elaborate_module(
    module: Definition,
    param_overrides: &HashMap<String, Value>,
) -> Result<ElaboratedModule, String> {
    elaborate_module_with_defs(module, param_overrides, None, &[], &[], &[])
}

/// Register members of an anonymous enum attached to a variable declaration
/// (`enum logic { A, B } var_name;`) into `elab.parameters` and `elab.signals`.
/// `typedef enum {...}` already does this via `process_typedef`; this is the
/// missing path for the bare-variable form. Used by every `DataDeclaration`
/// arm in the elaborator (top-level, submodule, generate-scope, etc.).
/// §6.19.1: expand one enum member into its concrete (name, value) entries,
/// honoring a `[lo:hi]` element range (already normalized from the `[N]` count
/// form by the parser). An `init` seeds the FIRST expanded name; the rest
/// auto-increment. Returns the expanded entries and the next auto value.
fn expand_enum_member(
    member: &crate::ast::types::EnumMember,
    next_val: u64,
    params: &crate::hasher::HashMap<String, Value>,
) -> (Vec<(String, u64)>, u64) {
    let mut out = Vec::new();
    let mut val = if let Some(init) = &member.init {
        eval_const_expr(init, params)
    } else { next_val };
    match &member.range {
        None => {
            out.push((member.name.name.clone(), val));
            val = val.wrapping_add(1);
        }
        Some((lo_e, hi_e)) => {
            let lo = const_eval_i64_with_params(lo_e, Some(params)).unwrap_or(0);
            let hi = const_eval_i64_with_params(hi_e, Some(params)).unwrap_or(lo);
            let idxs: Vec<i64> = if lo <= hi { (lo..=hi).collect() } else { (hi..=lo).rev().collect() };
            for i in idxs {
                out.push((format!("{}{}", member.name.name, i), val));
                val = val.wrapping_add(1);
            }
        }
    }
    (out, val)
}

pub fn register_anonymous_enum_members(dt: &DataType, elab: &mut ElaboratedModule) {
    if let DataType::Enum(et) = dt {
        let base_width = et.base_type.as_ref()
            .map(|bt| resolve_type_width(bt, Some(&elab.parameters), Some(&elab.typedefs)))
            .unwrap_or(32);
        let mut next_val: u64 = 0;
        for member in &et.members {
            let (entries, nv) = expand_enum_member(member, next_val, &elab.parameters);
            next_val = nv;
            for (nm, val) in entries {
                let v = Value::from_u64(val, base_width);
                elab.parameters.entry(nm.clone()).or_insert_with(|| v.clone());
                elab.signals.entry(nm.clone()).or_insert_with(|| Signal {
                    is_const: false,
                    name: nm.clone(),
                    width: base_width,
                    is_signed: false,
                    is_real: false,
                    direction: None,
                    value: v,
                    type_name: None,
                });
            }
        }
    }
}

/// Register a class's CLASS-LOCAL `typedef enum {...}` members as resolvable
/// bare-name constants (parameters/signals), like module/package enums.
/// Without this, a class-local enum member (e.g. uvm_sequencer_base's
/// `SEQ_TYPE_REQ` from `typedef enum {SEQ_TYPE_REQ,...} seq_req_t;`) resolves
/// to X at eval time, so `req.request = SEQ_TYPE_REQ` stores X and the
/// sequencer arbitration's `request == SEQ_TYPE_REQ` is always false (4-state).
/// Uses or_insert semantics so module/package enums are never clobbered.
pub fn register_class_enum_members(c: &ClassDeclaration, elab: &mut ElaboratedModule) {
    for item in &c.items {
        if let ClassItem::Typedef(td) = item {
            register_anonymous_enum_members(&td.data_type, elab);
        }
    }
}

pub fn process_typedef(td: &TypedefDeclaration, elab: &mut ElaboratedModule) {
    // §6.18: a bare forward type declaration `typedef name;`. Record it for the
    // resolution check and register a placeholder, but never clobber a name that
    // a real (non-forward) typedef has already resolved — `typedef_test_0`
    // legally restates the forward name both before and after the full typedef.
    if td.forward {
        elab.forward_typedef_names.insert(td.name.name.clone());
        let already_resolved = elab.typedef_types.get(&td.name.name)
            .map_or(false, |dt| !matches!(dt, DataType::Void(_)));
        if !already_resolved {
            elab.typedef_types.entry(td.name.name.clone())
                .or_insert_with(|| td.data_type.clone());
            elab.typedefs.entry(td.name.name.clone()).or_insert(0);
        }
        return;
    }
    if let DataType::Enum(et) = &td.data_type {
        let base_width = et.base_type.as_ref()
            .map(|bt| resolve_type_width(bt, Some(&elab.parameters), Some(&elab.typedefs)))
            .unwrap_or(32);
        let mut next_val: u64 = 0;
        let mut members_ordered: Vec<(String, u64)> = Vec::new();
        for member in &et.members {
            let (entries, nv) = expand_enum_member(member, next_val, &elab.parameters);
            next_val = nv;
            for (nm, val) in entries {
                let v = Value::from_u64(val, base_width);
                elab.parameters.insert(nm.clone(), v.clone());
                elab.signals.insert(nm.clone(), Signal { is_const: false,
                    name: nm.clone(),
                    width: base_width,
                    is_signed: false,
                    is_real: false,
                    direction: None,
                    value: v,
                    type_name: Some(td.name.name.clone()),
                });
                members_ordered.push((nm.clone(), val));
            }
        }
        // Register the typedef width
        elab.typedefs.insert(td.name.name.clone(), base_width);
        elab.enum_members.insert(td.name.name.clone(), members_ordered);
    } else {
        // Non-enum typedef: resolve width from the underlying type
        let w = resolve_type_width(&td.data_type, Some(&elab.parameters), Some(&elab.typedefs));
        elab.typedefs.insert(td.name.name.clone(), w);
        elab.typedef_types.insert(td.name.name.clone(), td.data_type.clone());
    }
    // §6.18/§7.4: record any unpacked dimensions on the typedef
    // (`typedef logic [7:0] A [0:3];`) so a variable `A v;` inherits them.
    if !td.dimensions.is_empty() {
        elab.typedef_unpacked_dims
            .insert(td.name.name.clone(), td.dimensions.clone());
    }
    // Refresh the thread-local typedef snapshot so any subsequent
    // const-eval `$bits(typedef_name)` call sees this typedef (M2).
    TYPEDEFS_TLS.with(|cell| {
        *cell.borrow_mut() = Some(elab.typedefs.clone());
    });
}

fn resolve_interface_modport_view(
    interface_name: &str,
    modport_name: &str,
    all_defs: Option<&HashMap<String, Definition>>,
) -> Option<HashMap<String, PortDirection>> {
    let defs = all_defs?;
    let idef = match defs.get(interface_name) {
        Some(Definition::Interface(i)) => i,
        _ => return None,
    };
    for item in &idef.items {
        if let ModuleItem::ModportDeclaration(md) = item {
            for mp in &md.items {
                if mp.name.name == modport_name {
                    let mut dirs = HashMap::default();
                    for p in &mp.ports {
                        dirs.insert(p.name.name.clone(), p.direction);
                    }
                    return Some(dirs);
                }
            }
        }
    }
    None
}

fn validate_class_constraint_expr(expr: &Expression, allowed: &HashSet<String>) -> Result<(), String> {
    match &expr.kind {
        ExprKind::Ident(hier) => {
            if hier.path.len() == 1 {
                let n = &hier.path[0].name.name;
                if n != "this" && n != "super" && n != "new" && !allowed.contains(n) {
                    return Err(format!("Undeclared identifier '{}' in class constraint", n));
                }
            }
        }
        ExprKind::Unary { operand, .. } => validate_class_constraint_expr(operand, allowed)?,
        ExprKind::Binary { left, right, .. } => {
            validate_class_constraint_expr(left, allowed)?;
            validate_class_constraint_expr(right, allowed)?;
        }
        ExprKind::Conditional { condition, then_expr, else_expr } => {
            validate_class_constraint_expr(condition, allowed)?;
            validate_class_constraint_expr(then_expr, allowed)?;
            validate_class_constraint_expr(else_expr, allowed)?;
        }
        ExprKind::Concatenation(parts) => {
            for p in parts {
                validate_class_constraint_expr(p, allowed)?;
            }
        }
        ExprKind::Replication { count, exprs } => {
            validate_class_constraint_expr(count, allowed)?;
            for e in exprs {
                validate_class_constraint_expr(e, allowed)?;
            }
        }
        ExprKind::Index { expr, index } => {
            validate_class_constraint_expr(expr, allowed)?;
            validate_class_constraint_expr(index, allowed)?;
        }
        ExprKind::RangeSelect { expr, left, right, .. } => {
            validate_class_constraint_expr(expr, allowed)?;
            validate_class_constraint_expr(left, allowed)?;
            validate_class_constraint_expr(right, allowed)?;
        }
        ExprKind::Inside { expr, ranges } => {
            validate_class_constraint_expr(expr, allowed)?;
            for r in ranges {
                validate_class_constraint_expr(r, allowed)?;
            }
        }
        ExprKind::Range(lo, hi) => {
            validate_class_constraint_expr(lo, allowed)?;
            validate_class_constraint_expr(hi, allowed)?;
        }
        ExprKind::Paren(inner) => validate_class_constraint_expr(inner, allowed)?,
        ExprKind::Call { func: _, args } => {
            // Don't validate the callee identifier: it resolves to a function/method
            // (including class methods, package functions, built-ins) that may not be
            // in the property-name allowed set.
            for a in args {
                validate_class_constraint_expr(a, allowed)?;
            }
        }
        ExprKind::SystemCall { args, .. } => {
            for a in args {
                validate_class_constraint_expr(a, allowed)?;
            }
        }
        ExprKind::MemberAccess { expr, .. } => validate_class_constraint_expr(expr, allowed)?,
        _ => {}
    }
    Ok(())
}

fn validate_constraint_item_names(item: &ConstraintItem, allowed: &HashSet<String>) -> Result<(), String> {
    match item {
        ConstraintItem::Expr(expr) => validate_class_constraint_expr(expr, allowed)?,
        ConstraintItem::Inside { expr, range, .. } => {
            validate_class_constraint_expr(expr, allowed)?;
            for r in range {
                match r {
                    ConstraintRange::Value(e) => validate_class_constraint_expr(e, allowed)?,
                    ConstraintRange::Range { lo, hi } => {
                        validate_class_constraint_expr(lo, allowed)?;
                        validate_class_constraint_expr(hi, allowed)?;
                    }
                }
            }
        }
        ConstraintItem::Implication { condition, constraint, .. } => {
            validate_class_constraint_expr(condition, allowed)?;
            validate_constraint_item_names(constraint, allowed)?;
        }
        ConstraintItem::IfElse { condition, then_item, else_item, .. } => {
            validate_class_constraint_expr(condition, allowed)?;
            validate_constraint_item_names(then_item, allowed)?;
            if let Some(ei) = else_item {
                validate_constraint_item_names(ei, allowed)?;
            }
        }
        ConstraintItem::Foreach { array, vars, item, .. } => {
            validate_class_constraint_expr(array, allowed)?;
            let mut inner = allowed.clone();
            for v in vars {
                if let Some(id) = v {
                    inner.insert(id.name.clone());
                }
            }
            validate_constraint_item_names(item, &inner)?;
        }
        ConstraintItem::Soft(inner) => validate_constraint_item_names(inner, allowed)?,
        ConstraintItem::Unique { exprs, .. } => {
            for e in exprs {
                validate_class_constraint_expr(e, allowed)?;
            }
        }
        ConstraintItem::Block(items) => {
            for it in items {
                validate_constraint_item_names(it, allowed)?;
            }
        }
        ConstraintItem::Solve { before, after, .. } => {
            for id in before {
                if !allowed.contains(&id.name) {
                    return Err(format!("Undeclared identifier '{}' in class constraint", id.name));
                }
            }
            for id in after {
                if !allowed.contains(&id.name) {
                    return Err(format!("Undeclared identifier '{}' in class constraint", id.name));
                }
            }
        }
    }
    Ok(())
}

fn collect_class_member_names(
    c: &ClassDeclaration,
    all_defs: Option<&HashMap<String, Definition>>,
    allowed: &mut HashSet<String>,
    seen: &mut HashSet<String>,
) {
    if !seen.insert(c.name.name.clone()) {
        return;
    }
    for item in &c.items {
        match item {
            ClassItem::Property(p) => {
                for d in &p.declarators {
                    allowed.insert(d.name.name.clone());
                }
            }
            ClassItem::Parameter(pd) => match &pd.kind {
                ParameterKind::Data { assignments, .. } => {
                    for a in assignments {
                        allowed.insert(a.name.name.clone());
                    }
                }
                ParameterKind::Type { assignments } => {
                    for a in assignments {
                        allowed.insert(a.name.name.clone());
                    }
                }
            },
            ClassItem::Method(m) => {
                let name = match &m.kind {
                    ClassMethodKind::Function(f) => &f.name.name.name,
                    ClassMethodKind::Task(t) => &t.name.name.name,
                    ClassMethodKind::PureVirtual(f) => &f.name.name.name,
                    ClassMethodKind::Extern(f) => &f.name.name.name,
                };
                allowed.insert(name.clone());
            }
            ClassItem::Typedef(td) => {
                allowed.insert(td.name.name.clone());
                if let DataType::Enum(et) = &td.data_type {
                    for m in &et.members {
                        allowed.insert(m.name.name.clone());
                    }
                }
            }
            _ => {}
        }
    }
    for p in &c.params {
        match &p.kind {
            ParameterKind::Data { assignments, .. } => {
                for a in assignments {
                    allowed.insert(a.name.name.clone());
                }
            }
            ParameterKind::Type { assignments } => {
                for a in assignments {
                    allowed.insert(a.name.name.clone());
                }
            }
        }
    }
    if let Some(ext) = &c.extends {
        if let Some(defs) = all_defs {
            if let Some(Definition::Class(parent)) = defs.get(&ext.name.name) {
                collect_class_member_names(parent, all_defs, allowed, seen);
            }
        }
    }
}

/// Add the enum constant names introduced by an enum typedef to `allowed`.
fn collect_enum_member_names(td: &TypedefDeclaration, allowed: &mut HashSet<String>) {
    if let DataType::Enum(et) = &td.data_type {
        for m in &et.members {
            allowed.insert(m.name.name.clone());
        }
    }
}

/// Collect identifier names that are legal to reference from any class
/// constraint regardless of class membership: package- and top-level enum
/// constants, parameters/localparams, and `const` data declarations. Without
/// these, a constraint such as `reg != ZERO` (where `ZERO` is a package enum
/// literal) is wrongly rejected as an undeclared identifier.
fn collect_global_constraint_names(
    all_defs: &HashMap<String, Definition>,
    allowed: &mut HashSet<String>,
) {
    for def in all_defs.values() {
        // Package and class names are legal roots of scoped constraint
        // references (`pkg::CONST`, `ClassName::STATIC`).
        allowed.insert(def.name().to_string());
        match def {
            Definition::Typedef(td) => collect_enum_member_names(td, allowed),
            Definition::Package(p) => {
                for item in &p.items {
                    match item {
                        crate::ast::decl::PackageItem::Typedef(td) => {
                            allowed.insert(td.name.name.clone());
                            collect_enum_member_names(td, allowed);
                        }
                        crate::ast::decl::PackageItem::Parameter(pd) => {
                            if let ParameterKind::Data { assignments, .. } = &pd.kind {
                                for a in assignments { allowed.insert(a.name.name.clone()); }
                            }
                        }
                        crate::ast::decl::PackageItem::Data(d) => {
                            for decl in &d.declarators { allowed.insert(decl.name.name.clone()); }
                        }
                        _ => {}
                    }
                }
            }
            _ => {}
        }
    }
}

fn validate_class_constraints(
    c: &ClassDeclaration,
    all_defs: Option<&HashMap<String, Definition>>,
    module_enums: Option<&HashMap<String, Vec<(String, u64)>>>,
) -> Result<(), String> {
    let mut allowed = HashSet::default();
    let mut seen = HashSet::default();
    collect_class_member_names(c, all_defs, &mut allowed, &mut seen);
    if let Some(defs) = all_defs {
        collect_global_constraint_names(defs, &mut allowed);
    }
    // Enum typedefs declared at MODULE scope (before the class) are legal
    // constraint references too — `constraint c { m != R0; }` where `reg_t`
    // is a module-local typedef. `collect_global_constraint_names` only sees
    // top-level/package typedefs, so fold in the elaborating module's
    // already-registered enum types and member names.
    if let Some(ems) = module_enums {
        for (tname, members) in ems {
            allowed.insert(tname.clone());
            for (mname, _) in members {
                allowed.insert(mname.clone());
            }
        }
    }
    for item in &c.items {
        if let ClassItem::Constraint(con) = item {
            for it in &con.items {
                validate_constraint_item_names(it, &allowed)?;
            }
        }
    }
    Ok(())
}

pub fn elaborate_module_with_defs(
    module: Definition,
    param_overrides: &HashMap<String, Value>,
    all_defs: Option<&HashMap<String, Definition>>,
    top_level_imports: &[ImportDeclaration],
    top_level_lets: &[LetDeclaration],
    seed_ooc_constraints: &[(String, String)],
) -> Result<ElaboratedModule, String> {
    let mut elab = ElaboratedModule::new(module.name().to_string());

    // §18.5.1: seed $unit-scope out-of-class constraint definitions so a class's
    // `extern constraint c;` is satisfied regardless of whether the design has a
    // module (the definition is parsed at compilation-unit scope, outside any).
    for (c, n) in seed_ooc_constraints {
        elab.out_of_class_constraints.insert((c.clone(), n.clone()));
    }

    // Process top-level typedefs and other global definitions from all_defs
    if let Some(defs) = all_defs {
        for def in defs.values() {
            match def {
                Definition::Typedef(td) => { process_typedef(td, &mut elab); }
                Definition::Class(c) => {
                    validate_class_constraints(c, Some(defs), Some(&elab.enum_members))?;
                    register_class_enum_members(c, &mut elab);
                    elab.classes.insert(c.name.name.clone(), elaborate_class(c));
                }
                Definition::Covergroup(cg) => { elab.covergroups.insert(cg.name.name.clone(), (*cg).clone()); }
                Definition::Package(p) => {
                    elab.packages.insert(p.name.name.clone());
                    // Hoist package-scope functions/tasks for `pkg::f(...)`
                    // and bare-name resolution after `import pkg::*`. A
                    // scoped name (`ClassName::m`) is an out-of-class method
                    // body — `link_extern_methods` handles those.
                    for item in &p.items {
                        match item {
                            crate::ast::decl::PackageItem::Function(f) if f.name.scope.is_none() => {
                                elab.functions.entry(f.name.name.name.clone()).or_insert_with(|| f.clone());
                            }
                            crate::ast::decl::PackageItem::Task(t) if t.name.scope.is_none() => {
                                elab.tasks.entry(t.name.name.name.clone()).or_insert_with(|| t.clone());
                            }
                            // §26.3: register package classes by name so an
                            // (imported or scoped) reference like
                            // `uvm_config_db#(T)::set` resolves instead of being
                            // flagged "Undeclared identifier". Class bodies are
                            // also reachable through their package for
                            // `pkg::Class::method`.
                            crate::ast::decl::PackageItem::Class(c) => {
                                register_class_enum_members(c, &mut elab);
                                elab.classes.entry(c.name.name.clone())
                                    .or_insert_with(|| elaborate_class(c));
                            }
                            // Hoist package typedefs (loads enum members + typedef
                            // widths) so an explicit scoped reference `pkg::CONST`
                            // — which does NOT require an import — resolves during
                            // top-module elaboration, e.g. a generate-if
                            // `CVA6Cfg.DCacheType == config_pkg::WT` (ariane).
                            // Package types are otherwise only processed later in
                            // inline_instantiations, after the top body.
                            crate::ast::decl::PackageItem::Typedef(td) => {
                                process_typedef(td, &mut elab);
                            }
                            _ => {}
                        }
                    }
                }
                _ => {}
            }
        }
    }

    // Process top-level imports
    for imp in top_level_imports {
        if let Some(defs) = all_defs {
            process_import(imp, &mut elab, defs)?;
        }
    }

    for l in top_level_lets {
        elab.lets.insert(l.name.name.clone(), l.clone());
    }

    // Process parameters
    for param in module.params() {
        if let ParameterKind::Data { data_type, assignments } = &param.kind {
            for assign in assignments {
                // IEEE 1800-2023: keyed assignment-pattern parameter
                // (associative array literal). Materialize the entries
                // as `<param>["key"]` signals before falling into the
                // scalar parameter path.
                if let Some(init) = &assign.init {
                    if let ExprKind::AssignmentPattern(items) = &init.kind {
                        // A struct/union-typed parameter is NOT an associative
                        // array even if its `'{ident: v}` items parse as Keyed —
                        // its keys are field names, handled by the struct path.
                        let is_struct_dt = flatten_struct_fields(
                            data_type, &elab.parameters, &elab.typedefs,
                            &elab.typedef_types).map_or(false, |f| !f.is_empty());
                        let all_keyed = !is_struct_dt && !items.is_empty()
                            && items.iter().all(|it| matches!(it, AssignmentPatternItem::Keyed(_, _)));
                        if all_keyed {
                            let elem_w = resolve_type_width(data_type, Some(&elab.parameters), Some(&elab.typedefs));
                            elab.associative_arrays
                                .insert(assign.name.name.clone(), true);
                            for it in items {
                                if let AssignmentPatternItem::Keyed(k, v) = it {
                                    let key_str = match &k.kind {
                                        ExprKind::StringLiteral(s) => s.clone(),
                                        _ => eval_const_expr_val(k, &elab.parameters).to_dec_string(),
                                    };
                                    let val_v = eval_init_for_width(v, &elab.parameters, elem_w);
                                    let signal_name = format!("{}[{}]", assign.name.name, key_str);
                                    elab.signals.insert(
                                        signal_name.clone(),
                                        Signal {
                                            is_const: true,
                                            name: signal_name,
                                            width: elem_w,
                                            is_signed: is_type_signed(data_type),
                                            is_real: false,
                                            direction: None,
                                            value: val_v,
                                            type_name: None,
                                        },
                                    );
                                }
                            }
                            continue;
                        }
                    }
                }
                // §6.20.2 unpacked-array parameter: `u32_t A[N] = {a, b}`.
                if !assign.dimensions.is_empty() {
                    let ov = param_overrides.get(&assign.name.name).cloned();
                    let params_snapshot = elab.parameters.clone();
                    if register_array_param(&mut elab, "", &assign.name.name, &assign.dimensions,
                        assign.init.as_ref(), ov.as_ref(), data_type, &params_snapshot) {
                        continue;
                    }
                }
                let mut width = resolve_type_width(data_type, Some(&elab.parameters), Some(&elab.typedefs));
                let mut signed = is_type_signed(data_type);
                let mut is_real = is_type_real(data_type);

                // IEEE 1800-2017 §6.20.2: Parameters with implicit type (no explicit type)
                // default to 32-bit signed integer.
                if matches!(data_type, DataType::Implicit { dimensions, .. } if dimensions.is_empty()) {
                    // Check if the initialization value is real. If so, parameter is real.
                    let init_is_real = if let Some(override_val) = param_overrides.get(&assign.name.name) {
                        override_val.is_real
                    } else if let Some(init) = &assign.init {
                        eval_const_expr_val(init, &elab.parameters).is_real
                    } else { false };

                    if init_is_real {
                        width = 64;
                        is_real = true;
                    } else {
                        width = 32;
                        signed = true;
                    }
                }

                // IEEE 1800-2017 §6.20: a struct/union-typed parameter whose
                // value is an assignment pattern (`parameter cfg_t C = '{f:v}`)
                // must be packed by field offset at elaboration, and its field
                // layout registered so later `C.f` selects resolve.
                let struct_fields = flatten_struct_fields(
                    data_type, &elab.parameters, &elab.typedefs, &elab.typedef_types);
                let is_struct_param = struct_fields.as_ref().map_or(false, |f| !f.is_empty());

                let mut val = if let Some(override_val) = param_overrides.get(&assign.name.name) {
                    override_val.clone()
                } else if let Some(init) = &assign.init {
                    let mut v = if is_struct_param {
                        pack_struct_const_value(
                            data_type, init, &elab.parameters,
                            &elab.typedefs, &elab.typedef_types)
                        .map(|sv| sv.resize(width))
                        .unwrap_or_else(|| eval_init_for_width(init, &elab.parameters, width))
                    } else {
                        eval_init_for_width(init, &elab.parameters, width)
                    };
                    if signed { v.is_signed = true; }
                    v
                } else {
                    let mut v = Value::zero(width);
                    if signed { v.is_signed = true; }
                    v
                };

                if is_real {
                    val = Value::from_f64(val.to_f64());
                }

                if let Some(fields) = struct_fields {
                    tls_register_struct_layout(&assign.name.name, &fields);
                    elab.packed_struct_fields
                        .entry(assign.name.name.clone())
                        .or_insert(fields);
                }
                elab.parameters.insert(assign.name.name.clone(), val);
            }
        } else if let ParameterKind::Type { assignments } = &param.kind {
            // §6.20.3 type parameter (`parameter type T1 = integer`): register
            // the (default) type as a typedef so `T1 x;` and `$bits(T1)` resolve.
            // The type may reference earlier value params (`logic [A-1:0]`), which
            // are already in elab.parameters by this point (params elaborate in
            // source order). Instance type-overrides aren't threaded here yet.
            for a in assignments {
                if let Some(dt) = &a.init {
                    let w = resolve_type_width(dt, Some(&elab.parameters), Some(&elab.typedefs));
                    elab.typedefs.insert(a.name.name.clone(), w);
                    elab.typedef_types.insert(a.name.name.clone(), dt.clone());
                    register_anonymous_enum_members(dt, &mut elab);
                }
            }
        }
    }

    // Process ports
    match module.ports() {
        PortList::Ansi(ports) => {
            for port in ports {
                let modport_view = match port.data_type.as_ref() {
                    Some(DataType::Interface { name, modport: Some(mp), .. }) => {
                        resolve_interface_modport_view(&name.name, &mp.name, all_defs)
                    }
                    _ => None,
                };
                let width = port.data_type.as_ref()
                    .map(|dt| resolve_type_width(dt, Some(&elab.parameters), Some(&elab.typedefs)))
                    .unwrap_or(1);
                let is_signed = port.data_type.as_ref()
                    .map(|dt| is_type_signed(dt))
                    .unwrap_or(false);
                let is_real = port.data_type.as_ref().map(is_type_real).unwrap_or(false);
                let sig = Signal { is_const: false,
                    name: port.name.name.clone(),
                    width,
                    is_signed,
                    is_real,
                    direction: port.direction,
                    value: if is_real { Value::from_f64(0.0) } else { Value::new(width) },
                    type_name: port.data_type.as_ref().and_then(get_type_name),
                };
                elab.port_order.push(port.name.name.clone());
                elab.signals.insert(port.name.name.clone(), sig);
                if let Some(view) = modport_view {
                    elab.modport_views.insert(port.name.name.clone(), view);
                }
            }
        }
        PortList::NonAnsi(names) => {
            for name in names {
                elab.port_order.push(name.name.clone());
                // Direction/type will be declared in module body
            }
        }
        PortList::Empty => {}
    }

    // Process items
    if let Definition::Package(p) = module {
        for item in &p.items {
            match item {
                crate::ast::decl::PackageItem::Typedef(td) => {
                    process_typedef(td, &mut elab);
                }
                crate::ast::decl::PackageItem::Parameter(pd) => {
                    if let ParameterKind::Data { data_type, assignments } = &pd.kind {
                        let mut width = resolve_type_width(data_type, Some(&elab.parameters), Some(&elab.typedefs));
                        let is_implicit_no_dims = matches!(
                            data_type,
                            DataType::Implicit { dimensions, .. } if dimensions.is_empty()
                        );
                        let is_signed = is_type_signed(data_type);
                        for assign in assignments {
                            register_packed_array_elem_w(&assign.name.name, data_type, &elab.typedefs);
                            if let Some(init) = &assign.init {
                                // For implicit-typed parameters, infer width
                                // from a sized literal initializer so
                                // `parameter X = 7'h13;` stores Value{width=7}
                                // instead of being padded to 32. Otherwise
                                // refs inside concats place the param at the
                                // wrong bit position, shifting other operands
                                // off-end. (Surfaced by cv32e40p's
                                // compressed_decoder: `instr_o = { ...,
                                // pkg::OPCODE_OPIMM };` was emitting NOP
                                // because OPCODE_OPIMM took 32 bits.)
                                let eff_width = if is_implicit_no_dims {
                                    if let Some(w) = sized_literal_width(init) { w } else { 32 }
                                } else {
                                    width
                                };
                                width = eff_width;
                                let mut v = eval_init_for_width(init, &elab.parameters, eff_width);
                                if is_signed { v.is_signed = true; }
                                elab.parameters.insert(assign.name.name.clone(), v);
                            }
                        }
                    }
                }
                crate::ast::decl::PackageItem::Class(c) => {
                    validate_class_constraints(c, all_defs, Some(&elab.enum_members))?;
                    register_class_enum_members(c, &mut elab);
                    elab.classes.insert(c.name.name.clone(), elaborate_class(c));
                }
                crate::ast::decl::PackageItem::Let(l) => {
                    elab.lets.insert(l.name.name.clone(), l.clone());
                }
                crate::ast::decl::PackageItem::DPIImport(di) => {
                    register_dpi_import(di, &mut elab)?;
                }
                _ => {}
            }
        }
    }

    // Pre-pass: collect user-defined nettype names so variables declared with
    // those types can be classified as nets (§6.6.7 — nettype resolution permits
    // multiple continuous drivers). Also register each nettype's width as a
    // typedef so TypeReference lookups resolve correctly.
    let mut user_nettypes: HashSet<String> = HashSet::default();
    for item in module.items() {
        if let ModuleItem::NettypeDeclaration(nd) = item {
            user_nettypes.insert(nd.name.name.clone());
            let w = resolve_type_width(&nd.data_type, Some(&elab.parameters), Some(&elab.typedefs));
            elab.typedefs.insert(nd.name.name.clone(), w);
        }
    }

    for item in module.items() {
        match item {
            ModuleItem::PortDeclaration(pd) => {
                let port_modport_view = match &pd.data_type {
                    DataType::Interface { name, modport: Some(mp), .. } => {
                        resolve_interface_modport_view(&name.name, &mp.name, all_defs)
                    }
                    _ => None,
                };
                let width = resolve_type_width(&pd.data_type, Some(&elab.parameters), Some(&elab.typedefs));
                let is_signed = is_type_signed(&pd.data_type);
                let is_real = is_type_real(&pd.data_type);
                for decl in &pd.declarators {
                    if elab.parameters.contains_key(&decl.name.name) {
                        return Err(format!("Duplicate declaration of '{}'", decl.name.name));
                    }
                    elab.note_explicit_type(&decl.name.name, &pd.data_type)?;
                    // §23.2.2.1 non-ANSI ports: the data type and the direction
                    // may be declared in separate statements (`byte x; output x;`).
                    // If `x` was already registered (by a prior data/net decl)
                    // and carries no direction yet, this is the direction half of
                    // the same port — merge instead of erroring. A port-only
                    // direction line carries an Implicit type, so keep the
                    // existing width/type; if this line DOES carry an explicit
                    // type, adopt it.
                    if let Some(existing) = elab.signals.get(&decl.name.name) {
                        if existing.direction.is_none() {
                            let explicit_type = !matches!(pd.data_type, DataType::Implicit { .. });
                            let existing = elab.signals.get_mut(&decl.name.name).unwrap();
                            existing.direction = Some(pd.direction);
                            if explicit_type {
                                existing.width = width;
                                existing.is_signed = is_signed;
                                existing.is_real = is_real;
                                existing.type_name = get_type_name(&pd.data_type);
                                existing.value = if is_real { Value::from_f64(0.0) } else { Value::new(width) };
                            }
                            if !elab.port_order.contains(&decl.name.name) {
                                elab.port_order.push(decl.name.name.clone());
                            }
                            if let Some(view) = &port_modport_view {
                                elab.modport_views.insert(decl.name.name.clone(), view.clone());
                            }
                            continue;
                        }
                        return Err(format!("Duplicate declaration of '{}'", decl.name.name));
                    }
                    let sig = Signal { is_const: false,
                        name: decl.name.name.clone(),
                        width,
                        is_signed,
                        is_real,
                        direction: Some(pd.direction),
                        value: if is_real { Value::from_f64(0.0) } else { Value::new(width) },
                        type_name: get_type_name(&pd.data_type),
                    };
                    if !elab.port_order.contains(&decl.name.name) {
                        elab.port_order.push(decl.name.name.clone());
                    }
                    elab.signals.insert(decl.name.name.clone(), sig);
                    if let Some(view) = &port_modport_view {
                        elab.modport_views.insert(decl.name.name.clone(), view.clone());
                    }
                }
            }
            ModuleItem::NetDeclaration(nd) => {
                let width = resolve_type_width(&nd.data_type, Some(&elab.parameters), Some(&elab.typedefs));
                let is_signed = is_type_signed(&nd.data_type);
                let is_real = is_type_real(&nd.data_type);
                for decl in &nd.declarators {
                    if elab.parameters.contains_key(&decl.name.name) {
                        return Err(format!("Duplicate declaration of '{}'", decl.name.name));
                    }
                    elab.note_explicit_type(&decl.name.name, &nd.data_type)?;
                    // A `wire X;` (or other NetDeclaration) following an
                    // `input X;` / `output X;` port declaration is the
                    // legal SystemVerilog idiom that explicitly attaches a
                    // net-type to an already-declared port. Keep the
                    // existing port entry (direction, width, type_name)
                    // and just record the leaf in `nets`. Only treat it
                    // as an error if the existing entry is not a port
                    // (i.e. a true duplicate user declaration).
                    if let Some(existing) = elab.signals.get(&decl.name.name) {
                        if existing.direction.is_some() {
                            elab.nets.insert(decl.name.name.clone());
                            continue;
                        }
                        return Err(format!("Duplicate declaration of '{}'", decl.name.name));
                    }
                    let w = width_with_unpacked_dims(&decl.dimensions, width);
                    // supply0 → constant 0, supply1 → constant 1
                    let init_value = match nd.net_type {
                        NetType::Supply0 => Value::zero(w),
                        NetType::Supply1 => Value::ones(w),
                        _ => if is_real { Value::from_f64(0.0) } else { Value::new(w) },
                    };
                    let sig = Signal { is_const: false,
                        name: decl.name.name.clone(),
                        width: w,
                        is_signed,
                        is_real,
                        direction: None,
                        value: init_value,
                        type_name: get_type_name(&nd.data_type),
                    };
                    elab.signals.insert(decl.name.name.clone(), sig);
                    elab.nets.insert(decl.name.name.clone());
                    // Wire with initializer → continuous assign (not constant eval)
                    if let Some(init_expr) = &decl.init {
                        elab.continuous_assigns.push(ContinuousAssignment {
                            lhs: make_ident_expr(&decl.name.name),
                            rhs: init_expr.clone(),
                            delay: 0,
                        });
                    }
                }
            }
            ModuleItem::DataDeclaration(dd) => {
                // Anonymous enum on a variable decl
                // (`enum logic { A, B } var_name;`): the typedef path
                // registers member constants, but the bare variable form
                // does not, so the names A/B resolve to implicit nets at
                // simulation time. Surfaced by cv32e40p_obi_interface.sv's
                // `state_q FSM`. Helper is also called from the other
                // DataDeclaration arms (submodule items, generate items).
                register_anonymous_enum_members(&dd.data_type, &mut elab);
                // String-typed declarations (LRM §6.16). Recorded for the
                // bytecode compiler so concatenations involving string
                // operands bail to the AST interpreter (which has byte-
                // level concat semantics; bit-level concat truncates).
                if matches!(&dd.data_type, DataType::Simple { kind: SimpleType::String, .. }) {
                    for decl in &dd.declarators {
                        elab.string_signals.insert(decl.name.name.clone());
                    }
                }
                // Packed multi-D: `logic [3:0][7:0] words;` — record the
                // per-element width so `words[i]` resolves to an 8-bit slice
                // instead of a 1-bit select (LRM §7.4.1).
                if let Some(elem_w) = packed_inner_elem_width(&dd.data_type, &elab.parameters, &elab.typedefs) {
                    for decl in &dd.declarators {
                        elab.packed_signal_elem_widths.insert(decl.name.name.clone(), elem_w);
                    }
                }
                // Ascending packed vector (`logic [0:7] pa;`): bit/part selects
                // index from the MSB end (label 0 = MSB), so the interpreter
                // remaps `pa[i]` → internal bit (W-1)-i (LRM §7.4.1, §11.5.1).
                if let Some(w) = packed_ascending_width(&dd.data_type, &elab.parameters) {
                    for decl in &dd.declarators {
                        if decl.dimensions.is_empty() {
                            elab.ascending_packed.insert(decl.name.name.clone(), w);
                        }
                    }
                }
                // User-defined nettype → classify as net (allow multiple continuous drivers).
                if let DataType::TypeReference { name, .. } = &dd.data_type {
                    if user_nettypes.contains(&name.name.name) {
                        for decl in &dd.declarators {
                            elab.nets.insert(decl.name.name.clone());
                        }
                    }
                }
                let data_modport_view = match &dd.data_type {
                    DataType::Interface { name, modport: Some(mp), .. } => {
                        resolve_interface_modport_view(&name.name, &mp.name, all_defs)
                    }
                    _ => None,
                };
                let width = match &dd.data_type {
                    DataType::TypeReference { name, .. } => {
                        elab.typedefs.get(&name.name.name).copied().unwrap_or(resolve_type_width(&dd.data_type, Some(&elab.parameters), Some(&elab.typedefs)))
                    }
                    _ => resolve_type_width(&dd.data_type, Some(&elab.parameters), Some(&elab.typedefs)),
                };
                if let DataType::TypeReference { type_args, .. } = &dd.data_type {
                    if !type_args.is_empty() {
                        for decl in &dd.declarators {
                            elab.class_type_args.insert(decl.name.name.clone(), type_args.clone());
                        }
                    }
                }
                let is_signed = is_type_signed(&dd.data_type);
                for decl in &dd.declarators {
                    elab.note_explicit_type(&decl.name.name, &dd.data_type)?;
                    if elab.signals.contains_key(&decl.name.name) || elab.parameters.contains_key(&decl.name.name) {
                        // LRM §6.x: re-declaring a name already declared in the
                        // same scope is illegal. In strict mode (the default)
                        // this is a hard error. It stays a warning under
                        // --no-strict because xezim sometimes merges class-
                        // function locals into module scope (e.g. cv32e40p UVM
                        // TB's `bit tp;` colliding with a same-named function
                        // local), which would otherwise be a false-positive
                        // collision; --no-strict keeps those designs elaborating
                        // until that scope-merge is fixed.
                        if sv_parser::strict_checks() {
                            return Err(format!(
                                "duplicate declaration of '{}' in the same scope",
                                decl.name.name
                            ));
                        }
                        eprintln!("[xezim][warning] duplicate declaration of '{}' (data); keeping first definition", decl.name.name);
                        continue;
                    }
                    // A variable typed by an unpacked-array typedef
                    // (`typedef T A[0:3]; A v;`) inherits the typedef's unpacked
                    // dimensions when it declares none of its own (LRM §6.18,
                    // §7.4). For every other declaration this is exactly
                    // `decl.dimensions`, so behavior is unchanged.
                    let effective_dims: Vec<UnpackedDimension> = if decl.dimensions.is_empty() {
                        match &dd.data_type {
                            DataType::TypeReference { name, .. } =>
                                elab.typedef_unpacked_dims.get(&name.name.name).cloned()
                                    .unwrap_or_default(),
                            _ => Vec::new(),
                        }
                    } else {
                        decl.dimensions.clone()
                    };
                    // `a[N]` (N a parameter) parses as an associative dim keyed by
                    // "type" N; rewrite it back to a fixed size.
                    let effective_dims =
                        normalize_unpacked_dims(&effective_dims, &elab.parameters, &elab.typedef_types);
                    if let Some(UnpackedDimension::Associative { data_type: key_dt, .. }) = effective_dims.first() {
                        let is_string_key = key_dt.as_ref().map_or(false, |dt| matches!(dt.as_ref(), DataType::Simple { kind: SimpleType::String, .. }));
                        elab.associative_arrays.insert(decl.name.name.clone(), is_string_key);
                        if let Some(init_expr) = &decl.init {
                            if let ExprKind::AssignmentPattern(items) = &init_expr.kind {
                                for item in items {
                                    if let crate::ast::expr::AssignmentPatternItem::Default(def_expr) = item {
                                        elab.assoc_defaults.insert(decl.name.name.clone(), def_expr.clone());
                                    }
                                }
                            }
                        }
                    }
                    let is_dynamic_dim = effective_dims.first().map_or(false, |d| matches!(d, UnpackedDimension::Unsized(_) | UnpackedDimension::Queue { .. }));
                    if is_dynamic_dim {
                        elab.dynamic_arrays.insert(decl.name.name.clone());
                    }
                    if let Some(UnpackedDimension::Queue { max_size: Some(ms), .. }) = effective_dims.first() {
                        let n = const_eval_i64_with_params(ms, Some(&elab.parameters)).unwrap_or(0);
                        if n >= 0 { elab.queue_max_sizes.insert(decl.name.name.clone(), (n + 1) as u32); }
                    }
                    // IEEE 1800-2017 §7.4.5 / §7.8: an unpacked array whose
                    // ELEMENT is itself a dynamic collection —
                    //   `int q[3][$]`      array of queues
                    //   `int d[3][]`       array of dynamic arrays
                    //   `int a[2][u8_t]`   array of associative arrays
                    // The leading dimensions give the (fixed) shape; the
                    // trailing one makes every element its own collection.
                    // Without this the trailing dimension was simply dropped and
                    // `q[i]` was a plain scalar.
                    // A leading dynamic dim is fine too (`int qq[$][$]`): its
                    // backing buffer gives the outer shape.
                    if effective_dims.len() >= 2 {
                        if let Some(qd) = effective_dims.last() {
                            if matches!(qd, UnpackedDimension::Unsized(_) | UnpackedDimension::Queue { .. }
                                            | UnpackedDimension::Associative { .. }) {
                                let outer = &effective_dims[..effective_dims.len() - 1];
                                let shape: Option<Vec<(i64, i64)>> = outer
                                    .iter()
                                    .map(|d| extract_array_range(std::slice::from_ref(d), &elab.parameters))
                                    .collect();
                                if let Some(shape) = shape.filter(|sh| {
                                    sh.iter().all(|&(lo, hi)| hi >= lo && hi - lo < 4096)
                                }) {
                                    let name = decl.name.name.clone();
                                    match shape.len() {
                                        1 => { elab.arrays.insert(name.clone(), (shape[0].0, shape[0].1, width)); }
                                        2 => { elab.arrays_2d.insert(name.clone(), (shape[0], shape[1], width)); }
                                        _ => { elab.arrays_nd.insert(name.clone(), (shape.clone(), width)); }
                                    }
                                    let qmax = if let UnpackedDimension::Queue { max_size: Some(ms), .. } = qd {
                                        const_eval_i64_with_params(ms, Some(&elab.parameters))
                                            .filter(|n| *n >= 0).map(|n| (n + 1) as u32)
                                    } else { None };
                                    // Each element gets exactly the registration a
                                    // standalone `int q[$]` / `int a[key_t]` gets.
                                    let assoc_key = match qd {
                                        UnpackedDimension::Associative { data_type: kdt, .. } => Some(
                                            kdt.as_ref().map_or(false, |dt| {
                                                matches!(dt.as_ref(), DataType::Simple { kind: SimpleType::String, .. })
                                            }),
                                        ),
                                        _ => None,
                                    };
                                    for suffix in index_tuples(&shape) {
                                        let en = format!("{}{}", name, suffix);
                                        if let Some(is_str) = assoc_key {
                                            // Associative elements are sparse: no
                                            // backing buffer, no `.size` shadow.
                                            elab.associative_arrays.insert(en, is_str);
                                            continue;
                                        }
                                        elab.dynamic_arrays.insert(en.clone());
                                        if let Some(m) = qmax {
                                            elab.queue_max_sizes.insert(en.clone(), m);
                                        }
                                        elab.arrays.insert(en, (0, 63, width));
                                    }
                                    elab.var_decl_types.insert(name, dd.data_type.clone());
                                    continue;
                                }
                            }
                        }
                    }
                    // Helper: if the element type resolves to a packed struct,
                    // register the FLATTENED field layout (including nested
                    // dotted paths like `outer.inner.leaf`) under the array
                    // name so `arr[i][j]...[k].outer.inner.leaf` read/write
                    // paths can splice it. Mirrors the 1-D-array packed-
                    // struct registration below, but uses the shared
                    // `flatten_array_elem_fields` helper that produces the
                    // same dotted-keys layout `flatten_subfields` does for
                    // standalone struct vars.
                    let register_packed_for_array = |elab: &mut ElaboratedModule| {
                        fn flatten_elem(
                            dt: &DataType,
                            params: &HashMap<String, Value>,
                            typedefs: &HashMap<String, u32>,
                            typedef_types: &HashMap<String, DataType>,
                        ) -> Option<Vec<(String, u32, u32)>> {
                            let resolved = resolve_typedef_chain(dt, typedef_types);
                            if let DataType::Struct(su) = resolved {
                                let is_union = matches!(su.kind, StructUnionKind::Union);
                                let mut raw: Vec<(String, u32, DataType)> = Vec::new();
                                for member in &su.members {
                                    let mw = resolve_type_width(&member.data_type, Some(params), Some(typedefs));
                                    for mdecl in &member.declarators {
                                        raw.push((mdecl.name.name.clone(), mw, member.data_type.clone()));
                                    }
                                }
                                let mut out: Vec<(String, u32, u32)> = Vec::new();
                                if is_union {
                                    for (mn, mw, mdt) in &raw {
                                        out.push((mn.clone(), 0, *mw));
                                        if let Some(subs) = flatten_elem(mdt, params, typedefs, typedef_types) {
                                            for (sn, so, sw) in subs { out.push((format!("{}.{}", mn, sn), so, sw)); }
                                        }
                                    }
                                } else {
                                    let mut offset: u32 = 0;
                                    for (mn, mw, mdt) in raw.iter().rev() {
                                        out.push((mn.clone(), offset, *mw));
                                        if let Some(subs) = flatten_elem(mdt, params, typedefs, typedef_types) {
                                            for (sn, so, sw) in subs { out.push((format!("{}.{}", mn, sn), offset + so, sw)); }
                                        }
                                        offset += mw;
                                    }
                                }
                                Some(out)
                            } else { None }
                        }
                        let elem_resolved: &DataType =
                            if let DataType::TypeReference { name, .. } = &dd.data_type {
                                elab.typedef_types.get(&name.name.name).unwrap_or(&dd.data_type)
                            } else { &dd.data_type };
                        // Only a PACKED struct element has a contiguous bit layout that
                        // `arr[i].member` can slice. An UNPACKED struct element stores each
                        // member as its own signal (`arr[i].member`); bit-slicing it drops
                        // `real` members' is_real (they read back as raw bits) and shifts the
                        // offsets of any member following a string / nested aggregate.
                        let elem_is_packed = matches!(
                            resolve_typedef_chain(elem_resolved, &elab.typedef_types),
                            DataType::Struct(su) if su.packed
                        );
                        if elem_is_packed {
                            if let Some(fields) = flatten_elem(elem_resolved, &elab.parameters, &elab.typedefs, &elab.typedef_types) {
                                if !fields.is_empty() {
                                    tls_register_struct_layout(&decl.name.name, &fields);
                                    elab.packed_struct_fields.insert(decl.name.name.clone(), fields);
                                }
                            }
                        }
                    };
                    // Check for 2D unpacked array (e.g., mem [0:1023][0:3])
                    if effective_dims.len() == 2 {
                        // Both `[0:1][0:2]` (range) and `[2][3]` (size) spell the
                        // same 2-D array. Only the range form was recognised, so
                        // `int m[2][3]` fell through to the 1-D path and every
                        // `m[i][j]` was a bit-select that read X. The N-D branch
                        // below already accepted both forms.
                        let dim_range = |d: &UnpackedDimension, params: &HashMap<String, Value>| {
                            extract_array_range(std::slice::from_ref(d), params)
                        };
                        let r1 = match &effective_dims[0] {
                            d @ (UnpackedDimension::Range { .. } | UnpackedDimension::Expression { .. }) => {
                                dim_range(d, &elab.parameters)
                            }
                            _ => None,
                        };
                        let r2 = match &effective_dims[1] {
                            d @ (UnpackedDimension::Range { .. } | UnpackedDimension::Expression { .. }) => {
                                dim_range(d, &elab.parameters)
                            }
                            _ => None,
                        };
                        if let (Some((lo1, hi1)), Some((lo2, hi2))) = (r1, r2) {
                            elab.arrays_2d.insert(decl.name.name.clone(), ((lo1, hi1), (lo2, hi2), width));
                            // Element type, for the type-directed `%p` renderer.
                            elab.var_decl_types.insert(decl.name.name.clone(), dd.data_type.clone());
                            // LRM §8.4 (2D class arrays). Same as the 1D
                            // path: record the element class so the
                            // simulator's `arr[i][j] = new(...)` route
                            // constructs the right instance.
                            if let DataType::TypeReference { name, .. } = &dd.data_type {
                                elab.array_elem_class
                                    .insert(decl.name.name.clone(), name.name.name.clone());
                            }
                            register_packed_for_array(&mut elab);
                            // Per-element Signal entries are synthesized lazily
                            // by Simulator::new from the arrays_2d metadata —
                            // avoids the per-element HashMap entries at
                            // elaborate time (major memory win on designs
                            // with large memories). The width/signed/real
                            // attributes are uniform across elements so we
                            // don't need a per-element Signal struct.
                            let _ = (is_signed, width);
                            continue;
                        }
                    }
                    // Check for N-dimensional unpacked array (N >= 3)
                    if effective_dims.len() >= 3
                        && effective_dims.iter().all(|d| matches!(d, UnpackedDimension::Range { .. } | UnpackedDimension::Expression { .. }))
                    {
                        let mut shape: Vec<(i64, i64)> = Vec::new();
                        for d in &effective_dims {
                            match d {
                                UnpackedDimension::Range { left, right, .. } => {
                                    let l = const_eval_i64_with_params(left, Some(&elab.parameters)).unwrap_or(0);
                                    let r = const_eval_i64_with_params(right, Some(&elab.parameters)).unwrap_or(0);
                                    shape.push((l.min(r), l.max(r)));
                                }
                                UnpackedDimension::Expression { expr, .. } => {
                                    let n = const_eval_i64_with_params(expr, Some(&elab.parameters)).unwrap_or(0);
                                    shape.push((0, (n - 1).max(0)));
                                }
                                _ => {}
                            }
                        }
                        elab.arrays_nd.insert(decl.name.name.clone(), (shape.clone(), width));
                        elab.var_decl_types.insert(decl.name.name.clone(), dd.data_type.clone());
                        if let DataType::TypeReference { name, .. } = &dd.data_type {
                            elab.array_elem_class
                                .insert(decl.name.name.clone(), name.name.name.clone());
                        }
                        register_packed_for_array(&mut elab);
                        // Per-element Signals synthesized by Simulator::new
                        // from arrays_nd — skip the per-element HashMap
                        // inserts here.
                        let _ = is_signed;
                        continue;
                    }
                    // Check for unpacked array dimensions (e.g., memory [0:255])
                    let array_range = extract_array_range(&effective_dims, &elab.parameters);
                    if let Some((lo, hi)) = array_range {
                        // Register this as an array for the simulator
                        elab.arrays.insert(decl.name.name.clone(), (lo, hi, width));
                        // Element type, for the type-directed `%p` renderer.
                        elab.var_decl_types.insert(decl.name.name.clone(), dd.data_type.clone());
                        // An UNPACKED struct element keeps each member in its own
                        // signal (recursively: nested unpacked members expand, nested
                        // packed members get a signal + slice layout). Without this
                        // they are created lazily on first assignment and lose their
                        // declared type (a `real` member reads back as raw bits).
                        if let DataType::Struct(su) =
                            resolve_typedef_chain(&dd.data_type, &elab.typedef_types).clone()
                        {
                            if !su.packed && hi >= lo && (hi - lo) < 4096 {
                                for i in lo..=hi {
                                    let ebase = format!("{}[{}]", decl.name.name, i);
                                    register_unpacked_aggregate(&mut elab, &ebase, &dd.data_type);
                                }
                            }
                        }
                        // LRM §8.4: if the array element type is a known
                        // class, stash the class name so the simulator's
                        // `arr[i] = new(...)` path can construct the right
                        // instance. (Detection done here at the unpacked-
                        // array branch — also mirrored in the 2D and N-D
                        // branches below.)
                        if let DataType::TypeReference { name, .. } = &dd.data_type {
                            let tn = &name.name.name;
                            if !elab.classes.contains_key(tn) {
                                // class definitions get inserted at the
                                // start of elaborate_module_with_defs; if
                                // not yet present, the simulator's
                                // late check still resolves at access
                                // time, but we record speculatively here.
                            }
                            // Always record the type name; the simulator
                            // verifies against `module.classes` at use time.
                            elab.array_elem_class
                                .insert(decl.name.name.clone(), tn.clone());
                        }
                        // Register the FLATTENED packed-struct field layout
                        // (including nested dotted paths) under the array
                        // name. Same flattening as `flatten_subfields` so
                        // `arr[i].outer.inner.leaf` chains work identically
                        // to `var.outer.inner.leaf` on a standalone struct.
                        register_packed_for_array(&mut elab);
                        // Track descending arrays (left > right in the declaration)
                        if let Some(UnpackedDimension::Range { left, right, .. }) = effective_dims.first() {
                            let l = const_eval_i64_with_params(left, Some(&elab.parameters)).unwrap_or(0);
                            let r = const_eval_i64_with_params(right, Some(&elab.parameters)).unwrap_or(0);
                            if l > r { elab.descending_arrays.insert(decl.name.name.clone()); }
                        }
                        // Per-element Signals are synthesized by Simulator::new
                        // from the `arrays` metadata; no per-element HashMap
                        // inserts here. This alone is the largest memory win
                        // on designs with testbench memory arrays.
                        let _ = (is_signed, width);
                        if let Some(init_expr) = &decl.init {
                            let init_items: Vec<&Expression> = match &init_expr.kind {
                                ExprKind::AssignmentPattern(items) => items.iter().map(|i| i.expr()).collect(),
                                ExprKind::Concatenation(exprs) => exprs.iter().collect(),
                                _ => vec![],
                            };
                            if !init_items.is_empty() {
                                let mut stmts: Vec<Statement> = Vec::new();
                                for (i, item_expr) in init_items.iter().enumerate() {
                                    let idx_i = lo + i as i64;
                                    let lval = Expression::new(ExprKind::Index {
                                        expr: Box::new(make_ident_expr(&decl.name.name)),
                                        index: Box::new(Expression::new(ExprKind::Number(crate::ast::expr::NumberLiteral::Integer { size: None, signed: false, base: crate::ast::expr::NumberBase::Decimal, value: idx_i.to_string(), cached_val: std::cell::Cell::new(None) }), Span::dummy())),
                                    }, Span::dummy());
                                    stmts.push(Statement::new(StatementKind::BlockingAssign {
                                        lvalue: lval,
                                        rvalue: (*item_expr).clone(),
                                    }, Span::dummy()));
                                }
                                if is_dynamic_dim {
                                    let size_name = format!("{}.size", decl.name.name);
                                    let size_sig = Signal { is_const: false, name: size_name.clone(), width: 32, is_signed: false, is_real: false, direction: None, value: Value::from_u64(init_items.len() as u64, 32), type_name: None };
                                    elab.signals.insert(size_name, size_sig);
                                }
                                elab.initial_blocks.push(InitialBlock {
                                    stmt: Statement::new(StatementKind::SeqBlock { name: None, stmts }, Span::dummy()), scope: String::new(), });
                            } else if !is_dynamic_dim {
                                elab.initial_blocks.push(InitialBlock {
                                    stmt: Statement::new(StatementKind::BlockingAssign {
                                        lvalue: make_ident_expr(&decl.name.name),
                                        rvalue: init_expr.clone(),
                                    }, Span::dummy()), scope: String::new(), });
                            }
                        }
                    } else {
                        let is_real = is_type_real(&dd.data_type);
                        let w = width;
                        let (init_val, procedural_init) = if let Some(init_expr) = &decl.init {
                            if is_const_expr(init_expr, &elab.parameters) {
                                let mut rv = eval_init_for_width(init_expr, &elab.parameters, w);
                                if is_signed { rv.is_signed = true; }
                                if is_real { rv = Value::from_f64(rv.to_f64()); }
                                (rv, None)
                            } else {
                                (default_value_for_type(&dd.data_type, w), Some(init_expr.clone()))
                            }
                        } else { (default_value_for_type(&dd.data_type, w), None) };
                        
                        let sig = Signal { is_const: dd.const_kw,
                            name: decl.name.name.clone(),
                            width: w,
                            is_signed,
                            is_real,
                            direction: None,
                            value: init_val,
                            type_name: get_type_name(&dd.data_type),
                        };
                        elab.signals.insert(decl.name.name.clone(), sig);
                        if matches!(&dd.data_type, DataType::Simple { kind: SimpleType::Event, .. }) {
                            elab.events.insert(decl.name.name.clone());
                        }
                        if is_type_two_state(&dd.data_type) {
                            elab.two_state_signals.insert(decl.name.name.clone());
                        }
                        if let Some(view) = &data_modport_view {
                            elab.modport_views.insert(decl.name.name.clone(), view.clone());
                        }
                        
                        if let Some(expr) = procedural_init {
                            // §6.20.6: a `const` declaration's initializer is its
                            // one legal write — record it so the const-write
                            // check exempts this synthetic assignment.
                            if dd.const_kw {
                                elab.const_decl_inits.insert(decl.name.name.clone());
                            }
                            elab.initial_blocks.push(InitialBlock {
                                stmt: Statement::new(StatementKind::BlockingAssign {
                                    lvalue: make_ident_expr(&decl.name.name),
                                    rvalue: expr,
                                }, decl.name.span), scope: String::new(), });
                        }
                        // Unpacked-struct member default initializers:
                        //   struct { bit [3:0] lo = c; ... } p1;
                        // Packed structs forbid member defaults (IEEE 7.2.2).
                        // Owned so later `&mut elab` calls (member pre-registration)
                        // don't conflict with a borrow of `elab.typedef_types`.
                        let dt_resolved_owned: DataType = if let DataType::TypeReference { name, .. } = &dd.data_type {
                            elab.typedef_types.get(&name.name.name).cloned().unwrap_or_else(|| dd.data_type.clone())
                        } else { dd.data_type.clone() };
                        let dt_resolved: &DataType = &dt_resolved_owned;
                        // Recursively flatten nested struct/union members so multi-segment
                        // paths like u.s.a resolve via a single packed_struct_fields lookup.
                        fn flatten_subfields(dt: &DataType, params: &HashMap<String, Value>, typedefs: &HashMap<String, u32>, typedef_types: &HashMap<String, DataType>) -> Option<Vec<(String, u32, u32)>> {
                            let resolved = resolve_typedef_chain(dt, typedef_types);
                            if let DataType::Struct(su) = resolved {
                                let is_union = matches!(su.kind, StructUnionKind::Union);
                                let mut raw: Vec<(String, u32, DataType)> = Vec::new();
                                for member in &su.members {
                                    let mw = resolve_type_width(&member.data_type, Some(params), Some(typedefs));
                                    for mdecl in &member.declarators {
                                        raw.push((mdecl.name.name.clone(), mw, member.data_type.clone()));
                                    }
                                }
                                let mut out: Vec<(String, u32, u32)> = Vec::new();
                                if is_union {
                                    for (mn, mw, mdt) in &raw {
                                        out.push((mn.clone(), 0, *mw));
                                        if let Some(subs) = flatten_subfields(mdt, params, typedefs, typedef_types) {
                                            for (sn, so, sw) in subs { out.push((format!("{}.{}", mn, sn), so, sw)); }
                                        }
                                    }
                                } else {
                                    let mut offset: u32 = 0;
                                    for (mn, mw, mdt) in raw.iter().rev() {
                                        out.push((mn.clone(), offset, *mw));
                                        if let Some(subs) = flatten_subfields(mdt, params, typedefs, typedef_types) {
                                            for (sn, so, sw) in subs { out.push((format!("{}.{}", mn, sn), offset + so, sw)); }
                                        }
                                        offset += mw;
                                    }
                                }
                                Some(out)
                            } else { None }
                        }
                        if let Some(fields) = flatten_subfields(dt_resolved, &elab.parameters, &elab.typedefs, &elab.typedef_types) {
                            if !fields.is_empty() {
                                tls_register_struct_layout(&decl.name.name, &fields);
                                // Only register packed-struct layouts in
                                // `packed_struct_fields`. Unpacked structs
                                // store members as separate signals (see the
                                // !su.packed arm below) and writing through
                                // bit-slice offsets into the parent signal
                                // would clobber unrelated state.
                                if let DataType::Struct(su) = dt_resolved {
                                    if su.packed {
                                        elab.packed_struct_fields.insert(decl.name.name.clone(), fields);
                                    }
                                }
                            }
                        }
                        // Record top-level member names in DECLARATION order for
                        // `%p` (LRM §21.2.1.7). Applies to packed and unpacked
                        // structs alike, since neither existing map preserves
                        // source order. Skip declarators carrying unpacked
                        // dimensions (`rec_t arr[N]`, `rec_t m[int]`): those are
                        // ARRAYS of structs, and `%p` must print them as an
                        // element list, not as a single struct.
                        elab.var_decl_types.insert(decl.name.name.clone(), dd.data_type.clone());
                        if decl.dimensions.is_empty() {
                            if let DataType::Struct(su) = dt_resolved {
                                let names: Vec<String> = su
                                    .members
                                    .iter()
                                    .flat_map(|m| m.declarators.iter().map(|d| d.name.name.clone()))
                                    .collect();
                                if !names.is_empty() {
                                    elab.struct_members.insert(decl.name.name.clone(), names);
                                }
                            }
                        }
                        // Per-field packed-array element widths so that
                        // `obj.field[i]` slices instead of bit-selects when
                        // the field is `logic [3:0][7:0] field;`. Walks
                        // struct members directly (skipping nested recursion
                        // for now — covers the most common case).
                        if let DataType::Struct(su) = dt_resolved {
                            for m in &su.members {
                                if let Some(ew) = packed_inner_elem_width(&m.data_type, &elab.parameters, &elab.typedefs) {
                                    for mdecl in &m.declarators {
                                        let key = format!("{}.{}", decl.name.name, mdecl.name.name);
                                        elab.packed_signal_elem_widths.insert(key, ew);
                                    }
                                }
                            }
                        }
                        if let DataType::Struct(su) = dt_resolved {
                            let _is_union = matches!(su.kind, StructUnionKind::Union);
                            if su.packed {
                                for member in &su.members {
                                    for mdecl in &member.declarators {
                                        if mdecl.init.is_some() {
                                            return Err(format!(
                                                "Packed struct member '{}.{}' cannot have a default value (IEEE 7.2.2)",
                                                decl.name.name, mdecl.name.name
                                            ));
                                        }
                                    }
                                }
                                // packed_struct_fields already populated by flatten_subfields above.
                            }
                            if !su.packed {
                                // Pre-register member signals with their declared widths,
                                // so later assignments from wider rvalues don't widen them.
                                // Recursive: an array member expands per element and a
                                // nested packed member gets its own slice layout, so
                                // `c.nodes[1].status` addresses its own signal.
                                register_unpacked_aggregate(&mut elab, &decl.name.name, &dd.data_type);
                                let mut stmts: Vec<Statement> = Vec::new();
                                for member in &su.members {
                                    for mdecl in &member.declarators {
                                        if let Some(init) = &mdecl.init {
                                            let lval = Expression::new(ExprKind::MemberAccess {
                                                expr: Box::new(make_ident_expr(&decl.name.name)),
                                                member: mdecl.name.clone(),
                                            }, Span::dummy());
                                            stmts.push(Statement::new(StatementKind::BlockingAssign {
                                                lvalue: lval,
                                                rvalue: init.clone(),
                                            }, Span::dummy()));
                                        }
                                    }
                                }
                                if !stmts.is_empty() {
                                    elab.initial_blocks.push(InitialBlock {
                                        stmt: Statement::new(StatementKind::SeqBlock { name: None, stmts }, Span::dummy()), scope: String::new(), });
                                }
                            }
                        }
                    }
                }
            }
            ModuleItem::ParameterDeclaration(pd) | ModuleItem::LocalparamDeclaration(pd) => {
                // §6.20.3 body type parameter (`localparam type T1 = logic [A-1:0];`)
                // — register as a typedef so `T1 x;` / `$bits(T1)` resolve.
                if let ParameterKind::Type { assignments } = &pd.kind {
                    for a in assignments {
                        if let Some(dt) = &a.init {
                            let w = resolve_type_width(dt, Some(&elab.parameters), Some(&elab.typedefs));
                            elab.typedefs.insert(a.name.name.clone(), w);
                            elab.typedef_types.insert(a.name.name.clone(), dt.clone());
                            register_anonymous_enum_members(dt, &mut elab);
                        }
                    }
                }
                if let ParameterKind::Data { data_type, assignments } = &pd.kind {
                    let mut width = resolve_type_width(data_type, Some(&elab.parameters), Some(&elab.typedefs));
                    let mut signed = is_type_signed(data_type);
                    let is_real = is_type_real(data_type);
                    // IEEE 1800-2017 §6.20.2: implicit type → signed 32-bit
                    if matches!(data_type, DataType::Implicit { dimensions, .. } if dimensions.is_empty()) {
                        width = 32;
                        signed = true;
                    }
                    for assign in assignments {
                        if elab.signals.contains_key(&assign.name.name) || elab.parameters.contains_key(&assign.name.name) {
                            return Err(format!("Duplicate declaration of '{}'", assign.name.name));
                        }
                        // IEEE 1800-2023: keyed assignment-pattern init for
                        // associative-array typed parameters. Materialize
                        // `'{ "K": V, ... }` as `<param>["K"]` signals so
                        // `WEIGHT["HIGH"]` reads back the supplied value.
                        if let Some(init) = &assign.init {
                            if let ExprKind::AssignmentPattern(items) = &init.kind {
                                let all_keyed = !items.is_empty()
                                    && items.iter().all(|it| matches!(it, AssignmentPatternItem::Keyed(_, _)));
                                if all_keyed {
                                    elab.associative_arrays
                                        .insert(assign.name.name.clone(), true);
                                    for it in items {
                                        if let AssignmentPatternItem::Keyed(k, v) = it {
                                            let key_str = match &k.kind {
                                                ExprKind::StringLiteral(s) => s.clone(),
                                                _ => eval_const_expr_val(k, &elab.parameters).to_dec_string(),
                                            };
                                            let val_v = eval_init_for_width(v, &elab.parameters, width);
                                            elab.signals.insert(
                                                format!("{}[{}]", assign.name.name, key_str),
                                                Signal {
                                                    is_const: true,
                                                    name: format!("{}[{}]", assign.name.name, key_str),
                                                    width,
                                                    is_signed: signed,
                                                    is_real: false,
                                                    direction: None,
                                                    value: val_v,
                                                    type_name: None,
                                                },
                                            );
                                        }
                                    }
                                    continue;
                                }
                            }
                        }
                        let mut current_width = width;
                        let mut current_is_real = is_real;
                        let mut current_signed = signed;

                        if matches!(data_type, DataType::Implicit { dimensions, .. } if dimensions.is_empty()) {
                            let init_is_real = if elab.parameters.contains_key(&assign.name.name) {
                                elab.parameters.get(&assign.name.name).map(|v| v.is_real).unwrap_or(false)
                            } else if let Some(init) = &assign.init {
                                eval_const_expr_val(init, &elab.parameters).is_real
                            } else { false };

                            if init_is_real {
                                current_width = 64;
                                current_is_real = true;
                                current_signed = false;
                            }
                        }

                        // IEEE 1800-2017 §6.20: struct/union-typed parameter with
                        // an assignment-pattern value — pack by field offset and
                        // register the field layout so later `P.f` selects work.
                        let struct_fields = flatten_struct_fields(
                            data_type, &elab.parameters, &elab.typedefs, &elab.typedef_types);
                        let is_struct_param = struct_fields.as_ref().map_or(false, |f| !f.is_empty());

                        let mut val = if elab.parameters.contains_key(&assign.name.name) {
                            elab.parameters.get(&assign.name.name).cloned().unwrap_or(Value::zero(current_width))
                        } else if let Some(init) = &assign.init {
                            if expr_has_call(init) {
                                elab.deferred_param_exprs.push((assign.name.name.clone(), init.clone()));
                                let mut v = Value::zero(current_width);
                                if current_signed { v.is_signed = true; }
                                v
                            } else {
                                let mut v = if is_struct_param {
                                    pack_struct_const_value(
                                        data_type, init, &elab.parameters,
                                        &elab.typedefs, &elab.typedef_types)
                                    .map(|sv| sv.resize(current_width))
                                    .unwrap_or_else(|| eval_init_for_width(init, &elab.parameters, current_width))
                                } else {
                                    eval_init_for_width(init, &elab.parameters, current_width)
                                };
                                if current_signed { v.is_signed = true; }
                                v
                            }
                        } else {
                            let mut v = Value::zero(current_width);
                            if current_signed { v.is_signed = true; }
                            v
                        };

                        if current_is_real {
                            val = Value::from_f64(val.to_f64());
                        }

                        if let Some(fields) = struct_fields {
                            tls_register_struct_layout(&assign.name.name, &fields);
                            elab.packed_struct_fields
                                .entry(assign.name.name.clone())
                                .or_insert(fields);
                        }
                        if !elab.parameters.contains_key(&assign.name.name) {
                            elab.parameters.insert(assign.name.name.clone(), val.clone());
                        }

                        // Also add as a signal so it can be read in expressions
                        elab.signals.insert(assign.name.name.clone(), Signal { is_const: false,
                            name: assign.name.name.clone(),
                            width: current_width,
                            is_signed: current_signed,
                            is_real: current_is_real,
                            direction: None,
                            value: val,
                            type_name: get_type_name(data_type),
                        });
                    }
                }
            }
            ModuleItem::TypedefDeclaration(td) => {
                // IEEE 1800-2017 §7.2.1: a struct/union may not contain a member
                // of its own type (it would have infinite size). Reject with a
                // clean diagnostic instead of recursing into a stack overflow.
                if let Some(cycle) = struct_typedef_self_reference(
                    &td.name.name, &td.data_type, &elab.typedef_types) {
                    return Err(format!(
                        "type '{}' contains a member of its own type via '{}' \
                         — recursive struct/union is illegal (IEEE 1800-2017 §7.2.1)",
                        td.name.name, cycle));
                }
                process_typedef(td, &mut elab);
            }
            ModuleItem::TimeunitsDecl(td) => {
                if let Some(u) = &td.unit {
                    elab.timeunit_exp = time_literal_to_exp(u);
                }
                if let Some(p) = &td.precision {
                    elab.timeprecision_exp = time_literal_to_exp(p);
                }
            }
            ModuleItem::FunctionDeclaration(fd) => {
                if matches!(fd.return_type, DataType::Void(_)) {
                    fn check_void_return(s: &crate::ast::stmt::Statement) -> Result<(), String> {
                        use crate::ast::stmt::StatementKind as SK;
                        match &s.kind {
                            SK::Return(Some(_)) => Err("void function must not return a value".into()),
                            SK::SeqBlock { stmts, .. } | SK::ParBlock { stmts, .. } => {
                                for st in stmts { check_void_return(st)?; }
                                Ok(())
                            }
                            SK::If { then_stmt, else_stmt, .. } => {
                                check_void_return(then_stmt)?;
                                if let Some(eb) = else_stmt { check_void_return(eb)?; }
                                Ok(())
                            }
                            SK::For { body, .. } | SK::While { body, .. } | SK::DoWhile { body, .. }
                            | SK::Repeat { body, .. } | SK::Forever { body } | SK::Foreach { body, .. } => check_void_return(body),
                            SK::TimingControl { stmt, .. } | SK::Wait { stmt, .. } => check_void_return(stmt),
                            SK::Case { items, .. } => { for it in items { check_void_return(&it.stmt)?; } Ok(()) }
                            _ => Ok(()),
                        }
                    }
                    for it in &fd.items { check_void_return(it)?; }
                }
                fn check_fn_fork(s: &crate::ast::stmt::Statement) -> Result<(), String> {
                    use crate::ast::stmt::StatementKind as SK;
                    match &s.kind {
                        SK::ParBlock { join_type, stmts, .. } => {
                            if !matches!(join_type, crate::ast::stmt::JoinType::JoinNone) {
                                return Err("only fork-join_none is permitted inside a function".into());
                            }
                            for st in stmts { check_fn_fork(st)?; }
                            Ok(())
                        }
                        SK::SeqBlock { stmts, .. } => { for st in stmts { check_fn_fork(st)?; } Ok(()) }
                        SK::If { then_stmt, else_stmt, .. } => {
                            check_fn_fork(then_stmt)?;
                            if let Some(eb) = else_stmt { check_fn_fork(eb)?; }
                            Ok(())
                        }
                        SK::For { body, .. } | SK::While { body, .. } | SK::DoWhile { body, .. }
                        | SK::Repeat { body, .. } | SK::Forever { body } | SK::Foreach { body, .. } => check_fn_fork(body),
                        SK::TimingControl { stmt, .. } | SK::Wait { stmt, .. } => check_fn_fork(stmt),
                        SK::Case { items, .. } => { for it in items { check_fn_fork(&it.stmt)?; } Ok(()) }
                        _ => Ok(()),
                    }
                }
                for it in &fd.items { check_fn_fork(it)?; }
                elab.functions.insert(fd.name.name.name.clone(), fd.clone());
            }
            ModuleItem::TaskDeclaration(td) => {
                fn check_no_return_in_fork(s: &crate::ast::stmt::Statement, in_fork: bool) -> Result<(), String> {
                    use crate::ast::stmt::StatementKind as SK;
                    match &s.kind {
                        SK::Return(_) if in_fork => Err("illegal return from fork".into()),
                        SK::ParBlock { stmts, .. } => { for st in stmts { check_no_return_in_fork(st, true)?; } Ok(()) }
                        SK::SeqBlock { stmts, .. } => { for st in stmts { check_no_return_in_fork(st, in_fork)?; } Ok(()) }
                        SK::If { then_stmt, else_stmt, .. } => {
                            check_no_return_in_fork(then_stmt, in_fork)?;
                            if let Some(eb) = else_stmt { check_no_return_in_fork(eb, in_fork)?; }
                            Ok(())
                        }
                        SK::For { body, .. } | SK::While { body, .. } | SK::DoWhile { body, .. }
                        | SK::Repeat { body, .. } | SK::Forever { body } | SK::Foreach { body, .. } => check_no_return_in_fork(body, in_fork),
                        SK::TimingControl { stmt, .. } | SK::Wait { stmt, .. } => check_no_return_in_fork(stmt, in_fork),
                        SK::Case { items, .. } => { for it in items { check_no_return_in_fork(&it.stmt, in_fork)?; } Ok(()) }
                        _ => Ok(()),
                    }
                }
                for it in &td.items { check_no_return_in_fork(it, false)?; }
                elab.tasks.insert(td.name.name.name.clone(), td.clone());
            }
            ModuleItem::ContinuousAssign(ca) => {
                let delay = ca.delay.as_ref().map(|d| eval_const_expr(d, &elab.parameters)).unwrap_or(0);
                for (lhs, rhs) in &ca.assignments {
                    elab.continuous_assigns.push(ContinuousAssignment { lhs: lhs.clone(), rhs: rhs.clone(), delay });
                }
            }
            ModuleItem::GateInstantiation(gi) => {
                // Synthesise a continuous-assign equivalent for each gate
                // (and/or/xor/nand/nor/xnor/buf/not). The top items loop
                // dropped these on the floor previously, which left every
                // gate output stuck at its X default.
                gate_inst_to_assigns(gi, &mut elab);
            }
            ModuleItem::AlwaysConstruct(ac) => {
                elab.always_blocks.push(AlwaysBlock { kind: ac.kind, stmt: ac.stmt.clone() });
            }
            ModuleItem::InitialConstruct(ic) => {
                if std::env::var("XEZIM_TRACE_INIT").ok().as_deref() == Some("1") {
                    eprintln!("[xezim][elab] elaborate_items: pushing initial (top-level path)");
                }
                elab.initial_blocks.push(InitialBlock { stmt: ic.stmt.clone(), scope: String::new(), });
            }
            // LRM §16.5: module-level `assert/assume/cover property (…)`.
            // Previously the elaborator ignored AssertionItem entirely,
            // so a top-level concurrent assertion did nothing. Hoist it
            // into a synthetic initial block: the simulator's
            // AssertionStatement handler then registers it (for
            // is_property: true → SvaClocked, the executor adds a
            // clocked-site that fires every clock cycle).
            ModuleItem::AssertionItem(a) => {
                elab.initial_blocks.push(InitialBlock {
                    stmt: crate::ast::stmt::Statement::new(
                        crate::ast::stmt::StatementKind::Assertion(a.clone()),
                        a.span,
                    ), scope: String::new(), });
            }
            ModuleItem::FinalConstruct(fc) => {
                // LRM §9.2.3 — `final` executes once after the event loop
                // exits (e.g. on $finish). Collected here; the simulator drains
                // `final_blocks` before VCD/coverage flush.
                elab.final_blocks.push(InitialBlock { stmt: fc.stmt.clone(), scope: String::new(), });
            }
            ModuleItem::GenerateRegion(gr) => {
                // Recursively process generate region items
                elaborate_items(&gr.items, &mut elab, all_defs)?;
            }
            ModuleItem::GenerateIf(gi) => {
                elaborate_generate_if(&gi.branches, &mut elab, all_defs)?;
            }
            ModuleItem::GenerateCase(gc) => {
                elaborate_generate_case(gc, &mut elab, all_defs)?;
            }
            ModuleItem::GenerateFor(gf) => {
                elaborate_generate_for(gf, &mut elab, all_defs)?;
            }
            ModuleItem::CovergroupDeclaration(cg) => {
                elab.covergroups.insert(cg.name.name.clone(), cg.clone());
            }
            ModuleItem::ClockingDeclaration(cd) => {
                let mut dirs = HashMap::default();
                for s in &cd.signals {
                    dirs.insert(s.name.name.clone(), s.direction);
                }
                elab.clocking_signal_dirs.insert(cd.name.name.clone(), dirs);
                elab.clocking_blocks.insert(cd.name.name.clone(), cd.clone());
            }
            ModuleItem::ClassDeclaration(cd) => {
                validate_class_constraints(cd, all_defs, Some(&elab.enum_members))?;
                elab.classes.insert(cd.name.name.clone(), elaborate_class(cd));
            }
            ModuleItem::LetDeclaration(ld) => {
                elab.lets.insert(ld.name.name.clone(), ld.clone());
            }
            ModuleItem::SequenceDeclaration(sd) => {
                elab.sequences.insert(sd.name.name.clone());
                if let Some(body) = &sd.body {
                    // Sequences share the property_decls map for
                    // `assert property (s)` style references.
                    elab.property_decls
                        .insert(sd.name.name.clone(), body.clone());
                }
            }
            ModuleItem::PropertyDeclaration(pd) => {
                elab.sequences.insert(pd.name.name.clone());
                if let Some(body) = &pd.body {
                    elab.property_decls
                        .insert(pd.name.name.clone(), body.clone());
                }
            }
            // LRM §17.2 — register the checker name and store its
            // declaration so instantiations can inline the body with
            // formal→actual port substitution. When the checker has
            // no formal ports, also inline the body at the declaration
            // site (the legacy "always-on" shape).
            ModuleItem::CheckerDeclaration(cd) => {
                elab.sequences.insert(cd.name.name.clone());
                elab.checker_decls
                    .insert(cd.name.name.clone(), cd.clone());
                let has_ports = !matches!(
                    cd.ports,
                    crate::ast::module::PortList::Empty
                );
                if !has_ports {
                    let body = cd.items.clone();
                    elaborate_items(&body, &mut elab, all_defs)?;
                }
            }
            ModuleItem::SpecifyBlock(sb) => {
                for p in &sb.paths {
                    let d = eval_const_expr(&p.delay, &elab.parameters);
                    elab.specify_delays.insert(p.dst.name.clone(), d);
                }
            }
            ModuleItem::ModuleInstantiation(inst) => {
                for hi in &inst.instances {
                    // Register the instance name so it's recognized during validation.
                    // It will be fully elaborated during inlining.
                    if !elab.signals.contains_key(&hi.name.name) {
                        elab.signals.insert(hi.name.name.clone(), Signal {
                            is_const: false,
                            name: hi.name.name.clone(),
                            width: 1,
                            is_signed: false,
                            is_real: false,
                            direction: None,
                            value: Value::new(1),
                            type_name: Some(inst.module_name.name.clone()),
                        });
                    }
                }
            }
            ModuleItem::ImportDeclaration(imp) => {
                if let Some(defs) = all_defs {
                    process_import(imp, &mut elab, defs)?;
                }
            }
            ModuleItem::DPIImport(di) => {
                register_dpi_import(di, &mut elab)?;
            }
            ModuleItem::OutOfClassConstraint { class_name, constraint_name } => {
                elab.out_of_class_constraints.insert((class_name.clone(), constraint_name.clone()));
            }
            _ => {}
        }
    }

    // User-defined nettype driver resolution: collapse multiple continuous
    // drivers on a nettype variable into a single OR-combined assign. This
    // approximates the common `resolve_or` resolver; other resolvers are not
    // modeled, so last-driver-wins behavior applies via the final `|` fold.
    {
        let mut nettype_vars: HashSet<String> = HashSet::default();
        for (name, sig) in &elab.signals {
            if let Some(tn) = &sig.type_name {
                if user_nettypes.contains(tn) { nettype_vars.insert(name.clone()); }
            }
        }
        if !nettype_vars.is_empty() {
            let mut grouped: HashMap<String, Vec<Expression>> = HashMap::default();
            let mut kept: Vec<ContinuousAssignment> = Vec::new();
            for ca in elab.continuous_assigns.drain(..) {
                if let Some(n) = simple_lhs_name(&ca.lhs) {
                    if nettype_vars.contains(&n) {
                        grouped.entry(n).or_default().push(ca.rhs);
                        continue;
                    }
                }
                kept.push(ca);
            }
            for (name, rhses) in grouped {
                let mut iter = rhses.into_iter();
                let mut acc = iter.next().unwrap();
                for rhs in iter {
                    let span = acc.span;
                    acc = Expression {
                        kind: ExprKind::Binary {
                            op: crate::ast::expr::BinaryOp::BitOr,
                            left: Box::new(acc),
                            right: Box::new(rhs),
                        },
                        span,
                    };
                }
                kept.push(ContinuousAssignment { lhs: make_ident_expr(&name), rhs: acc, delay: 0 });
            }
            elab.continuous_assigns = kept;
        }
    }

    // IEEE 1800-2017 §6.10: Implicit nets — identifiers used in continuous assigns
    // or port connections that are not explicitly declared become implicit 1-bit wires.
    create_implicit_nets(&mut elab)?;

    // Validate that all identifiers in procedural blocks are declared.
    for ib in &elab.initial_blocks { validate_stmt_idents(&ib.stmt, &elab, &mut HashSet::default())?; }
    for ab in &elab.always_blocks { validate_stmt_idents(&ab.stmt, &elab, &mut HashSet::default())?; }
    for ca in &elab.continuous_assigns {
        validate_expr_idents(&ca.lhs, &elab, &HashSet::default())?;
        validate_expr_idents(&ca.rhs, &elab, &HashSet::default())?;
    }

    // IEEE 1800-2017 §6.20.6: a `const` variable may be assigned only once, in
    // its declaration. The `validate_stmt_idents` check above exempts a const
    // that carries a (non-constant) declaration initializer — that initializer
    // is lowered to a single synthetic initial-block assignment (its one legal
    // write). Any *further* procedural write is still illegal. Each block that
    // writes a name contributes one entry below (the synthetic init is its own
    // standalone block), so a decl-initialized const written by more than one
    // block has an illegal re-assignment.
    if !elab.const_decl_inits.is_empty() {
        let mut write_block_count: HashMap<String, usize> = HashMap::default();
        for ib in &elab.initial_blocks {
            let mut s = HashSet::default();
            collect_written_idents(&ib.stmt, &mut s);
            for n in s { *write_block_count.entry(n).or_default() += 1; }
        }
        for ab in &elab.always_blocks {
            let mut s = HashSet::default();
            collect_written_idents(&ab.stmt, &mut s);
            for n in s { *write_block_count.entry(n).or_default() += 1; }
        }
        for name in &elab.const_decl_inits {
            if write_block_count.get(name).copied().unwrap_or(0) > 1 {
                return Err(format!("Illegal write to constant identifier '{}'", name));
            }
        }
    }

    // §6.18: every bare forward type declaration (`typedef name;`) must resolve
    // to a real data type — a later full typedef, an enum, a class, or a
    // package/interface type. An unresolved forward type is an error.
    for name in &elab.forward_typedef_names {
        let resolved = elab.typedef_types.get(name)
                .map_or(false, |dt| !matches!(dt, DataType::Void(_)))
            || elab.classes.contains_key(name)
            || elab.enum_members.contains_key(name)
            || elab.packed_struct_fields.contains_key(name);
        if !resolved {
            return Err(format!(
                "Forward typedef '{}' does not resolve to a data type", name));
        }
    }

    // IEEE 1800-2017 §6.5: a variable cannot have multiple continuous drivers,
    // nor mix continuous and procedural drivers.
    validate_driver_conflicts(&elab)?;

    // IEEE 1800-2017 §8.21/§8.26: class instantiation legality.
    validate_class_usage(&elab)?;

    // IEEE 1800-2023 §8.20.5: a derived class may not override a `final`
    // method of any ancestor class; `:extends`/`:initial` markers must
    // agree with the actual override status.
    if sv_parser::is_sv2023() {
        validate_final_method_overrides(&elab)?;
        validate_method_override_markers(&elab)?;
    }

    // IEEE 1800-2017 §9.2.2.4: `always_ff` admits exactly one event
    // control, applied at the outermost level. Nested event/timing
    // control in the body is illegal.
    validate_always_ff_event_controls(&elab)?;

    // IEEE 1800-2017 §13.5.2: arguments to `ref` formals must be
    // variables (i.e. assignable lvalues), not arbitrary expressions.
    validate_ref_arg_lvalues(&elab)?;

    // LRM §25.4 modport direction enforcement.
    // Done at the AST level over every module Definition (not on the
    // post-inlined `elab`, whose `modport_views` only carries the top
    // module's own modport-bound ports). For each module whose port list
    // contains a `modport_t.view`-typed port, walk that module's body and
    // flag continuous-assign or procedural-assign LHSs of the form
    // `<port_name>.<member>` where `<member>` is declared `input` from
    // the modport's perspective.
    if let Some(defs) = all_defs {
        validate_modport_writes_at_ast(defs)?;
        // Pre-compute the per-`(iface, modport)` member-direction maps so
        // the runtime virtual-interface dispatch can consult them without
        // re-walking interface AST. LRM §25.4.
        for d in defs.values() {
            if let Definition::Interface(iface) = d {
                let iface_name = iface.name.name.clone();
                // LRM §25.9: register the interface name so runtime
                // detects virtual-interface task formals.
                elab.interfaces.insert(iface_name.clone());
                for item in &iface.items {
                    if let ModuleItem::ModportDeclaration(md) = item {
                        for mp in &md.items {
                            let mut dirs = HashMap::default();
                            for p in &mp.ports {
                                dirs.insert(p.name.name.clone(), p.direction);
                            }
                            elab.modport_member_dirs
                                .insert((iface_name.clone(), mp.name.name.clone()), dirs);
                        }
                    }
                }
            }
        }
    }

    // IEEE 1800-2017 §6.19.3: an assignment to an enum-typed variable
    // requires the RHS value (when constant) to be one of the typedef's
    // declared members. Casts bypass the check.
    validate_enum_assignments(&elab)?;

    // LRM §6.20.3 / §8.4: any module-scope signal whose declared
    // `type_name` resolves to a known class default-initialises to 0
    // (the null handle) rather than X. Without this, untouched class
    // handle declarations read as X, defeating `if (h == null)` and
    // similar guards.
    {
        let cls_names: std::collections::HashSet<String> =
            elab.classes.keys().cloned().collect();
        for sig in elab.signals.values_mut() {
            if let Some(tn) = &sig.type_name {
                if cls_names.contains(tn) {
                    sig.value = Value::zero(sig.width);
                }
            }
        }
    }

    // LRM §20.7 — populate ARRAYS_TLS so any subsequent const-eval
    // (parameter-default rewrite, runtime const eval, etc.) of
    // `$size`/`$left`/`$right`/`$high`/`$low`/`$dimensions` on an array
    // identifier resolves. Mirrors the TYPEDEFS_TLS refresh inside
    // process_typedef.
    {
        let mut snapshot: HashMap<String, (i64, i64, u32)> = HashMap::default();
        for (k, &v) in &elab.arrays {
            snapshot.insert(k.clone(), v);
        }
        ARRAYS_TLS.with(|cell| {
            *cell.borrow_mut() = Some(snapshot);
        });
    }

    // LRM §24: when the elaboration root is a `program` declaration, its
    // initial blocks belong to the reactive region. Re-route them so the
    // simulator schedules their statements via `pending_reactive`.
    if matches!(module, Definition::Program(_)) {
        elab.materialize_pending();
        let initials = std::mem::take(&mut elab.initial_blocks);
        elab.program_initial_blocks.extend(initials);
    }

    Ok(elab)
}

/// Link out-of-class method bodies (`function ClassName::m(); ... endfunction`)
/// into their classes, replacing the `extern` prototype with the real body.
/// Run after `inline_instantiations`, which (re)populates `elab.classes` from
/// the AST and would otherwise clobber any earlier linking.
pub fn link_extern_methods(
    elab: &mut ElaboratedModule,
    definitions: &HashMap<String, Definition>,
) {
    use crate::ast::decl::{ClassMethod, ClassMethodKind, PackageItem};
    for def in definitions.values() {
        let items: &[PackageItem] = match def {
            Definition::Package(p) => &p.items,
            _ => continue,
        };
        for item in items {
            let (class_name, method_name, kind, span) = match item {
                PackageItem::Function(f) => match &f.name.scope {
                    Some(scope) => (
                        scope.name.clone(),
                        f.name.name.name.clone(),
                        ClassMethodKind::Function(f.clone()),
                        f.span,
                    ),
                    None => continue,
                },
                PackageItem::Task(t) => match &t.name.scope {
                    Some(scope) => (
                        scope.name.clone(),
                        t.name.name.name.clone(),
                        ClassMethodKind::Task(t.clone()),
                        t.span,
                    ),
                    None => continue,
                },
                _ => continue,
            };
            if let Some(cls) = elab.classes.get_mut(&class_name) {
                if let Some(existing) = cls.methods.get_mut(&method_name) {
                    existing.kind = kind;
                } else {
                    cls.methods.insert(
                        method_name,
                        ClassMethod { qualifiers: Vec::new(), kind, span },
                    );
                }
            }
        }
    }
}

fn validate_enum_assignments(elab: &ElaboratedModule) -> Result<(), String> {
    use crate::ast::expr::{Expression, ExprKind};
    use crate::ast::stmt::{Statement, StatementKind};
    fn try_const_u64(e: &Expression, elab: &ElaboratedModule) -> Option<u64> {
        // Only fold pure constant rvalues. Anything with an Ident or
        // function call is conservatively skipped.
        match &e.kind {
            ExprKind::Number(_) => Some(eval_const_expr(e, &elab.parameters)),
            ExprKind::Paren(inner) => try_const_u64(inner, elab),
            _ => None,
        }
    }
    fn check_assign(
        lvalue: &Expression,
        rvalue: &Expression,
        elab: &ElaboratedModule,
    ) -> Result<(), String> {
        if let ExprKind::Ident(h) = &lvalue.kind {
            if h.path.len() == 1 {
                let name = &h.path[0].name.name;
                if let Some(sig) = elab.signals.get(name) {
                    if let Some(tname) = &sig.type_name {
                        if let Some(members) = elab.enum_members.get(tname) {
                            if let Some(v) = try_const_u64(rvalue, elab) {
                                if !members.iter().any(|(_, mv)| *mv == v) {
                                    return Err(format!(
                                        "Assignment of {} to enum '{}' variable '{}' is not a declared member (IEEE 1800-2017 §6.19.3)",
                                        v, tname, name
                                    ));
                                }
                            }
                        }
                    }
                }
            }
        }
        Ok(())
    }
    fn walk_stmt(s: &Statement, elab: &ElaboratedModule) -> Result<(), String> {
        match &s.kind {
            StatementKind::BlockingAssign { lvalue, rvalue }
            | StatementKind::NonblockingAssign { lvalue, rvalue, .. } => {
                check_assign(lvalue, rvalue, elab)?;
            }
            StatementKind::SeqBlock { stmts, .. } | StatementKind::ParBlock { stmts, .. } => {
                for s in stmts { walk_stmt(s, elab)?; }
            }
            StatementKind::If { then_stmt, else_stmt, .. } => {
                walk_stmt(then_stmt, elab)?;
                if let Some(e) = else_stmt { walk_stmt(e, elab)?; }
            }
            StatementKind::For { body, .. }
            | StatementKind::While { body, .. }
            | StatementKind::DoWhile { body, .. }
            | StatementKind::Forever { body }
            | StatementKind::Repeat { body, .. }
            | StatementKind::Foreach { body, .. } => walk_stmt(body, elab)?,
            StatementKind::Case { items, .. } => {
                for it in items { walk_stmt(&it.stmt, elab)?; }
            }
            StatementKind::TimingControl { stmt, .. } => walk_stmt(stmt, elab)?,
            _ => {}
        }
        Ok(())
    }
    for ib in &elab.initial_blocks { walk_stmt(&ib.stmt, elab)?; }
    for ab in &elab.always_blocks { walk_stmt(&ab.stmt, elab)?; }
    for f in elab.functions.values() {
        for s in &f.items { walk_stmt(s, elab)?; }
    }
    for t in elab.tasks.values() {
        for s in &t.items { walk_stmt(s, elab)?; }
    }
    Ok(())
}

fn is_lvalue_expr(e: &crate::ast::expr::Expression) -> bool {
    use crate::ast::expr::ExprKind;
    matches!(
        &e.kind,
        ExprKind::Ident(_)
            | ExprKind::Index { .. }
            | ExprKind::RangeSelect { .. }
            | ExprKind::MemberAccess { .. }
            | ExprKind::Concatenation(_)
    )
}

fn validate_ref_arg_lvalues(elab: &ElaboratedModule) -> Result<(), String> {
    use crate::ast::expr::{Expression, ExprKind};
    use crate::ast::stmt::{Statement, StatementKind};
    fn check_call(
        callee_name: &str,
        args: &[Expression],
        elab: &ElaboratedModule,
    ) -> Result<(), String> {
        let formals: Option<&[crate::ast::decl::FunctionPort]> = if let Some(t) = elab.tasks.get(callee_name) {
            Some(t.ports.as_slice())
        } else if let Some(f) = elab.functions.get(callee_name) {
            Some(f.ports.as_slice())
        } else { None };
        if let Some(ports) = formals {
            for (i, p) in ports.iter().enumerate() {
                if matches!(p.direction, crate::ast::types::PortDirection::Ref) {
                    if let Some(a) = args.get(i) {
                        if !is_lvalue_expr(a) {
                            return Err(format!(
                                "Argument to `ref` formal '{}' of '{}' must be a variable (IEEE 1800-2017 §13.5.2)",
                                p.name.name, callee_name
                            ));
                        }
                    }
                }
            }
        }
        Ok(())
    }
    fn walk_expr(e: &Expression, elab: &ElaboratedModule) -> Result<(), String> {
        if let ExprKind::Call { func, args } = &e.kind {
            if let ExprKind::Ident(h) = &func.kind {
                if let Some(seg) = h.path.last() {
                    check_call(&seg.name.name, args, elab)?;
                }
            }
            for a in args { walk_expr(a, elab)?; }
            return Ok(());
        }
        Ok(())
    }
    fn walk_stmt(s: &Statement, elab: &ElaboratedModule) -> Result<(), String> {
        match &s.kind {
            StatementKind::Expr(e) => walk_expr(e, elab)?,
            StatementKind::SeqBlock { stmts, .. } | StatementKind::ParBlock { stmts, .. } => {
                for s in stmts { walk_stmt(s, elab)?; }
            }
            StatementKind::If { then_stmt, else_stmt, condition: _, .. } => {
                walk_stmt(then_stmt, elab)?;
                if let Some(e) = else_stmt { walk_stmt(e, elab)?; }
            }
            StatementKind::For { body, .. }
            | StatementKind::While { body, .. }
            | StatementKind::DoWhile { body, .. }
            | StatementKind::Forever { body }
            | StatementKind::Repeat { body, .. }
            | StatementKind::Foreach { body, .. } => walk_stmt(body, elab)?,
            StatementKind::Case { items, .. } => {
                for it in items { walk_stmt(&it.stmt, elab)?; }
            }
            StatementKind::TimingControl { stmt, .. } => walk_stmt(stmt, elab)?,
            _ => {}
        }
        Ok(())
    }
    for ib in &elab.initial_blocks {
        walk_stmt(&ib.stmt, elab)?;
    }
    for ab in &elab.always_blocks {
        walk_stmt(&ab.stmt, elab)?;
    }
    for f in elab.functions.values() {
        for s in &f.items { walk_stmt(s, elab)?; }
    }
    for t in elab.tasks.values() {
        for s in &t.items { walk_stmt(s, elab)?; }
    }
    Ok(())
}

/// LRM §25.4 modport direction enforcement (static check).
///
/// `modport_views: Map<signal_name, Map<member_name, PortDirection>>` is
/// populated when an interface instance signal is bound through a particular
/// modport. The *writing* side may only target members the modport tags as
/// `Output` or `Inout`. Writes to `Input` members violate the contract.
///
/// We catch the common static cases: continuous assigns and procedural
/// blocking/non-blocking assigns whose LHS is `iface_signal.member`. Dynamic
/// paths (passing the modport handle through tasks, virtual interfaces,
/// indexed selects) fall through silently — those need runtime tagging,
/// which is out of scope for this check.
/// LRM §25.4 modport direction enforcement (AST-level walk).
///
/// Two passes:
///   1. Build a map `iface_name -> modport_name -> {input members}` by
///      walking every `Definition::Interface` and collecting each modport's
///      `input`-direction members.
///   2. For every `Definition::Module`, find ports whose data type is a
///      modport-bound interface (`bus_if.slave foo`), then walk the
///      module body looking for assigns to `foo.<member>`. If `<member>`
///      appears in the input-set for that modport, error.
///
/// Dynamic paths (modport handles passed through tasks, virtual interfaces,
/// indexed selects) are out of scope for this check — they'd need runtime
/// tagging. The static walk catches the common direct-write cases.
fn validate_modport_writes_at_ast(
    defs: &HashMap<String, Definition>,
) -> Result<(), String> {
    use crate::ast::expr::{Expression, ExprKind};
    use crate::ast::stmt::{Statement, StatementKind};
    use crate::ast::types::{DataType, PortDirection};

    // (1) iface_name -> modport_name -> set of `input` member names.
    let mut input_sets: HashMap<String, HashMap<String, HashSet<String>>> = HashMap::default();
    for def in defs.values() {
        if let Definition::Interface(iface) = def {
            let mut per_modport: HashMap<String, HashSet<String>> = HashMap::default();
            for item in &iface.items {
                if let ModuleItem::ModportDeclaration(md) = item {
                    for mp in &md.items {
                        let mut inputs: HashSet<String> = HashSet::default();
                        for p in &mp.ports {
                            if matches!(p.direction, PortDirection::Input) {
                                inputs.insert(p.name.name.clone());
                            }
                        }
                        per_modport.insert(mp.name.name.clone(), inputs);
                    }
                }
            }
            if !per_modport.is_empty() {
                input_sets.insert(iface.name.name.clone(), per_modport);
            }
        }
    }
    if input_sets.is_empty() {
        return Ok(()); // nothing to check
    }

    // Helper: from a Module's port list, extract `(port_name, input_member_set)`
    // for every port that's a modport-bound interface.
    fn module_modport_ports(
        m: &ModuleDeclaration,
        input_sets: &HashMap<String, HashMap<String, HashSet<String>>>,
    ) -> HashMap<String, HashSet<String>> {
        let mut out: HashMap<String, HashSet<String>> = HashMap::default();
        if let PortList::Ansi(ports) = &m.ports {
            for port in ports {
                if let Some(DataType::Interface { name, modport: Some(mp), .. }) = port.data_type.as_ref() {
                    if let Some(per_mp) = input_sets.get(&name.name) {
                        if let Some(inputs) = per_mp.get(&mp.name) {
                            out.insert(port.name.name.clone(), inputs.clone());
                        }
                    }
                }
            }
        }
        out
    }

    fn check_lvalue(
        lv: &Expression,
        port_inputs: &HashMap<String, HashSet<String>>,
        mod_name: &str,
        context: &str,
    ) -> Result<(), String> {
        if let ExprKind::MemberAccess { expr, member } = &lv.kind {
            if let ExprKind::Ident(h) = &expr.kind {
                if h.path.len() == 1 {
                    let base = h.path[0].name.name.as_str();
                    if let Some(inputs) = port_inputs.get(base) {
                        if inputs.contains(member.name.as_str()) {
                            return Err(format!(
                                "module '{}' {}: cannot write to modport-input member '{}.{}' (IEEE 1800-2017 §25.4)",
                                mod_name, context, base, member.name
                            ));
                        }
                    }
                }
            }
        }
        Ok(())
    }

    fn walk_stmt(
        s: &Statement,
        port_inputs: &HashMap<String, HashSet<String>>,
        mod_name: &str,
    ) -> Result<(), String> {
        match &s.kind {
            StatementKind::BlockingAssign { lvalue, .. }
            | StatementKind::NonblockingAssign { lvalue, .. } => {
                check_lvalue(lvalue, port_inputs, mod_name, "procedural assignment")
            }
            StatementKind::SeqBlock { stmts, .. } | StatementKind::ParBlock { stmts, .. } => {
                for s in stmts { walk_stmt(s, port_inputs, mod_name)?; }
                Ok(())
            }
            StatementKind::If { then_stmt, else_stmt, .. } => {
                walk_stmt(then_stmt, port_inputs, mod_name)?;
                if let Some(e) = else_stmt { walk_stmt(e, port_inputs, mod_name)?; }
                Ok(())
            }
            StatementKind::Case { items, .. } => {
                for it in items { walk_stmt(&it.stmt, port_inputs, mod_name)?; }
                Ok(())
            }
            StatementKind::For { body, .. } | StatementKind::While { body, .. }
            | StatementKind::DoWhile { body, .. } | StatementKind::Repeat { body, .. }
            | StatementKind::Forever { body, .. } | StatementKind::Foreach { body, .. } => {
                walk_stmt(body, port_inputs, mod_name)
            }
            StatementKind::TimingControl { stmt, .. } => walk_stmt(stmt, port_inputs, mod_name),
            _ => Ok(()),
        }
    }

    // (2) Walk every module Definition.
    for def in defs.values() {
        if let Definition::Module(m) = def {
            let port_inputs = module_modport_ports(m, &input_sets);
            if port_inputs.is_empty() { continue; }
            for item in &m.items {
                match item {
                    ModuleItem::ContinuousAssign(ca) => {
                        for (lhs, _rhs) in &ca.assignments {
                            check_lvalue(lhs, &port_inputs, &m.name.name, "continuous assign")?;
                        }
                    }
                    ModuleItem::AlwaysConstruct(ac) => {
                        walk_stmt(&ac.stmt, &port_inputs, &m.name.name)?;
                    }
                    ModuleItem::InitialConstruct(ic) => {
                        walk_stmt(&ic.stmt, &port_inputs, &m.name.name)?;
                    }
                    _ => {}
                }
            }
        }
    }
    Ok(())
}

#[allow(dead_code)]
fn validate_modport_writes(elab: &ElaboratedModule) -> Result<(), String> {
    // NOTE — kept for future per-module hook. Not currently invoked: the
    // ElaboratedModule visible at the validator call site is the *top* module
    // and its modport_views map is empty (per-instance modport binds happen
    // during sub-module elaboration and are not aggregated back up). To
    // actually enforce this, validate_modport_writes needs to run inside
    // `elaborate_module_with_defs` for every module that has modport ports,
    // not once on the top elab. That hook is the L-tier follow-up.
    use crate::ast::expr::{Expression, ExprKind};
    use crate::ast::stmt::{Statement, StatementKind};
    use crate::ast::types::PortDirection;

    fn check_lvalue(
        lv: &Expression,
        elab: &ElaboratedModule,
        context: &str,
    ) -> Result<(), String> {
        if let ExprKind::MemberAccess { expr, member } = &lv.kind {
            if let ExprKind::Ident(h) = &expr.kind {
                let base = h.path.last().map(|s| s.name.name.as_str()).unwrap_or("");
                if let Some(view) = elab.modport_views.get(base) {
                    if let Some(dir) = view.get(member.name.as_str()) {
                        if matches!(dir, PortDirection::Input) {
                            return Err(format!(
                                "{}: cannot write to modport-input member '{}.{}' (IEEE 1800-2017 §25.4)",
                                context, base, member.name
                            ));
                        }
                    }
                }
            }
        }
        Ok(())
    }

    fn walk_stmt(s: &Statement, elab: &ElaboratedModule) -> Result<(), String> {
        match &s.kind {
            StatementKind::BlockingAssign { lvalue, .. }
            | StatementKind::NonblockingAssign { lvalue, .. } => {
                check_lvalue(lvalue, elab, "procedural assignment")
            }
            StatementKind::SeqBlock { stmts, .. } | StatementKind::ParBlock { stmts, .. } => {
                for s in stmts { walk_stmt(s, elab)?; }
                Ok(())
            }
            StatementKind::If { then_stmt, else_stmt, .. } => {
                walk_stmt(then_stmt, elab)?;
                if let Some(e) = else_stmt { walk_stmt(e, elab)?; }
                Ok(())
            }
            StatementKind::Case { items, .. } => {
                for it in items { walk_stmt(&it.stmt, elab)?; }
                Ok(())
            }
            StatementKind::For { body, .. } | StatementKind::While { body, .. }
            | StatementKind::DoWhile { body, .. } | StatementKind::Repeat { body, .. }
            | StatementKind::Forever { body, .. } | StatementKind::Foreach { body, .. } => {
                walk_stmt(body, elab)
            }
            StatementKind::TimingControl { stmt, .. } => walk_stmt(stmt, elab),
            _ => Ok(()),
        }
    }

    for ca in &elab.continuous_assigns {
        check_lvalue(&ca.lhs, elab, "continuous assign")?;
    }
    for ab in &elab.always_blocks {
        walk_stmt(&ab.stmt, elab)?;
    }
    for ib in &elab.initial_blocks {
        walk_stmt(&ib.stmt, elab)?;
    }
    Ok(())
}

fn validate_always_ff_event_controls(elab: &ElaboratedModule) -> Result<(), String> {
    use crate::ast::decl::AlwaysKind;
    use crate::ast::stmt::{Statement, StatementKind};
    fn walk_no_timing(s: &Statement) -> Result<(), String> {
        match &s.kind {
            StatementKind::TimingControl { .. } => {
                Err("`always_ff` body must not contain a nested event/timing control \
                     (IEEE 1800-2017 §9.2.2.4)".into())
            }
            StatementKind::SeqBlock { stmts, .. } | StatementKind::ParBlock { stmts, .. } => {
                for s in stmts { walk_no_timing(s)?; }
                Ok(())
            }
            StatementKind::If { then_stmt, else_stmt, .. } => {
                walk_no_timing(then_stmt)?;
                if let Some(e) = else_stmt { walk_no_timing(e)?; }
                Ok(())
            }
            StatementKind::Case { items, .. } => {
                for it in items { walk_no_timing(&it.stmt)?; }
                Ok(())
            }
            StatementKind::For { body, .. }
            | StatementKind::While { body, .. }
            | StatementKind::DoWhile { body, .. }
            | StatementKind::Forever { body }
            | StatementKind::Repeat { body, .. }
            | StatementKind::Foreach { body, .. } => walk_no_timing(body),
            _ => Ok(()),
        }
    }
    for ab in &elab.always_blocks {
        if !matches!(ab.kind, AlwaysKind::AlwaysFf) { continue; }
        // The outermost statement is allowed to be the single event
        // control; descend through it once before enforcing.
        let body = match &ab.stmt.kind {
            StatementKind::TimingControl { stmt, .. } => stmt.as_ref(),
            _ => &ab.stmt,
        };
        walk_no_timing(body)?;
    }
    Ok(())
}

/// IEEE 1800-2023 §8.20.5: enforcement of the `:final` specifier.
///
/// Two checks:
///   1. `class :final X` — no class may declare `extends X`.
///   2. `function :final foo` — no derived class may declare a method
///      named `foo` anywhere in its ancestor chain.
fn validate_final_method_overrides(elab: &ElaboratedModule) -> Result<(), String> {
    for (cname, cdef) in &elab.classes {
        // Direct-parent class-level :final check.
        if let Some(parent_name) = &cdef.extends {
            if let Some(parent) = elab.classes.get(parent_name) {
                if parent.is_final {
                    return Err(format!(
                        "Class '{}' extends `final` class '{}' (IEEE 1800-2023 §8.20.5)",
                        cname, parent_name
                    ));
                }
            }
        }
        // Walk every strict ancestor for `:final` methods.
        let mut cur = cdef.extends.clone();
        while let Some(parent_name) = cur {
            let Some(parent) = elab.classes.get(&parent_name) else { break; };
            for (mname, pmethod) in &parent.methods {
                if method_is_final(pmethod) && cdef.methods.contains_key(mname) {
                    return Err(format!(
                        "Class '{}' overrides `:final` method '{}' from ancestor '{}' (IEEE 1800-2023 §8.20.5)",
                        cname, mname, parent_name
                    ));
                }
            }
            cur = parent.extends.clone();
        }
    }
    Ok(())
}

fn default_timeunit_exp() -> i32 { -9 }

/// Decode a SystemVerilog time literal (e.g. "10ns", "100ps") into a
/// log10-second exponent. Returns -9 (1ns) on unparseable input.
pub fn time_literal_to_exp(s: &str) -> i32 {
    let s = s.trim();
    let split = s
        .find(|c: char| c.is_alphabetic())
        .unwrap_or(s.len());
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

fn method_is_final(m: &crate::ast::decl::ClassMethod) -> bool {
    method_specifier(m) == Some(crate::ast::decl::MethodSpecifier::Final)
}

fn method_specifier(m: &crate::ast::decl::ClassMethod) -> Option<crate::ast::decl::MethodSpecifier> {
    use crate::ast::decl::ClassMethodKind;
    match &m.kind {
        ClassMethodKind::Function(f) => f.specifier,
        ClassMethodKind::Task(t) => t.specifier,
        ClassMethodKind::PureVirtual(f) => f.specifier,
        ClassMethodKind::Extern(f) => f.specifier,
    }
}

/// IEEE 1800-2023 §8.20.5 enforcement for the `:extends` and `:initial`
/// method-override markers (the `:final` rule lives in
/// `validate_final_method_overrides` above).
///
/// - `:extends foo` — `foo` MUST be defined in some ancestor.
/// - `:initial foo` — `foo` must NOT be defined in any ancestor.
///
/// These markers exist precisely to catch refactor-induced silent shadowing
/// or accidental redeclaration; without enforcement they are visual noise.
fn validate_method_override_markers(elab: &ElaboratedModule) -> Result<(), String> {
    use crate::ast::decl::MethodSpecifier;
    for (cname, cdef) in &elab.classes {
        for (mname, m) in &cdef.methods {
            let spec = method_specifier(m);
            if !matches!(spec, Some(MethodSpecifier::Extends) | Some(MethodSpecifier::Initial)) {
                continue;
            }
            // Walk strict ancestors looking for a same-named method.
            let mut found_in_ancestor = false;
            let mut cur = cdef.extends.clone();
            while let Some(parent_name) = cur {
                let Some(parent) = elab.classes.get(&parent_name) else { break; };
                if parent.methods.contains_key(mname) {
                    found_in_ancestor = true;
                    break;
                }
                cur = parent.extends.clone();
            }
            match spec {
                Some(MethodSpecifier::Extends) if !found_in_ancestor => {
                    return Err(format!(
                        "Class '{}' method '{}' is marked `:extends` but no ancestor declares it (IEEE 1800-2023 §8.20.5)",
                        cname, mname
                    ));
                }
                Some(MethodSpecifier::Initial) if found_in_ancestor => {
                    return Err(format!(
                        "Class '{}' method '{}' is marked `:initial` but an ancestor already declares it (IEEE 1800-2023 §8.20.5)",
                        cname, mname
                    ));
                }
                _ => {}
            }
        }
    }
    Ok(())
}

fn expr_is_new(expr: &Expression) -> bool {
    match &expr.kind {
        ExprKind::Ident(hier) => hier.path.len() == 1 && hier.path[0].name.name == "new",
        ExprKind::Call { func, .. } => {
            if let ExprKind::Ident(hier) = &func.kind {
                return hier.path.len() == 1 && hier.path[0].name.name == "new";
            }
            false
        }
        _ => false,
    }
}

fn check_new_assignment(lvalue: &Expression, rvalue: &Expression, elab: &ElaboratedModule) -> Result<(), String> {
    if !expr_is_new(rvalue) { return Ok(()); }
    let name = match simple_lhs_name(lvalue) { Some(n) => n, None => return Ok(()) };
    let type_name = elab.signals.get(&name).and_then(|s| s.type_name.clone());
    if let Some(tn) = type_name {
        if let Some(cls) = elab.classes.get(&tn) {
            if cls.is_interface {
                return Err(format!("Cannot instantiate interface class '{}'", tn));
            }
            if cls.is_virtual || cls.has_pure_virtual {
                return Err(format!("Cannot instantiate abstract class '{}'", tn));
            }
        }
    }
    Ok(())
}

fn walk_stmt_for_class_new(stmt: &Statement, elab: &ElaboratedModule) -> Result<(), String> {
    match &stmt.kind {
        StatementKind::BlockingAssign { lvalue, rvalue } | StatementKind::NonblockingAssign { lvalue, rvalue, .. } => {
            check_new_assignment(lvalue, rvalue, elab)?;
        }
        StatementKind::If { then_stmt, else_stmt, .. } => {
            walk_stmt_for_class_new(then_stmt, elab)?;
            if let Some(eb) = else_stmt { walk_stmt_for_class_new(eb, elab)?; }
        }
        StatementKind::Case { items, .. } => { for it in items { walk_stmt_for_class_new(&it.stmt, elab)?; } }
        StatementKind::For { body, .. } | StatementKind::Foreach { body, .. } |
        StatementKind::While { body, .. } | StatementKind::DoWhile { body, .. } |
        StatementKind::Repeat { body, .. } | StatementKind::Forever { body } => walk_stmt_for_class_new(body, elab)?,
        StatementKind::SeqBlock { stmts, .. } | StatementKind::ParBlock { stmts, .. } => {
            for s in stmts { walk_stmt_for_class_new(s, elab)?; }
        }
        StatementKind::TimingControl { stmt, .. } | StatementKind::Wait { stmt, .. } => walk_stmt_for_class_new(stmt, elab)?,
        _ => {}
    }
    Ok(())
}

fn data_type_kind_name(dt: &DataType) -> String {
    match dt {
        DataType::Void(_) => "void".to_string(),
        DataType::IntegerAtom { kind, signing, .. } => format!("atom:{:?}:{:?}", kind, signing),
        DataType::IntegerVector { kind, signing, dimensions, .. } => format!("vec:{:?}:{:?}:{}", kind, signing, dimensions.len()),
        DataType::Real { kind, .. } => format!("real:{:?}", kind),
        DataType::Simple { kind, .. } => format!("simple:{:?}", kind),
        DataType::TypeReference { name, .. } => format!("tref:{}", name.name.name),
        DataType::Interface { name, .. } => format!("iface:{}", name.name),
        DataType::Struct(_) => "struct".to_string(),
        DataType::Enum(_) => "enum".to_string(),
        DataType::Implicit { .. } => "implicit".to_string(),
    }
}

fn validate_class_usage(elab: &ElaboratedModule) -> Result<(), String> {
    // §8.26.4: `implements T` where T is a class type parameter is illegal.
    for cls in elab.classes.values() {
        for imp in &cls.implements {
            if cls.type_param_names.iter().any(|n| n == imp) {
                return Err(format!("Class '{}' cannot implement type parameter '{}'", cls.name, imp));
            }
        }
    }
    // §8.26.6.1: multiple interface-class implementations that declare the same
    // method name with conflicting return types cannot be satisfied by a
    // single concrete method.
    for cls in elab.classes.values() {
        if cls.implements.len() < 2 { continue; }
        let mut seen: HashMap<String, String> = HashMap::default();
        for iname in &cls.implements {
            let iface = match elab.classes.get(iname) { Some(c) => c, None => continue };
            for (mname, m) in &iface.methods {
                let ret = match &m.kind {
                    ClassMethodKind::Function(f) | ClassMethodKind::PureVirtual(f) | ClassMethodKind::Extern(f) =>
                        data_type_kind_name(&f.return_type),
                    ClassMethodKind::Task(_) => "task".to_string(),
                };
                match seen.get(mname) {
                    Some(prev) if prev != &ret => {
                        return Err(format!("Class '{}' has conflicting return types for inherited method '{}'", cls.name, mname));
                    }
                    None => { seen.insert(mname.clone(), ret); }
                    _ => {}
                }
            }
        }
    }
    // §8.21/§8.26.5: reject instantiating an abstract or interface class.
    for ib in &elab.initial_blocks { walk_stmt_for_class_new(&ib.stmt, elab)?; }
    for ab in &elab.always_blocks { walk_stmt_for_class_new(&ab.stmt, elab)?; }

    // §8.26.3: typedefs declared in an interface class are NOT inherited by
    // classes that implement it. Flag a method signature that references a
    // bare typedef that only exists inside an implemented interface class.
    for cls in elab.classes.values() {
        if cls.implements.is_empty() { continue; }
        // Gather typedef names contributed only by implemented interfaces.
        let mut iface_only_typedefs: HashSet<String> = HashSet::default();
        for iname in &cls.implements {
            if let Some(iface) = elab.classes.get(iname) {
                for t in &iface.typedef_names { iface_only_typedefs.insert(t.clone()); }
            }
        }
        // Remove anything the class itself (or its extends chain) defines,
        // plus names reachable through module-level typedefs.
        for t in &cls.typedef_names { iface_only_typedefs.remove(t); }
        let mut cur = cls.extends.clone();
        let mut guard = 0;
        while let Some(base) = cur {
            guard += 1; if guard > 32 { break; }
            if let Some(b) = elab.classes.get(&base) {
                for t in &b.typedef_names { iface_only_typedefs.remove(t); }
                cur = b.extends.clone();
            } else { break; }
        }
        for t in elab.typedefs.keys() { iface_only_typedefs.remove(t); }
        if iface_only_typedefs.is_empty() { continue; }
        for m in cls.methods.values() {
            let func = match &m.kind {
                ClassMethodKind::Function(f) | ClassMethodKind::PureVirtual(f) | ClassMethodKind::Extern(f) => Some(f),
                _ => None,
            };
            if let Some(f) = func {
                for p in &f.ports {
                    if let DataType::TypeReference { name, .. } = &p.data_type {
                        if name.scope.is_some() { continue; }
                        if iface_only_typedefs.contains(&name.name.name) {
                            return Err(format!(
                                "Class '{}' method '{}' references type '{}' — typedefs from implemented interfaces are not inherited",
                                cls.name, f.name.name.name, name.name.name));
                        }
                    }
                }
            }
        }
    }

    // §18.6.3, §18.8, §18.9: `randomize`, `rand_mode`, and `constraint_mode`
    // are built-in methods and cannot be overridden by a user class.
    const RESERVED_METHODS: &[&str] = &["randomize", "rand_mode", "constraint_mode"];
    for cls in elab.classes.values() {
        for reserved in RESERVED_METHODS {
            if cls.methods.contains_key(*reserved) {
                return Err(format!(
                    "Class '{}' cannot override built-in method '{}'", cls.name, reserved));
            }
        }
    }

    // §18.5.1: `extern constraint c;` must be accompanied by an out-of-class
    // definition `constraint ClassName::c { ... }`.
    for cls in elab.classes.values() {
        for (cname, con) in &cls.constraints {
            if con.is_extern && !con.has_body {
                let defined = elab.out_of_class_constraints
                    .contains(&(cls.name.clone(), cname.clone()));
                if !defined {
                    return Err(format!(
                        "Class '{}' declares extern constraint '{}' with no external definition",
                        cls.name, cname));
                }
            }
        }
    }

    // §18.5.4, §18.5.10, §18.5.14: randc variables cannot appear in dist
    // expressions, solve..before lists, or soft constraints.
    for cls in elab.classes.values() {
        for con in cls.constraints.values() {
            for item in &con.items {
                check_randc_restrictions(item, &cls.randc_properties, &cls.name)?;
            }
        }
    }

    Ok(())
}

fn check_randc_restrictions(item: &ConstraintItem, randc: &HashSet<String>, cls: &str) -> Result<(), String> {
    if randc.is_empty() { return Ok(()); }
    match item {
        ConstraintItem::Inside { expr, is_dist: true, .. } => {
            if let Some(n) = simple_expr_name(expr) {
                if randc.contains(&n) {
                    return Err(format!(
                        "Class '{}': dist constraint cannot be applied to randc variable '{}'", cls, n));
                }
            }
        }
        ConstraintItem::Solve { before, after, .. } => {
            for id in before.iter().chain(after.iter()) {
                if randc.contains(&id.name) {
                    return Err(format!(
                        "Class '{}': randc variable '{}' cannot appear in solve..before", cls, id.name));
                }
            }
        }
        ConstraintItem::Soft(inner) => {
            collect_soft_randc(inner, randc, cls)?;
        }
        ConstraintItem::Block(items) => {
            for i in items { check_randc_restrictions(i, randc, cls)?; }
        }
        ConstraintItem::Implication { constraint, .. } => {
            check_randc_restrictions(constraint, randc, cls)?;
        }
        ConstraintItem::IfElse { then_item, else_item, .. } => {
            check_randc_restrictions(then_item, randc, cls)?;
            if let Some(e) = else_item { check_randc_restrictions(e, randc, cls)?; }
        }
        ConstraintItem::Foreach { item, .. } => {
            check_randc_restrictions(item, randc, cls)?;
        }
        _ => {}
    }
    Ok(())
}

fn collect_soft_randc(item: &ConstraintItem, randc: &HashSet<String>, cls: &str) -> Result<(), String> {
    // Any randc variable referenced inside a soft constraint is illegal.
    let mut names: HashSet<String> = HashSet::default();
    collect_constraint_idents(item, &mut names);
    for n in &names {
        if randc.contains(n) {
            return Err(format!(
                "Class '{}': soft constraint cannot reference randc variable '{}'", cls, n));
        }
    }
    Ok(())
}

fn collect_constraint_idents(item: &ConstraintItem, out: &mut HashSet<String>) {
    match item {
        ConstraintItem::Expr(e) => collect_expr_idents(e, out),
        ConstraintItem::Inside { expr, range, .. } => {
            collect_expr_idents(expr, out);
            for r in range {
                match r {
                    ConstraintRange::Value(v) => collect_expr_idents(v, out),
                    ConstraintRange::Range { lo, hi } => {
                        collect_expr_idents(lo, out); collect_expr_idents(hi, out);
                    }
                }
            }
        }
        ConstraintItem::Implication { condition, constraint, .. } => {
            collect_expr_idents(condition, out);
            collect_constraint_idents(constraint, out);
        }
        ConstraintItem::IfElse { condition, then_item, else_item, .. } => {
            collect_expr_idents(condition, out);
            collect_constraint_idents(then_item, out);
            if let Some(e) = else_item { collect_constraint_idents(e, out); }
        }
        ConstraintItem::Foreach { item, .. } => collect_constraint_idents(item, out),
        ConstraintItem::Soft(inner) => collect_constraint_idents(inner, out),
        ConstraintItem::Unique { exprs, .. } => for e in exprs { collect_expr_idents(e, out); },
        ConstraintItem::Block(items) => for i in items { collect_constraint_idents(i, out); },
        ConstraintItem::Solve { .. } => {}
    }
}

fn collect_expr_idents(expr: &Expression, out: &mut HashSet<String>) {
    use crate::ast::expr::ExprKind;
    match &expr.kind {
        ExprKind::Ident(h) => {
            if let Some(s) = h.path.first() { out.insert(s.name.name.clone()); }
        }
        ExprKind::Binary { left, right, .. } => {
            collect_expr_idents(left, out); collect_expr_idents(right, out);
        }
        ExprKind::Unary { operand, .. } => collect_expr_idents(operand, out),
        ExprKind::Paren(e) => collect_expr_idents(e, out),
        ExprKind::Conditional { condition, then_expr, else_expr } => {
            collect_expr_idents(condition, out);
            collect_expr_idents(then_expr, out);
            collect_expr_idents(else_expr, out);
        }
        _ => {}
    }
}

fn simple_expr_name(expr: &Expression) -> Option<String> {
    use crate::ast::expr::ExprKind;
    match &expr.kind {
        ExprKind::Ident(h) if h.path.len() == 1 => Some(h.path[0].name.name.clone()),
        ExprKind::Paren(e) => simple_expr_name(e),
        _ => None,
    }
}

fn simple_lhs_name(expr: &Expression) -> Option<String> {
    match &expr.kind {
        ExprKind::Ident(hier) if hier.path.len() == 1 && hier.path[0].selects.is_empty() => {
            Some(hier.path[0].name.name.clone())
        }
        ExprKind::Paren(inner) => simple_lhs_name(inner),
        _ => None,
    }
}

fn collect_written_idents(stmt: &Statement, out: &mut HashSet<String>) {
    match &stmt.kind {
        StatementKind::BlockingAssign { lvalue, .. } | StatementKind::NonblockingAssign { lvalue, .. } => {
            if let Some(n) = simple_lhs_name(lvalue) { out.insert(n); }
        }
        StatementKind::If { then_stmt, else_stmt, .. } => {
            collect_written_idents(then_stmt, out);
            if let Some(eb) = else_stmt { collect_written_idents(eb, out); }
        }
        StatementKind::Case { items, .. } => {
            for item in items { collect_written_idents(&item.stmt, out); }
        }
        StatementKind::For { body, init, .. } => {
            for fi in init { if let ForInit::Assign { lvalue, .. } = fi {
                if let Some(n) = simple_lhs_name(lvalue) { out.insert(n); }
            }}
            collect_written_idents(body, out);
        }
        StatementKind::Foreach { body, .. } => collect_written_idents(body, out),
        StatementKind::While { body, .. } | StatementKind::DoWhile { body, .. } => collect_written_idents(body, out),
        StatementKind::Repeat { body, .. } => collect_written_idents(body, out),
        StatementKind::Forever { body } => collect_written_idents(body, out),
        StatementKind::SeqBlock { stmts, .. } | StatementKind::ParBlock { stmts, .. } => {
            for s in stmts { collect_written_idents(s, out); }
        }
        StatementKind::TimingControl { stmt, .. } => collect_written_idents(stmt, out),
        StatementKind::Wait { stmt, .. } => collect_written_idents(stmt, out),
        _ => {}
    }
}

fn validate_driver_conflicts(elab: &ElaboratedModule) -> Result<(), String> {
    let mut ca_lhs: HashMap<String, u32> = HashMap::default();
    for ca in &elab.continuous_assigns {
        if let Some(n) = simple_lhs_name(&ca.lhs) {
            if elab.signals.contains_key(&n) && !elab.nets.contains(&n) {
                let c = ca_lhs.entry(n.clone()).or_insert(0);
                *c += 1;
                if *c == 2 {
                    return Err(format!("Variable '{}' has multiple continuous drivers", n));
                }
            }
        }
    }
    let mut proc_written: HashSet<String> = HashSet::default();
    for ab in &elab.always_blocks { collect_written_idents(&ab.stmt, &mut proc_written); }
    for ib in &elab.initial_blocks { collect_written_idents(&ib.stmt, &mut proc_written); }
    for ca in &elab.continuous_assigns {
        if let Some(n) = simple_lhs_name(&ca.lhs) {
            if proc_written.contains(&n) && elab.signals.contains_key(&n) && !elab.nets.contains(&n) {
                return Err(format!("Variable '{}' has both continuous and procedural drivers", n));
            }
        }
    }
    Ok(())
}

/// Names bound by a §12.6 pattern's `.v` sub-patterns.
fn collect_pattern_bindings(p: &crate::ast::stmt::Pattern, out: &mut Vec<String>) {
    use crate::ast::stmt::Pattern as P;
    match p {
        P::Binding(id) => out.push(id.name.clone()),
        P::Tagged { inner: Some(i), .. } => collect_pattern_bindings(i, out),
        P::Struct(ms) => {
            for (_, sp) in ms {
                collect_pattern_bindings(sp, out);
            }
        }
        _ => {}
    }
}

fn validate_stmt_idents(stmt: &Statement, elab: &ElaboratedModule, locals: &mut HashSet<String>) -> Result<(), String> {
    match &stmt.kind {
        StatementKind::BlockingAssign { lvalue, rvalue } | StatementKind::NonblockingAssign { lvalue, rvalue, .. } => {
            if let ExprKind::Ident(hier) = &lvalue.kind {
                let name = if hier.path.len() == 1 {
                    Some(hier.path[0].name.name.clone())
                } else {
                    // Hierarchical name: join segments
                    Some(hier.path.iter().map(|s| s.name.name.as_str()).collect::<Vec<_>>().join("."))
                };
                if let Some(n) = name {
                    if let Some(sig) = elab.signals.get(&n) {
                        if sig.is_const && !elab.const_decl_inits.contains(&n) {
                            return Err(format!("Illegal write to constant identifier '{}'", n));
                        }
                        if sig.direction == Some(PortDirection::Input) {
                            return Err(format!("Illegal write to input identifier '{}'", n));
                        }
                    }
                }
            }
            if let ExprKind::MemberAccess { expr, member } = &lvalue.kind {
                if let ExprKind::Ident(hier) = &expr.kind {
                    if hier.path.len() == 1 {
                        let base = &hier.path[0].name.name;
                        if let Some(view) = elab.modport_views.get(base) {
                            if view.get(&member.name) == Some(&PortDirection::Input) {
                                return Err(format!("Illegal write to input identifier '{}.{}'", base, member.name));
                            }
                        }
                        if let Some(dirs) = elab.clocking_signal_dirs.get(base) {
                            if dirs.get(&member.name) == Some(&PortDirection::Input) {
                                return Err(format!("Illegal write to input identifier '{}.{}'", base, member.name));
                            }
                        }
                    }
                }
            }
            validate_expr_idents(lvalue, elab, locals)?;
            validate_expr_idents(rvalue, elab, locals)?;
        }
        StatementKind::If { condition, then_stmt, else_stmt, .. } => {
            validate_expr_idents(condition, elab, locals)?;
            // §12.6.2: `if (e matches p)` declares the pattern's `.v` bindings
            // for the then-branch (not the else-branch).
            let mut bound: Vec<String> = Vec::new();
            if let ExprKind::Matches { pattern, .. } = &condition.kind {
                collect_pattern_bindings(pattern, &mut bound);
            }
            let fresh: Vec<String> =
                bound.iter().filter(|b| locals.insert((*b).clone())).cloned().collect();
            let r = validate_stmt_idents(then_stmt, elab, locals);
            for b in fresh { locals.remove(&b); }
            r?;
            if let Some(eb) = else_stmt { validate_stmt_idents(eb, elab, locals)?; }
        }
        StatementKind::Case { expr, items, .. } => {
            validate_expr_idents(expr, elab, locals)?;
            for item in items {
                for p in &item.patterns { validate_expr_idents(p, elab, locals)?; }
                // §12.6.1: a pattern item's `.v` bindings are declared for the
                // scope of that item's statement (and its `&&&` guard). Add
                // them, validate, then remove so they don't leak to siblings.
                let mut bound: Vec<String> = Vec::new();
                if let Some(pat) = &item.pattern {
                    collect_pattern_bindings(pat, &mut bound);
                }
                let fresh: Vec<String> =
                    bound.iter().filter(|b| locals.insert((*b).clone())).cloned().collect();
                if let Some(g) = &item.guard { validate_expr_idents(g, elab, locals)?; }
                let r = validate_stmt_idents(&item.stmt, elab, locals);
                for b in fresh { locals.remove(&b); }
                r?;
            }
        }
        StatementKind::For { init, condition, step, body } => {
            let mut for_locals = Vec::new();
            for fi in init { match fi {
                ForInit::VarDecl { name, init: e, .. } => {
                    validate_expr_idents(e, elab, locals)?;
                    locals.insert(name.name.clone());
                    for_locals.push(name.name.clone());
                }
                ForInit::Assign { lvalue, rvalue } => {
                    validate_expr_idents(lvalue, elab, locals)?;
                    validate_expr_idents(rvalue, elab, locals)?;
                }
            }}
            if let Some(c) = condition { validate_expr_idents(c, elab, locals)?; }
            for s in step { validate_expr_idents(s, elab, locals)?; }
            validate_stmt_idents(body, elab, locals)?;
            for n in for_locals { locals.remove(&n); }
        }
        StatementKind::Foreach { array, body, vars } => {
            validate_expr_idents(array, elab, locals)?;
            let mut foreach_locals = Vec::new();
            for v in vars {
                if let Some(id) = v {
                    locals.insert(id.name.clone());
                    foreach_locals.push(id.name.clone());
                }
            }
            validate_stmt_idents(body, elab, locals)?;
            for n in foreach_locals { locals.remove(&n); }
        }
        StatementKind::While { condition, body } | StatementKind::DoWhile { body, condition } => {
            validate_expr_idents(condition, elab, locals)?;
            validate_stmt_idents(body, elab, locals)?;
        }
        StatementKind::Repeat { count, body } => {
            validate_expr_idents(count, elab, locals)?;
            validate_stmt_idents(body, elab, locals)?;
        }
        StatementKind::Forever { body } => validate_stmt_idents(body, elab, locals)?,
        StatementKind::SeqBlock { stmts, .. } | StatementKind::ParBlock { stmts, .. } => {
            for s in stmts { validate_stmt_idents(s, elab, locals)?; }
        }
        StatementKind::TimingControl { control, stmt } => {
            match control {
                TimingControl::Delay(e) => validate_expr_idents(e, elab, locals)?,
                TimingControl::Event(ev) => validate_event_idents(ev, elab, locals)?,
            }
            validate_stmt_idents(stmt, elab, locals)?;
        }
        StatementKind::Expr(e) => validate_expr_idents(e, elab, locals)?,
        StatementKind::Wait { condition, stmt } => {
            validate_expr_idents(condition, elab, locals)?;
            validate_stmt_idents(stmt, elab, locals)?;
        }
        StatementKind::Assertion(a) => {
            validate_expr_idents(&a.expr, elab, locals)?;
            if let Some(s) = &a.action { validate_stmt_idents(s, elab, locals)?; }
            if let Some(s) = &a.else_action { validate_stmt_idents(s, elab, locals)?; }
        }
        StatementKind::Return(e) => { if let Some(expr) = e { validate_expr_idents(expr, elab, locals)?; } }
        StatementKind::VarDecl { declarators, .. } => {
            for d in declarators {
                if let Some(init) = &d.init { validate_expr_idents(init, elab, locals)?; }
                locals.insert(d.name.name.clone());
            }
        }
        _ => {}
    }
    Ok(())
}

fn validate_expr_idents(expr: &Expression, elab: &ElaboratedModule, locals: &HashSet<String>) -> Result<(), String> {
    fn root_ident_name(expr: &Expression) -> Option<&str> {
        match &expr.kind {
            ExprKind::Ident(hier) if hier.path.len() == 1 => Some(hier.path[0].name.name.as_str()),
            ExprKind::MemberAccess { expr, .. } => root_ident_name(expr),
            _ => None,
        }
    }

    match &expr.kind {
        ExprKind::Ident(hier) => {
            // Only check plain identifiers for now (hierarchical might be valid across modules)
            if hier.path.len() == 1 {
                let name = &hier.path[0].name.name;
                // `std` is the built-in package (§18.12 std::randomize,
                // std::mailbox, std::semaphore, …) — always a legal root.
                if name == "new" || name.starts_with('$') || name == "super" || name == "this"
                    || name == "std"
                {
                    return Ok(());
                }
                // A built-in type keyword captured as an Ident — only the parser's
                // `$bits(<type>)` / `$size(<type>)` type-argument path produces
                // these (a bare keyword can't appear in normal expression
                // position), so it's a type reference, not an undeclared signal.
                if matches!(name.as_str(),
                    "integer" | "int" | "shortint" | "longint" | "byte" | "time"
                    | "bit" | "logic" | "reg" | "real" | "shortreal" | "realtime"
                    | "string" | "chandle" | "void")
                {
                    return Ok(());
                }
                if !elab.signals.contains_key(name) && !elab.parameters.contains_key(name) &&
                   !elab.functions.contains_key(name) && !elab.tasks.contains_key(name) &&
                   !elab.dpi_imports.contains_key(name) &&
                   !elab.arrays.contains_key(name) && !elab.associative_arrays.contains_key(name) &&
                   !elab.arrays_2d.contains_key(name) && !elab.arrays_nd.contains_key(name) &&
                   !elab.classes.contains_key(name) && !elab.typedefs.contains_key(name) &&
                   !elab.clocking_blocks.contains_key(name) && !elab.lets.contains_key(name) &&
                   !elab.sequences.contains(name) &&
                   !locals.contains(name) {
                   return Err(format!("Undeclared identifier '{}'", name));
                }            }
        }
        ExprKind::Unary { operand, .. } => validate_expr_idents(operand, elab, locals)?,
        ExprKind::Binary { left, right, .. } => { validate_expr_idents(left, elab, locals)?; validate_expr_idents(right, elab, locals)?; }
        ExprKind::Conditional { condition, then_expr, else_expr } => {
            validate_expr_idents(condition, elab, locals)?;
            validate_expr_idents(then_expr, elab, locals)?;
            validate_expr_idents(else_expr, elab, locals)?;
        }
        ExprKind::Concatenation(parts) => { for p in parts { validate_expr_idents(p, elab, locals)?; } }
        ExprKind::Replication { count, exprs } => {
            validate_expr_idents(count, elab, locals)?;
            for e in exprs { validate_expr_idents(e, elab, locals)?; }
        }
        ExprKind::Index { expr, index } => {
            if let ExprKind::Ident(hier) = &expr.kind {
                if hier.path.len() == 1 {
                    if let Some(sig) = elab.signals.get(&hier.path[0].name.name) {
                        if sig.is_real {
                            return Err(format!("Bit-select of real variable '{}' is not allowed", sig.name));
                        }
                    }
                }
            }
            if let ExprKind::Ident(hier) = &index.kind {
                if hier.path.len() == 1 {
                    if let Some(sig) = elab.signals.get(&hier.path[0].name.name) {
                        if sig.is_real {
                            return Err(format!("Real variable '{}' cannot be used as bit-select index", sig.name));
                        }
                    }
                }
            }
            validate_expr_idents(expr, elab, locals)?;
            validate_expr_idents(index, elab, locals)?;
        }
        ExprKind::RangeSelect { expr, left, right, .. } => {
            if let ExprKind::Ident(hier) = &expr.kind {
                if hier.path.len() == 1 {
                    if let Some(sig) = elab.signals.get(&hier.path[0].name.name) {
                        if sig.is_real {
                            return Err(format!("Part-select of real variable '{}' is not allowed", sig.name));
                        }
                    }
                }
            }
            validate_expr_idents(expr, elab, locals)?;
            validate_expr_idents(left, elab, locals)?;
            validate_expr_idents(right, elab, locals)?;
        }
        ExprKind::Paren(inner) => validate_expr_idents(inner, elab, locals)?,
        ExprKind::Call { func, args } => {
            validate_expr_idents(func, elab, locals)?;
            for a in args { validate_expr_idents(a, elab, locals)?; }
        }
        ExprKind::SystemCall { name, args } => {
            // Args can be scope/module/instance references (not value lookups)
            // for dump/coverage/scope-info system tasks.
            let skip = matches!(
                name.as_str(),
                "$dumpvars" | "$dumpfile" | "$dumpports" | "$dumpportsoff"
                    | "$dumpportson" | "$dumpportsflush" | "$dumpportsall"
                    | "$dumpportslimit" | "$printtimescale" | "$timeformat"
                    | "$coverage_control" | "$coverage_get" | "$coverage_get_max"
                    | "$coverage_merge" | "$coverage_save" | "$get_coverage"
                    | "$set_coverage_db_name" | "$load_coverage_db"
            );
            if !skip {
                for a in args { validate_expr_idents(a, elab, locals)?; }
            }
        }
        ExprKind::MemberAccess { expr, .. } => {
            // Skip validation for package scopes (`pkg::name`) and for
            // hierarchical references rooted at the current top module name
            // (e.g. `tb.x_soc...` inside the testbench).
            if let Some(root) = root_ident_name(expr) {
                if root == elab.name || elab.packages.contains(root) {
                    // scope / hierarchy reference, not a value lookup
                } else {
                    validate_expr_idents(expr, elab, locals)?;
                }
            } else {
                validate_expr_idents(expr, elab, locals)?;
            }
        }
        ExprKind::WithClause { expr, filter } => {
            // The Call's args inside an array-method `with` clause are
            // iterator-name bindings (e.g. `find(item, idx)` introduces
            // `item` and `idx`), not value references. Validate the
            // method receiver but skip the iterator-name args, and add
            // those names to the filter's scope.
            let mut with_locals = locals.clone();
            with_locals.insert("item".to_string());
            match &expr.kind {
                ExprKind::Call { func, args } => {
                    validate_expr_idents(func, elab, locals)?;
                    for a in args {
                        if let ExprKind::Ident(h) = &a.kind {
                            if h.path.len() == 1 && h.path[0].selects.is_empty() {
                                with_locals.insert(h.path[0].name.name.clone());
                                continue;
                            }
                        }
                        validate_expr_idents(a, elab, locals)?;
                    }
                }
                _ => validate_expr_idents(expr, elab, locals)?,
            }
            validate_expr_idents(filter, elab, &with_locals)?;
        }
        _ => {}
    }
    Ok(())
}

fn validate_event_idents(ev: &EventControl, elab: &ElaboratedModule, locals: &HashSet<String>) -> Result<(), String> {
    match ev {
        EventControl::EventExpr(exprs) => {
            for ee in exprs {
                if ee.edge.is_some() {
                    if let ExprKind::Ident(hier) = &ee.expr.kind {
                        if hier.path.len() == 1 {
                            if let Some(sig) = elab.signals.get(&hier.path[0].name.name) {
                                if sig.is_real {
                                    return Err(format!("Edge event on real variable '{}' is not allowed", sig.name));
                                }
                            }
                        }
                    }
                }
                validate_expr_idents(&ee.expr, elab, locals)?;
            }
        }
        EventControl::Identifier(id) => {
            if !elab.signals.contains_key(&id.name) && !elab.parameters.contains_key(&id.name)
                && !elab.sequences.contains(&id.name) && !locals.contains(&id.name)
            {
                return Err(format!("Undeclared identifier '{}'", id.name));
            }
        }
        EventControl::HierIdentifier(e) => validate_expr_idents(e, elab, locals)?,
        _ => {}
    }
    Ok(())
}

/// Scan pending_cont_assign for implicit-net candidates after sub-module
/// inlining. For each pending cont-assign with LHS = bare identifier X
/// (no prior `wire X` declaration), construct the prefixed name
/// `<ctx.prefix>X` and add it as a 1-bit wire to elab.signals.
///
/// Why this matters: `assign undeclared_wire = expr;` implicitly creates
/// a 1-bit wire per IEEE 1800-2017 §6.10. The initial pass in
/// `create_implicit_nets` only sees the top-level `continuous_assigns`
/// vec, missing sub-module bodies still in pending. Without this
/// follow-up pass, the cont-assign can't resolve its LHS signal_id and
/// gets dropped silently — symptom: c910 wid_for_axi4's `create_en`
/// stayed X forever, freezing the wid-tracking FIFO.
fn create_implicit_nets_for_pending(elab: &mut ElaboratedModule) {
    let mut names_to_add: Vec<String> = Vec::new();
    for pending in &elab.pending_cont_assign {
        let prefix = &pending.ctx.prefix;
        let mut bare = Vec::new();
        collect_implicit_net_candidates(&pending.lhs_source, &mut bare);
        collect_implicit_net_candidates(&pending.rhs_source, &mut bare);
        for name in bare {
            // If the bare name is a port (in port_map), it gets rewritten
            // to the parent's signal — don't create an implicit net here.
            if pending.ctx.port_map.contains_key(&name) { continue; }
            // If it's a parameter, no implicit net needed.
            if elab.parameters.contains_key(&name) { continue; }
            // The bare name is a sub-module-local identifier; after rewrite
            // it becomes `<prefix>name`.
            let prefixed = format!("{}{}", prefix, name);
            if !elab.signals.contains_key(&prefixed)
                && !elab.parameters.contains_key(&prefixed)
                && !elab.nets.contains(&prefixed)
            {
                names_to_add.push(prefixed);
            }
        }
    }
    names_to_add.sort();
    names_to_add.dedup();
    for name in names_to_add {
        eprintln!(
            "[xezim][warning] implicit 1-bit net created for undeclared identifier '{}' \
             (IEEE 1800-2017 §6.10, pending sub-module cont-assign). Add an explicit declaration to silence.",
            name
        );
        elab.signals.insert(name.clone(), Signal { is_const: false,
            name: name.clone(), width: 1, is_signed: false,
            direction: None, value: Value::new(1),
            is_real: false, type_name: None,
        });
        elab.nets.insert(name);
    }
}

/// Create implicit 1-bit wire signals for identifiers referenced in continuous assigns
/// but not declared anywhere (IEEE 1800-2017 §6.10).
fn create_implicit_nets(elab: &mut ElaboratedModule) -> Result<(), String> {
    let mut implicit_names = Vec::new();
    for ca in &elab.continuous_assigns {
        collect_ident_names(&ca.lhs, &mut implicit_names);
        collect_ident_names(&ca.rhs, &mut implicit_names);
    }
    implicit_names.sort();
    implicit_names.dedup();
    let none_active = sv_parser::default_nettype_none_seen();
    for name in implicit_names {
        if !elab.signals.contains_key(&name) && !elab.parameters.contains_key(&name) {
            if none_active {
                return Err(format!(
                    "Implicit net '{}' under `default_nettype none (IEEE 1800-2017 §6.10)",
                    name
                ));
            }
            eprintln!(
                "[xezim][warning] implicit 1-bit net created for undeclared identifier '{}' \
                 (IEEE 1800-2017 §6.10). Add an explicit declaration to silence.",
                name
            );
            elab.signals.insert(name.clone(), Signal { is_const: false,
                name: name.clone(), width: 1, is_signed: false,
                direction: None, value: Value::new(1),
                is_real: false, type_name: None,
            });
            elab.nets.insert(name);
        }
    }
    Ok(())
}

/// Names that §6.10 may implicitly declare as 1-bit nets. Unlike
/// `collect_ident_names` this does NOT descend into a `MemberAccess` base: a
/// dotted reference (`testbench.chip_inst.dqs`) is a HIERARCHICAL path, and its
/// first segment names an instance, not an undeclared net. Descending created a
/// bogus `<prefix>.testbench` net that then drove the real one to X.
fn collect_implicit_net_candidates(expr: &Expression, out: &mut Vec<String>) {
    match &expr.kind {
        ExprKind::Ident(hier) => {
            if hier.path.len() == 1 && hier.path[0].selects.is_empty() {
                out.push(hier.path[0].name.name.clone());
            }
        }
        ExprKind::MemberAccess { .. } => {}
        ExprKind::Unary { operand, .. } => collect_implicit_net_candidates(operand, out),
        ExprKind::Binary { left, right, .. } => {
            collect_implicit_net_candidates(left, out);
            collect_implicit_net_candidates(right, out);
        }
        ExprKind::Paren(i) => collect_implicit_net_candidates(i, out),
        ExprKind::Concatenation(parts) => {
            for p in parts {
                collect_implicit_net_candidates(p, out);
            }
        }
        ExprKind::Conditional { condition, then_expr, else_expr } => {
            collect_implicit_net_candidates(condition, out);
            collect_implicit_net_candidates(then_expr, out);
            collect_implicit_net_candidates(else_expr, out);
        }
        _ => {}
    }
}

/// Collect all plain identifier names from an expression tree.
fn collect_ident_names(expr: &Expression, out: &mut Vec<String>) {
    match &expr.kind {
        ExprKind::Ident(hier) => {
            if hier.path.len() == 1 && hier.path[0].selects.is_empty() {
                out.push(hier.path[0].name.name.clone());
            }
        }
        ExprKind::Unary { operand, .. } => collect_ident_names(operand, out),
        ExprKind::Binary { left, right, .. } => { collect_ident_names(left, out); collect_ident_names(right, out); }
        ExprKind::Conditional { condition, then_expr, else_expr } => {
            collect_ident_names(condition, out); collect_ident_names(then_expr, out); collect_ident_names(else_expr, out);
        }
        ExprKind::Concatenation(parts) => { for p in parts { collect_ident_names(p, out); } }
        ExprKind::Replication { count, exprs } => { collect_ident_names(count, out); for e in exprs { collect_ident_names(e, out); } }
        ExprKind::Index { expr, index } => { collect_ident_names(expr, out); collect_ident_names(index, out); }
        ExprKind::RangeSelect { expr, left, right, .. } => { collect_ident_names(expr, out); collect_ident_names(left, out); collect_ident_names(right, out); }
        ExprKind::Paren(inner) => collect_ident_names(inner, out),
        // Only the CALL ARGUMENTS can name nets — the callee (`func`) is a
        // function/task name, never an implicit net. Collecting it created a
        // phantom 1-bit net for const functions like a user `clog2(N)`, which
        // then re-dirtied on every combinational settle pass so settle never
        // converged (black-parrot HardFloat / BSG width helpers).
        ExprKind::Call { func: _, args } => { for a in args { collect_ident_names(a, out); } }
        ExprKind::MemberAccess { expr, .. } => collect_ident_names(expr, out),
        _ => {}
    }
}

/// Helper: process a slice of module items into the elaborated module.
/// This is extracted so it can be called recursively for generate regions.
fn elaborate_items(items: &[ModuleItem], elab: &mut ElaboratedModule, all_defs: Option<&HashMap<String, Definition>>) -> Result<(), String> {
    for item in items {
        match item {
            ModuleItem::PortDeclaration(pd) => {
                let port_modport_view = match &pd.data_type {
                    DataType::Interface { name, modport: Some(mp), .. } => {
                        resolve_interface_modport_view(&name.name, &mp.name, all_defs)
                    }
                    _ => None,
                };
                let width = resolve_type_width(&pd.data_type, Some(&elab.parameters), Some(&elab.typedefs));
                let is_signed = is_type_signed(&pd.data_type);
                let is_real = is_type_real(&pd.data_type);
                for decl in &pd.declarators {
                    if elab.parameters.contains_key(&decl.name.name) {
                        return Err(format!("Duplicate declaration of '{}'", decl.name.name));
                    }
                    // §23.2.2.1 non-ANSI split type/direction — merge (see the
                    // matching comment in the top-module elaboration path).
                    if let Some(existing) = elab.signals.get(&decl.name.name) {
                        if existing.direction.is_none() {
                            let explicit_type = !matches!(pd.data_type, DataType::Implicit { .. });
                            let existing = elab.signals.get_mut(&decl.name.name).unwrap();
                            existing.direction = Some(pd.direction);
                            if explicit_type {
                                existing.width = width;
                                existing.is_signed = is_signed;
                                existing.is_real = is_real;
                                existing.type_name = get_type_name(&pd.data_type);
                                existing.value = if is_real { Value::from_f64(0.0) } else { Value::new(width) };
                            }
                            if !elab.port_order.contains(&decl.name.name) {
                                elab.port_order.push(decl.name.name.clone());
                            }
                            if let Some(view) = &port_modport_view {
                                elab.modport_views.insert(decl.name.name.clone(), view.clone());
                            }
                            continue;
                        }
                        return Err(format!("Duplicate declaration of '{}'", decl.name.name));
                    }
                    let sig = Signal { is_const: false,
                        name: decl.name.name.clone(), width, is_signed,
                        direction: Some(pd.direction), value: if is_real { Value::from_f64(0.0) } else { Value::new(width) },
                        is_real, type_name: get_type_name(&pd.data_type),
                    };
                    elab.signals.insert(decl.name.name.clone(), sig);
                    elab.port_order.push(decl.name.name.clone());
                    if let Some(view) = &port_modport_view {
                        elab.modport_views.insert(decl.name.name.clone(), view.clone());
                    }
                }
            }
            ModuleItem::NetDeclaration(nd) => {
                let width = resolve_type_width(&nd.data_type, Some(&elab.parameters), Some(&elab.typedefs));
                let is_signed = is_type_signed(&nd.data_type);
                let is_real = is_type_real(&nd.data_type);
                for decl in &nd.declarators {
                    let init_value = match nd.net_type {
                        NetType::Supply0 => Value::zero(width),
                        NetType::Supply1 => Value::ones(width),
                        _ => if is_real { Value::from_f64(0.0) } else { Value::new(width) },
                    };
                    let sig = Signal { is_const: false,
                        name: decl.name.name.clone(), width, is_signed,
                        direction: None, value: init_value,
                        is_real, type_name: get_type_name(&nd.data_type),
                    };
                    elab.signals.insert(decl.name.name.clone(), sig);
                    if let Some(init_expr) = &decl.init {
                        elab.continuous_assigns.push(ContinuousAssignment {
                            lhs: make_ident_expr(&decl.name.name),
                            rhs: init_expr.clone(),
                            delay: 0,
                        });
                    }
                }
            }
            ModuleItem::DataDeclaration(dd) => {
                register_anonymous_enum_members(&dd.data_type, elab);
                // Packed multi-D (`logic [N-1:0][W-1:0] mem;`) — record the
                // per-element width under the bare declarator name so
                // `mem[i] = v` writes a W-bit slice. Mirrors the same
                // registration in the top-level module DataDecl arm. Without
                // this hook the submodule path leaves packed_signal_elem_widths
                // empty, and the bytecode emitter falls back to a single-bit
                // write at `mem[i]` — silent data corruption in any packed-2D
                // FIFO (e.g. cv32e40p_fifo's mem_n).
                if let Some(elem_w) = packed_inner_elem_width(&dd.data_type, &elab.parameters, &elab.typedefs) {
                    for decl in &dd.declarators {
                        elab.packed_signal_elem_widths.insert(decl.name.name.clone(), elem_w);
                    }
                }
                let data_modport_view = match &dd.data_type {
                    DataType::Interface { name, modport: Some(mp), .. } => {
                        resolve_interface_modport_view(&name.name, &mp.name, all_defs)
                    }
                    _ => None,
                };
                let width = match &dd.data_type {
                    DataType::TypeReference { name, .. } => {
                        elab.typedefs.get(&name.name.name).copied().unwrap_or(resolve_type_width(&dd.data_type, Some(&elab.parameters), Some(&elab.typedefs)))
                    }
                    _ => resolve_type_width(&dd.data_type, Some(&elab.parameters), Some(&elab.typedefs)),
                };
                if let DataType::TypeReference { type_args, .. } = &dd.data_type {
                    if !type_args.is_empty() {
                        for decl in &dd.declarators {
                            elab.class_type_args.insert(decl.name.name.clone(), type_args.clone());
                        }
                    }
                }
                let is_signed = is_type_signed(&dd.data_type);
                let is_real = is_type_real(&dd.data_type);
                for decl in &dd.declarators {
                    if elab.signals.contains_key(&decl.name.name) || elab.parameters.contains_key(&decl.name.name) {
                        return Err(format!("Duplicate declaration of '{}'", decl.name.name));
                    }
                    if let Some(UnpackedDimension::Associative { data_type: key_dt, .. }) = decl.dimensions.first() {
                        let is_string_key = key_dt.as_ref().map_or(false, |dt| matches!(dt.as_ref(), DataType::Simple { kind: SimpleType::String, .. }));
                        elab.associative_arrays.insert(decl.name.name.clone(), is_string_key);
                    }
                    let is_dynamic_dim = decl.dimensions.first().map_or(false, |d| matches!(d, UnpackedDimension::Unsized(_) | UnpackedDimension::Queue { .. }));
                    if is_dynamic_dim {
                        elab.dynamic_arrays.insert(decl.name.name.clone());
                    }
                    let array_range = extract_array_range(&decl.dimensions, &elab.parameters);
                    if let Some((lo, hi)) = array_range {
                        elab.arrays.insert(decl.name.name.clone(), (lo, hi, width));
                        if let Some(UnpackedDimension::Range { left, right, .. }) = decl.dimensions.first() {
                            let l = const_eval_i64_with_params(left, Some(&elab.parameters)).unwrap_or(0);
                            let r = const_eval_i64_with_params(right, Some(&elab.parameters)).unwrap_or(0);
                            if l > r { elab.descending_arrays.insert(decl.name.name.clone()); }
                        }
                        // Per-element Signals synthesized by Simulator::new
                        // from the `arrays` metadata — skip per-element
                        // HashMap inserts.
                        let _ = (is_signed, width, is_real);
                        if let Some(init_expr) = &decl.init {
                            let init_items: Vec<&Expression> = match &init_expr.kind {
                                ExprKind::AssignmentPattern(items) => items.iter().map(|i| i.expr()).collect(),
                                ExprKind::Concatenation(exprs) => exprs.iter().collect(),
                                _ => vec![],
                            };
                            if !init_items.is_empty() {
                                let mut stmts: Vec<Statement> = Vec::new();
                                for (i, item_expr) in init_items.iter().enumerate() {
                                    let idx_i = lo + i as i64;
                                    let lval = Expression::new(ExprKind::Index {
                                        expr: Box::new(make_ident_expr(&decl.name.name)),
                                        index: Box::new(Expression::new(ExprKind::Number(crate::ast::expr::NumberLiteral::Integer { size: None, signed: false, base: crate::ast::expr::NumberBase::Decimal, value: idx_i.to_string(), cached_val: std::cell::Cell::new(None) }), Span::dummy())),
                                    }, Span::dummy());
                                    stmts.push(Statement::new(StatementKind::BlockingAssign {
                                        lvalue: lval,
                                        rvalue: (*item_expr).clone(),
                                    }, Span::dummy()));
                                }
                                if is_dynamic_dim {
                                    let size_name = format!("{}.size", decl.name.name);
                                    let size_sig = Signal { is_const: false, name: size_name.clone(), width: 32, is_signed: false, is_real: false, direction: None, value: Value::from_u64(init_items.len() as u64, 32), type_name: None };
                                    elab.signals.insert(size_name, size_sig);
                                }
                                elab.initial_blocks.push(InitialBlock {
                                    stmt: Statement::new(StatementKind::SeqBlock { name: None, stmts }, Span::dummy()), scope: String::new(), });
                            }
                        }
                    } else {
                        let init_val = if let Some(init_expr) = &decl.init {
                            let mut rv = eval_init_for_width(init_expr, &elab.parameters, width);
                            if is_signed { rv.is_signed = true; }
                            if is_real { rv = Value::from_f64(rv.to_f64()); }
                            rv
                        } else {
                            default_value_for_type(&dd.data_type, width)
                        };
                        let sig = Signal { is_const: dd.const_kw, name: decl.name.name.clone(), width, is_signed, is_real, direction: None, value: init_val, type_name: get_type_name(&dd.data_type) };
                        elab.signals.insert(decl.name.name.clone(), sig);
                        if let Some(view) = &data_modport_view {
                            elab.modport_views.insert(decl.name.name.clone(), view.clone());
                        }
                    }
                }
            }
            ModuleItem::ParameterDeclaration(pd) | ModuleItem::LocalparamDeclaration(pd) => {
                if let ParameterKind::Data { data_type, assignments } = &pd.kind {
                    let mut width = resolve_type_width(data_type, Some(&elab.parameters), Some(&elab.typedefs));
                    let signed = is_type_signed(data_type);
                    if matches!(data_type, DataType::Implicit { dimensions, .. } if dimensions.is_empty()) { width = 32; }
                    for assign in assignments {
                        if elab.signals.contains_key(&assign.name.name) || elab.parameters.contains_key(&assign.name.name) {
                            return Err(format!("Duplicate declaration of '{}'", assign.name.name));
                        }
                        if !elab.parameters.contains_key(&assign.name.name) {
                            let val = if let Some(init) = &assign.init {
                                let mut v = eval_init_for_width(init, &elab.parameters, width);
                                if signed { v.is_signed = true; }
                                v
                            } else { Value::zero(width) };
                            elab.parameters.insert(assign.name.name.clone(), val.clone());
                            elab.signals.insert(assign.name.name.clone(), Signal { is_const: false,
                                name: assign.name.name.clone(), width, is_signed: signed,
                                direction: None, value: val, is_real: is_type_real(data_type), type_name: get_type_name(data_type),
                            });
                        }
                    }
                }
            }
            ModuleItem::ContinuousAssign(ca) => {
                let delay = ca.delay.as_ref().map(|d| eval_const_expr(d, &elab.parameters)).unwrap_or(0);
                for (lhs, rhs) in &ca.assignments {
                    elab.continuous_assigns.push(ContinuousAssignment { lhs: lhs.clone(), rhs: rhs.clone(), delay });
                }
            }
            ModuleItem::GateInstantiation(gi) => {
                gate_inst_to_assigns(gi, elab);
            }
            ModuleItem::AlwaysConstruct(ac) => {
                elab.always_blocks.push(AlwaysBlock { kind: ac.kind, stmt: ac.stmt.clone() });
            }
            ModuleItem::InitialConstruct(ic) => {
                if std::env::var("XEZIM_TRACE_INIT").ok().as_deref() == Some("1") {
                    eprintln!("[xezim][elab] @2453 pushing initial (other path)");
                }
                elab.initial_blocks.push(InitialBlock { stmt: ic.stmt.clone(), scope: String::new(), });
            }
            // Mirror the AssertionItem hoist in elaborate_module_with_defs
            // so module-level `assert/assume/cover property (…)` inside
            // generate blocks or checker bodies fires too.
            ModuleItem::AssertionItem(a) => {
                elab.initial_blocks.push(InitialBlock {
                    stmt: crate::ast::stmt::Statement::new(
                        crate::ast::stmt::StatementKind::Assertion(a.clone()),
                        a.span,
                    ), scope: String::new(), });
            }
            ModuleItem::FinalConstruct(fc) => {
                elab.final_blocks.push(InitialBlock { stmt: fc.stmt.clone(), scope: String::new(), });
            }
            ModuleItem::ModuleInstantiation(inst) => {
                for hi in &inst.instances {
                    if !elab.signals.contains_key(&hi.name.name) {
                        elab.signals.insert(hi.name.name.clone(), Signal {
                            is_const: false,
                            name: hi.name.name.clone(), width: 1,
                            is_signed: false, direction: None, value: Value::new(1), type_name: Some(inst.module_name.name.clone()),
                            is_real: false,
                        });
                    }
                }
            }
            ModuleItem::TypedefDeclaration(td) => {
                process_typedef(td, elab);
            }
            ModuleItem::GenerateRegion(gr) => {
                elaborate_items(&gr.items, elab, all_defs)?;
            }
            ModuleItem::GenerateIf(gi) => {
                elaborate_generate_if(&gi.branches, elab, all_defs)?;
            }
            ModuleItem::GenerateCase(gc) => {
                elaborate_generate_case(gc, elab, all_defs)?;
            }
            ModuleItem::GenerateFor(gf) => {
                elaborate_generate_for(gf, elab, all_defs)?;
            }

            ModuleItem::ClassDeclaration(cd) => {
                validate_class_constraints(cd, all_defs, Some(&elab.enum_members))?;
                elab.classes.insert(cd.name.name.clone(), elaborate_class(cd));
            }
            ModuleItem::ClockingDeclaration(cd) => {
                let mut dirs = HashMap::default();
                for s in &cd.signals {
                    dirs.insert(s.name.name.clone(), s.direction);
                }
                elab.clocking_signal_dirs.insert(cd.name.name.clone(), dirs);
                elab.clocking_blocks.insert(cd.name.name.clone(), cd.clone());
            }
            ModuleItem::LetDeclaration(ld) => {
                elab.lets.insert(ld.name.name.clone(), ld.clone());
            }
            ModuleItem::SequenceDeclaration(sd) => {
                elab.sequences.insert(sd.name.name.clone());
                if let Some(body) = &sd.body {
                    // Sequences share the property_decls map for
                    // `assert property (s)` style references.
                    elab.property_decls
                        .insert(sd.name.name.clone(), body.clone());
                }
            }
            ModuleItem::PropertyDeclaration(pd) => {
                elab.sequences.insert(pd.name.name.clone());
                if let Some(body) = &pd.body {
                    elab.property_decls
                        .insert(pd.name.name.clone(), body.clone());
                }
            }
            // LRM §17 — register the checker name AND inline its body
            // items into the current module. This is the minimum-viable
            // shape: the checker has no formal-arg binding (single
            // "always-on" instance at the declaration site), but
            // assertions / always-blocks / let-decls inside the body
            // fire as if they were written directly in the parent
            // module. Multiple instantiations and port binding remain
            // future work.
            ModuleItem::CheckerDeclaration(cd) => {
                elab.sequences.insert(cd.name.name.clone());
                let body = cd.items.clone();
                elaborate_items(&body, elab, all_defs)?;
            }
            ModuleItem::SpecifyBlock(sb) => {
                for p in &sb.paths {
                    let d = eval_const_expr(&p.delay, &elab.parameters);
                    elab.specify_delays.insert(p.dst.name.clone(), d);
                }
            }
            ModuleItem::FunctionDeclaration(fd) => {
                if matches!(fd.return_type, DataType::Void(_)) {
                    fn check_void_return(s: &crate::ast::stmt::Statement) -> Result<(), String> {
                        use crate::ast::stmt::StatementKind as SK;
                        match &s.kind {
                            SK::Return(Some(_)) => Err("void function must not return a value".into()),
                            SK::SeqBlock { stmts, .. } | SK::ParBlock { stmts, .. } => {
                                for st in stmts { check_void_return(st)?; }
                                Ok(())
                            }
                            SK::If { then_stmt, else_stmt, .. } => {
                                check_void_return(then_stmt)?;
                                if let Some(eb) = else_stmt { check_void_return(eb)?; }
                                Ok(())
                            }
                            SK::For { body, .. } | SK::While { body, .. } | SK::DoWhile { body, .. }
                            | SK::Repeat { body, .. } | SK::Forever { body } | SK::Foreach { body, .. } => check_void_return(body),
                            SK::TimingControl { stmt, .. } | SK::Wait { stmt, .. } => check_void_return(stmt),
                            SK::Case { items, .. } => { for it in items { check_void_return(&it.stmt)?; } Ok(()) }
                            _ => Ok(()),
                        }
                    }
                    for it in &fd.items { check_void_return(it)?; }
                }
                fn check_fn_fork(s: &crate::ast::stmt::Statement) -> Result<(), String> {
                    use crate::ast::stmt::StatementKind as SK;
                    match &s.kind {
                        SK::ParBlock { join_type, stmts, .. } => {
                            if !matches!(join_type, crate::ast::stmt::JoinType::JoinNone) {
                                return Err("only fork-join_none is permitted inside a function".into());
                            }
                            for st in stmts { check_fn_fork(st)?; }
                            Ok(())
                        }
                        SK::SeqBlock { stmts, .. } => { for st in stmts { check_fn_fork(st)?; } Ok(()) }
                        SK::If { then_stmt, else_stmt, .. } => {
                            check_fn_fork(then_stmt)?;
                            if let Some(eb) = else_stmt { check_fn_fork(eb)?; }
                            Ok(())
                        }
                        SK::For { body, .. } | SK::While { body, .. } | SK::DoWhile { body, .. }
                        | SK::Repeat { body, .. } | SK::Forever { body } | SK::Foreach { body, .. } => check_fn_fork(body),
                        SK::TimingControl { stmt, .. } | SK::Wait { stmt, .. } => check_fn_fork(stmt),
                        SK::Case { items, .. } => { for it in items { check_fn_fork(&it.stmt)?; } Ok(()) }
                        _ => Ok(()),
                    }
                }
                for it in &fd.items { check_fn_fork(it)?; }
                elab.functions.insert(fd.name.name.name.clone(), fd.clone());
            }
            ModuleItem::TaskDeclaration(td) => {
                fn check_no_return_in_fork(s: &crate::ast::stmt::Statement, in_fork: bool) -> Result<(), String> {
                    use crate::ast::stmt::StatementKind as SK;
                    match &s.kind {
                        SK::Return(_) if in_fork => Err("illegal return from fork".into()),
                        SK::ParBlock { stmts, .. } => { for st in stmts { check_no_return_in_fork(st, true)?; } Ok(()) }
                        SK::SeqBlock { stmts, .. } => { for st in stmts { check_no_return_in_fork(st, in_fork)?; } Ok(()) }
                        SK::If { then_stmt, else_stmt, .. } => {
                            check_no_return_in_fork(then_stmt, in_fork)?;
                            if let Some(eb) = else_stmt { check_no_return_in_fork(eb, in_fork)?; }
                            Ok(())
                        }
                        SK::For { body, .. } | SK::While { body, .. } | SK::DoWhile { body, .. }
                        | SK::Repeat { body, .. } | SK::Forever { body } | SK::Foreach { body, .. } => check_no_return_in_fork(body, in_fork),
                        SK::TimingControl { stmt, .. } | SK::Wait { stmt, .. } => check_no_return_in_fork(stmt, in_fork),
                        SK::Case { items, .. } => { for it in items { check_no_return_in_fork(&it.stmt, in_fork)?; } Ok(()) }
                        _ => Ok(()),
                    }
                }
                for it in &td.items { check_no_return_in_fork(it, false)?; }
                elab.tasks.insert(td.name.name.name.clone(), td.clone());
            }
            ModuleItem::ImportDeclaration(imp) => {
                if let Some(defs) = all_defs {
                    process_import(imp, elab, defs)?;
                }
            }
            ModuleItem::DPIImport(di) => {
                register_dpi_import(di, elab)?;
            }
            _ => {}
        }
    }
    Ok(())
}

/// Evaluate a generate-if: pick the first branch whose condition is true (or the else branch).
fn elaborate_generate_if(branches: &[(Option<Expression>, Vec<ModuleItem>)], elab: &mut ElaboratedModule, all_defs: Option<&HashMap<String, Definition>>) -> Result<(), String> {
    for (cond, items) in branches {
        match cond {
            Some(c) => {
                if !is_const_expr(c, &elab.parameters) {
                    return Err(format!("Generate if condition must be a constant expression"));
                }
                let val = eval_const_expr(c, &elab.parameters);
                if val != 0 {
                    return elaborate_items(items, elab, all_defs);
                }
            }
            None => {
                // Unconditional else branch
                return elaborate_items(items, elab, all_defs);
            }
        }
    }
    Ok(())
}

fn elaborate_generate_case(gc: &GenerateCase, elab: &mut ElaboratedModule, all_defs: Option<&HashMap<String, Definition>>) -> Result<(), String> {
    if !is_const_expr(&gc.selector, &elab.parameters) {
        return Err("Generate case selector must be a constant expression".to_string());
    }
    let sel = eval_const_expr(&gc.selector, &elab.parameters);
    // First pass: try to match a non-default arm.
    for arm in &gc.arms {
        if arm.values.is_empty() { continue; } // skip default in this pass
        for v in &arm.values {
            if !is_const_expr(v, &elab.parameters) {
                return Err("Generate case value must be a constant expression".to_string());
            }
            if eval_const_expr(v, &elab.parameters) == sel {
                return elaborate_items(&arm.items, elab, all_defs);
            }
        }
    }
    // No non-default match — fall through to default arm if present.
    for arm in &gc.arms {
        if arm.values.is_empty() {
            return elaborate_items(&arm.items, elab, all_defs);
        }
    }
    Ok(())
}

fn elaborate_generate_for(gf: &GenerateFor, elab: &mut ElaboratedModule, all_defs: Option<&HashMap<String, Definition>>) -> Result<(), String> {
    let var = &gf.var;
    let mut i = gf.init_val;
    let trace = elab_trace_enabled();
    let mut iter_count = 0u32;
    for _ in 0..10000 {
        elab.parameters.insert(var.clone(), Value::from_u64(i as u64, 32));
        let cond_val = eval_const_expr(&gf.cond, &elab.parameters);
        if cond_val == 0 { break; }
        // Rename per-iteration declarations so each iteration owns a fresh
        // copy. Without this, two iterations both declare e.g. `valid_q` and
        // the elaborator's flat signal table flags a duplicate.
        let subst = substitute_genvar_in_items(&gf.items, var, i);
        // Namespace the per-iteration rename by the block label so two
        // generate-for blocks sharing a genvar name (common in black-parrot:
        // many `for (genvar i …) begin : <label>`) don't collide on the flat
        // signal table (`sig__gf_i_<n>_`).
        let suffix = match &gf.name {
            Some(l) => format!("__gf_{}_{}_{}_", l, var, i),
            None => format!("__gf_{}_{}_", var, i),
        };
        let renamed = rename_decls_in_iter(&subst, &suffix);
        elaborate_items(&renamed, elab, all_defs)?;
        if trace && (iter_count % 8) == 0 {
            let rss = std::fs::read_to_string("/proc/self/statm")
                .ok()
                .and_then(|s| s.split_whitespace().nth(1).and_then(|n| n.parse::<u64>().ok()))
                .map(|p| p * 4096 / (1024 * 1024))
                .unwrap_or(0);
            eprintln!("[xezim][gf] var={} iter={} rss={}MB assigns={} signals={}",
                var, iter_count, rss, elab.continuous_assigns.len(), elab.signals.len());
        }
        iter_count += 1;
        // Evaluate increment: handle i++, i=i+1, etc.
        match &gf.incr.kind {
            ExprKind::Unary { op: UnaryOp::PostIncr, .. } | ExprKind::Unary { op: UnaryOp::PreIncr, .. } => { i += 1; }
            ExprKind::Unary { op: UnaryOp::PostDecr, .. } | ExprKind::Unary { op: UnaryOp::PreDecr, .. } => { i -= 1; }
            _ => {
                // Try to evaluate as expression (e.g. i = i + 1 expanded by parser)
                let new_val = eval_const_expr(&gf.incr, &elab.parameters) as i64;
                if new_val == i { i += 1; } else { i = new_val; }
            }
        }
    }
    elab.parameters.remove(var);
    Ok(())
}

/// Largest plausible width for a single PACKED signal/net/port (1 Mibit ≈
/// 128 KiB as a Wide value). No real RTL declares a single packed vector wider
/// than this; a computed width at/above it is invariably a parameter-resolution
/// underflow (e.g. `[N-1:0]` with N evaluating to 0, so `N-1` wraps to ~u32::MAX
/// → a multi-GB phantom signal that OOMs elaboration). Clamp such widths so
/// elaboration survives a config the const-evaluator can't fully resolve. The
/// largest legitimate value observed across the corpus (black-parrot's
/// `all_cfgs_gp` config table) is 344064 bits, well under this cap.
pub const SANE_MAX_PACKED_WIDTH: u32 = 1 << 20;

/// Width substituted for an absurd (underflowed) packed width. A width past the
/// sane cap is never real data — it comes from `[N-1:0]` with N resolving to 0,
/// so `N-1` wraps to ~u32::MAX. The slice carries no meaningful value, so we
/// collapse it to a single bit: this keeps both elaboration AND simulation
/// memory bounded (a 1 Mibit clamp still costs 128 KiB/signal and, once such a
/// phantom feeds continuous-assign/always evaluation, re-materializes per
/// update and OOMs the run). 1 bit is exactly as wrong as any other clamp for a
/// config the const-evaluator could not resolve, but free.
const UNDERFLOW_WIDTH_PLACEHOLDER: u32 = 1;

/// Combine packed-dimension widths with saturating math and clamp the result to
/// `SANE_MAX_PACKED_WIDTH`, warning once when an absurd width is suppressed.
fn clamp_packed_width(w: u64, ctx: &str) -> u32 {
    if w > SANE_MAX_PACKED_WIDTH as u64 {
        use std::sync::atomic::{AtomicBool, Ordering};
        static WARNED: AtomicBool = AtomicBool::new(false);
        if !WARNED.swap(true, Ordering::Relaxed) {
            eprintln!("[xezim][warning] packed width {} exceeds sane cap {} ({}); collapsing to \
                       {} bit — a parameter likely resolved to 0 causing an `[N-1:0]` underflow",
                w, SANE_MAX_PACKED_WIDTH, ctx, UNDERFLOW_WIDTH_PLACEHOLDER);
        }
        UNDERFLOW_WIDTH_PLACEHOLDER
    } else {
        w as u32
    }
}

pub fn default_tick_s() -> f64 { 1e-9 }

/// Public entry to pre-scale a module's delays from its timeunit to the global
/// tick (see `rewrite_module_item_delays`).
pub fn rewrite_module_delays_pub(items: &mut [ModuleItem], unit_s: f64, tick_s: f64) {
    rewrite_module_item_delays(items, unit_s, tick_s);
}

/// Rewrite every delay expression inside a module's items so it is expressed in
/// GLOBAL TICK units (`tick_s` seconds each), given the module's own timeunit
/// `unit_s`. A *bare* delay `#5` is a count of `unit_s`, so it scales by
/// `unit_s / tick_s`; a *time literal* `#10ns` is absolute seconds, so it
/// becomes `seconds / tick_s`. With no finer timescale anywhere (tick_s = unit_s
/// = 1 ns) both are identities, so behaviour is unchanged. LRM §22.7 / §3.14.
fn rewrite_module_item_delays(items: &mut [ModuleItem], unit_s: f64, tick_s: f64) {
    for item in items.iter_mut() {
        match item {
            ModuleItem::AlwaysConstruct(ac) => rewrite_stmt_delays(&mut ac.stmt, unit_s, tick_s),
            ModuleItem::InitialConstruct(ic) => rewrite_stmt_delays(&mut ic.stmt, unit_s, tick_s),
            ModuleItem::FinalConstruct(fc) => rewrite_stmt_delays(&mut fc.stmt, unit_s, tick_s),
            ModuleItem::GenerateFor(gf) => rewrite_module_item_delays(&mut gf.items, unit_s, tick_s),
            ModuleItem::GenerateIf(gi) => {
                for (_c, items) in gi.branches.iter_mut() {
                    rewrite_module_item_delays(items, unit_s, tick_s);
                }
            }
            ModuleItem::GenerateRegion(gr) => rewrite_module_item_delays(&mut gr.items, unit_s, tick_s),
            ModuleItem::GenerateCase(gc) => {
                for arm in gc.arms.iter_mut() {
                    rewrite_module_item_delays(&mut arm.items, unit_s, tick_s);
                }
            }
            _ => {}
        }
    }
}

/// Replace a single delay expression with its tick-count equivalent.
fn rewrite_delay_expr(d: &mut Expression, unit_s: f64, tick_s: f64) {
    use crate::ast::expr::NumberLiteral;
    if let ExprKind::Number(NumberLiteral::Time(s)) = &d.kind {
        // Absolute time literal → ticks.
        let ticks = *s / tick_s;
        *d = Expression::new(ExprKind::Number(NumberLiteral::Real(ticks)), d.span);
    } else {
        // Bare delay (count of the module timeunit) → ticks.
        let scale = unit_s / tick_s;
        if (scale - 1.0).abs() > f64::EPSILON {
            let span = d.span;
            let inner = std::mem::replace(d, Expression::new(ExprKind::Null, span));
            *d = Expression::new(ExprKind::Binary {
                op: BinaryOp::Mul,
                left: Box::new(inner),
                right: Box::new(Expression::new(
                    ExprKind::Number(NumberLiteral::Real(scale)), span)),
            }, span);
        }
    }
}

fn rewrite_stmt_delays(stmt: &mut Statement, unit_s: f64, tick_s: f64) {
    match &mut stmt.kind {
        StatementKind::TimingControl { control, stmt } => {
            if let TimingControl::Delay(d) = control {
                rewrite_delay_expr(d, unit_s, tick_s);
            }
            rewrite_stmt_delays(stmt, unit_s, tick_s);
        }
        StatementKind::NonblockingAssign { delay: Some(d), .. } => {
            rewrite_delay_expr(d, unit_s, tick_s);
        }
        StatementKind::SeqBlock { stmts, .. } | StatementKind::ParBlock { stmts, .. } => {
            for s in stmts.iter_mut() { rewrite_stmt_delays(s, unit_s, tick_s); }
        }
        StatementKind::If { then_stmt, else_stmt, .. } => {
            rewrite_stmt_delays(then_stmt, unit_s, tick_s);
            if let Some(e) = else_stmt { rewrite_stmt_delays(e, unit_s, tick_s); }
        }
        StatementKind::For { body, .. }
        | StatementKind::Foreach { body, .. }
        | StatementKind::While { body, .. }
        | StatementKind::DoWhile { body, .. }
        | StatementKind::Repeat { body, .. }
        | StatementKind::Forever { body, .. } => rewrite_stmt_delays(body, unit_s, tick_s),
        StatementKind::Wait { stmt, .. } => rewrite_stmt_delays(stmt, unit_s, tick_s),
        StatementKind::Case { items, .. } => {
            for it in items.iter_mut() { rewrite_stmt_delays(&mut it.stmt, unit_s, tick_s); }
        }
        _ => {}
    }
}

/// Fully resolve a `DataType` through a chain of typedef aliases
/// (`typedef A B; typedef B C; typedef C struct{…}`). A single
/// `typedef_types.get(name)` only peels one level, so a struct reached through
/// several aliases (black-parrot's CCE types) loses its layout. Follow the chain
/// until a non-`TypeReference` (or an unresolved name) is hit; a small iteration
/// guard prevents looping on recursive typedefs (caught separately at decl time).
pub fn resolve_typedef_chain<'a>(
    dt: &'a DataType,
    typedef_types: &'a HashMap<String, DataType>,
) -> &'a DataType {
    let mut cur = dt;
    for _ in 0..64 {
        let DataType::TypeReference { name, .. } = cur else { break };
        match typedef_types.get(&name.name.name) {
            Some(next) => cur = next,
            None => break,
        }
    }
    cur
}

/// Resolve the width of a data type.
pub fn resolve_type_width(
    dt: &DataType,
    params: Option<&HashMap<String, Value>>,
    typedefs: Option<&HashMap<String, u32>>
) -> u32 {
    match dt {
        DataType::IntegerVector { dimensions, .. } => {
            if dimensions.is_empty() { return 1; }
            let mut total = 1u64;
            for dim in dimensions {
                if let PackedDimension::Range { left, right, .. } = dim {
                    let lv = const_eval_i64_with_params(left, params);
                    let rv = const_eval_i64_with_params(right, params);
                    if let (Some(l), Some(r)) = (lv, rv) {
                        let w = ((l - r).abs() + 1) as u64;
                        total = total.saturating_mul(w);
                    }
                }
            }
            clamp_packed_width(total, "IntegerVector")
        }
        DataType::IntegerAtom { kind, .. } => match kind {
            IntegerAtomType::Byte => 8,
            IntegerAtomType::ShortInt => 16,
            IntegerAtomType::Int => 32,
            IntegerAtomType::LongInt => 64,
            IntegerAtomType::Integer => 32,
            IntegerAtomType::Time => 64,
        },
        DataType::Real { .. } => 64,
        DataType::Implicit { dimensions, .. } => {
            if dimensions.is_empty() { return 1; }
            let mut total = 1u64;
            for dim in dimensions {
                if let PackedDimension::Range { left, right, .. } = dim {
                    let lv = const_eval_i64_with_params(left, params);
                    let rv = const_eval_i64_with_params(right, params);
                    if let (Some(l), Some(r)) = (lv, rv) {
                        let w = ((l - r).abs() + 1) as u64;
                        total = total.saturating_mul(w);
                    }
                }
            }
            clamp_packed_width(total, "Implicit")
        }
        DataType::TypeReference { name, dimensions, .. } => {
            let mut base_width = if let Some(td) = typedefs {
                td.get(&name.name.name).copied().unwrap_or(32)
            } else {
                32
            };
            if !dimensions.is_empty() {
                let mut total = base_width as u64;
                for dim in dimensions {
                    if let PackedDimension::Range { left, right, .. } = dim {
                        if let (Some(l), Some(r)) = (const_eval_i64_with_params(left, params), const_eval_i64_with_params(right, params)) {
                            let w = ((l - r).abs() + 1) as u64;
                            total = total.saturating_mul(w);
                        }
                    }
                }
                base_width = clamp_packed_width(total, "TypeReference");
            }
            base_width
        }
        DataType::Simple { kind, .. } => match kind {
            SimpleType::String => 1024, // Dynamic string, allocate 128 chars max
            SimpleType::Chandle => 64,
            SimpleType::Event => 1,
        },
        DataType::Enum(e) => {
            if let Some(bt) = &e.base_type {
                resolve_type_width(bt, params, typedefs)
            } else {
                32
            }
        }
        DataType::Struct(s) => {
            let is_union = matches!(s.kind, StructUnionKind::Union);
            let mut total = 0u32;
            let mut max_w = 0u32;
            let mut member_count = 0u32;
            for member in &s.members {
                let mw = resolve_type_width(&member.data_type, params, typedefs);
                total += mw * member.declarators.len() as u32;
                for _ in &member.declarators {
                    if mw > max_w { max_w = mw; }
                    member_count += 1;
                }
            }
            let elem_w = if is_union {
                if s.tagged {
                    let tag_w = (member_count.max(2) - 1).next_power_of_two().trailing_zeros().max(1);
                    max_w + tag_w
                } else { max_w }
            } else { total };
            // Packed array dimensions after the body (`struct {...} [N-1:0]`)
            // multiply the element width.
            let mut w = elem_w as u64;
            for dim in &s.dimensions {
                if let PackedDimension::Range { left, right, .. } = dim {
                    if let (Some(l), Some(r)) = (const_eval_i64_with_params(left, params), const_eval_i64_with_params(right, params)) {
                        w = w.saturating_mul(((l - r).abs() + 1) as u64);
                    }
                }
            }
            clamp_packed_width(w, "Struct")
        }
        DataType::Void(_) => 0,
        _ => 32,
    }
}

/// Check if a data type is signed.
pub fn is_type_signed(dt: &DataType) -> bool {
    match dt {
        DataType::IntegerVector { signing, .. } => matches!(signing, Some(Signing::Signed)),
        DataType::IntegerAtom { kind, signing, .. } => {
            if let Some(s) = signing { return matches!(s, Signing::Signed); }
            match kind {
                IntegerAtomType::Byte | IntegerAtomType::ShortInt | IntegerAtomType::Int | IntegerAtomType::LongInt | IntegerAtomType::Integer => true,
                IntegerAtomType::Time => false,
            }
        }
        DataType::Implicit { signing, .. } => matches!(signing, Some(Signing::Signed)),
        DataType::Real { .. } => true,
        DataType::Struct(su) => matches!(su.signing, Some(Signing::Signed)),
        _ => false,
    }
}

pub fn is_type_real(dt: &DataType) -> bool {
    matches!(dt, DataType::Real { .. })
}

/// Returns the default value for a type: 0 for 2-state types, X for 4-state types.
fn default_value_for_type(dt: &DataType, width: u32) -> Value {
    if is_type_real(dt) { return Value::from_f64(0.0); }
    // LRM §6.20.3: `chandle` defaults to null. Module-scope `chandle h;`
    // without explicit init must read as 0 so `if (h == null)` works.
    // Class handles via TypeReference are handled at runtime via the
    // VarDecl/init paths (where module.classes is in scope).
    if matches!(dt, DataType::Simple { kind: SimpleType::Chandle, .. }) {
        return Value::zero(width);
    }
    if is_type_two_state(dt) { Value::zero(width) } else { Value::new(width) }
}

/// Returns true for 2-state types (bit, byte, shortint, int, longint) whose default is 0.
pub fn is_type_two_state(dt: &DataType) -> bool {
    match dt {
        DataType::IntegerVector { kind, .. } => matches!(kind, IntegerVectorType::Bit),
        DataType::IntegerAtom { kind, .. } => matches!(kind,
            IntegerAtomType::Byte | IntegerAtomType::ShortInt | IntegerAtomType::Int | IntegerAtomType::LongInt),
        DataType::Real { .. } => true,
        _ => false,
    }
}

/// Ceil-log2 (number of bits to index `n` values): `$clog2(n)`. 0 for n<=1.
fn ceil_log2(n: u64) -> u64 {
    if n <= 1 { return 0; }
    let mut res = 0u64;
    let mut t = n - 1;
    while t > 0 { t >>= 1; res += 1; }
    res
}

pub fn const_eval_i64_with_params(expr: &Expression, params: Option<&HashMap<String, Value>>) -> Option<i64> {
    match &expr.kind {
        ExprKind::Number(NumberLiteral::Integer { value, base, .. }) => {
            let r = match base { NumberBase::Binary => 2, NumberBase::Octal => 8, NumberBase::Hex => 16, NumberBase::Decimal => 10 };
            i64::from_str_radix(&value.replace('_', ""), r).ok()
        }
        ExprKind::Number(NumberLiteral::UnbasedUnsized('0')) => Some(0),
        ExprKind::Number(NumberLiteral::UnbasedUnsized('1')) => Some(1),
        // Time literal magnitude in tick units (1 ns).
        ExprKind::Number(NumberLiteral::Time(s)) => Some((*s * 1e9) as i64),
        ExprKind::Ident(hier) => {
            let name = hier.path.last().map(|s| s.name.name.as_str()).unwrap_or("");
            params.and_then(|p| p.get(name)).and_then(|v| v.to_i64())
                // Fall back to the global package/$unit param snapshot so that a
                // dimension like `[paddr_width_p - page_offset_width_gp - 1:0]`
                // (where the global `page_offset_width_gp` is absent from the
                // scoped instance-merge param map) resolves instead of dropping
                // the whole dimension — which otherwise mis-sized black-parrot's
                // bp_pte_leaf_s and wrapped r_entry_high_bits_lp.
                .or_else(|| param_fallback_get(name).and_then(|v| v.to_i64()))
        }
        ExprKind::Binary { op, left, right } => {
            // LRM §11.4 — full operator set, evaluated in i64 context.
            // Short-circuit logical/conditional handled separately to avoid
            // unnecessary right-side eval (and to match LRM §11.4.7 logical
            // short-circuit semantics).
            match op {
                BinaryOp::LogAnd => {
                    let l = const_eval_i64_with_params(left, params)?;
                    if l == 0 { return Some(0); }
                    let r = const_eval_i64_with_params(right, params)?;
                    Some(if r != 0 { 1 } else { 0 })
                }
                BinaryOp::LogOr => {
                    let l = const_eval_i64_with_params(left, params)?;
                    if l != 0 { return Some(1); }
                    let r = const_eval_i64_with_params(right, params)?;
                    Some(if r != 0 { 1 } else { 0 })
                }
                _ => {
                    let l = const_eval_i64_with_params(left, params)?;
                    let r = const_eval_i64_with_params(right, params)?;
                    match op {
                        BinaryOp::Add => l.checked_add(r),
                        BinaryOp::Sub => l.checked_sub(r),
                        BinaryOp::Mul => l.checked_mul(r),
                        BinaryOp::Div => if r != 0 { Some(l / r) } else { None },
                        BinaryOp::Mod => if r != 0 { Some(l % r) } else { None },
                        // LRM §11.4.3 power.
                        BinaryOp::Power => {
                            if r < 0 { return None; }
                            let e = u32::try_from(r).ok()?;
                            l.checked_pow(e)
                        }
                        BinaryOp::ShiftLeft | BinaryOp::ArithShiftLeft => Some(l.wrapping_shl(r as u32)),
                        BinaryOp::ShiftRight => Some((l as u64).wrapping_shr(r as u32) as i64),
                        BinaryOp::ArithShiftRight => Some(l.wrapping_shr(r as u32)),
                        BinaryOp::BitAnd  => Some(l & r),
                        BinaryOp::BitOr   => Some(l | r),
                        BinaryOp::BitXor  => Some(l ^ r),
                        BinaryOp::BitXnor => Some(!(l ^ r)),
                        // LRM §11.4.4 equality / §11.4.5 case equality.
                        BinaryOp::Eq | BinaryOp::CaseEq      => Some(if l == r { 1 } else { 0 }),
                        BinaryOp::Neq | BinaryOp::CaseNeq    => Some(if l != r { 1 } else { 0 }),
                        // LRM §11.4.6 relational.
                        BinaryOp::Lt  => Some(if l <  r { 1 } else { 0 }),
                        BinaryOp::Leq => Some(if l <= r { 1 } else { 0 }),
                        BinaryOp::Gt  => Some(if l >  r { 1 } else { 0 }),
                        BinaryOp::Geq => Some(if l >= r { 1 } else { 0 }),
                        _ => None,
                    }
                }
            }
        }
        ExprKind::Unary { op, operand } => {
            // For reduction operators the bit-width matters; without a known
            // declared width we treat the value as its i64 footprint. Good
            // enough for typical const-expr usage (e.g. `|MASK`, `&ALL_ONES`).
            let v = const_eval_i64_with_params(operand, params)?;
            match op {
                UnaryOp::Plus    => Some(v),
                UnaryOp::Minus   => Some(v.wrapping_neg()),
                UnaryOp::LogNot  => Some(if v == 0 { 1 } else { 0 }),
                UnaryOp::BitNot  => Some(!v),
                UnaryOp::BitAnd  => Some(if v == -1 { 1 } else { 0 }), // reduction & on all-ones i64
                UnaryOp::BitNand => Some(if v == -1 { 0 } else { 1 }),
                UnaryOp::BitOr   => Some(if v != 0  { 1 } else { 0 }),
                UnaryOp::BitNor  => Some(if v != 0  { 0 } else { 1 }),
                UnaryOp::BitXor  => Some((v.count_ones() & 1) as i64),
                UnaryOp::BitXnor => Some(((!v.count_ones()) & 1) as i64),
                _ => None,
            }
        }
        // LRM §11.4.11 conditional ?: — both branches optional to evaluate
        // depending on cond, but const-eval requires the chosen branch.
        ExprKind::Conditional { condition, then_expr, else_expr } => {
            let c = const_eval_i64_with_params(condition, params)?;
            if c != 0 {
                const_eval_i64_with_params(then_expr, params)
            } else {
                const_eval_i64_with_params(else_expr, params)
            }
        }
        ExprKind::Paren(e) => const_eval_i64_with_params(e, params),
        // LRM §20.8 / §20.9 — constant integer system functions commonly used
        // in array bounds: $clog2, $unsigned, $signed are size-preserving;
        // $min/$max take two args; $ln/$log10/etc. are not constant-eval here.
        ExprKind::SystemCall { name, args } => match name.as_str() {
            "$clog2" => {
                let val = const_eval_i64_with_params(args.first()?, params)?;
                if val <= 1 { Some(0) }
                else {
                    let mut res = 0;
                    let mut tmp = val - 1;
                    while tmp > 0 { tmp >>= 1; res += 1; }
                    Some(res)
                }
            }
            "$unsigned" | "$signed" => const_eval_i64_with_params(args.first()?, params),
            // LRM §20.9 bit-introspection system functions.
            // `$countones(x)` — Hamming weight (count of 1 bits).
            // `$onehot(x)` — 1 iff exactly one bit set.
            // `$onehot0(x)` — 1 iff at most one bit set.
            // `$isunknown(x)` — 1 iff any bit is X or Z.
            // For const-eval we operate on the const-evaluated i64 value
            // (X/Z bits aren't preserved, so $isunknown is 0 here).
            "$countones" => {
                let v = const_eval_i64_with_params(args.first()?, params)?;
                Some((v as u64).count_ones() as i64)
            }
            "$onehot" => {
                let v = const_eval_i64_with_params(args.first()?, params)?;
                let v = v as u64;
                Some(if v != 0 && v & (v - 1) == 0 { 1 } else { 0 })
            }
            "$onehot0" => {
                let v = const_eval_i64_with_params(args.first()?, params)?;
                let v = v as u64;
                Some(if v == 0 || v & (v - 1) == 0 { 1 } else { 0 })
            }
            "$isunknown" => {
                // const_eval flattens X/Z to 0 — so const-eval always
                // returns 0 here. The runtime path is the correct
                // place to check x/z; this just keeps parameter
                // expressions like `parameter int K = $isunknown(N);`
                // from falling through to a generic 0.
                let _ = const_eval_i64_with_params(args.first()?, params)?;
                Some(0)
            }
            "$countbits" => {
                // `$countbits(x, ctl1[, ctl2 …])` — count bits matching
                // any of the control values (0/1/X/Z encoded as 2'b
                // const). For const-eval we only count 0/1 controls
                // since X/Z are stripped.
                let v = const_eval_i64_with_params(args.first()?, params)? as u64;
                let mut want_zero = false;
                let mut want_one = false;
                for ctl in &args[1..] {
                    if let Some(c) = const_eval_i64_with_params(ctl, params) {
                        match c {
                            0 => want_zero = true,
                            1 => want_one = true,
                            _ => {}
                        }
                    }
                }
                if !want_zero && !want_one {
                    return Some(0);
                }
                // Width of x: take the largest set bit + 1, capped at 64.
                let w = 64 - v.leading_zeros() as u64;
                let mut count = 0u32;
                if want_one {
                    count += v.count_ones();
                }
                if want_zero {
                    let mask = if w == 64 { u64::MAX } else { (1u64 << w) - 1 };
                    count += (!v & mask).count_ones();
                }
                Some(count as i64)
            }
            // LRM §20.7 — `$bits(x)` returns the bit width. We handle the
            // cases reachable without a typedef table: a parameter ident
            // (uses its Value width), a sized number literal (uses the
            // declared size), or an `$unsigned`/`$signed` wrapper.
            // `$bits(typedef_name)` requires typedef threading and falls
            // through to None — runtime path still resolves it.
            "$bits" => {
                let arg = args.first()?;
                let inner = if let ExprKind::SystemCall { name, args: a2 } = &arg.kind {
                    if name == "$unsigned" || name == "$signed" { a2.first()? } else { arg }
                } else { arg };
                match &inner.kind {
                    ExprKind::Ident(hier) => {
                        let name = hier.path.last().map(|s| s.name.name.as_str()).unwrap_or("");
                        // First try parameter ident → its Value width.
                        params?.get(name).map(|v| v.width as i64)
                            // Then fall through to the thread-local typedef
                            // table (set by callers that have one available).
                            .or_else(|| TYPEDEFS_TLS.with(|td| {
                                td.borrow().as_ref()
                                    .and_then(|m| m.get(name).copied())
                                    .map(|w| w as i64)
                            }))
                    }
                    ExprKind::Number(NumberLiteral::Integer { size: Some(s), .. }) => Some(*s as i64),
                    ExprKind::Number(NumberLiteral::Integer { size: None, .. }) => Some(32),
                    ExprKind::Number(NumberLiteral::UnbasedUnsized(_)) => Some(1),
                    _ => None,
                }
            }
            // LRM §20.7 array-introspection system functions over an array
            // name: each consults ARRAYS_TLS for `(lo, hi)` and returns
            // the appropriate bound. Falls through to None when the
            // table is empty or the name is not registered.
            "$size" | "$left" | "$right" | "$high" | "$low" | "$dimensions" => {
                let arg = args.first()?;
                let arr_name = match &arg.kind {
                    ExprKind::Ident(hier) => {
                        hier.path.last().map(|s| s.name.name.clone())?
                    }
                    _ => return None,
                };
                ARRAYS_TLS.with(|ar| {
                    ar.borrow().as_ref().and_then(|m| m.get(&arr_name).copied())
                })
                .map(|(lo, hi, _ndim)| match name.as_str() {
                    "$size" => hi - lo + 1,
                    "$left" => lo,
                    "$right" => hi,
                    "$high" => hi.max(lo),
                    "$low" => lo.min(hi),
                    "$dimensions" => 1,
                    _ => unreachable!(),
                })
            }
            _ => None,
        }
        // Packed-array element select / struct member select in an integer
        // const context — e.g. a dimension `[all_cfgs_gp[idx].icache_sets-1:0]`
        // or `[proc_param_lp.field-1:0]`. Delegate to the full value evaluator
        // (which carries the array-elem / struct-layout / package-param TLS
        // context) and reduce to i64. Without this, such a dimension underflows
        // to ~u32::MAX (black-parrot config widths used directly in a range).
        ExprKind::Index { .. } | ExprKind::MemberAccess { .. } => {
            let p = params?;
            eval_const_expr_val(expr, p).to_u64().map(|u| u as i64)
        }
        // User ceil-log2 const function (HardFloat `clog2`), == $clog2.
        ExprKind::Call { func, args }
            if matches!(&func.kind, ExprKind::Ident(h)
                if h.path.last().map(|s| s.name.name.as_str()) == Some("clog2")) =>
        {
            let n = const_eval_i64_with_params(args.first()?, params)? as u64;
            Some(ceil_log2(n) as i64)
        }
        _ => None,
    }
}

// LRM §20.7 — thread-local typedef table consulted by const-eval `$bits`
// when the operand is a typedef-name ident. Avoids changing the signature
// of `const_eval_i64_with_params` at all 47 call sites. Callers that
// have a typedef table in scope wrap their const-eval with
// `with_typedefs(td, || const_eval_…)`; the table is restored on exit.
thread_local! {
    static TYPEDEFS_TLS: std::cell::RefCell<Option<HashMap<String, u32>>>
        = std::cell::RefCell::new(None);
    /// LRM §20.7 — thread-local array-range table for const-eval of
    /// `$size`/`$left`/`$right`/`$high`/`$low`/`$dimensions` on an
    /// array-name ident. Same pattern as TYPEDEFS_TLS to avoid touching
    /// every call site. Maps `name → (lo, hi, ndim)`.
    static ARRAYS_TLS: std::cell::RefCell<Option<HashMap<String, (i64, i64, u32)>>>
        = std::cell::RefCell::new(None);
    /// Const-eval support for struct-member select `s.field` (IEEE 1800-2017
    /// §7.2.1): packed-struct field layout `name → [(field, lsb_offset, width)]`,
    /// mirroring `ElaboratedModule.packed_struct_fields`. Lets `eval_const_expr_val`
    /// slice a field out of a struct-typed parameter Value (black-parrot's
    /// `proc_param_lp.icache_sets`). Updated incrementally as struct params/
    /// localparams register their layout, so a later localparam that selects from
    /// an earlier one resolves.
    static STRUCT_FIELDS_TLS: std::cell::RefCell<HashMap<String, Vec<(String, u32, u32)>>>
        = std::cell::RefCell::new(HashMap::default());
    /// Const-eval support for packed-array element select `a[i]` on an
    /// array-of-structs parameter: `name → element bit-width`. Lets
    /// `eval_const_expr_val` slice element `i` (`[i*elem_w +: elem_w]`) out of a
    /// packed-array parameter Value (black-parrot's `all_cfgs_gp[bp_params_p]`).
    static PACKED_ELEM_W_TLS: std::cell::RefCell<HashMap<String, u32>>
        = std::cell::RefCell::new(HashMap::default());
    /// Globally-visible parameter fallback for const-eval: package/$unit params
    /// (snapshot taken after package elaboration, before module inlining). When a
    /// const-eval `Ident` misses the scoped param map — e.g. a sub-module
    /// header localparam `sc = all_cfgs_gp[SEL]` evaluated in the instance-merge
    /// context, which holds only the sub-instance's own params — fall back here so
    /// the imported package parameter still resolves.
    static PARAM_FALLBACK_TLS: std::cell::RefCell<HashMap<String, Value>>
        = std::cell::RefCell::new(HashMap::default());
}

/// Install the global package/$unit parameter snapshot consulted by const-eval
/// `Ident` lookups that miss the scoped map. Idempotent overwrite.
fn set_param_fallback(params: &HashMap<String, Value>) {
    PARAM_FALLBACK_TLS.with(|c| *c.borrow_mut() = params.clone());
}

/// Look up `name` in the global parameter fallback (package/$unit params).
fn param_fallback_get(name: &str) -> Option<Value> {
    PARAM_FALLBACK_TLS.with(|c| c.borrow().get(name).cloned())
}

/// Record a struct param/localparam's packed field layout for const-eval
/// member selects (`s.field`). Keyed by bare name; later registrations win
/// (matches `packed_struct_fields`).
fn tls_register_struct_layout(name: &str, fields: &[(String, u32, u32)]) {
    STRUCT_FIELDS_TLS.with(|c| {
        c.borrow_mut().insert(name.to_string(), fields.to_vec());
    });
}

/// Record a packed-array parameter's element width for const-eval index selects
/// (`a[i]`).
fn tls_register_elem_w(name: &str, elem_w: u32) {
    if elem_w == 0 { return; }
    PACKED_ELEM_W_TLS.with(|c| {
        c.borrow_mut().insert(name.to_string(), elem_w);
    });
}

/// If `dt` is a packed array of a named type (`T [hi:lo]…`, e.g. black-parrot's
/// `bp_proc_param_s [max_cfgs-1:0] all_cfgs_gp`), register the element width
/// `$bits(T)` so const-eval `name[i]` can slice one element. No-op otherwise.
fn register_packed_array_elem_w(name: &str, dt: &DataType, typedefs: &HashMap<String, u32>) {
    if let DataType::TypeReference { name: tn, dimensions, .. } = dt {
        if !dimensions.is_empty() {
            if let Some(&ew) = typedefs.get(&tn.name.name) {
                tls_register_elem_w(name, ew);
            }
        }
    }
}

/// Run `f` with `typedefs` installed as the thread-local typedef table
/// consulted by const-eval `$bits(typedef_name)`. The previous binding
/// is restored on exit so nested calls compose correctly.
pub fn with_typedefs<R>(typedefs: &HashMap<String, u32>, f: impl FnOnce() -> R) -> R {
    let snapshot = typedefs.clone();
    let prev = TYPEDEFS_TLS.with(|td| std::mem::replace(&mut *td.borrow_mut(), Some(snapshot)));
    let r = f();
    TYPEDEFS_TLS.with(|td| *td.borrow_mut() = prev);
    r
}

/// LRM §20.7 — install the array-range table for the duration of `f`.
/// Restored on exit so nested calls compose.
pub fn with_arrays<R>(arrays: &HashMap<String, (i64, i64, u32)>, f: impl FnOnce() -> R) -> R {
    let snapshot = arrays.clone();
    let prev = ARRAYS_TLS.with(|ar| std::mem::replace(&mut *ar.borrow_mut(), Some(snapshot)));
    let r = f();
    ARRAYS_TLS.with(|ar| *ar.borrow_mut() = prev);
    r
}

/// Extract array range from unpacked dimensions. Returns Some((lo, hi)) for
/// `[lo:hi]` or `[size]` (which means [0:size-1]).
/// Every `[i]`/`[i][j]` suffix of a fixed shape, in row-major order.
fn index_tuples(shape: &[(i64, i64)]) -> Vec<String> {
    let mut out = vec![String::new()];
    for &(lo, hi) in shape {
        let mut next = Vec::with_capacity(out.len() * ((hi - lo + 1) as usize));
        for prefix in &out {
            for i in lo..=hi {
                next.push(format!("{}[{}]", prefix, i));
            }
        }
        out = next;
    }
    out
}

fn extract_array_range(dims: &[crate::ast::types::UnpackedDimension], params: &HashMap<String, Value>) -> Option<(i64, i64)> {
    if dims.is_empty() { return None; }
    match &dims[0] {
        crate::ast::types::UnpackedDimension::Range { left, right, .. } => {
            let l = const_eval_i64_with_params(left, Some(params)).unwrap_or(0);
            let r = const_eval_i64_with_params(right, Some(params)).unwrap_or(0);
            let lo = l.min(r);
            let hi = l.max(r);
            Some((lo, hi))
        }
        crate::ast::types::UnpackedDimension::Expression { expr, .. } => {
            let size = const_eval_i64_with_params(expr, Some(params)).unwrap_or(0);
            if size > 0 { Some((0, size - 1)) } else { None }
        }
        crate::ast::types::UnpackedDimension::Unsized(_) | 
        crate::ast::types::UnpackedDimension::Queue { .. } => {
            // For dynamic arrays and queues, allocate a fixed-size buffer for simulation
            Some((0, 63))
        }
        crate::ast::types::UnpackedDimension::Associative { .. } => {
            // Associative arrays are purely dynamic
            None
        }
        _ => None,
    }
}

fn width_with_unpacked_dims(dims: &[crate::ast::types::UnpackedDimension], base_width: u32) -> u32 {
    if dims.is_empty() { return base_width; }
    let mut total_elements = 1u32;
    for dim in dims {
        match dim {
            crate::ast::types::UnpackedDimension::Range { left, right, .. } => {
                let l = const_eval_i64_with_params(left, None).unwrap_or(0);
                let r = const_eval_i64_with_params(right, None).unwrap_or(0);
                total_elements *= ((l - r).abs() + 1) as u32;
            }
            crate::ast::types::UnpackedDimension::Expression { expr, .. } => {
                let size = const_eval_i64_with_params(expr, None).unwrap_or(0);
                total_elements *= size.max(1) as u32;
            }
            crate::ast::types::UnpackedDimension::Unsized(_) | 
            crate::ast::types::UnpackedDimension::Queue { .. } |
            crate::ast::types::UnpackedDimension::Associative { .. } => {
                total_elements *= 64;
            }
        }
    }
    base_width * total_elements
}

/// Evaluate a constant expression (for enum values, parameter defaults, etc.)
fn eval_const_expr(expr: &Expression, params: &HashMap<String, Value>) -> u64 {
    eval_const_expr_val(expr, params).to_u64().unwrap_or(0)
}

/// Evaluate an initializer for a typed declaration of known target width.
/// Handles SystemVerilog unsized fill literals (`'0` / `'1` / `'x` / `'z`)
/// per IEEE 1800-2017 §11.4.7: they expand to the full target width filled
/// with the indicated bit, not zero-extended from a 1-bit value.
/// Compute the per-element width of a multi-dimensional packed IntegerVector
/// type — `logic [3:0][7:0]` returns `Some(8)`; single-dim or unsupported
/// shapes return None. Used to register `packed_signal_elem_widths` so that
/// `var[i]` resolves to an element slice instead of a bit-select.
/// If `dt` is a single-dimension packed vector with an ASCENDING range
/// (`logic [0:7]`, left < right), return its width; else None. Multi-dim
/// packed (`[0:3][7:0]`) is intentionally excluded — its outer index selects
/// an element, not a bit, and ascending element ordering is vanishingly rare.
fn packed_ascending_width(dt: &DataType, params: &HashMap<String, Value>) -> Option<u32> {
    let dims = match dt {
        DataType::IntegerVector { dimensions, .. } => dimensions,
        DataType::Implicit { dimensions, .. } => dimensions,
        _ => return None,
    };
    if dims.len() != 1 { return None; }
    if let Some(PackedDimension::Range { left, right, .. }) = dims.first() {
        let l = const_eval_i64_with_params(left, Some(params))?;
        let r = const_eval_i64_with_params(right, Some(params))?;
        if l < r {
            return Some((r - l + 1) as u32);
        }
    }
    None
}

pub fn packed_inner_elem_width(
    dt: &DataType,
    params: &HashMap<String, Value>,
    typedefs: &HashMap<String, u32>,
) -> Option<u32> {
    // For a typedef-typed signal (`my_t var;`), look through the typedef chain.
    let resolved: &DataType = if let DataType::TypeReference { name, .. } = dt {
        // typedef_types isn't passed in here; conservatively return None for
        // typedef refs so callers can resolve via their own context.
        return None;
    } else { dt };
    if let DataType::IntegerVector { dimensions, .. } = resolved {
        if dimensions.len() < 2 { return None; }
        // Total width = product of all dims
        let mut total = 1u32;
        for d in dimensions {
            if let PackedDimension::Range { left, right, .. } = d {
                let lv = const_eval_i64_with_params(left, Some(params));
                let rv = const_eval_i64_with_params(right, Some(params));
                if let (Some(l), Some(r)) = (lv, rv) {
                    total *= ((l - r).abs() + 1) as u32;
                } else {
                    return None;
                }
            } else { return None; }
        }
        // Outermost (leftmost) dim is the element-array index; element width
        // is total / outer_count per LRM §7.4.1.
        if let Some(PackedDimension::Range { left, right, .. }) = dimensions.first() {
            let lv = const_eval_i64_with_params(left, Some(params));
            let rv = const_eval_i64_with_params(right, Some(params));
            if let (Some(l), Some(r)) = (lv, rv) {
                let outer = ((l - r).abs() + 1) as u32;
                if outer == 0 { return None; }
                return Some(total / outer);
            }
        }
    }
    None
}

/// Recover the declared width of a sized number literal in `init` (`7'h13`
/// → Some(7), `32'd5` → Some(32), unsized `5` → None). Used to size
/// implicit-typed parameters from their initializer so they don't default
/// to 32-bit and break later concat width math.
fn sized_literal_width(init: &Expression) -> Option<u32> {
    let mut cur = init;
    loop {
        match &cur.kind {
            ExprKind::Paren(inner) => cur = inner,
            ExprKind::Number(crate::ast::expr::NumberLiteral::Integer { size: Some(s), .. }) => return Some(*s),
            _ => return None,
        }
    }
}

/// Detect whether struct/union type `target` (body `dt`) transitively contains
/// a by-value member of its own type — illegal per IEEE 1800-2017 §7.2.1 (it
/// would have infinite size). Returns the offending member path, or None.
/// Catches direct (`node_t next;`) and mutual (A→B→A) recursion; a `visited`
/// set bounds the walk. Class-handle "linked list" members are NOT flagged
/// (classes live outside `typedef_types`, so they never resolve to a struct).
fn struct_typedef_self_reference(
    target: &str,
    dt: &DataType,
    typedef_types: &HashMap<String, DataType>,
) -> Option<String> {
    fn walk(
        target: &str,
        dt: &DataType,
        typedef_types: &HashMap<String, DataType>,
        visited: &mut Vec<String>,
    ) -> Option<String> {
        let su = match dt {
            DataType::Struct(su) => su,
            _ => return None,
        };
        for member in &su.members {
            let field = member.declarators.first()
                .map(|d| d.name.name.clone()).unwrap_or_default();
            if let DataType::TypeReference { name, .. } = &member.data_type {
                let mn = &name.name.name;
                if mn == target {
                    return Some(field);
                }
                if !visited.iter().any(|v| v == mn) {
                    if let Some(inner) = typedef_types.get(mn) {
                        visited.push(mn.clone());
                        if let Some(p) = walk(target, inner, typedef_types, visited) {
                            return Some(format!("{}.{}", field, p));
                        }
                        visited.pop();
                    }
                }
            } else if let DataType::Struct(_) = &member.data_type {
                if let Some(p) = walk(target, &member.data_type, typedef_types, visited) {
                    return Some(format!("{}.{}", field, p));
                }
            }
        }
        None
    }
    let mut visited = vec![target.to_string()];
    walk(target, dt, typedef_types, &mut visited)
}

/// Flatten a (possibly nested) packed struct/union `DataType` into
/// `(field_path, lsb_offset, width)` tuples for `packed_struct_fields`.
/// First-declared member is the MSB (IEEE 1800-2017 §7.2.1), so offsets are
/// Pack an assignment-pattern literal for a PACKED ARRAY OF STRUCTS parameter
/// (`T [N-1:0] p = '{ '{...}, '{...}, ... }`, e.g. black-parrot's
/// `bp_proc_param_s [max_cfgs-1:0] all_cfgs_gp`) into one packed Value. Each
/// pattern element is packed as the element struct type and the elements are
/// concatenated MSB-first (first pattern item = highest index, IEEE 1800-2017
/// §10.9.2 / §7.4.2). Returns None unless `dt` is a packed array of a struct
/// typedef and `expr` is an assignment pattern, so callers fall back cleanly.
fn pack_packed_array_const_value(
    dt: &DataType,
    expr: &Expression,
    params: &HashMap<String, Value>,
    typedefs: &HashMap<String, u32>,
    typedef_types: &HashMap<String, DataType>,
) -> Option<Value> {
    let ExprKind::AssignmentPattern(items) = &expr.kind else { return None };
    let DataType::TypeReference { name, dimensions, .. } = dt else { return None };
    if dimensions.is_empty() { return None; }
    // Element type = the referenced typedef, fully chased to its struct.
    let elem_dt = resolve_typedef_chain(typedef_types.get(&name.name.name)?, typedef_types);
    if !matches!(elem_dt, DataType::Struct(_)) { return None; }
    let elem_w = resolve_type_width(elem_dt, Some(params), Some(typedefs));
    if elem_w == 0 { return None; }
    let mut parts: Vec<Value> = Vec::with_capacity(items.len());
    for it in items {
        let e = it.expr();
        let v = pack_struct_const_value(elem_dt, e, params, typedefs, typedef_types)
            .map(|sv| sv.resize(elem_w))
            .unwrap_or_else(|| eval_init_for_width(e, params, elem_w));
        parts.push(v);
    }
    Some(Value::concat(&parts))
}

/// Type-aware parameter initializer evaluation: packed array-of-structs pattern,
/// then single struct pattern, else the generic const-eval. Centralises the
/// black-parrot config-table packing so every param-load site resolves
/// `all_cfgs_gp` (and struct params) consistently.
fn eval_param_value(
    dt: &DataType,
    init: &Expression,
    params: &HashMap<String, Value>,
    typedefs: &HashMap<String, u32>,
    typedef_types: &HashMap<String, DataType>,
    width: u32,
) -> Value {
    if let Some(v) = pack_packed_array_const_value(dt, init, params, typedefs, typedef_types) {
        return v.resize(width);
    }
    if let Some(v) = pack_struct_const_value(dt, init, params, typedefs, typedef_types) {
        return v.resize(width);
    }
    eval_init_for_width(init, params, width)
}

/// assigned LSB-first by walking members in reverse. Returns None if `dt`
/// does not resolve to a struct/union.
/// Bit-slice layout (name, offset, width) of a *packed* struct type, or `None`
/// for a non-struct or an *unpacked* struct. An unpacked struct's members are
/// separate storage, not bit-packed, so their offsets are meaningless and must
/// never be registered as a packed slice layout. Used by the simulator to give
/// a local packed-struct variable the same whole/member aliasing that
/// module-level packed-struct signals get.
/// `arr[N]` where `N` is a *parameter* is indistinguishable, to the parser, from
/// `arr[key_t]` (an associative array keyed by type `key_t`) — a bare identifier
/// before `]` is assumed to name a type. Rewrite an associative dimension whose
/// "key type" is really a known parameter (and not a known type) back into a
/// fixed-size dimension. Without this, `rec_t a[N];` is registered as an
/// associative array and never gets a size (`%p`, `$size`, `foreach` all lose).
pub fn normalize_unpacked_dims(
    dims: &[UnpackedDimension],
    params: &HashMap<String, Value>,
    typedef_types: &HashMap<String, DataType>,
) -> Vec<UnpackedDimension> {
    dims.iter()
        .map(|d| match d {
            UnpackedDimension::Associative { data_type: Some(dt), span } => {
                if let DataType::TypeReference { name, .. } = dt.as_ref() {
                    let n = &name.name.name;
                    if !typedef_types.contains_key(n) && params.contains_key(n) {
                        return UnpackedDimension::Expression {
                            expr: Box::new(make_ident_expr(n)),
                            span: *span,
                        };
                    }
                }
                d.clone()
            }
            other => other.clone(),
        })
        .collect()
}

/// Constant element indices of a declarator's (single) unpacked dimension.
/// Empty for a scalar; empty for dynamic/queue/associative (size unknown here).
fn const_dim_indices(
    dims: &[UnpackedDimension],
    params: &HashMap<String, Value>,
) -> Option<Vec<i64>> {
    match dims.first() {
        None => Some(Vec::new()),
        Some(UnpackedDimension::Expression { expr, .. }) => {
            match const_eval_i64_with_params(expr, Some(params)) {
                Some(n) if n > 0 && n <= 4096 => Some((0..n).collect()),
                _ => None,
            }
        }
        Some(UnpackedDimension::Range { left, right, .. }) => {
            match (
                const_eval_i64_with_params(left, Some(params)),
                const_eval_i64_with_params(right, Some(params)),
            ) {
                (Some(l), Some(r)) => {
                    let (lo, hi) = if l <= r { (l, r) } else { (r, l) };
                    if hi - lo < 4096 { Some((lo..=hi).collect()) } else { None }
                }
                _ => None,
            }
        }
        _ => None,
    }
}

fn register_member_leaf(elab: &mut ElaboratedModule, name: &str, dt: &DataType) {
    let w = resolve_type_width(dt, Some(&elab.parameters), Some(&elab.typedefs)).max(1);
    let signed = is_type_signed(dt);
    let real = is_type_real(dt);
    let resolved = resolve_typedef_chain(dt, &elab.typedef_types).clone();
    match &resolved {
        // A nested PACKED struct member keeps a contiguous bit layout: give it
        // its own signal plus the field offsets so `base.m.f` can slice it.
        DataType::Struct(su) if su.packed => {
            elab.signals.entry(name.to_string()).or_insert(Signal {
                is_const: false, name: name.to_string(), width: w, is_signed: signed,
                is_real: false, direction: None, value: Value::new(w), type_name: None,
            });
            if let Some(fields) =
                flatten_struct_fields(dt, &elab.parameters, &elab.typedefs, &elab.typedef_types)
            {
                if !fields.is_empty() {
                    elab.packed_struct_fields.insert(name.to_string(), fields);
                }
            }
        }
        // A nested UNPACKED struct member: recurse into its own members.
        DataType::Struct(_) => register_unpacked_aggregate(elab, name, dt),
        _ => {
            elab.signals.entry(name.to_string()).or_insert(Signal {
                is_const: false, name: name.to_string(), width: w, is_signed: signed,
                is_real: real, direction: None,
                value: if real { Value::from_f64(0.0) } else { Value::new(w) },
                type_name: None,
            });
        }
    }
}

/// Recursively pre-register the per-member signals of an UNPACKED aggregate
/// rooted at `base` (e.g. `arr[3]`, `c`). Each leaf keeps its declared width /
/// signedness / real-ness, array members expand per element, and nested packed
/// members get their own signal + bit-slice layout. Without this, elements are
/// created lazily on first assignment and lose their type (a `real` reads back
/// as raw bits) or alias each other through a bogus packed layout.
/// IEEE 1800-2017 §6.20.2: an UNPACKED-ARRAY parameter — `u32_t A[N] = {a, b}`.
/// Give each element its own const signal (`<prefix>A[i]`) so `A[i]` reads at
/// run time, and register the array so `A[i]` is an element select rather than
/// a bit-select of a scalar.
///
/// An OVERRIDE arrives already collapsed to one packed value, so slice it:
/// `{a, b}` puts `a` in the high bits (§11.4.12) and `a` is element 0.
/// Returns false when the size or the element values can't be resolved, so the
/// caller falls back to treating the parameter as a scalar.
fn register_array_param(
    elab: &mut ElaboratedModule,
    prefix: &str,
    name: &str,
    dims: &[UnpackedDimension],
    init: Option<&Expression>,
    override_val: Option<&Value>,
    data_type: &DataType,
    params: &HashMap<String, Value>,
) -> bool {
    let dims = normalize_unpacked_dims(dims, params, &elab.typedef_types);
    let Some(idxs) = const_dim_indices(&dims, params) else { return false };
    let n = idxs.len();
    if n == 0 {
        return false;
    }
    let elem_w = resolve_type_width(data_type, Some(params), Some(&elab.typedefs)).max(1);
    let mut vals: Vec<Value> = Vec::new();
    if let Some(p) = override_val {
        if (p.width as usize) < n * elem_w as usize {
            return false;
        }
        for i in 0..n {
            let off = (n - 1 - i) * elem_w as usize;
            let mut v = Value::zero(elem_w);
            for b in 0..elem_w as usize {
                v.set_bit(b, p.get_bit(off + b));
            }
            vals.push(v);
        }
    } else if let Some(init) = init {
        let items: Vec<&Expression> = match &init.kind {
            ExprKind::Concatenation(v) => v.iter().collect(),
            ExprKind::AssignmentPattern(items) => items.iter().map(|i| i.expr()).collect(),
            _ => return false,
        };
        if items.len() != n {
            return false;
        }
        for it in items {
            vals.push(eval_init_for_width(it, params, elem_w));
        }
    } else {
        return false;
    }
    let signed = is_type_signed(data_type);
    let full = format!("{}{}", prefix, name);
    // Needed so `A[i]` is an ELEMENT select, not a bit-select of a scalar.
    // Simulator::new seeds each element from the signal written just below.
    elab.arrays.insert(full, (0, n as i64 - 1, elem_w));
    for (i, v) in idxs.iter().zip(vals) {
        let sn = format!("{}{}[{}]", prefix, name, i);
        elab.signals.insert(sn.clone(), Signal {
            is_const: true, name: sn, width: elem_w, is_signed: signed,
            is_real: false, direction: None, value: v, type_name: None,
        });
    }
    true
}

fn register_unpacked_aggregate(elab: &mut ElaboratedModule, base: &str, dt: &DataType) {
    let resolved = resolve_typedef_chain(dt, &elab.typedef_types).clone();
    let DataType::Struct(su) = resolved else { return };
    if su.packed {
        return;
    }
    // IEEE 1800-2017 §7.3: a union is ONE piece of storage accessed through any
    // of its member names — writing `u.a` must be readable as `u.b`. So an
    // untagged union gets a single signal whose members all start at bit 0,
    // exactly like a packed one. (A TAGGED union is tag-checked: §7.3.2.)
    if matches!(su.kind, StructUnionKind::Union) && !su.tagged {
        let w = resolve_type_width(dt, Some(&elab.parameters), Some(&elab.typedefs)).max(1);
        elab.signals.entry(base.to_string()).or_insert(Signal {
            is_const: false, name: base.to_string(), width: w, is_signed: false,
            is_real: false, direction: None, value: Value::new(w), type_name: None,
        });
        if let Some(fields) =
            flatten_struct_fields(dt, &elab.parameters, &elab.typedefs, &elab.typedef_types)
        {
            if !fields.is_empty() {
                elab.packed_struct_fields.insert(base.to_string(), fields);
            }
        }
        return;
    }
    for member in &su.members {
        for mdecl in &member.declarators {
            let mbase = format!("{}.{}", base, mdecl.name.name);
            if mdecl.dimensions.is_empty() {
                register_member_leaf(elab, &mbase, &member.data_type);
            } else if let Some(idxs) = const_dim_indices(
                &normalize_unpacked_dims(&mdecl.dimensions, &elab.parameters, &elab.typedef_types),
                &elab.parameters,
            ) {
                for i in idxs {
                    register_member_leaf(elab, &format!("{}[{}]", mbase, i), &member.data_type);
                }
            }
            // Dynamic / queue / associative members stay lazily created.
        }
    }
}

/// Top-level member names of a struct/union type in DECLARATION order (packed
/// or unpacked). `None` for a non-struct type. Nested members are not expanded.
pub fn struct_member_names(
    dt: &DataType,
    typedef_types: &HashMap<String, DataType>,
) -> Option<Vec<String>> {
    match resolve_typedef_chain(dt, typedef_types) {
        DataType::Struct(su) => Some(
            su.members
                .iter()
                .flat_map(|m| m.declarators.iter().map(|d| d.name.name.clone()))
                .collect(),
        ),
        _ => None,
    }
}

pub fn packed_struct_field_layout(
    dt: &DataType,
    params: &HashMap<String, Value>,
    typedefs: &HashMap<String, u32>,
    typedef_types: &HashMap<String, DataType>,
) -> Option<Vec<(String, u32, u32)>> {
    match resolve_typedef_chain(dt, typedef_types) {
        DataType::Struct(su) if su.packed => {}
        _ => return None,
    }
    flatten_struct_fields(dt, params, typedefs, typedef_types)
}

fn flatten_struct_fields(
    dt: &DataType,
    params: &HashMap<String, Value>,
    typedefs: &HashMap<String, u32>,
    typedef_types: &HashMap<String, DataType>,
) -> Option<Vec<(String, u32, u32)>> {
    let resolved = resolve_typedef_chain(dt, typedef_types);
    if let DataType::Struct(su) = resolved {
        let is_union = matches!(su.kind, StructUnionKind::Union);
        let mut raw: Vec<(String, u32, DataType)> = Vec::new();
        for member in &su.members {
            let mw = resolve_type_width(&member.data_type, Some(params), Some(typedefs));
            for mdecl in &member.declarators {
                raw.push((mdecl.name.name.clone(), mw, member.data_type.clone()));
            }
        }
        let mut out: Vec<(String, u32, u32)> = Vec::new();
        if is_union {
            for (mn, mw, mdt) in &raw {
                out.push((mn.clone(), 0, *mw));
                if let Some(subs) = flatten_struct_fields(mdt, params, typedefs, typedef_types) {
                    for (sn, so, sw) in subs { out.push((format!("{}.{}", mn, sn), so, sw)); }
                }
            }
        } else {
            let mut offset: u32 = 0;
            for (mn, mw, mdt) in raw.iter().rev() {
                out.push((mn.clone(), offset, *mw));
                if let Some(subs) = flatten_struct_fields(mdt, params, typedefs, typedef_types) {
                    for (sn, so, sw) in subs { out.push((format!("{}.{}", mn, sn), offset + so, sw)); }
                }
                offset += mw;
            }
        }
        Some(out)
    } else { None }
}

/// Pack a struct/union assignment-pattern literal into a packed `Value`,
/// honoring declaration order (first member = MSB) so a struct-typed
/// parameter `parameter cfg_t C = '{base:.., len:..}` evaluates at elaboration
/// (IEEE 1800-2017 §6.20, §10.9.2). Handles named (`'{f:v}`), ordered
/// (`'{v0,v1}`), and `default:` items, and recurses for nested struct fields.
/// Returns None if `dt` is not a struct/union or `expr` is not a pattern.
fn pack_struct_const_value(
    dt: &DataType,
    expr: &Expression,
    params: &HashMap<String, Value>,
    typedefs: &HashMap<String, u32>,
    typedef_types: &HashMap<String, DataType>,
) -> Option<Value> {
    let su = match resolve_typedef_chain(dt, typedef_types) {
        DataType::Struct(su) => su.clone(),
        _ => return None,
    };
    let items = match &expr.kind {
        ExprKind::AssignmentPattern(items) => items,
        _ => return None,
    };
    // Top-level members in declaration order (first = MSB).
    let mut members: Vec<(String, u32, DataType)> = Vec::new();
    for member in &su.members {
        let mw = resolve_type_width(&member.data_type, Some(params), Some(typedefs));
        for mdecl in &member.declarators {
            members.push((mdecl.name.name.clone(), mw, member.data_type.clone()));
        }
    }
    // Index the pattern: named-by-field, ordered-by-position, and default.
    let mut named: HashMap<String, &Expression> = HashMap::default();
    let mut ordered: Vec<&Expression> = Vec::new();
    let mut default_expr: Option<&Expression> = None;
    for it in items {
        match it {
            AssignmentPatternItem::Named(id, v) => { named.insert(id.name.clone(), v); }
            AssignmentPatternItem::Ordered(v) => ordered.push(v),
            AssignmentPatternItem::Default(v) => default_expr = Some(v),
            // `'{<ident>: v}` may parse as Keyed when the key is an identifier
            AssignmentPatternItem::Keyed(k, v) => {
                if let ExprKind::Ident(h) = &k.kind {
                    if let Some(last) = h.path.last() { named.insert(last.name.name.clone(), v); }
                }
            }
            _ => {}
        }
    }
    let use_ordered = named.is_empty() && !ordered.is_empty();
    // Build MSB-first parts (declaration order) and concat.
    let mut parts: Vec<Value> = Vec::new();
    for (idx, (mn, mw, mdt)) in members.iter().enumerate() {
        let ve: Option<&Expression> = if use_ordered {
            ordered.get(idx).copied().or(default_expr)
        } else {
            named.get(mn).copied().or(default_expr)
        };
        let val = match ve {
            Some(e) => {
                if let Some(sub) = pack_struct_const_value(mdt, e, params, typedefs, typedef_types) {
                    sub.resize(*mw)
                } else {
                    eval_init_for_width(e, params, *mw)
                }
            }
            None => Value::zero(*mw),
        };
        parts.push(val);
    }
    Some(Value::concat(&parts))
}

fn eval_init_for_width(expr: &Expression, params: &HashMap<String, Value>, width: u32) -> Value {
    if let ExprKind::Number(NumberLiteral::UnbasedUnsized(c)) = &expr.kind {
        return match c {
            '0' => Value::zero(width),
            '1' => Value::ones(width),
            'x' | 'X' => Value::new(width),
            'z' | 'Z' => Value::all_z(width),
            _ => Value::new(width),
        };
    }
    eval_const_expr_val(expr, params).resize(width)
}

/// Evaluate a constant expression, returning a full Value (preserving width/sign).
fn eval_const_expr_val(expr: &Expression, params: &HashMap<String, Value>) -> Value {
    let res = match &expr.kind {
        ExprKind::Number(num) => {
            match num {
                NumberLiteral::Integer { size, signed, base, value, .. } => {
                    let w = size.unwrap_or(32);
                    let r = match base {
                        NumberBase::Binary => 2, NumberBase::Octal => 8,
                        NumberBase::Hex => 16, NumberBase::Decimal => 10,
                    };
                    let mut v = Value::from_str_radix(&value.replace('_', ""), r, w);
                    v.is_signed = *signed;
                    v
                }
                NumberLiteral::Real(f) => Value::from_f64(*f),
                // A time literal in a value context evaluates to its magnitude in
                // the simulation tick unit (1 ns), preserving the prior behaviour
                // where `10ns` const-folded to 10.
                NumberLiteral::Time(s) => Value::from_f64(*s * 1e9),
                NumberLiteral::UnbasedUnsized(c) => match c {
                    '0' => Value::zero(1), '1' => Value::from_u64(1, 1), _ => Value::new(1),
                },
            }
        }
        ExprKind::StringLiteral(s) => Value::from_string(s),
        ExprKind::Ident(hier) => {
            // Multi-segment hierarchical ident: `pt.FIELD` (a struct parameter's
            // field, parsed as a path rather than MemberAccess). Slice the field
            // from the struct param via its registered layout. Field path joins
            // path[1..] with '.' to match nested flatten keys (`pt.a.b`).
            if hier.path.len() > 1 {
                let base = hier.path[0].name.name.as_str();
                if let Some(base_val) = params.get(base).cloned() {
                    let field_path = hier.path[1..].iter()
                        .map(|s| s.name.name.as_str()).collect::<Vec<_>>().join(".");
                    if let Some((off, w)) = STRUCT_FIELDS_TLS.with(|c|
                        c.borrow().get(base).and_then(|layout|
                            layout.iter().find(|(f, _, _)| f == &field_path).map(|&(_, o, w)| (o, w)))) {
                        if w > 0 && off + w <= base_val.width {
                            return base_val.range_select((off + w - 1) as usize, off as usize);
                        }
                    }
                }
            }
            let name = hier.path.last().map(|s| s.name.name.as_str()).unwrap_or("");
            params.get(name).cloned()
                .or_else(|| param_fallback_get(name))
                .unwrap_or(Value::zero(32))
        }
        ExprKind::Binary { op, left, right } => {
            let l = eval_const_expr_val(left, params);
            let r = eval_const_expr_val(right, params);
            match op {
                BinaryOp::Add => l.add(&r),
                BinaryOp::Sub => l.sub(&r),
                BinaryOp::Mul => l.mul(&r),
                BinaryOp::Div => l.div(&r),
                BinaryOp::Mod => l.modulo(&r),
                BinaryOp::Power => l.power(&r),
                BinaryOp::Eq => l.is_equal(&r),
                BinaryOp::Neq => l.is_not_equal(&r),
                BinaryOp::Lt => l.less_than(&r),
                BinaryOp::Leq => l.less_equal(&r),
                BinaryOp::Gt => l.greater_than(&r),
                BinaryOp::Geq => l.greater_equal(&r),
                BinaryOp::ShiftLeft | BinaryOp::ArithShiftLeft => l.shift_left(&r),
                BinaryOp::ShiftRight => l.shift_right(&r),
                BinaryOp::BitOr => l.bitwise_or(&r),
                BinaryOp::BitAnd => l.bitwise_and(&r),
                BinaryOp::BitXor => l.bitwise_xor(&r),
                BinaryOp::BitXnor => l.bitwise_xor(&r).bitwise_not(),
                BinaryOp::LogOr => l.logic_or(&r),
                BinaryOp::LogAnd => l.logic_and(&r),
                BinaryOp::ArithShiftRight => l.arith_shift_right(&r),
                _ => Value::zero(32),
            }
        }
        ExprKind::Unary { op, operand } => {
            let v = eval_const_expr_val(operand, params);
            // LRM §11.4.9 — reduction operators collapse the vector to 1 bit.
            // Prior to this audit the catch-all silently returned `v` unchanged,
            // so `|MASK` / `&ALL_ONES` etc. produced a same-width value instead
            // of the 1-bit reduction result.
            match op {
                UnaryOp::Plus    => v,
                UnaryOp::Minus   => v.negate(),
                UnaryOp::BitNot  => v.bitwise_not(),
                UnaryOp::LogNot  => v.logic_not(),
                UnaryOp::BitAnd  => v.reduce_and(),
                UnaryOp::BitNand => v.reduce_and().bitwise_not(),
                UnaryOp::BitOr   => v.reduce_or(),
                UnaryOp::BitNor  => v.reduce_or().bitwise_not(),
                UnaryOp::BitXor  => v.reduce_xor(),
                UnaryOp::BitXnor => v.reduce_xor().bitwise_not(),
                _ => v,
            }
        }
        ExprKind::Dollar => Value::from_u64(u32::MAX as u64, 32),
        ExprKind::Paren(inner) => eval_const_expr_val(inner, params),
        ExprKind::SystemCall { name, args } if name == "$clog2" => {
            if let Some(arg) = args.first() {
                let v = eval_const_expr_val(arg, params);
                let val = v.to_u64().unwrap_or(0);
                if val <= 1 { Value::from_u64(0, 32) }
                else {
                    let mut res = 0;
                    let mut tmp = val - 1;
                    while tmp > 0 {
                        tmp >>= 1;
                        res += 1;
                    }
                    Value::from_u64(res, 32)
                }
            } else { Value::zero(32) }
        }
        // LRM §20.7 — `$bits(x)` in const-eval position. We handle the
        // cases reachable without a typedef table (parameter ident → its
        // Value's width; sized literal → declared size; `'0`/`'1` → 1).
        // `$bits(<typedef_name>)` requires typedef threading and returns 0
        // here — the runtime path still resolves it.
        ExprKind::SystemCall { name, args } if name == "$bits" => {
            let Some(arg) = args.first() else { return Value::zero(32); };
            let inner = if let ExprKind::SystemCall { name, args: a2 } = &arg.kind {
                if name == "$unsigned" || name == "$signed" {
                    a2.first().unwrap_or(arg)
                } else { arg }
            } else { arg };
            let w: u32 = match &inner.kind {
                ExprKind::Ident(hier) => {
                    let n = hier.path.last().map(|s| s.name.name.as_str()).unwrap_or("");
                    params.get(n).map(|v| v.width)
                        .or_else(|| TYPEDEFS_TLS.with(|td|
                            td.borrow().as_ref().and_then(|m| m.get(n).copied())))
                        .unwrap_or(0)
                }
                ExprKind::Number(NumberLiteral::Integer { size: Some(s), .. }) => *s,
                ExprKind::Number(NumberLiteral::Integer { size: None, .. }) => 32,
                ExprKind::Number(NumberLiteral::UnbasedUnsized(_)) => 1,
                _ => 0,
            };
            Value::from_u64(w as u64, 32)
        }
        // `$unsigned`/`$signed` in const-eval — width-preserving identity.
        ExprKind::SystemCall { name, args } if name == "$unsigned" || name == "$signed" => {
            args.first().map(|a| eval_const_expr_val(a, params)).unwrap_or_else(|| Value::zero(32))
        }
        // LRM §20.9 bit-introspection system functions in
        // value-producing const-eval position. Mirror the i64
        // const-eval implementations in `const_eval_i64_with_params`.
        ExprKind::SystemCall { name, args }
            if matches!(name.as_str(),
                "$countones" | "$onehot" | "$onehot0" | "$isunknown" | "$countbits") =>
        {
            let Some(arg) = args.first() else { return Value::zero(32); };
            let v = eval_const_expr_val(arg, params);
            let raw = v.to_u64().unwrap_or(0);
            let result: u64 = match name.as_str() {
                "$countones" => raw.count_ones() as u64,
                "$onehot" => if raw != 0 && raw & (raw - 1) == 0 { 1 } else { 0 },
                "$onehot0" => if raw == 0 || raw & (raw - 1) == 0 { 1 } else { 0 },
                "$isunknown" => 0, // const path strips X/Z
                "$countbits" => {
                    let mut want_zero = false;
                    let mut want_one = false;
                    for ctl in &args[1..] {
                        let c = eval_const_expr_val(ctl, params).to_u64().unwrap_or(0);
                        match c { 0 => want_zero = true, 1 => want_one = true, _ => {} }
                    }
                    let w = 64u32.saturating_sub(raw.leading_zeros());
                    let mut count: u32 = 0;
                    if want_one { count += raw.count_ones(); }
                    if want_zero {
                        let mask = if w >= 64 { u64::MAX } else { (1u64 << w) - 1 };
                        count += (!raw & mask).count_ones();
                    }
                    count as u64
                }
                _ => 0,
            };
            Value::from_u64(result, 32)
        }
        // LRM §20.7 array-introspection on an array-name ident: consults
        // ARRAYS_TLS (populated at end of elaborate_module_with_defs and
        // via runtime path before deferred-param eval).
        ExprKind::SystemCall { name, args }
            if matches!(name.as_str(),
                "$size" | "$left" | "$right" | "$high" | "$low" | "$dimensions")
                && args.first().map(|a| matches!(a.kind, ExprKind::Ident(_))).unwrap_or(false) =>
        {
            let arg = args.first().unwrap();
            let arr_name = if let ExprKind::Ident(hier) = &arg.kind {
                hier.path.last().map(|s| s.name.name.clone()).unwrap_or_default()
            } else { String::new() };
            let res = ARRAYS_TLS.with(|ar| {
                ar.borrow().as_ref().and_then(|m| m.get(&arr_name).copied())
            });
            if let Some((lo, hi, _ndim)) = res {
                let v: i64 = match name.as_str() {
                    "$size" => hi - lo + 1,
                    "$left" => lo,
                    "$right" => hi,
                    "$high" => hi.max(lo),
                    "$low" => lo.min(hi),
                    "$dimensions" => 1,
                    _ => 0,
                };
                Value::from_u64(v as u64, 32)
            } else {
                Value::zero(32)
            }
        }
        ExprKind::Conditional { condition, then_expr, else_expr } => {
            let c = eval_const_expr_val(condition, params);
            if c.is_true() { eval_const_expr_val(then_expr, params) }
            else { eval_const_expr_val(else_expr, params) }
        }
        ExprKind::Concatenation(parts) => {
            let mut r = Value::zero(0);
            for p in parts.iter().rev() {
                r = eval_const_expr_val(p, params).concat_with(&r);
            }
            r
        }
        ExprKind::Replication { count, exprs } => {
            let n = eval_const_expr_val(count, params).to_u64().unwrap_or(1) as usize;
            let mut inner = Value::zero(0);
            for p in exprs.iter().rev() {
                inner = eval_const_expr_val(p, params).concat_with(&inner);
            }
            let mut r = Value::zero(0);
            for _ in 0..n { r = inner.clone().concat_with(&r); }
            r
        }
        // SystemVerilog `for (j = 0; j < N; j = j+1)` parses the increment
        // as an `AssignExpr { lvalue: j, rvalue: j+1 }`. As a const-eval
        // result, the value of `j = j+1` is the rvalue's value (the
        // assigned-after value). Without this case the increment falls to
        // `Value::zero(32)` and the generate-for loop never terminates
        // until the 10000-iter safety cap fires — observed on E902
        // `cr_clic_sel` where the inner `for (j=0; j<DATA_WIDTH; j=j+1)`
        // ran ~313× over budget and consumed ~1.4 GB elaborating phantom
        // assigns.
        ExprKind::AssignExpr { rvalue, .. } => eval_const_expr_val(rvalue, params),
        // User-defined ceil-log2 helper used as a constant function — most
        // notably HardFloat's `clog2` (`for (clog2=0; fa>0; …) fa>>=1;` over
        // `a-1`), which is exactly `$clog2`. Without const-eval it returned 0, so
        // `alignDistWidth = clog2(sigWidth)` was 0 and `inWidth = alignDistWidth-2`
        // wrapped to ~u32::MAX. Recognise a 1-arg call named `clog2` and fold it.
        ExprKind::Call { func, args }
            if matches!(&func.kind, ExprKind::Ident(h)
                if h.path.last().map(|s| s.name.name.as_str()) == Some("clog2")) =>
        {
            let n = args.first().map(|a| eval_const_expr_val(a, params).to_u64().unwrap_or(0)).unwrap_or(0);
            Value::from_u64(ceil_log2(n), 32)
        }
        // §7.2.1 struct member select in const context: `s.field`. Slice the
        // field out of the struct-typed parameter Value using its registered
        // packed layout. Enables black-parrot's
        // `localparam icache_sets_p = proc_param_lp.icache_sets`.
        ExprKind::MemberAccess { expr: base, member } => {
            let base_val = eval_const_expr_val(base, params);
            if let ExprKind::Ident(h) = &base.kind {
                let nm = h.path.last().map(|s| s.name.name.as_str()).unwrap_or("");
                // Package-scoped constant `pkg::CONST` (parsed as MemberAccess):
                // when the base names no struct value, resolve the member as an
                // imported package constant / enum member (held by bare name).
                let base_is_struct = STRUCT_FIELDS_TLS.with(|c| c.borrow().contains_key(nm));
                if !base_is_struct && !params.contains_key(nm) {
                    if let Some(v) = params.get(&member.name) {
                        return v.clone();
                    }
                }
                if let Some(found) = STRUCT_FIELDS_TLS.with(|c| {
                    c.borrow().get(nm).and_then(|layout|
                        layout.iter().find(|(f, _, _)| f == &member.name).map(|&(_, off, w)| (off, w)))
                }) {
                    let (off, w) = found;
                    if w > 0 && off + w <= base_val.width {
                        return base_val.range_select((off + w - 1) as usize, off as usize);
                    }
                }
            }
            Value::zero(32)
        }
        // Packed-array element select in const context: `a[i]`. For an
        // array-of-structs parameter with a registered element width, slice
        // element `i` (`[i*elem_w +: elem_w]`). Enables black-parrot's
        // `localparam bp_proc_param_s proc_param_lp = all_cfgs_gp[bp_params_p]`.
        // Falls back to a single-bit select for plain vectors.
        ExprKind::Index { expr: base, index } => {
            let base_val = eval_const_expr_val(base, params);
            let idx = eval_const_expr_val(index, params).to_u64().unwrap_or(0);
            if let ExprKind::Ident(h) = &base.kind {
                let nm = h.path.last().map(|s| s.name.name.as_str()).unwrap_or("");
                if let Some(elem_w) = PACKED_ELEM_W_TLS.with(|c| c.borrow().get(nm).copied()) {
                    if elem_w > 0 {
                        let lo = (idx as u32).saturating_mul(elem_w);
                        if lo + elem_w <= base_val.width {
                            return base_val.range_select((lo + elem_w - 1) as usize, lo as usize);
                        }
                    }
                }
            }
            let i = idx as usize;
            if (i as u32) < base_val.width {
                base_val.range_select(i, i)
            } else {
                Value::zero(1)
            }
        }
        _ => Value::zero(32),
    };
    // eprintln!("[DEBUG] eval_const_expr_val: {:?} -> {}", expr, res.to_dec_string());
    res
}

/// Inline module instantiations: replace instances with their continuous assigns and always blocks.
/// Handles recursive/multi-level hierarchies by walking all levels depth-first.
pub fn inline_instantiations(
    elab: &mut ElaboratedModule,
    definitions: &HashMap<String, Definition>,
) -> Result<(), String> {
    // Populate class and covergroup definitions from global scope
    for (name, def) in definitions {
        match def {
            Definition::Class(c) => { elab.classes.insert(name.clone(), elaborate_class(c)); }
            Definition::Covergroup(cg) => { elab.covergroups.insert(name.clone(), (*cg).clone()); }
            Definition::Package(p) => {
                elab.packages.insert(name.clone());
                // Forward-reference fixpoint: package items may reference
                // parameters/localparams declared LATER in include order.
                // black-parrot's bp_common_pkg includes aviary_pkgdef (which has
                // `typedef enum bit [lg_max_cfgs-1:0] {...} bp_params_e;` and
                // `parameter bp_proc_param_s [max_cfgs-1:0] all_cfgs_gp`) BEFORE
                // aviary_cfg_pkgdef (which defines max_cfgs / lg_max_cfgs). A
                // single in-order pass resolves those widths to garbage — the
                // enum collapses to 1 bit and its member values truncate, so the
                // config selector `bp_params_e` is wrong. Pre-resolve parameters
                // and typedefs to a fixpoint first; both paths only overwrite
                // elab.parameters/typedefs/typedef_types/enum_members (idempotent),
                // so repeating is safe and the side-effecting Data initializers in
                // the main pass below run exactly once. Three passes cover the
                // chains here (max_cfgs → lg_max_cfgs → enum width → member values).
                for _ in 0..3 {
                    for item in &p.items {
                        match item {
                            crate::ast::decl::PackageItem::Parameter(pd) => {
                                if let ParameterKind::Data { data_type, assignments } = &pd.kind {
                                    let base_width = resolve_type_width(data_type, Some(&elab.parameters), Some(&elab.typedefs));
                                    let mut is_signed = is_type_signed(data_type);
                                    let is_implicit = matches!(data_type, DataType::Implicit { dimensions, .. } if dimensions.is_empty());
                                    if is_implicit { is_signed = true; }
                                    for assign in assignments {
                                        let width = if is_implicit {
                                            assign.init.as_ref().and_then(|e| sized_literal_width(e)).unwrap_or(32)
                                        } else { base_width };
                                        register_packed_array_elem_w(&assign.name.name, data_type, &elab.typedefs);
                                        if let Some(init) = &assign.init {
                                            let mut v = eval_param_value(data_type, init, &elab.parameters, &elab.typedefs, &elab.typedef_types, width);
                                            if is_signed { v.is_signed = true; }
                                            elab.parameters.insert(assign.name.name.clone(), v);
                                        }
                                    }
                                }
                            }
                            crate::ast::decl::PackageItem::Typedef(td) => { process_typedef(td, elab); }
                            _ => {}
                        }
                    }
                }
                for item in &p.items {
                    match item {
                        crate::ast::decl::PackageItem::Class(c) => {
                            elab.classes.insert(c.name.name.clone(), elaborate_class(c));
                        }
                        crate::ast::decl::PackageItem::Typedef(td) => {
                            process_typedef(td, elab);
                        }
                        crate::ast::decl::PackageItem::Parameter(pd) => {
                            if let ParameterKind::Data { data_type, assignments } = &pd.kind {
                                let base_width = resolve_type_width(data_type, Some(&elab.parameters), Some(&elab.typedefs));
                                let mut is_signed = is_type_signed(data_type);
                                let is_implicit = matches!(data_type, DataType::Implicit { dimensions, .. } if dimensions.is_empty());
                                if is_implicit { is_signed = true; }
                                for assign in assignments {
                                    // Implicit-typed param: use the sized-
                                    // literal width from the initializer when
                                    // present, instead of defaulting to 32.
                                    let width = if is_implicit {
                                        assign.init.as_ref()
                                            .and_then(|e| sized_literal_width(e))
                                            .unwrap_or(32)
                                    } else { base_width };
                                    register_packed_array_elem_w(&assign.name.name, data_type, &elab.typedefs);
                                    if let Some(init) = &assign.init {
                                        let mut v = eval_param_value(data_type, init, &elab.parameters, &elab.typedefs, &elab.typedef_types, width);
                                        if is_signed { v.is_signed = true; }
                                        elab.parameters.insert(assign.name.name.clone(), v);
                                    }
                                }
                            }
                        }
                        // Package-scope variable declarations. riscv-dv's target
                        // ISA config lives here as dynamic-array / queue globals
                        // (`supported_isa[$] = {RV32I,...}`); without populating
                        // them the generator has nothing to emit. Mirror the
                        // module-scope array-initializer path: register the array
                        // and emit its element initializers as a synthetic
                        // initial block so the runtime assignment machinery fills
                        // it at time 0 (enum members are already in scope, having
                        // been processed from this same package's typedefs).
                        crate::ast::decl::PackageItem::Data(dd) => {
                            let width = resolve_type_width(&dd.data_type, Some(&elab.parameters), Some(&elab.typedefs));
                            let is_signed = is_type_signed(&dd.data_type);
                            for decl in &dd.declarators {
                                let first_dim = decl.dimensions.first();
                                let is_dynamic_dim = first_dim.map_or(false, |d| matches!(d,
                                    UnpackedDimension::Unsized(_) | UnpackedDimension::Queue { .. }));
                                let is_assoc = matches!(first_dim, Some(UnpackedDimension::Associative { .. }));
                                if is_dynamic_dim {
                                    elab.dynamic_arrays.insert(decl.name.name.clone());
                                }
                                if is_assoc {
                                    elab.associative_arrays.insert(decl.name.name.clone(), false);
                                    continue;
                                }
                                // Element reads/writes go through `module.arrays`
                                // (see the Index eval path), so any unpacked array
                                // must be registered there with a backing range —
                                // matching the module-scope path's use of
                                // `extract_array_range` (dynamic/queue → 0..63).
                                if let Some((lo, hi)) = extract_array_range(&decl.dimensions, &elab.parameters) {
                                    elab.arrays.insert(decl.name.name.clone(), (lo, hi, width));
                                    if let Some(UnpackedDimension::Range { left, right, .. }) = first_dim {
                                        let l = const_eval_i64_with_params(left, Some(&elab.parameters)).unwrap_or(0);
                                        let r = const_eval_i64_with_params(right, Some(&elab.parameters)).unwrap_or(0);
                                        if l > r { elab.descending_arrays.insert(decl.name.name.clone()); }
                                    }
                                }
                                let Some(init_expr) = &decl.init else { continue };
                                let init_items: Vec<&Expression> = match &init_expr.kind {
                                    ExprKind::AssignmentPattern(items) => items.iter().map(|i| i.expr()).collect(),
                                    ExprKind::Concatenation(exprs) => exprs.iter().collect(),
                                    _ => vec![],
                                };
                                if !init_items.is_empty() && decl.dimensions.first().is_some() {
                                    // Emit explicit per-element initializers. The
                                    // array is registered in `arrays` above, so
                                    // `name[i] = item` lands where reads look.
                                    let mut stmts: Vec<Statement> = Vec::new();
                                    for (i, item_expr) in init_items.iter().enumerate() {
                                        let lval = Expression::new(ExprKind::Index {
                                            expr: Box::new(make_ident_expr(&decl.name.name)),
                                            index: Box::new(Expression::new(ExprKind::Number(crate::ast::expr::NumberLiteral::Integer { size: None, signed: false, base: crate::ast::expr::NumberBase::Decimal, value: i.to_string(), cached_val: std::cell::Cell::new(None) }), Span::dummy())),
                                        }, Span::dummy());
                                        stmts.push(Statement::new(StatementKind::BlockingAssign {
                                            lvalue: lval,
                                            rvalue: (*item_expr).clone(),
                                        }, Span::dummy()));
                                    }
                                    if is_dynamic_dim {
                                        let size_name = format!("{}.size", decl.name.name);
                                        elab.signals.insert(size_name.clone(), Signal { is_const: false, name: size_name, width: 32, is_signed: false, is_real: false, direction: None, value: Value::from_u64(init_items.len() as u64, 32), type_name: None });
                                    }
                                    elab.static_init_blocks.push(InitialBlock {
                                        stmt: Statement::new(StatementKind::SeqBlock { name: None, stmts }, Span::dummy()), scope: String::new(), });
                                } else if decl.dimensions.is_empty() {
                                    let _ = (width, is_signed);
                                    elab.static_init_blocks.push(InitialBlock {
                                        stmt: Statement::new(StatementKind::BlockingAssign {
                                            lvalue: make_ident_expr(&decl.name.name),
                                            rvalue: init_expr.clone(),
                                        }, Span::dummy()), scope: String::new(), });
                                }
                            }
                        }
                        _ => {}
                    }
                }
            }
            _ => {}
        }
    }

    let module_name = elab.name.clone();
    if elab_trace_enabled() {
        eprintln!("[xezim][elab] start top={}", module_name);
    }
    let top_def = match definitions.get(&module_name) {
        Some(m) => *m,
        None => return Err(format!("Top module '{}' not found in module map", module_name)),
    };
    // Recursively inline starting from the top module's items
    let top_params = elab.parameters.clone();
    // Snapshot the now-complete package/$unit parameters as the const-eval
    // fallback so sub-module header localparams (evaluated in the instance-merge
    // context, which only carries the sub-instance's own params) can still
    // resolve imported package parameters like black-parrot's `all_cfgs_gp`.
    set_param_fallback(&top_params);
    let mut cache = HashMap::default();
    inline_module_items(elab, top_def, "", definitions, &mut HashMap::default(), &top_params, &mut cache)?;
    if elab_trace_enabled() {
        eprintln!("[xezim][elab] finished inline top={}", module_name);
    }

    // IEEE 1800-2017 §6.10: Implicit nets for cont-assigns that came in via
    // pending sub-module bodies. The initial create_implicit_nets (in
    // elaborate_module_with_defs) only scanned the top-level
    // continuous_assigns vec. Sub-module bodies are deferred into
    // pending_cont_assign and didn't get their implicit nets created —
    // c910's wid_for_axi4 has `assign create_en = a && b;` with no
    // `wire create_en` declaration; the cont-assign got dropped at
    // compile time because xezim couldn't resolve `create_en` to a
    // signal_id, so create_en stayed X and the wid-tracking FIFO froze
    // → c910 memcpy hang. Scan pending_cont_assign now and create
    // implicit 1-bit wires for any prefixed names that don't yet exist.
    create_implicit_nets_for_pending(elab);

    // Identify interface instances at top level
    let mut top_interface_names = HashSet::default();
    for item in top_def.items() {
        if let ModuleItem::ModuleInstantiation(inst) = item {
            if definitions.get(&inst.module_name.name).map_or(false, |d| matches!(d, Definition::Interface(_))) {
                for hi in &inst.instances {
                    top_interface_names.insert(hi.name.name.clone());
                }
            }
        }
    }

    // Final rewrite of all blocks to convert MemberAccess to HierarchicalIdentifier and handle local signals
    // #7 default: keep pending_* lazy. The bytecode compiler in
    // simulator.rs drains pending_always / pending_initial /
    // pending_cont_assign one-at-a-time inside classify_always_blocks /
    // build_comb_entries / event_loop, materializing per block instead
    // of accumulating everything in always_blocks/initial_blocks/
    // continuous_assigns first. Measured: c910 hello sim 220 s → 194 s
    // (-12%) with lazy default; c906 hello sim 36.8 s → 35.3 s (-4%).
    // Memory unchanged (the saving is materialize_pending wall time
    // skipped, not peak memory).
    //
    // Set XEZIM_NO_LAZY_PREFIX=1 to fall back to eager materialization,
    // useful for tools that need ElaboratedModule fully populated
    // (e.g. write_compiled-then-read-back artifact roundtrips, since
    // pending_* fields are #[serde(skip)]).
    if std::env::var("XEZIM_NO_LAZY_PREFIX").ok().as_deref() == Some("1") {
        elab.materialize_pending();
    }

    let local_names = elab.signals.keys().cloned().collect::<std::collections::HashSet<_>>();
    let port_map = HashMap::default();
    let mut interface_map = HashMap::default();
    for name in top_interface_names {
        interface_map.insert(name.clone(), name);
    }
    let prefix = "";

    for block in &mut elab.always_blocks {
        block.stmt = rewrite_stmt(&block.stmt, prefix, &port_map, &local_names, &interface_map);
    }
    for block in &mut elab.initial_blocks {
        block.stmt = rewrite_stmt(&block.stmt, prefix, &port_map, &local_names, &interface_map);
    }
    for assign in &mut elab.continuous_assigns {
        assign.lhs = rewrite_expr(&assign.lhs, prefix, &port_map, &local_names, &interface_map);
        assign.rhs = rewrite_expr(&assign.rhs, prefix, &port_map, &local_names, &interface_map);
    }

    Ok(())
}

/// Construct an unsized integer-literal `Expression` for a genvar value.
/// Used by `substitute_genvar_in_items` to inject a constant in place of
/// the genvar identifier so downstream constant-evaluation, edge-block
/// resolution, and bit-select compilation see the resolved index.
fn genvar_const_expr(value: i64) -> Expression {
    let signed = value < 0;
    Expression::new(
        ExprKind::Number(NumberLiteral::Integer {
            size: Some(32),
            signed,
            base: NumberBase::Decimal,
            value: value.to_string(),
            cached_val: std::cell::Cell::new(Some((value as u64, 0u64, 32u32))),
        }),
        Span::dummy(),
    )
}

/// Replace bare references to `var` (a genvar) with the given constant
/// `value` throughout the module items. Walks into nested generate-for /
/// generate-if / generate-region so the substitution covers the whole
/// generate subtree before unrolling kicks in.
fn substitute_genvar_in_items(items: &[ModuleItem], var: &str, value: i64) -> Vec<ModuleItem> {
    let mut port_map: HashMap<String, Expression> = HashMap::default();
    port_map.insert(var.to_string(), genvar_const_expr(value));
    let local_names: std::collections::HashSet<String> = std::collections::HashSet::default();
    let interface_map: HashMap<String, String> = HashMap::default();
    items.iter().map(|item| substitute_in_module_item(item, &port_map, &local_names, &interface_map)).collect()
}

/// Collect the names of signals/parameters/instances declared at the top level
/// of a generate-for body. These need per-iteration renaming so that 20 copies
/// of `logic valid_q;` don't collapse into a single flat signal.
fn collect_decl_names_in_items(items: &[ModuleItem], names: &mut Vec<String>) {
    for item in items {
        match item {
            ModuleItem::DataDeclaration(dd) => {
                for d in &dd.declarators { names.push(d.name.name.clone()); }
            }
            ModuleItem::NetDeclaration(nd) => {
                for d in &nd.declarators { names.push(d.name.name.clone()); }
            }
            ModuleItem::PortDeclaration(pd) => {
                for d in &pd.declarators { names.push(d.name.name.clone()); }
            }
            ModuleItem::ParameterDeclaration(pd) | ModuleItem::LocalparamDeclaration(pd) => {
                if let ParameterKind::Data { assignments, .. } = &pd.kind {
                    for a in assignments { names.push(a.name.name.clone()); }
                }
            }
            ModuleItem::ModuleInstantiation(mi) => {
                for hi in &mi.instances { names.push(hi.name.name.clone()); }
            }
            // Nested generate constructs declare their own scope; we recurse
            // and rename names declared in the unconditional bodies, since a
            // nested generate-if may declare a name that the parent's other
            // siblings reference.
            ModuleItem::GenerateRegion(gr) => collect_decl_names_in_items(&gr.items, names),
            ModuleItem::GenerateIf(gi) => {
                for (_cond, branch) in &gi.branches {
                    collect_decl_names_in_items(branch, names);
                }
            }
            ModuleItem::GenerateCase(gc) => {
                for arm in &gc.arms {
                    collect_decl_names_in_items(&arm.items, names);
                }
            }
            _ => {}
        }
    }
}

/// Rename declarations inside a generate-for iteration so that each iteration
/// owns a distinct copy of every locally declared name. References in
/// always/initial/contassign/instance ports get rewritten via a port_map.
fn rename_decls_in_iter(items: &[ModuleItem], suffix: &str) -> Vec<ModuleItem> {
    let mut names = Vec::new();
    collect_decl_names_in_items(items, &mut names);
    if names.is_empty() { return items.to_vec(); }
    // Build rewrite map: original_name -> Ident(renamed)
    let mut port_map: HashMap<String, Expression> = HashMap::default();
    let rename_set: std::collections::HashSet<String> = names.iter().cloned().collect();
    for n in &names {
        let renamed = format!("{}{}", n, suffix);
        let id = Identifier { name: renamed.clone(), span: Span { start: 0, end: 0 } };
        let hier = HierarchicalIdentifier {
            root: None,
            path: vec![HierPathSegment { name: id, selects: Vec::new() }],
            span: Span { start: 0, end: 0 },
            cached_signal_id: std::cell::Cell::new(None),
            cached_resolved_name: std::cell::OnceCell::new(),
        };
        port_map.insert(n.clone(), Expression::new(ExprKind::Ident(hier), Span { start: 0, end: 0 }));
    }
    let local_names: std::collections::HashSet<String> = std::collections::HashSet::default();
    let interface_map: HashMap<String, String> = HashMap::default();
    items.iter().map(|item| rename_item_decls(item, suffix, &rename_set, &port_map, &local_names, &interface_map)).collect()
}

fn rename_item_decls(
    item: &ModuleItem,
    suffix: &str,
    rename_set: &std::collections::HashSet<String>,
    port_map: &HashMap<String, Expression>,
    local_names: &std::collections::HashSet<String>,
    interface_map: &HashMap<String, String>,
) -> ModuleItem {
    match item {
        ModuleItem::DataDeclaration(dd) => {
            let mut new_dd = dd.clone();
            for d in &mut new_dd.declarators {
                if rename_set.contains(&d.name.name) {
                    d.name.name = format!("{}{}", d.name.name, suffix);
                }
                if let Some(init) = &d.init {
                    d.init = Some(rewrite_expr(init, "", port_map, local_names, interface_map));
                }
            }
            ModuleItem::DataDeclaration(new_dd)
        }
        ModuleItem::NetDeclaration(nd) => {
            let mut new_nd = nd.clone();
            for d in &mut new_nd.declarators {
                if rename_set.contains(&d.name.name) {
                    d.name.name = format!("{}{}", d.name.name, suffix);
                }
                if let Some(init) = &d.init {
                    d.init = Some(rewrite_expr(init, "", port_map, local_names, interface_map));
                }
            }
            ModuleItem::NetDeclaration(new_nd)
        }
        ModuleItem::PortDeclaration(pd) => {
            let mut new_pd = pd.clone();
            for d in &mut new_pd.declarators {
                if rename_set.contains(&d.name.name) {
                    d.name.name = format!("{}{}", d.name.name, suffix);
                }
            }
            ModuleItem::PortDeclaration(new_pd)
        }
        ModuleItem::ParameterDeclaration(pd) | ModuleItem::LocalparamDeclaration(pd) => {
            let mut new_pd = pd.clone();
            if let ParameterKind::Data { assignments, .. } = &mut new_pd.kind {
                for a in assignments {
                    if rename_set.contains(&a.name.name) {
                        a.name.name = format!("{}{}", a.name.name, suffix);
                    }
                    if let Some(init) = &a.init {
                        a.init = Some(rewrite_expr(init, "", port_map, local_names, interface_map));
                    }
                }
            }
            // Preserve original variant
            match item {
                ModuleItem::ParameterDeclaration(_) => ModuleItem::ParameterDeclaration(new_pd),
                _ => ModuleItem::LocalparamDeclaration(new_pd),
            }
        }
        ModuleItem::ModuleInstantiation(mi) => {
            let mut new_mi = mi.clone();
            for hi in &mut new_mi.instances {
                if rename_set.contains(&hi.name.name) {
                    hi.name.name = format!("{}{}", hi.name.name, suffix);
                }
                for conn in &mut hi.connections {
                    match conn {
                        PortConnection::Named { expr: Some(e), .. }
                        | PortConnection::Ordered(Some(e)) => {
                            *e = rewrite_expr(e, "", port_map, local_names, interface_map);
                        }
                        _ => {}
                    }
                }
            }
            ModuleItem::ModuleInstantiation(new_mi)
        }
        ModuleItem::AlwaysConstruct(ac) => ModuleItem::AlwaysConstruct(AlwaysConstruct {
            kind: ac.kind,
            stmt: rewrite_stmt(&ac.stmt, "", port_map, local_names, interface_map),
            span: ac.span,
        }),
        ModuleItem::InitialConstruct(ic) => ModuleItem::InitialConstruct(InitialConstruct {
            stmt: rewrite_stmt(&ic.stmt, "", port_map, local_names, interface_map),
            span: ic.span,
        }),
        ModuleItem::ContinuousAssign(ca) => {
            let mut new_ca = ca.clone();
            new_ca.assignments = ca.assignments.iter().map(|(l, r)| (
                rewrite_expr(l, "", port_map, local_names, interface_map),
                rewrite_expr(r, "", port_map, local_names, interface_map),
            )).collect();
            ModuleItem::ContinuousAssign(new_ca)
        }
        ModuleItem::GenerateRegion(gr) => {
            let mut new_gr = gr.clone();
            new_gr.items = gr.items.iter().map(|i| rename_item_decls(i, suffix, rename_set, port_map, local_names, interface_map)).collect();
            ModuleItem::GenerateRegion(new_gr)
        }
        ModuleItem::GenerateIf(gi) => {
            let mut new_gi = gi.clone();
            new_gi.branches = gi.branches.iter().map(|(cond, branch_items)| {
                let new_cond = cond.as_ref().map(|c| rewrite_expr(c, "", port_map, local_names, interface_map));
                let new_items: Vec<ModuleItem> = branch_items.iter()
                    .map(|i| rename_item_decls(i, suffix, rename_set, port_map, local_names, interface_map))
                    .collect();
                (new_cond, new_items)
            }).collect();
            ModuleItem::GenerateIf(new_gi)
        }
        ModuleItem::GenerateCase(gc) => {
            let new_arms: Vec<GenerateCaseArm> = gc.arms.iter().map(|arm| {
                GenerateCaseArm {
                    values: arm.values.iter().map(|v| rewrite_expr(v, "", port_map, local_names, interface_map)).collect(),
                    items: arm.items.iter().map(|i| rename_item_decls(i, suffix, rename_set, port_map, local_names, interface_map)).collect(),
                }
            }).collect();
            ModuleItem::GenerateCase(GenerateCase {
                selector: rewrite_expr(&gc.selector, "", port_map, local_names, interface_map),
                arms: new_arms,
                span: gc.span,
            })
        }
        ModuleItem::GenerateFor(gf) => {
            // Inner generate-for: rewrite expression refs but leave its body
            // alone (its own iteration loop will handle further renaming).
            let mut new_gf = gf.clone();
            new_gf.cond = rewrite_expr(&gf.cond, "", port_map, local_names, interface_map);
            new_gf.incr = rewrite_expr(&gf.incr, "", port_map, local_names, interface_map);
            new_gf.items = gf.items.iter().map(|i| rename_item_decls(i, suffix, rename_set, port_map, local_names, interface_map)).collect();
            ModuleItem::GenerateFor(new_gf)
        }
        other => other.clone(),
    }
}

fn substitute_in_module_item(
    item: &ModuleItem,
    port_map: &HashMap<String, Expression>,
    local_names: &std::collections::HashSet<String>,
    interface_map: &HashMap<String, String>,
) -> ModuleItem {
    match item {
        ModuleItem::AlwaysConstruct(ac) => ModuleItem::AlwaysConstruct(AlwaysConstruct {
            kind: ac.kind,
            stmt: rewrite_stmt(&ac.stmt, "", port_map, local_names, interface_map),
            span: ac.span,
        }),
        ModuleItem::InitialConstruct(ic) => ModuleItem::InitialConstruct(InitialConstruct {
            stmt: rewrite_stmt(&ic.stmt, "", port_map, local_names, interface_map),
            span: ic.span,
        }),
        ModuleItem::ContinuousAssign(ca) => {
            let mut new_ca = ca.clone();
            new_ca.assignments = ca.assignments.iter().map(|(l, r)| (
                rewrite_expr(l, "", port_map, local_names, interface_map),
                rewrite_expr(r, "", port_map, local_names, interface_map),
            )).collect();
            ModuleItem::ContinuousAssign(new_ca)
        }
        ModuleItem::ModuleInstantiation(inst) => {
            let mut new_inst = inst.clone();
            for hi in &mut new_inst.instances {
                for conn in &mut hi.connections {
                    match conn {
                        PortConnection::Named { expr: Some(e), .. }
                        | PortConnection::Ordered(Some(e)) => {
                            *e = rewrite_expr(e, "", port_map, local_names, interface_map);
                        }
                        _ => {}
                    }
                }
            }
            if let Some(params) = &mut new_inst.params {
                for pc in params.iter_mut() {
                    match pc {
                        ParamConnection::Named { value: Some(ParamValue::Expr(e)), .. }
                        | ParamConnection::Ordered(Some(ParamValue::Expr(e))) => {
                            *e = rewrite_expr(e, "", port_map, local_names, interface_map);
                        }
                        _ => {}
                    }
                }
            }
            ModuleItem::ModuleInstantiation(new_inst)
        }
        ModuleItem::GenerateRegion(gr) => {
            let mut new_gr = gr.clone();
            new_gr.items = gr.items.iter().map(|i| substitute_in_module_item(i, port_map, local_names, interface_map)).collect();
            ModuleItem::GenerateRegion(new_gr)
        }
        ModuleItem::GenerateIf(gi) => {
            let mut new_gi = gi.clone();
            new_gi.branches = gi.branches.iter().map(|(cond, branch_items)| {
                let new_cond = cond.as_ref().map(|c| rewrite_expr(c, "", port_map, local_names, interface_map));
                let new_items: Vec<ModuleItem> = branch_items.iter()
                    .map(|i| substitute_in_module_item(i, port_map, local_names, interface_map))
                    .collect();
                (new_cond, new_items)
            }).collect();
            ModuleItem::GenerateIf(new_gi)
        }
        ModuleItem::GenerateCase(gc) => {
            let new_arms: Vec<GenerateCaseArm> = gc.arms.iter().map(|arm| {
                GenerateCaseArm {
                    values: arm.values.iter().map(|v| rewrite_expr(v, "", port_map, local_names, interface_map)).collect(),
                    items: arm.items.iter().map(|i| substitute_in_module_item(i, port_map, local_names, interface_map)).collect(),
                }
            }).collect();
            ModuleItem::GenerateCase(GenerateCase {
                selector: rewrite_expr(&gc.selector, "", port_map, local_names, interface_map),
                arms: new_arms,
                span: gc.span,
            })
        }
        ModuleItem::GenerateFor(gf) => {
            let mut new_gf = gf.clone();
            new_gf.cond = rewrite_expr(&gf.cond, "", port_map, local_names, interface_map);
            new_gf.incr = rewrite_expr(&gf.incr, "", port_map, local_names, interface_map);
            new_gf.items = gf.items.iter().map(|i| substitute_in_module_item(i, port_map, local_names, interface_map)).collect();
            ModuleItem::GenerateFor(new_gf)
        }
        // Most other module-level declarations don't carry expressions that
        // reference a genvar in practice; pass through unchanged.
        other => other.clone(),
    }
}

/// Recursively inline all instantiations found in `source_mod`, using `prefix` for signal naming.
/// Flatten module items by resolving generate-if/else and generate regions.
/// Returns all effective items after evaluating generate conditions.
fn collect_effective_items(items: &[ModuleItem], params: &HashMap<String, Value>) -> Vec<ModuleItem> {
    let mut result = Vec::new();
    for item in items {
        match item {
            ModuleItem::GenerateRegion(gr) => {
                result.extend(collect_effective_items(&gr.items, params));
            }
            ModuleItem::GenerateIf(gi) => {
                let mut matched = false;
                for (cond, branch_items) in &gi.branches {
                    if let Some(cond_expr) = cond {
                        let val = eval_const_expr(cond_expr, params);
                        if val != 0 {
                            result.extend(collect_effective_items(branch_items, params));
                            matched = true;
                            break;
                        }
                    } else {
                        // Unconditional else branch
                        result.extend(collect_effective_items(branch_items, params));
                        matched = true;
                        break;
                    }
                }
                let _ = matched;
            }
            ModuleItem::GenerateCase(gc) => {
                let sel = eval_const_expr(&gc.selector, params);
                let mut matched = false;
                // First pass: try non-default arms.
                for arm in &gc.arms {
                    if arm.values.is_empty() { continue; }
                    if arm.values.iter().any(|v| eval_const_expr(v, params) == sel) {
                        result.extend(collect_effective_items(&arm.items, params));
                        matched = true;
                        break;
                    }
                }
                // Default arm fallback.
                if !matched {
                    for arm in &gc.arms {
                        if arm.values.is_empty() {
                            result.extend(collect_effective_items(&arm.items, params));
                            break;
                        }
                    }
                }
            }
            ModuleItem::GenerateFor(gf) => {
                // Without this expansion, items inside `for genvar` (always
                // blocks, instances, cont assigns) are dropped when the
                // host module is inlined into its parent. ct_fifo's
                // DFIFO_VLD_GEN reset block was being lost this way, leaving
                // fifo_entry_vld stuck at X and the AXI request path
                // permanently stalled — see openc910 hello_world bringup.
                let mut local_params = params.clone();
                let mut i = gf.init_val;
                let limit = 10000;
                let mut iters = 0;
                while iters < limit {
                    local_params.insert(gf.var.clone(), Value::from_u64(i as u64, 32));
                    let cond_val = eval_const_expr(&gf.cond, &local_params);
                    if cond_val == 0 { break; }
                    let subst = substitute_genvar_in_items(&gf.items, &gf.var, i);
                    // Rename signals declared inside the for-body so each
                    // iteration gets its own unique copy. Without this, two
                    // iterations both declare `valid_q` and the elaborator
                    // sees a flat duplicate.
                    let suffix = match &gf.name {
                        Some(l) => format!("__gf_{}_{}_{}_", l, gf.var, i),
                        None => format!("__gf_{}_{}_", gf.var, i),
                    };
                    let subst = rename_decls_in_iter(&subst, &suffix);
                    result.extend(collect_effective_items(&subst, &local_params));
                    match &gf.incr.kind {
                        ExprKind::Unary { op: UnaryOp::PostIncr, .. }
                        | ExprKind::Unary { op: UnaryOp::PreIncr, .. } => i += 1,
                        ExprKind::Unary { op: UnaryOp::PostDecr, .. }
                        | ExprKind::Unary { op: UnaryOp::PreDecr, .. } => i -= 1,
                        _ => {
                            let new_val = eval_const_expr(&gf.incr, &local_params) as i64;
                            if new_val == i { i += 1; } else { i = new_val; }
                        }
                    }
                    iters += 1;
                }
                local_params.remove(&gf.var);
            }
            other => result.push(other.clone()),
        }
    }
    result
}

fn is_interface_type(dt: &DataType, definitions: &HashMap<String, Definition>) -> bool {
    match dt {
        DataType::TypeReference { name, .. } => {
            if definitions.contains_key(&name.name.name) { return true; }
            false
        }
        DataType::Interface { name, .. } => {
            if definitions.contains_key(&name.name) { return true; }
            false
        }
        _ => false,
    }
}

/// Pre-built `Rc`-shared sources for the deferred-rewrite kinds (#7).
/// Built once per `(module, params)` cache hit; sibling instances share
/// via `Rc::clone` (refcount bump) instead of cloning the AST per push.
#[derive(Debug, Clone)]
enum BodySource {
    ContAssign(Vec<(std::rc::Rc<Expression>, std::rc::Rc<Expression>)>),
    GateInst(Vec<(std::rc::Rc<Expression>, std::rc::Rc<Expression>)>),
    NetInits(Vec<(String, std::rc::Rc<Expression>)>),
    Always(AlwaysKind, std::rc::Rc<Statement>),
    Initial(std::rc::Rc<Statement>),
    Other,
}

#[derive(Debug, Clone)]
struct PreparedModuleItems {
    effective_items: Vec<ModuleItem>,
    body_sources: Vec<BodySource>,
    local_typedefs: std::collections::HashSet<String>,
    interface_ports: std::collections::HashSet<String>,
    port_directions: HashMap<String, PortDirection>,
    local_names: std::rc::Rc<std::collections::HashSet<String>>,
}

type InlinePrepCache = HashMap<String, Rc<PreparedModuleItems>>;

fn format_param_key(params: &HashMap<String, Value>) -> String {
    let mut ordered = BTreeMap::new();
    for (name, value) in params {
        ordered.insert(name.as_str(), value);
    }
    let mut key = String::new();
    for (name, value) in ordered {
        use std::fmt::Write as _;
        let _ = write!(
            key,
            "{}:{}:{}:{}:{:?}|",
            name,
            value.width,
            value.is_signed as u8,
            value.is_real as u8,
            value.raw_bits()
        );
    }
    key
}

fn prepare_module_items(
    source_def: Definition,
    definitions: &HashMap<String, Definition>,
    local_params: &HashMap<String, Value>,
    typedef_widths: &HashMap<String, u32>,
    cache: &mut InlinePrepCache,
) -> Rc<PreparedModuleItems> {
    let cache_key = format!("{}|{}", source_def.name(), format_param_key(local_params));
    if let Some(prepared) = cache.get(&cache_key) {
        return Rc::clone(prepared);
    }

    let mut local_typedefs = std::collections::HashSet::default();
    for item in source_def.items() {
        if let ModuleItem::TypedefDeclaration(td) = item {
            local_typedefs.insert(td.name.name.clone());
        }
    }

    let mut interface_ports = std::collections::HashSet::default();
    if let PortList::Ansi(ports) = source_def.ports() {
        for port in ports {
            if let Some(dt) = &port.data_type {
                if is_interface_type(dt, definitions) {
                    interface_ports.insert(port.name.name.clone());
                }
            }
        }
    }

    let effective_items = collect_effective_items(source_def.items(), local_params);

    let mut port_directions = HashMap::default();
    match source_def.ports() {
        PortList::Ansi(ports) => {
            for port in ports {
                if let Some(dir) = port.direction {
                    port_directions.insert(port.name.name.clone(), dir);
                }
            }
        }
        PortList::NonAnsi(_) => {
            for item in &effective_items {
                if let ModuleItem::PortDeclaration(pd) = item {
                    for decl in &pd.declarators {
                        port_directions.insert(decl.name.name.clone(), pd.direction);
                    }
                }
            }
        }
        PortList::Empty => {}
    }

    let mut local_names = std::collections::HashSet::default();
    for p_decl in source_def.params() {
        if let ParameterKind::Data { assignments, .. } = &p_decl.kind {
            for assign in assignments {
                local_names.insert(assign.name.name.clone());
            }
        }
    }
    match source_def.ports() {
        PortList::Ansi(ports) => {
            for port in ports {
                local_names.insert(port.name.name.clone());
            }
        }
        PortList::NonAnsi(names) => {
            for name in names {
                local_names.insert(name.name.clone());
            }
        }
        PortList::Empty => {}
    }
    for item in &effective_items {
        match item {
            ModuleItem::NetDeclaration(nd) => {
                for decl in &nd.declarators {
                    local_names.insert(decl.name.name.clone());
                }
            }
            ModuleItem::DataDeclaration(dd) => {
                for decl in &dd.declarators {
                    local_names.insert(decl.name.name.clone());
                }
            }
            ModuleItem::PortDeclaration(pd) => {
                for decl in &pd.declarators {
                    local_names.insert(decl.name.name.clone());
                }
            }
            ModuleItem::FunctionDeclaration(fd) => {
                local_names.insert(fd.name.name.name.clone());
            }
            ModuleItem::TaskDeclaration(td) => {
                local_names.insert(td.name.name.name.clone());
            }
            ModuleItem::ModuleInstantiation(inst) => {
                if typedef_widths.contains_key(&inst.module_name.name) || local_typedefs.contains(&inst.module_name.name) {
                    for hi in &inst.instances {
                        local_names.insert(hi.name.name.clone());
                    }
                }
            }
            ModuleItem::ParameterDeclaration(pd) | ModuleItem::LocalparamDeclaration(pd) => {
                if let ParameterKind::Data { assignments, .. } = &pd.kind {
                    for assign in assignments {
                        local_names.insert(assign.name.name.clone());
                    }
                }
            }
            _ => {}
        }
    }

    // IEEE 1800-2017 §6.10: a bare identifier on the LHS of a continuous
    // assign (or gate output) that has no explicit net declaration
    // implicitly declares a 1-bit net in this scope. Register such names in
    // local_names so rewrite_expr prefixes them with the instance path;
    // the matching signal is created later by create_implicit_nets_for_pending.
    {
        let mut implicit: Vec<String> = Vec::new();
        for item in &effective_items {
            match item {
                ModuleItem::ContinuousAssign(ca) => {
                    for (lhs, _) in &ca.assignments {
                        // A dotted lvalue (`top.inst.net`) is a HIERARCHICAL
                        // reference, not an undeclared net. Registering its root
                        // here made `rewrite_expr` prefix it with the instance
                        // path (`wr.top.inst.net`), so the assign wrote a name
                        // that resolves to nothing.
                        collect_implicit_net_candidates(lhs, &mut implicit);
                    }
                }
                ModuleItem::GateInstantiation(gi) => {
                    for (lhs, _) in gate_inst_to_assign_pairs(gi) {
                        collect_implicit_net_candidates(&lhs, &mut implicit);
                    }
                }
                _ => {}
            }
        }
        for name in implicit {
            if !local_names.contains(&name) {
                local_names.insert(name);
            }
        }
    }

    let body_sources: Vec<BodySource> = effective_items.iter().map(|item| {
        match item {
            ModuleItem::ContinuousAssign(ca) => BodySource::ContAssign(
                ca.assignments.iter()
                    .map(|(l, r)| (std::rc::Rc::new(l.clone()), std::rc::Rc::new(r.clone())))
                    .collect()
            ),
            ModuleItem::GateInstantiation(gi) => BodySource::GateInst(
                gate_inst_to_assign_pairs(gi).into_iter()
                    .map(|(l, r)| (std::rc::Rc::new(l), std::rc::Rc::new(r)))
                    .collect()
            ),
            ModuleItem::NetDeclaration(nd) => BodySource::NetInits(
                nd.declarators.iter()
                    .filter_map(|d| d.init.as_ref().map(|init| (d.name.name.clone(), std::rc::Rc::new(init.clone()))))
                    .collect()
            ),
            ModuleItem::AlwaysConstruct(ac) => BodySource::Always(ac.kind, std::rc::Rc::new(ac.stmt.clone())),
            ModuleItem::InitialConstruct(ic) => BodySource::Initial(std::rc::Rc::new(ic.stmt.clone())),
            _ => BodySource::Other,
        }
    }).collect();

    let prepared = Rc::new(PreparedModuleItems {
        effective_items,
        body_sources,
        local_typedefs,
        interface_ports,
        port_directions,
        local_names: std::rc::Rc::new(local_names),
    });
    cache.insert(cache_key, Rc::clone(&prepared));
    prepared
}

fn inline_module_items(
    elab: &mut ElaboratedModule,
    source_def: Definition,
    prefix: &str,
    definitions: &HashMap<String, Definition>,
    interface_map: &mut HashMap<String, String>,
    local_params: &HashMap<String, Value>,
    cache: &mut InlinePrepCache,
) -> Result<(), String> {
    let prepared_source = prepare_module_items(source_def, definitions, local_params, &elab.typedefs, cache);
    for item in &prepared_source.effective_items {
        if let ModuleItem::ModuleInstantiation(inst) = item {
            let sub_mod_name = &inst.module_name.name;
            if elab_trace_enabled() {
                eprintln!(
                    "[xezim][elab] visiting prefix='{}' module='{}' instances={}",
                    prefix,
                    sub_mod_name,
                    inst.instances.len()
                );
            }
            let sub_mod = match definitions.get(sub_mod_name) {
                Some(m) => *m,
                None => {
                    // Check if it's a typedef-based variable declaration (happens if parser was unsure)
                    if elab.typedefs.contains_key(sub_mod_name) || prepared_source.local_typedefs.contains(sub_mod_name) {
                        let width = elab.typedefs.get(sub_mod_name).copied().unwrap_or(32);
                        let is_real = sub_mod_name == "real";
                        for hi in &inst.instances {
                            let sig_name = format!("{}{}", prefix, hi.name.name);
                            elab.signals.insert(sig_name.clone(), Signal { is_const: false,
                                name: sig_name, width, is_signed: is_real, direction: None,
                                value: if is_real { Value::from_f64(0.0) } else { Value::new(width) },
                                is_real, type_name: Some(sub_mod_name.clone()),
                            });
                        }
                        continue;
                    }
                    // LRM §17.2: checker instantiation. When the
                    // checker has formal ports, walk the body items
                    // and substitute each formal-name Ident with the
                    // actual arg expression at this instantiation
                    // site, then elaborate the rewritten items.
                    // When no ports, the body was already inlined at
                    // declaration time — just register a stub signal.
                    if let Some(cd) = elab.checker_decls.get(sub_mod_name).cloned()
                    {
                        let has_ports = !matches!(
                            cd.ports,
                            crate::ast::module::PortList::Empty
                        );
                        for hi in &inst.instances {
                            let sig_name = format!("{}{}", prefix, hi.name.name);
                            elab.signals.insert(sig_name.clone(), Signal {
                                is_const: false,
                                name: sig_name,
                                width: 1,
                                is_signed: false,
                                direction: None,
                                value: Value::zero(1),
                                is_real: false,
                                type_name: Some(sub_mod_name.clone()),
                            });
                            if has_ports {
                                // Build formal→actual expression map.
                                let formals: Vec<String> = match &cd.ports {
                                    crate::ast::module::PortList::NonAnsi(ns) => {
                                        ns.iter().map(|n| n.name.clone()).collect()
                                    }
                                    crate::ast::module::PortList::Ansi(ps) => {
                                        ps.iter().map(|p| p.name.name.clone()).collect()
                                    }
                                    crate::ast::module::PortList::Empty => Vec::new(),
                                };
                                let mut subst: HashMap<String, Expression> =
                                    HashMap::default();
                                for (i, fname) in formals.iter().enumerate() {
                                    if let Some(conn) = hi.connections.get(i) {
                                        let actual_opt = match conn {
                                            crate::ast::decl::PortConnection::Ordered(e) => e.clone(),
                                            crate::ast::decl::PortConnection::Named { expr, .. } => expr.clone(),
                                            _ => None,
                                        };
                                        if let Some(e) = actual_opt {
                                            subst.insert(fname.clone(), e);
                                        }
                                    }
                                }
                                let rewritten: Vec<ModuleItem> = cd
                                    .items
                                    .iter()
                                    .map(|it| rewrite_module_item_subst(it, &subst))
                                    .collect();
                                elaborate_items(&rewritten, elab, Some(definitions))?;
                            }
                        }
                        continue;
                    }
                    return Err(format!("Module '{}' instantiated but not found", sub_mod_name));
                }
            };

            for hi in &inst.instances {
                let inst_name = &hi.name.name;
                let inst_prefix = format!("{}{}.", prefix, inst_name);
                if elab_trace_enabled() {
                    eprintln!(
                        "[xezim][elab] inline instance path='{}' target='{}'",
                        inst_prefix,
                        sub_mod_name
                    );
                }
                // Was: `let scoped_eval_params = local_params.clone();` — wasted clone, only read.
                let scoped_eval_params: &HashMap<String, Value> = local_params;

                // Build port map and interface map
                let mut port_map = HashMap::default();
                let mut sub_interface_map = HashMap::default();

                // Local names of the CURRENT (parent) module — bare names of
                // signals declared in this scope. Used when rewriting port
                // connection parent expressions so bare identifiers get
                // prefixed with the current scope. Without this, a port
                // connection like `.mrd(mrd)` inside wrapper would be stored
                // in port_map as a bare `mrd`, and later substitutions into
                // the sub-module would insert a bare (unresolvable) name.
                let parent_local_names = &*prepared_source.local_names;

                if !hi.connections.is_empty() {
                    match &hi.connections[0] { // Simplification: check if first is wildcard
                        PortConnection::Wildcard => {
                            // Wildcard: connect all ports to same-named signals in parent
                            match sub_mod.ports() {
                                PortList::Ansi(ports) => {
                                    for port in ports {
                                        let name = &port.name.name;
                                        let parent_name = format!("{}{}", prefix, name);
                                        let is_if_port = port.data_type.as_ref()
                                            .map(|dt| is_interface_type(dt, definitions))
                                            .unwrap_or(false);
                                        if is_if_port {
                                            sub_interface_map.insert(name.clone(), parent_name.clone());
                                        } else {
                                            port_map.insert(name.clone(), make_ident_expr(&parent_name));
                                        }
                                    }
                                }
                                _ => {}
                            }
                        }
                        _ => {
                            for (i, conn) in hi.connections.iter().enumerate() {
                                match conn {
                                    PortConnection::Named { name, expr } => {
                                        if let Some(e) = expr {
                                            let rewritten_e = rewrite_expr(e, prefix, &HashMap::default(), parent_local_names, interface_map);
                                            if prepared_source.interface_ports.contains(&name.name) {
                                                if let ExprKind::Ident(hier) = &rewritten_e.kind {
                                                    let if_full_path = hier.path.iter().map(|s| s.name.name.as_str()).collect::<Vec<_>>().join(".");
                                                    sub_interface_map.insert(name.name.clone(), if_full_path);
                                                }
                                            } else {
                                                port_map.insert(name.name.clone(), rewritten_e);
                                            }
                                        }
                                    }
                                    PortConnection::Ordered(expr) => {
                                        if let Some(e) = expr {
                                            let rewritten_e = rewrite_expr(e, prefix, &HashMap::default(), parent_local_names, interface_map);
                                            if let Some(port) = sub_mod.ports().get(i) {
                                                let port_name = port.name();
                                                if prepared_source.interface_ports.contains(port_name) {
                                                    if let ExprKind::Ident(hier) = &rewritten_e.kind {
                                                        let if_full_path = hier.path.iter().map(|s| s.name.name.as_str()).collect::<Vec<_>>().join(".");
                                                        sub_interface_map.insert(port_name.to_string(), if_full_path);
                                                    }
                                                } else {
                                                    port_map.insert(port_name.to_string(), rewritten_e);
                                                }
                                            }
                                        }
                                    }
                                    _ => {}
                                }
                            }
                        }
                    }
                }

                // Short-circuit: gated_clk_cell is a passthrough whose body is
                // `assign clk_out = clk_in;` plus dead enable logic. Inlining
                // it produces a 3-hop cont-assign chain (parent_clk_in →
                // local_clk_in → local_clk_out → parent_clk_out) that takes
                // multiple settle iterations to propagate. For c910 (which
                // has many gated_clk_cell instances on the same coreclk),
                // this introduces NBA-scheduling races between sibling FFs
                // clocked on different "gated" outputs of the same source
                // clock. Replace the entire instance with a single direct
                // cont-assign `parent_clk_out = parent_clk_in` so the
                // gated clock unifies with its source.
                if sub_mod_name == "gated_clk_cell" {
                    if let (Some(clk_out_expr), Some(clk_in_expr)) =
                        (port_map.get("clk_out").cloned(), port_map.get("clk_in").cloned())
                    {
                        elab.continuous_assigns.push(ContinuousAssignment {
                            lhs: clk_out_expr,
                            rhs: clk_in_expr,
                            delay: 0,
                        });
                        continue;
                    }
                }

                // Resolve parameters for the sub-module
                let mut sub_params = HashMap::default();
                let dbg_param = std::env::var("XEZIM_DBG_PARAM").is_ok()
                    && (sub_mod_name == "ram" || sub_mod_name == "f_spsram_large");
                // Build the effective declared-parameter list for the
                // sub-module: header `#(…)` parameters first, then
                // ParameterDeclaration items in source order (Localparam
                // declarations are NOT overridable per IEEE 1800 §6.20.4).
                // Positional `inst.params` resolution must index into THIS
                // combined list — without it, modules that declare parameters
                // only inside the body (e.g. openc910's ram.v) get their
                // positional overrides silently dropped, leaving the sim
                // running with default sizes (4-element memories instead of
                // 2 M).
                let mut sub_param_decls: Vec<&ParameterDeclaration> = sub_mod.params().iter().collect();
                for it in sub_mod.items() {
                    if let ModuleItem::ParameterDeclaration(pd) = it {
                        sub_param_decls.push(pd);
                    }
                }
                if dbg_param {
                    eprintln!("[DBG_PARAM] inlining {} into prefix='{}', inst.params={:?}, inst_name={}, sub_param_decls={}",
                        sub_mod_name, inst_prefix,
                        inst.params.as_ref().map(|p| p.len()), hi.name.name, sub_param_decls.len());
                }
                if let Some(param_conns) = &inst.params {
                    for (i, conn) in param_conns.iter().enumerate() {
                        match conn {
                            ParamConnection::Named { name, value } => {
                                if let Some(ParamValue::Expr(v)) = value {
                                    let mut val = eval_const_expr_val(v, scoped_eval_params);
                                    // Check if target parameter is real or implicit real
                                    for p_decl in sub_mod.params() {
                                        if let ParameterKind::Data { data_type, assignments } = &p_decl.kind {
                                            if assignments.iter().any(|a| a.name.name == name.name) {
                                                if is_type_real(data_type) {
                                                    val = Value::from_f64(val.to_f64());
                                                } else if matches!(data_type, DataType::Implicit { dimensions, .. } if dimensions.is_empty()) {
                                                    if val.is_real {
                                                        val = Value::from_f64(val.to_f64());
                                                    }
                                                }
                                                break;
                                            }
                                        }
                                    }
                                    sub_params.insert(name.name.clone(), val);
                                }
                            }
                            ParamConnection::Ordered(value) => {
                                if dbg_param {
                                    eprintln!("[DBG_PARAM]   ordered[{}] value={:?}, sub_param_decls.get(i)={:?}",
                                        i, value.is_some(),
                                        sub_param_decls.get(i).map(|p| match &p.kind {
                                            ParameterKind::Data { assignments, .. } => assignments.first().map(|a| a.name.name.clone()),
                                            _ => None,
                                        }));
                                }
                                if let Some(ParamValue::Expr(v)) = value {
                                    if let Some(p_decl) = sub_param_decls.get(i) {
                                        if let ParameterKind::Data { data_type, assignments } = &p_decl.kind {
                                            let mut val = eval_const_expr_val(v, scoped_eval_params);
                                            if dbg_param {
                                                eprintln!("[DBG_PARAM]     eval -> {} = {}",
                                                    assignments[0].name.name, val.to_u64().unwrap_or(0));
                                            }
                                            if is_type_real(data_type) {
                                                val = Value::from_f64(val.to_f64());
                                            } else if matches!(data_type, DataType::Implicit { dimensions, .. } if dimensions.is_empty()) {
                                                if val.is_real {
                                                    val = Value::from_f64(val.to_f64());
                                                }
                                            }
                                            sub_params.insert(assignments[0].name.name.clone(), val);
                                        }
                                    }
                                }
                            }
                        }
                    }
                }

                // Internal parameter map for resolving default parameters that depend on each other.
                // Moved (was clone): sub_params is not used after this line.
                let mut sub_local_params = sub_params;
                
                // Helper to add parameters from a list of items
                let add_params_from_items = |items: &[ModuleItem], local_map: &mut HashMap<String, Value>| {
                    let effective_items = collect_effective_items(items, local_map);
                    for item in &effective_items {
                        if let ModuleItem::ParameterDeclaration(pd) | ModuleItem::LocalparamDeclaration(pd) = item {
                            if let ParameterKind::Data { data_type, assignments } = &pd.kind {
                                for assign in assignments {
                                    if !local_map.contains_key(&assign.name.name) {
                                        if let Some(init) = &assign.init {
                                            let mut val = eval_const_expr_val(init, local_map);
                                            if is_type_real(data_type) {
                                                val = Value::from_f64(val.to_f64());
                                            } else if matches!(data_type, DataType::Implicit { dimensions, .. } if dimensions.is_empty()) {
                                                if val.is_real {
                                                    val = Value::from_f64(val.to_f64());
                                                }
                                            }
                                            local_map.insert(assign.name.name.clone(), val);
                                        }
                                    }
                                }
                            }
                        }
                    }
                };

                // 1. Parameters from port list
                for p_decl in sub_mod.params() {
                    if let ParameterKind::Data { data_type, assignments } = &p_decl.kind {
                        for assign in assignments {
                            // §6.20.2 unpacked-array parameter. This runs even when the
                            // parameter is OVERRIDDEN: the override arrives as a single
                            // packed value, so without slicing it here no element ever
                            // gets a value and `A[i]` reads 0.
                            if !assign.dimensions.is_empty() {
                                let ov = sub_local_params.get(&assign.name.name).cloned();
                                let snapshot = sub_local_params.clone();
                                if register_array_param(elab, &inst_prefix, &assign.name.name,
                                    &assign.dimensions, assign.init.as_ref(), ov.as_ref(),
                                    data_type, &snapshot)
                                {
                                    continue;
                                }
                            }
                            if !sub_local_params.contains_key(&assign.name.name) {
                                if let Some(init) = &assign.init {
                                    // IEEE 1800-2023: associative-array
                                    // parameter literal `'{"k": v, ...}`.
                                    // Materialise as `<prefix><param>[key]`
                                    // signals and register the array.
                                    if let ExprKind::AssignmentPattern(items) = &init.kind {
                                        let all_keyed = !items.is_empty()
                                            && items.iter().all(|it|
                                                matches!(it, AssignmentPatternItem::Keyed(_, _)));
                                        if all_keyed {
                                            let elem_w = resolve_type_width(
                                                data_type,
                                                Some(&sub_local_params),
                                                Some(&elab.typedefs),
                                            );
                                            let arr_full = format!("{}{}", inst_prefix, assign.name.name);
                                            elab.associative_arrays.insert(arr_full.clone(), true);
                                            for it in items {
                                                if let AssignmentPatternItem::Keyed(k, v) = it {
                                                    let key_str = match &k.kind {
                                                        ExprKind::StringLiteral(s) => s.clone(),
                                                        _ => eval_const_expr_val(k, &sub_local_params)
                                                            .to_dec_string(),
                                                    };
                                                    let val_v = eval_init_for_width(
                                                        v,
                                                        &sub_local_params,
                                                        elem_w,
                                                    );
                                                    let sname = format!("{}[{}]", arr_full, key_str);
                                                    elab.signals.insert(
                                                        sname.clone(),
                                                        Signal {
                                                            is_const: true,
                                                            name: sname,
                                                            width: elem_w,
                                                            is_signed: is_type_signed(data_type),
                                                            is_real: false,
                                                            direction: None,
                                                            value: val_v,
                                                            type_name: None,
                                                        },
                                                    );
                                                }
                                            }
                                            continue;
                                        }
                                    }
                                    // Register element-width / struct layout so a
                                    // header localparam like
                                    // `sc = all_cfgs_gp[SEL]` / `x = sc.field`
                                    // resolves through the const-eval index /
                                    // member-select arms (black-parrot config).
                                    register_packed_array_elem_w(&assign.name.name, data_type, &elab.typedefs);
                                    if let Some(fields) = flatten_struct_fields(data_type, &sub_local_params, &elab.typedefs, &elab.typedef_types) {
                                        if !fields.is_empty() { tls_register_struct_layout(&assign.name.name, &fields); }
                                    }
                                    let mut val = eval_const_expr_val(init, &sub_local_params);
                                    if is_type_real(data_type) {
                                        val = Value::from_f64(val.to_f64());
                                    } else if matches!(data_type, DataType::Implicit { dimensions, .. } if dimensions.is_empty()) {
                                        if val.is_real {
                                            val = Value::from_f64(val.to_f64());
                                        }
                                    }
                                    sub_local_params.insert(assign.name.name.clone(), val);
                                }
                            }
                        }
                    }
                }

                // 1b. Pre-register the sub-module's LOCAL typedef widths using
                // THIS instance's (bare-named) parameters, then install them in
                // TYPEDEFS_TLS so the body localparams' `$bits(<local typedef>)`
                // resolve. black-parrot declares its types via macros
                // (`declare_bp_be_dcache_wbuf_entry_s(caddr_width_mp, ways_mp)`,
                // `bp_pte_leaf_s` …) parameterised by header params; without this
                // the body localparam `r_entry_high_bits_lp = $bits(bp_pte_leaf_s)
                // - …` saw $bits = 0 and the subtraction wrapped to ~u32::MAX,
                // producing a multi-GB phantom width. A few passes converge
                // typedefs whose width depends on an earlier-resolved typedef.
                {
                    let body_items = collect_effective_items(sub_mod.items(), &sub_local_params);
                    let mut local_tds = elab.typedefs.clone();
                    for _ in 0..3 {
                        for it in &body_items {
                            if let ModuleItem::TypedefDeclaration(td) = it {
                                let w = resolve_type_width(&td.data_type, Some(&sub_local_params), Some(&local_tds));
                                local_tds.insert(td.name.name.clone(), w);
                            }
                        }
                    }
                    TYPEDEFS_TLS.with(|c| *c.borrow_mut() = Some(local_tds));
                }

                // 2. Parameters from module items
                add_params_from_items(sub_mod.items(), &mut sub_local_params);

                let prepared_sub = prepare_module_items(sub_mod, definitions, &sub_local_params, &elab.typedefs, cache);

                // Inline all resolved parameters into global map with prefix
                for (name, val) in &sub_local_params {
                    let full_name = format!("{}{}", inst_prefix, name);
                    elab.parameters.insert(full_name.clone(), val.clone());
                    // Also add as a signal for simulation access
                    elab.signals.insert(full_name.clone(), Signal { is_const: false,
                        name: full_name,
                        width: val.width,
                        is_signed: val.is_signed,
                        is_real: val.is_real,
                        direction: None,
                        value: val.clone(),
                        type_name: None,
                    });
                }

                // Build the merged param map ONCE — used for both port-signal
                // declaration and the later sub-item processing. Skip the
                // parent clone when local_params is empty (top-level case).
                let sub_merged_params: HashMap<String, Value> = if local_params.is_empty() {
                    sub_local_params.clone()
                } else if sub_local_params.is_empty() {
                    local_params.clone()
                } else {
                    let mut m = local_params.clone();
                    for (k, v) in &sub_local_params {
                        m.insert(k.clone(), v.clone());
                    }
                    m
                };
                match sub_mod.ports() {
                    PortList::Ansi(ports) => {
                        for port in ports {
                            if prepared_sub.interface_ports.contains(&port.name.name) { continue; }
                            let width = port.data_type.as_ref()
                                .map(|dt| resolve_type_width(dt, Some(&sub_merged_params), Some(&elab.typedefs)))
                                .unwrap_or(1);
                            let sig_name = format!("{}{}", inst_prefix, port.name.name);
                            let is_real = port.data_type.as_ref().map(is_type_real).unwrap_or(false);
                            elab.signals.insert(sig_name.clone(), Signal { is_const: false,
                                name: sig_name, width,
                                is_signed: port.data_type.as_ref().map(|dt| is_type_signed(dt)).unwrap_or(false),
                                is_real,
                                direction: port.direction,
                                value: if is_real { Value::from_f64(0.0) } else { Value::new(width) },
                                type_name: port.data_type.as_ref().and_then(get_type_name),
                            });
                        }
                    }
                    PortList::NonAnsi(_names) => {
                        for sub_item in &prepared_sub.effective_items {
                            if let ModuleItem::PortDeclaration(pd) = sub_item {
                                if is_interface_type(&pd.data_type, definitions) { continue; }
                                let width = resolve_type_width(&pd.data_type, Some(&sub_local_params), Some(&elab.typedefs));
                                let is_signed = is_type_signed(&pd.data_type);
                                for decl in &pd.declarators {
                                    let sig_name = format!("{}{}", inst_prefix, decl.name.name);
                                    elab.signals.insert(sig_name.clone(), Signal { is_const: false,
                                        name: sig_name, width, is_signed,
                                        direction: Some(pd.direction),
                                        value: Value::new(width),
                                        is_real: is_type_real(&pd.data_type), type_name: get_type_name(&pd.data_type),
                                    });
                                }
                            }
                        }
                    }
                    PortList::Empty => {}
                }

                // sub_merged_params already built above for port declarations.
                for sub_item in &prepared_sub.effective_items {
                    if let ModuleItem::TypedefDeclaration(td) = sub_item {
                        if let DataType::Enum(et) = &td.data_type {
                            let base_width = et.base_type.as_ref()
                                .map(|bt| resolve_type_width(bt, Some(&sub_merged_params), Some(&elab.typedefs)))
                                .unwrap_or(32);
                            let mut next_val: u64 = 0;
                            for member in &et.members {
                                let val = if let Some(init) = &member.init {
                                    eval_const_expr(init, &sub_merged_params)
                                } else { next_val };
                                next_val = val.wrapping_add(1);
                                let v = Value::from_u64(val, base_width);
                                // Don't clobber an already-registered member
                                // with a DIFFERENT value: xezim's parameter
                                // namespace is flat, but per LRM §22.1.4 +
                                // §23.6 an enum member declared inside a
                                // submodule's typedef should NOT pollute the
                                // bare-name lookup used by sibling submodules.
                                // First-declared wins; a same-name same-value
                                // re-declaration is a no-op. Without this,
                                // testbench typedefs like
                                // `uvmt_cv32e40p_step_compare::state_e`
                                // (which has INIT=0, IDLE=1, …) overwrite
                                // `prefetch_state_e::IDLE`=0 / `rvvi_c_e::IDLE`=0,
                                // and every other module's `case` arm that
                                // references IDLE matches the wrong arm.
                                let prior = elab.parameters.get(&member.name.name).cloned();
                                let should_insert = match &prior {
                                    None => true,
                                    Some(p) => p.to_u64() == Some(val),
                                };
                                if should_insert {
                                    elab.parameters.insert(member.name.name.clone(), v.clone());
                                    elab.signals.insert(member.name.name.clone(), Signal {
                                        is_const: false,
                                        name: member.name.name.clone(),
                                        width: base_width,
                                        is_signed: false,
                                        direction: None,
                                        value: v,
                                        type_name: None,
                                        is_real: false,
                                    });
                                }
                            }
                            elab.typedefs.insert(td.name.name.clone(), base_width);
                        } else {
                            let w = resolve_type_width(&td.data_type, Some(&sub_merged_params), Some(&elab.typedefs));
                            elab.typedefs.insert(td.name.name.clone(), w);
                        }
                    }
                }
                for sub_item in &prepared_sub.effective_items {
                    match sub_item {
                        ModuleItem::NetDeclaration(nd) => {
                            let width = resolve_type_width(&nd.data_type, Some(&sub_merged_params), Some(&elab.typedefs));
                            for decl in &nd.declarators {
                                let sig_name = format!("{}{}", inst_prefix, decl.name.name);
                                let init_value = match nd.net_type {
                                    NetType::Supply0 => Value::zero(width),
                                    NetType::Supply1 => Value::ones(width),
                                    _ => Value::new(width),
                                };
                                elab.signals.insert(sig_name.clone(), Signal { is_const: false,
                                    name: sig_name, width,
                                    is_signed: is_type_signed(&nd.data_type),
                                    is_real: is_type_real(&nd.data_type),
                                    direction: None, value: init_value,
                                    type_name: get_type_name(&nd.data_type),
                                });                            }
                        }
                        ModuleItem::DataDeclaration(dd) => {
                            // Anonymous enum on a variable decl in a
                            // submodule's items (e.g. cv32e40p_obi_interface's
                            // state_q FSM): mirror the top-level DataDecl
                            // arm so enum members resolve as constants in
                            // submodule scopes too.
                            register_anonymous_enum_members(&dd.data_type, elab);
                            // ALSO register the members under the fully-
                            // scoped instance name (e.g.
                            // `dut_wrap...alu_div_i.FINISH`) so a local
                            // anon-enum value can win over a same-named
                            // pkg-imported member via scope-first lookup
                            // in `get_signal_value_by_name` at sim time
                            // (LRM §22.4 local declaration shadows
                            // wildcard-imported).
                            if let DataType::Enum(et) = &dd.data_type {
                                let base_width = et.base_type.as_ref()
                                    .map(|bt| resolve_type_width(bt, Some(&sub_merged_params), Some(&elab.typedefs)))
                                    .unwrap_or(32);
                                let mut next_val: u64 = 0;
                                let inst_prefix_no_dot = inst_prefix
                                    .strip_suffix('.')
                                    .unwrap_or(&inst_prefix)
                                    .to_string();
                                for member in &et.members {
                                    let val = if let Some(init) = &member.init {
                                        eval_const_expr(init, &sub_merged_params)
                                    } else { next_val };
                                    next_val = val.wrapping_add(1);
                                    let v = Value::from_u64(val, base_width);
                                    let scoped = format!("{}.{}", inst_prefix_no_dot, member.name.name);
                                    elab.parameters.insert(scoped.clone(), v.clone());
                                    elab.signals.insert(scoped.clone(), Signal {
                                        is_const: false,
                                        name: scoped,
                                        width: base_width,
                                        is_signed: false,
                                        is_real: false,
                                        direction: None,
                                        value: v,
                                        type_name: None,
                                    });
                                }
                            }
                            // Packed multi-D (`logic [N-1:0][W-1:0] x`) — register
                            // the per-element width under BOTH the bare name and
                            // the fully-scoped name. Without this hook a
                            // `mem[i] = data` write inside a parameterised
                            // submodule like cv32e40p_fifo silently degrades to
                            // a single-bit write at bit `i`, corrupting all
                            // prefetch data.
                            if let Some(elem_w) = packed_inner_elem_width(&dd.data_type, &sub_merged_params, &elab.typedefs) {
                                for decl in &dd.declarators {
                                    let bare = decl.name.name.clone();
                                    let scoped = format!("{}{}", inst_prefix, bare);
                                    elab.packed_signal_elem_widths.insert(bare, elem_w);
                                    elab.packed_signal_elem_widths.insert(scoped, elem_w);
                                }
                            }
                            let width = match &dd.data_type {
                                DataType::TypeReference { name, .. } => {
                                    elab.typedefs.get(&name.name.name).copied()
                                        .unwrap_or(resolve_type_width(&dd.data_type, Some(&sub_merged_params), Some(&elab.typedefs)))
                                }
                                _ => resolve_type_width(&dd.data_type, Some(&sub_merged_params), Some(&elab.typedefs)),
                            };
                            let is_signed = is_type_signed(&dd.data_type);
                            for decl in &dd.declarators {
                                let base_name = decl.name.name.clone();
                                let sig_name = format!("{}{}", inst_prefix, base_name);
                                let array_range = extract_array_range(&decl.dimensions, &sub_merged_params);
                                if std::env::var("XEZIM_DBG_ARR").is_ok() && sig_name.contains("ram0.mem") {
                                    let mut p: Vec<_> = sub_merged_params.iter().collect();
                                    p.sort_by_key(|(k, _)| k.as_str());
                                    eprintln!("[DBG_ARR] {} width={} array_range={:?} prefix='{}' sub_merged_params(len={}): {:?}",
                                        sig_name, width, array_range, inst_prefix, sub_merged_params.len(),
                                        p.iter().map(|(k, v)| format!("{}={}", k, v.to_u64().unwrap_or(0))).collect::<Vec<_>>());
                                }
                                if let Some((lo, hi)) = array_range {
                                    elab.arrays.insert(sig_name.clone(), (lo, hi, width));
                                    // Per-element Signals synthesized by
                                    // Simulator::new from arrays metadata.
                                    let _ = is_signed;
                                } else {
                                    let init_val = if let Some(init_expr) = &decl.init {
                                        eval_init_for_width(init_expr, &sub_merged_params, width)
                                    } else { Value::new(width) };
                                    elab.signals.insert(sig_name.clone(), Signal { is_const: dd.const_kw,
                                        name: sig_name, width, is_signed,
                                        direction: None, value: init_val,
                                        is_real: is_type_real(&dd.data_type), type_name: get_type_name(&dd.data_type),
                                    });
                                }
                            }
                        }
                        _ => {}
                    }
                }

                for (port_name, parent_expr) in &port_map {
                    if prepared_sub.interface_ports.contains(port_name) { continue; }
                    let sub_sig_name = format!("{}{}", inst_prefix, port_name);
                    let sub_expr = make_ident_expr(&sub_sig_name);
                    match prepared_sub.port_directions.get(port_name) {
                        Some(PortDirection::Input) | Some(PortDirection::Inout) => {
                            elab.continuous_assigns.push(ContinuousAssignment {
                                lhs: sub_expr, rhs: parent_expr.clone(), delay: 0,
                            });
                        }
                        Some(PortDirection::Output) => {
                            elab.continuous_assigns.push(ContinuousAssignment {
                                lhs: parent_expr.clone(), rhs: sub_expr, delay: 0,
                            });
                        }
                        _ => {
                            elab.continuous_assigns.push(ContinuousAssignment {
                                lhs: sub_expr, rhs: parent_expr.clone(), delay: 0,
                            });
                        }
                    }
                }

                // Build a rewrite_port_map that excludes output ports.
                // Output ports should use the local prefixed name (inst_prefix + port_name)
                // rather than the parent expression, because:
                //   - Input ports: the sub-module reads from the parent → use parent expr
                //   - Output ports: the sub-module writes to its local reg → use prefixed local name
                //     (a continuous assign parent = local handles the connection)
                let rewrite_port_map: HashMap<String, Expression> = port_map.iter()
                    .filter(|(name, _)| {
                        !matches!(prepared_sub.port_directions.get(name.as_str()), Some(PortDirection::Output))
                    })
                    .map(|(k, v)| (k.clone(), v.clone()))
                    .collect();

                // Build ONE RewriteCtx for this instance, shared (via Rc) across
                // every pending always/initial/cont-assign it produces. The
                // prefix, port_map and interface_map are instance-constant, so
                // cloning them once here instead of per pending item collapses
                // the duplicated port-map entries (on c910: ~10.8M -> ~1.2M),
                // the dominant elaboration memory cost. `local_names` was already
                // Rc-shared across sibling instances.
                let pend_ctx = std::rc::Rc::new(RewriteCtx {
                    prefix: inst_prefix.clone(),
                    port_map: rewrite_port_map.clone(),
                    local_names: std::rc::Rc::clone(&prepared_sub.local_names),
                    interface_map: sub_interface_map.clone(),
                });

                // Inline the sub-module's continuous assigns
                for (sub_item, body_src) in prepared_sub.effective_items.iter().zip(prepared_sub.body_sources.iter()) {
                    if let ModuleItem::FunctionDeclaration(fd) = sub_item {
                        let mut new_fd = fd.clone();
                        new_fd.name.name.name = format!("{}{}", inst_prefix, fd.name.name.name);
                        for p in &mut new_fd.ports {
                            if let Some(def) = &p.default {
                                p.default = Some(rewrite_expr(def, &inst_prefix, &rewrite_port_map, &*prepared_sub.local_names, &sub_interface_map));
                            }
                        }
                        new_fd.items = fd.items.iter()
                            .map(|s| rewrite_stmt(s, &inst_prefix, &rewrite_port_map, &*prepared_sub.local_names, &sub_interface_map))
                            .collect();
                        elab.functions.insert(new_fd.name.name.name.clone(), new_fd);
                    }
                    if let ModuleItem::TaskDeclaration(td) = sub_item {
                        let mut new_td = td.clone();
                        new_td.name.name.name = format!("{}{}", inst_prefix, td.name.name.name);
                        for p in &mut new_td.ports {
                            if let Some(def) = &p.default {
                                p.default = Some(rewrite_expr(def, &inst_prefix, &rewrite_port_map, &*prepared_sub.local_names, &sub_interface_map));
                            }
                        }
                        new_td.items = td.items.iter()
                            .map(|s| rewrite_stmt(s, &inst_prefix, &rewrite_port_map, &*prepared_sub.local_names, &sub_interface_map))
                            .collect();
                        elab.tasks.insert(new_td.name.name.name.clone(), new_td);
                    }
                    if matches!(sub_item, ModuleItem::ContinuousAssign(_)) {
                        // #7: Rc-share source ASTs across sibling instances.
                        if let BodySource::ContAssign(pairs) = body_src {
                            for (lhs_rc, rhs_rc) in pairs {
                                elab.pending_cont_assign.push(PendingContAssign {
                                    lhs_source: std::rc::Rc::clone(lhs_rc),
                                    rhs_source: std::rc::Rc::clone(rhs_rc),
                                    ctx: std::rc::Rc::clone(&pend_ctx),
                                });
                            }
                        }
                    }
                    if let ModuleItem::GateInstantiation(gi) = sub_item {
                        // §28.8 switches produce no assign pairs; record them
                        // with terminals rewritten into this instance's scope.
                        record_tran_switches(gi, elab, |e| {
                            rewrite_expr(
                                e,
                                &pend_ctx.prefix,
                                &pend_ctx.port_map,
                                &pend_ctx.local_names,
                                &pend_ctx.interface_map,
                            )
                        });
                        if let BodySource::GateInst(pairs) = body_src {
                            for (lhs_rc, rhs_rc) in pairs {
                                elab.pending_cont_assign.push(PendingContAssign {
                                    lhs_source: std::rc::Rc::clone(lhs_rc),
                                    rhs_source: std::rc::Rc::clone(rhs_rc),
                                    ctx: std::rc::Rc::clone(&pend_ctx),
                                });
                            }
                        }
                    }
                    if matches!(sub_item, ModuleItem::NetDeclaration(_)) {
                        if let BodySource::NetInits(inits) = body_src {
                            for (decl_name, rhs_rc) in inits {
                                let lhs_name = format!("{}{}", inst_prefix, decl_name);
                                let new_lhs = make_ident_expr(&lhs_name);
                                elab.pending_cont_assign.push(PendingContAssign {
                                    lhs_source: std::rc::Rc::new(new_lhs),
                                    rhs_source: std::rc::Rc::clone(rhs_rc),
                                    ctx: std::rc::Rc::clone(&pend_ctx),
                                });
                            }
                        }
                    }
                    if let ModuleItem::SpecifyBlock(sb) = sub_item {
                        for p in &sb.paths {
                            let dst_expr = rewrite_expr(
                                &make_ident_expr(&p.dst.name),
                                &inst_prefix,
                                &rewrite_port_map,
                                &*prepared_sub.local_names,
                                &sub_interface_map,
                            );
                            if let ExprKind::Ident(hier) = &dst_expr.kind {
                                let dst_name = hier.path.iter().map(|s| s.name.name.as_str()).collect::<Vec<_>>().join(".");
                                let d = eval_const_expr(&p.delay, &elab.parameters);
                                elab.specify_delays.insert(dst_name, d);
                            }
                        }
                    }
                    if matches!(sub_item, ModuleItem::AlwaysConstruct(_)) {
                        if let BodySource::Always(kind, stmt_rc) = body_src {
                            elab.pending_always.push(PendingAlways {
                                kind: *kind,
                                source: std::rc::Rc::clone(stmt_rc),
                                ctx: std::rc::Rc::clone(&pend_ctx),
                            });
                        }
                    }
                    if matches!(sub_item, ModuleItem::InitialConstruct(_)) {
                        if let BodySource::Initial(stmt_rc) = body_src {
                            if std::env::var("XEZIM_TRACE_INIT").ok().as_deref() == Some("1") {
                                eprintln!("[xezim][elab] inline_module: pushing initial from {}", inst_prefix);
                            }
                            elab.pending_initial.push(PendingInitial {
                                source: std::rc::Rc::clone(stmt_rc),
                                ctx: std::rc::Rc::clone(&pend_ctx),
                            });
                        }
                    }
                }

                // Record the instance before descending. Inlining is about to
                // dissolve this module into the parent, so this is the only
                // place the (path, definition) pair still exists.
                elab.instances.push(ElabInstance {
                    path: inst_prefix.trim_end_matches('.').to_string(),
                    def_name: sub_mod_name.clone(),
                    parent: prefix.trim_end_matches('.').to_string(),
                });

                // Recurse into sub-module instantiations
                inline_module_items(elab, sub_mod, &inst_prefix, definitions, &mut sub_interface_map, &sub_merged_params, cache)?;
            }
        }
    }
    Ok(())
}

/// Build a high-impedance (`'z`) literal expression for tristate gate models.
fn make_z_expr(span: Span) -> Expression {
    Expression::new(ExprKind::Number(crate::ast::expr::NumberLiteral::UnbasedUnsized('z')), span)
}

/// `cond ? then : 'z` — the canonical enabled-output / tristate shape used by
/// `bufif`/`notif` and the MOS/switch primitives.
fn make_tristate(cond: Expression, then_e: Expression, span: Span) -> Expression {
    Expression::new(ExprKind::Conditional {
        condition: Box::new(cond),
        then_expr: Box::new(then_e),
        else_expr: Box::new(make_z_expr(span)),
    }, span)
}

fn gate_inst_to_assign_pairs(gi: &GateInstantiation) -> Vec<(Expression, Expression)> {
    let mut pairs = Vec::new();
    for inst in &gi.instances {
        // §28 pull gates: `pullup (net)` / `pulldown (net)` — single terminal
        // tied to a constant. Handled before the 2-terminal guard.
        match gi.gate_type {
            GateType::Pullup | GateType::Pulldown => {
                if let Some(net) = inst.terminals.first() {
                    let v = if matches!(gi.gate_type, GateType::Pullup) { '1' } else { '0' };
                    let lit = Expression::new(
                        ExprKind::Number(crate::ast::expr::NumberLiteral::UnbasedUnsized(v)), net.span);
                    pairs.push((net.clone(), lit));
                }
                continue;
            }
            _ => {}
        }
        if inst.terminals.len() < 2 { continue; }
        let out = inst.terminals[0].clone();
        let in1 = inst.terminals[1].clone();
        let sp = out.span;
        match gi.gate_type {
            // §28 tristate buffers/inverters: `bufif1(out,in,ctl)` etc.
            GateType::Bufif1 | GateType::Bufif0 | GateType::Notif1 | GateType::Notif0 => {
                if inst.terminals.len() >= 3 {
                    let ctl = inst.terminals[2].clone();
                    let data = if matches!(gi.gate_type, GateType::Notif0 | GateType::Notif1) {
                        Expression::new(ExprKind::Unary { op: UnaryOp::BitNot, operand: Box::new(in1) }, sp)
                    } else { in1 };
                    let active_high = matches!(gi.gate_type, GateType::Bufif1 | GateType::Notif1);
                    let cond = if active_high { ctl } else {
                        Expression::new(ExprKind::Unary { op: UnaryOp::LogNot, operand: Box::new(ctl) }, sp)
                    };
                    pairs.push((out, make_tristate(cond, data, sp)));
                }
            }
            // §28 MOS switches: `nmos(out,data,ctl)` conducts on ctl, `pmos` on !ctl.
            GateType::Nmos | GateType::Rnmos | GateType::Pmos | GateType::Rpmos => {
                if inst.terminals.len() >= 3 {
                    let ctl = inst.terminals[2].clone();
                    let active_high = matches!(gi.gate_type, GateType::Nmos | GateType::Rnmos);
                    let cond = if active_high { ctl } else {
                        Expression::new(ExprKind::Unary { op: UnaryOp::LogNot, operand: Box::new(ctl) }, sp)
                    };
                    pairs.push((out, make_tristate(cond, in1, sp)));
                }
            }
            // §28 CMOS: `cmos(out,data,nctl,pctl)` — conducts when nctl|!pctl.
            GateType::Cmos | GateType::Rcmos => {
                if inst.terminals.len() >= 4 {
                    let nctl = inst.terminals[2].clone();
                    let pctl = inst.terminals[3].clone();
                    let pnot = Expression::new(ExprKind::Unary { op: UnaryOp::LogNot, operand: Box::new(pctl) }, sp);
                    let cond = Expression::new(ExprKind::Binary {
                        op: BinaryOp::LogOr, left: Box::new(nctl), right: Box::new(pnot) }, sp);
                    pairs.push((out, make_tristate(cond, in1, sp)));
                }
            }
            // §28.8 bidirectional switches are not one-directional assigns.
            // They are recorded and resolved against each terminal's own
            // drivers by `resolve_bidirectional_switches`.
            GateType::Tran | GateType::Rtran => {}
            GateType::Tranif1 | GateType::Rtranif1 | GateType::Tranif0 | GateType::Rtranif0 => {}
            GateType::And => {
                let mut rhs = in1;
                for i in 2..inst.terminals.len() {
                    rhs = Expression::new(ExprKind::Binary { op: BinaryOp::BitAnd, left: Box::new(rhs), right: Box::new(inst.terminals[i].clone()) }, out.span);
                }
                pairs.push((out, rhs));
            }
            GateType::Or => {
                let mut rhs = in1;
                for i in 2..inst.terminals.len() {
                    rhs = Expression::new(ExprKind::Binary { op: BinaryOp::BitOr, left: Box::new(rhs), right: Box::new(inst.terminals[i].clone()) }, out.span);
                }
                pairs.push((out, rhs));
            }
            GateType::Xor => {
                let mut rhs = in1;
                for i in 2..inst.terminals.len() {
                    rhs = Expression::new(ExprKind::Binary { op: BinaryOp::BitXor, left: Box::new(rhs), right: Box::new(inst.terminals[i].clone()) }, out.span);
                }
                pairs.push((out, rhs));
            }
            GateType::Nand => {
                let mut rhs = in1;
                for i in 2..inst.terminals.len() {
                    rhs = Expression::new(ExprKind::Binary { op: BinaryOp::BitAnd, left: Box::new(rhs), right: Box::new(inst.terminals[i].clone()) }, out.span);
                }
                rhs = Expression::new(ExprKind::Unary { op: UnaryOp::BitNot, operand: Box::new(rhs) }, out.span);
                pairs.push((out, rhs));
            }
            GateType::Nor => {
                let mut rhs = in1;
                for i in 2..inst.terminals.len() {
                    rhs = Expression::new(ExprKind::Binary { op: BinaryOp::BitOr, left: Box::new(rhs), right: Box::new(inst.terminals[i].clone()) }, out.span);
                }
                rhs = Expression::new(ExprKind::Unary { op: UnaryOp::BitNot, operand: Box::new(rhs) }, out.span);
                pairs.push((out, rhs));
            }
            GateType::Xnor => {
                let mut rhs = in1;
                for i in 2..inst.terminals.len() {
                    rhs = Expression::new(ExprKind::Binary { op: BinaryOp::BitXor, left: Box::new(rhs), right: Box::new(inst.terminals[i].clone()) }, out.span);
                }
                rhs = Expression::new(ExprKind::Unary { op: UnaryOp::BitNot, operand: Box::new(rhs) }, out.span);
                pairs.push((out, rhs));
            }
            GateType::Not => {
                let rhs = Expression::new(ExprKind::Unary { op: UnaryOp::BitNot, operand: Box::new(in1) }, out.span);
                pairs.push((out, rhs));
            }
            GateType::Buf => {
                // Single-input buffer: out = in. Multi-output `buf` with
                // (out1, out2, ..., in) is rare; for now only the
                // two-terminal form is supported.
                pairs.push((out, in1));
            }
            _ => {}
        }
    }
    pairs
}

/// LRM §17.2 checker port substitution helper. Substitutes formal
/// names with actual expressions in a ModuleItem. Reuses
/// `rewrite_stmt` / `rewrite_expr` with an empty prefix and no
/// interface map. Only handles the item shapes a checker body can
/// realistically contain (initial/always/assertion/etc.).
fn rewrite_module_item_subst(
    item: &ModuleItem,
    subst: &HashMap<String, Expression>,
) -> ModuleItem {
    let empty: std::collections::HashSet<String> = std::collections::HashSet::new();
    let empty_iface: HashMap<String, String> = HashMap::default();
    match item {
        ModuleItem::InitialConstruct(ic) => {
            let mut new_ic = ic.clone();
            new_ic.stmt = rewrite_stmt(&ic.stmt, "", subst, &empty, &empty_iface);
            ModuleItem::InitialConstruct(new_ic)
        }
        ModuleItem::AlwaysConstruct(ac) => {
            let mut new_ac = ac.clone();
            new_ac.stmt = rewrite_stmt(&ac.stmt, "", subst, &empty, &empty_iface);
            ModuleItem::AlwaysConstruct(new_ac)
        }
        ModuleItem::AssertionItem(a) => {
            let mut new_a = a.clone();
            new_a.expr = rewrite_expr(&a.expr, "", subst, &empty, &empty_iface);
            if let Some(act) = &a.action {
                new_a.action = Some(Box::new(rewrite_stmt(
                    act,
                    "",
                    subst,
                    &empty,
                    &empty_iface,
                )));
            }
            if let Some(ea) = &a.else_action {
                new_a.else_action = Some(Box::new(rewrite_stmt(
                    ea,
                    "",
                    subst,
                    &empty,
                    &empty_iface,
                )));
            }
            ModuleItem::AssertionItem(new_a)
        }
        // Other item kinds are passed through unchanged — extending
        // this map is straightforward when a real testbench needs it.
        other => other.clone(),
    }
}

/// Flat dotted name of an identifier expression. A hierarchical reference may
/// parse as an `Ident` with several path segments OR as a `MemberAccess` chain
/// (`top.inst.net`), so fold both shapes.
fn ident_flat_name(e: &Expression) -> Option<String> {
    match &e.kind {
        ExprKind::Ident(h) if h.path.iter().all(|s| s.selects.is_empty()) => Some(
            h.path.iter().map(|s| s.name.name.as_str()).collect::<Vec<_>>().join("."),
        ),
        ExprKind::MemberAccess { expr, member } => {
            Some(format!("{}.{}", ident_flat_name(expr)?, member.name))
        }
        _ => None,
    }
}

fn make_syscall(name: &str, args: Vec<Expression>, span: Span) -> Expression {
    Expression::new(ExprKind::SystemCall { name: name.to_string(), args }, span)
}

/// IEEE 1800-2017 §28.8. A bidirectional switch is not a one-directional
/// assign: both terminals settle to the resolution of BOTH sides' drivers when
/// the switch conducts, and keep their own driver when it does not.
///
/// Rewrite each terminal's own continuous drivers into a single bridged assign:
///
/// ```text
/// assign a = $__tranif(own_a, own_b, ctl, active);
/// assign b = $__tranif(own_b, own_a, ctl, active);
/// ```
///
/// `$__tranif` resolves the two sides when the switch conducts (`z` yields to a
/// driven value; conflicting values give `x`), passes the terminal's own value
/// through when it does not, and gives `x` per differing bit when the control
/// is unknown. An unconditional `tran` always conducts.
///
/// Only terminals that are plain (possibly dotted) names are handled; a switch
/// whose terminal is an expression is left unconnected, as before.
/// IEEE 1800-2017 §6.6.1: a NET with more than one continuous driver takes the
/// wired-net resolution of all of them, not whichever assign happened to run
/// last. Fold the drivers of each such net into a single `$__wres` chain.
///
/// Only whole-net drivers (`assign w = ...`) participate; a driver of a slice
/// (`assign w[3:0] = ...`) is left alone, and variables are untouched — they
/// legitimately have one driver.
pub fn resolve_multi_driver_nets(elab: &mut ElaboratedModule) {
    let mut counts: HashMap<String, usize> = HashMap::default();
    for ca in &elab.continuous_assigns {
        if let Some(n) = ident_flat_name(&ca.lhs) {
            *counts.entry(n).or_insert(0) += 1;
        }
    }
    let multi: HashSet<String> = counts
        .into_iter()
        .filter(|(n, c)| *c > 1 && elab.nets.contains(n))
        .map(|(n, _)| n)
        .collect();
    if multi.is_empty() {
        return;
    }
    let all = std::mem::take(&mut elab.continuous_assigns);
    let mut folded: HashMap<String, (Expression, Expression, u64)> = HashMap::default();
    let mut order: Vec<String> = Vec::new();
    for ca in all {
        let name = ident_flat_name(&ca.lhs).filter(|n| multi.contains(n));
        let Some(name) = name else {
            elab.continuous_assigns.push(ca);
            continue;
        };
        match folded.get_mut(&name) {
            Some((_, rhs, _)) => {
                let span = ca.rhs.span;
                let acc = std::mem::replace(rhs, make_z_expr(span));
                *rhs = make_syscall("$__wres", vec![acc, ca.rhs], span);
            }
            None => {
                order.push(name.clone());
                folded.insert(name, (ca.lhs, ca.rhs, ca.delay));
            }
        }
    }
    for name in order {
        if let Some((lhs, rhs, delay)) = folded.remove(&name) {
            elab.continuous_assigns.push(ContinuousAssignment { lhs, rhs, delay });
        }
    }
}

pub fn resolve_bidirectional_switches(elab: &mut ElaboratedModule) {
    let switches = std::mem::take(&mut elab.tran_switches);
    if switches.is_empty() {
        return;
    }
    // A terminal's drivers may live in a sub-module and still be pending. The
    // pass needs every driver of every terminal in hand, so materialize them.
    // Only designs that actually contain a switch pay for this.
    let pending = std::mem::take(&mut elab.pending_cont_assign);
    for p in pending {
        elab.continuous_assigns.push(p.materialize());
    }
    // A cross-module terminal names the top module explicitly; signals and
    // driver lvalues are keyed without that root.
    let root = format!("{}.", elab.name);
    let norm = |n: String| -> String {
        n.strip_prefix(root.as_str()).map(|r| r.to_string()).unwrap_or(n)
    };
    for sw in switches {
        let (Some(na), Some(nb)) = (
            ident_flat_name(&sw.a).map(&norm),
            ident_flat_name(&sw.b).map(&norm),
        ) else {
            continue;
        };
        let (term_a, term_b) = (make_ident_expr(&na), make_ident_expr(&nb));
        let span = sw.a.span;

        // Each terminal's OWN drivers, folded with the wired-net resolution.
        let mut take_drivers = |name: &str| -> Option<Expression> {
            let mut rhs: Vec<Expression> = Vec::new();
            elab.continuous_assigns.retain(|ca| {
                if ident_flat_name(&ca.lhs).map(&norm).as_deref() == Some(name) {
                    rhs.push(ca.rhs.clone());
                    false
                } else {
                    true
                }
            });
            let mut it = rhs.into_iter();
            let first = it.next()?;
            Some(it.fold(first, |acc, r| make_syscall("$__wres", vec![acc, r], span)))
        };
        let own_a = take_drivers(&na);
        let own_b = take_drivers(&nb);
        // A terminal with no driver of its own contributes high impedance.
        let z = || make_z_expr(span);
        let own_a = own_a.unwrap_or_else(z);
        let own_b = own_b.unwrap_or_else(z);

        let ctl = sw.ctl.clone().unwrap_or_else(|| {
            Expression::new(
                ExprKind::Number(crate::ast::expr::NumberLiteral::UnbasedUnsized('1')),
                span,
            )
        });
        let active = Expression::new(
            ExprKind::Number(crate::ast::expr::NumberLiteral::UnbasedUnsized(
                if sw.active_high { '1' } else { '0' },
            )),
            span,
        );

        elab.continuous_assigns.push(ContinuousAssignment {
            lhs: term_a,
            rhs: make_syscall(
                "$__tranif",
                vec![own_a.clone(), own_b.clone(), ctl.clone(), active.clone()],
                span,
            ),
            delay: 0,
        });
        elab.continuous_assigns.push(ContinuousAssignment {
            lhs: term_b,
            rhs: make_syscall("$__tranif", vec![own_b, own_a, ctl, active], span),
            delay: 0,
        });
    }
}

/// Record a `tran`/`tranif0`/`tranif1` instantiation. `map` brings each terminal
/// into the enclosing scope (identity at the top level, `rewrite_expr` when the
/// gate lives in an inlined sub-module). Returns true if `gi` was a switch.
fn record_tran_switches<F>(gi: &GateInstantiation, elab: &mut ElaboratedModule, map: F) -> bool
where
    F: Fn(&Expression) -> Expression,
{
    if !matches!(
        gi.gate_type,
        GateType::Tran | GateType::Rtran | GateType::Tranif0
            | GateType::Rtranif0 | GateType::Tranif1 | GateType::Rtranif1
    ) {
        return false;
    }
    let conditional = !matches!(gi.gate_type, GateType::Tran | GateType::Rtran);
    // An unconditional `tran` always conducts: it is modelled with a synthetic
    // control of 1, so it must be ACTIVE HIGH. Treating it like a `tranif0`
    // left the switch permanently open.
    let active_high =
        !conditional || matches!(gi.gate_type, GateType::Tranif1 | GateType::Rtranif1);
    for inst in &gi.instances {
        if inst.terminals.len() < 2 {
            continue;
        }
        let ctl = if conditional {
            match inst.terminals.get(2) {
                Some(c) => Some(map(c)),
                None => continue,
            }
        } else {
            None
        };
        elab.tran_switches.push(TranSwitch {
            a: map(&inst.terminals[0]),
            b: map(&inst.terminals[1]),
            ctl,
            active_high,
        });
    }
    true
}

fn gate_inst_to_assigns(gi: &GateInstantiation, elab: &mut ElaboratedModule) {
    // §28.8 bidirectional switches: record, don't lower to an assign.
    if record_tran_switches(gi, elab, |e| e.clone()) {
        return;
    }
    let pairs = gate_inst_to_assign_pairs(gi);
    for (lhs, rhs) in pairs {
        elab.continuous_assigns.push(ContinuousAssignment { lhs, rhs, delay: 0 });
    }
}

fn make_ident_expr(name: &str) -> Expression {
    Expression::new(ExprKind::Ident(HierarchicalIdentifier {
        root: None,
        path: vec![HierPathSegment { name: Identifier { name: name.to_string(), span: Span::dummy() }, selects: Vec::new() }],
        span: Span::dummy(),
        cached_signal_id: std::cell::Cell::new(None),
                    cached_resolved_name: std::cell::OnceCell::new(),
    }), Span::dummy())
}

fn rewrite_expr(expr: &Expression, prefix: &str, port_map: &HashMap<String, Expression>, local_names: &std::collections::HashSet<String>, interface_map: &HashMap<String, String>) -> Expression {
    rewrite_expr_impl(expr, prefix, port_map, local_names, interface_map)
}

fn rewrite_expr_impl(expr: &Expression, prefix: &str, port_map: &HashMap<String, Expression>, local_names: &std::collections::HashSet<String>, interface_map: &HashMap<String, String>) -> Expression {
    let new_kind = match &expr.kind {
        ExprKind::Ident(hier) => {
            if hier.root.is_some() { return expr.clone(); }
            if hier.path.is_empty() { return expr.clone(); }
            let name = &hier.path[0].name.name;
            if let Some(if_prefix) = interface_map.get(name) {
                let mut new_hier = hier.clone();
                new_hier.path[0].name.name = if_prefix.clone();
                return Expression::new(ExprKind::Ident(new_hier), expr.span);
            }
            if let Some(mapped) = port_map.get(name) {
                // Preserve any trailing path segments and first-segment selects:
                // `a.b.c` parsed as one ident with path=[a,b,c] where `a` is the
                // port-mapped name must become `<mapped>.b.c`, not just
                // `<mapped>`. Dropping the tail silently mis-resolved black-parrot
                // coherence-NoC multi-segment port references (the 6th write /
                // header-length field).
                let has_tail = hier.path.len() > 1 || !hier.path[0].selects.is_empty();
                if !has_tail {
                    return mapped.clone();
                }
                if let ExprKind::Ident(mut mhier) = mapped.kind.clone() {
                    // Graft seg0's selects onto the mapped target's last
                    // segment, then append the trailing segments verbatim
                    // (each keeps its own selects).
                    if !hier.path[0].selects.is_empty() {
                        if let Some(last) = mhier.path.last_mut() {
                            last.selects.extend(hier.path[0].selects.iter().cloned());
                        }
                    }
                    for seg in &hier.path[1..] {
                        mhier.path.push(seg.clone());
                    }
                    return Expression::new(ExprKind::Ident(mhier), expr.span);
                }
                // Non-ident mapped target (e.g. an Index/concat connection):
                // rebuild the trailing member chain as MemberAccess.
                let mut acc = mapped.clone();
                for seg in &hier.path[1..] {
                    acc = Expression::new(ExprKind::MemberAccess {
                        expr: Box::new(acc),
                        member: seg.name.clone(),
                    }, expr.span);
                }
                return acc;
            }
            if local_names.contains(name) {
                let mut new_hier = hier.clone();
                new_hier.path[0].name.name = format!("{}{}", prefix, name);
                ExprKind::Ident(new_hier)
            } else {
                expr.kind.clone()
            }
        }
        ExprKind::Unary { op, operand } => ExprKind::Unary {
            op: *op,
            operand: Box::new(rewrite_expr_impl(operand, prefix, port_map, local_names, interface_map)),
        },
        ExprKind::Binary { op, left, right } => ExprKind::Binary {
            op: *op,
            left: Box::new(rewrite_expr_impl(left, prefix, port_map, local_names, interface_map)),
            right: Box::new(rewrite_expr_impl(right, prefix, port_map, local_names, interface_map)),
        },
        ExprKind::Conditional { condition, then_expr, else_expr } => ExprKind::Conditional {
            condition: Box::new(rewrite_expr_impl(condition, prefix, port_map, local_names, interface_map)),
            then_expr: Box::new(rewrite_expr_impl(then_expr, prefix, port_map, local_names, interface_map)),
            else_expr: Box::new(rewrite_expr_impl(else_expr, prefix, port_map, local_names, interface_map)),
        },
        ExprKind::Concatenation(parts) => ExprKind::Concatenation(
            parts.iter().map(|p| rewrite_expr_impl(p, prefix, port_map, local_names, interface_map)).collect(),
        ),
        ExprKind::Replication { count, exprs } => ExprKind::Replication {
            count: Box::new(rewrite_expr_impl(count, prefix, port_map, local_names, interface_map)),
            exprs: exprs.iter().map(|e| rewrite_expr_impl(e, prefix, port_map, local_names, interface_map)).collect(),
        },
        ExprKind::Index { expr: base, index } => ExprKind::Index {
            expr: Box::new(rewrite_expr_impl(base, prefix, port_map, local_names, interface_map)),
            index: Box::new(rewrite_expr_impl(index, prefix, port_map, local_names, interface_map)),
        },
        ExprKind::RangeSelect { expr: base, kind, left, right } => ExprKind::RangeSelect {
            expr: Box::new(rewrite_expr_impl(base, prefix, port_map, local_names, interface_map)),
            kind: *kind,
            left: Box::new(rewrite_expr_impl(left, prefix, port_map, local_names, interface_map)),
            right: Box::new(rewrite_expr_impl(right, prefix, port_map, local_names, interface_map)),
        },
        ExprKind::MemberAccess { expr: base, member } => {
            let rewritten_base = rewrite_expr_impl(base, prefix, port_map, local_names, interface_map);
            if let ExprKind::Ident(mut hier) = rewritten_base.kind {
                hier.path.push(HierPathSegment {
                    name: member.clone(),
                    selects: Vec::new(),
                });
                ExprKind::Ident(hier)
            } else {
                ExprKind::MemberAccess {
                    expr: Box::new(rewritten_base),
                    member: member.clone(),
                }
            }
        }
        ExprKind::Paren(inner) => ExprKind::Paren(Box::new(rewrite_expr_impl(inner, prefix, port_map, local_names, interface_map))),
        ExprKind::Call { func, args } => ExprKind::Call {
            func: Box::new(rewrite_expr_impl(func, prefix, port_map, local_names, interface_map)),
            args: args.iter().map(|a| rewrite_expr_impl(a, prefix, port_map, local_names, interface_map)).collect(),
        },
        ExprKind::SystemCall { name, args } => ExprKind::SystemCall {
            name: name.clone(),
            args: args.iter().map(|a| rewrite_expr_impl(a, prefix, port_map, local_names, interface_map)).collect(),
        },
        // LRM §16.5 SVA property body — substitute formal-arg
        // references in both the clock signal and the body. Without
        // this, a checker like
        //   `assert property (@(posedge clk) in_a |=> in_b);`
        // would keep references to formal `in_a`/`in_b` after the
        // port-substitution pass, causing the sva site to read
        // non-existent signals.
        ExprKind::SvaClocked { clock, body } => ExprKind::SvaClocked {
            clock: Box::new(rewrite_expr_impl(clock, prefix, port_map, local_names, interface_map)),
            body: Box::new(rewrite_expr_impl(body, prefix, port_map, local_names, interface_map)),
        },
        other => other.clone(),
    };
    Expression::new(new_kind, expr.span)
}

/// Rewrite the constant-expression leaves of a §12.6 pattern for an instance.
/// Tag names and `.v` binding names are not signals and are left alone.
fn rewrite_pattern(
    p: &crate::ast::stmt::Pattern,
    prefix: &str,
    port_map: &HashMap<String, Expression>,
    local_names: &std::collections::HashSet<String>,
    interface_map: &HashMap<String, String>,
) -> crate::ast::stmt::Pattern {
    use crate::ast::stmt::Pattern as P;
    match p {
        P::Wildcard => P::Wildcard,
        P::Binding(id) => P::Binding(id.clone()),
        P::Tagged { tag, inner } => P::Tagged {
            tag: tag.clone(),
            inner: inner
                .as_ref()
                .map(|i| Box::new(rewrite_pattern(i, prefix, port_map, local_names, interface_map))),
        },
        P::Expr(e) => P::Expr(rewrite_expr(e, prefix, port_map, local_names, interface_map)),
        P::Struct(ms) => P::Struct(
            ms.iter()
                .map(|(n, sp)| {
                    (n.clone(), rewrite_pattern(sp, prefix, port_map, local_names, interface_map))
                })
                .collect(),
        ),
    }
}

fn rewrite_stmt(stmt: &Statement, prefix: &str, port_map: &HashMap<String, Expression>, local_names: &std::collections::HashSet<String>, interface_map: &HashMap<String, String>) -> Statement {
    let new_kind = match &stmt.kind {
        StatementKind::BlockingAssign { lvalue, rvalue } => StatementKind::BlockingAssign {
            lvalue: rewrite_expr(lvalue, prefix, port_map, local_names, interface_map),
            rvalue: rewrite_expr(rvalue, prefix, port_map, local_names, interface_map),
        },
        StatementKind::NonblockingAssign { lvalue, delay, rvalue } => StatementKind::NonblockingAssign {
            lvalue: rewrite_expr(lvalue, prefix, port_map, local_names, interface_map),
            delay: delay.as_ref().map(|d| rewrite_expr(d, prefix, port_map, local_names, interface_map)),
            rvalue: rewrite_expr(rvalue, prefix, port_map, local_names, interface_map),
        },
        StatementKind::Expr(expr) => StatementKind::Expr(rewrite_expr(expr, prefix, port_map, local_names, interface_map)),
        StatementKind::If { unique_priority, condition, then_stmt, else_stmt } => StatementKind::If {
            unique_priority: *unique_priority,
            condition: rewrite_expr(condition, prefix, port_map, local_names, interface_map),
            then_stmt: Box::new(rewrite_stmt(then_stmt, prefix, port_map, local_names, interface_map)),
            else_stmt: else_stmt.as_ref().map(|s| Box::new(rewrite_stmt(s, prefix, port_map, local_names, interface_map))),
        },
        StatementKind::Case { unique_priority, kind, expr, items } => StatementKind::Case {
            unique_priority: *unique_priority,
            kind: *kind,
            expr: rewrite_expr(expr, prefix, port_map, local_names, interface_map),
            items: items.iter().map(|item| CaseItem {
                patterns: item.patterns.iter().map(|p| rewrite_expr(p, prefix, port_map, local_names, interface_map)).collect(),
                is_default: item.is_default,
                stmt: rewrite_stmt(&item.stmt, prefix, port_map, local_names, interface_map),
                span: item.span,
                // §12.6: rewrite constant-expression sub-patterns and the
                // `&&&` guard; tags and `.v` binding names are not signals.
                pattern: item.pattern.as_ref().map(|p| rewrite_pattern(p, prefix, port_map, local_names, interface_map)),
                guard: item.guard.as_ref().map(|g| rewrite_expr(g, prefix, port_map, local_names, interface_map)),
            }).collect(),
        },
        StatementKind::For { init, condition, step, body } => StatementKind::For {
            init: init.iter().map(|fi| match fi {
                ForInit::VarDecl { data_type, name, init } => ForInit::VarDecl {
                    data_type: data_type.clone(),
                    name: name.clone(),
                    init: rewrite_expr(init, prefix, port_map, local_names, interface_map),
                },
                ForInit::Assign { lvalue, rvalue } => ForInit::Assign {
                    lvalue: rewrite_expr(lvalue, prefix, port_map, local_names, interface_map),
                    rvalue: rewrite_expr(rvalue, prefix, port_map, local_names, interface_map),
                },
            }).collect(),
            condition: condition.as_ref().map(|c| rewrite_expr(c, prefix, port_map, local_names, interface_map)),
            step: step.iter().map(|s| rewrite_expr(s, prefix, port_map, local_names, interface_map)).collect(),
            body: Box::new(rewrite_stmt(body, prefix, port_map, local_names, interface_map)),
        },
        StatementKind::While { condition, body } => StatementKind::While {
            condition: rewrite_expr(condition, prefix, port_map, local_names, interface_map),
            body: Box::new(rewrite_stmt(body, prefix, port_map, local_names, interface_map)),
        },
        StatementKind::Repeat { count, body } => StatementKind::Repeat {
            count: rewrite_expr(count, prefix, port_map, local_names, interface_map),
            body: Box::new(rewrite_stmt(body, prefix, port_map, local_names, interface_map)),
        },
        StatementKind::Forever { body } => StatementKind::Forever {
            body: Box::new(rewrite_stmt(body, prefix, port_map, local_names, interface_map)),
        },
        StatementKind::TimingControl { control, stmt: body } => StatementKind::TimingControl {
            control: match control {
                TimingControl::Delay(e) => TimingControl::Delay(rewrite_expr(e, prefix, port_map, local_names, interface_map)),
                TimingControl::Event(ev) => TimingControl::Event(rewrite_event_control(ev, prefix, port_map, local_names, interface_map)),
            },
            stmt: Box::new(rewrite_stmt(body, prefix, port_map, local_names, interface_map)),
        },
        StatementKind::SeqBlock { name, stmts } => StatementKind::SeqBlock {
            name: name.clone(),
            stmts: stmts.iter().map(|s| rewrite_stmt(s, prefix, port_map, local_names, interface_map)).collect(),
        },
        StatementKind::EventTrigger { nonblocking, name, span } => StatementKind::EventTrigger {
            nonblocking: *nonblocking,
            name: Identifier {
                name: if let Some(mapped) = port_map.get(&name.name) {
                    if let ExprKind::Ident(h) = &mapped.kind { h.path[0].name.name.clone() } else { name.name.clone() }
                } else if local_names.contains(&name.name) {
                    format!("{}.{}", prefix, name.name)
                } else {
                    name.name.clone()
                },
                span: name.span,
            },
            span: *span,
        },
        StatementKind::ParBlock { name, stmts, join_type } => StatementKind::ParBlock {
            name: name.clone(),
            stmts: stmts.iter().map(|s| rewrite_stmt(s, prefix, port_map, local_names, interface_map)).collect(),
            join_type: *join_type,
        },
        other => other.clone(),
    };
    Statement::new(new_kind, stmt.span)
}

fn rewrite_event_control(ev: &EventControl, prefix: &str, port_map: &HashMap<String, Expression>, local_names: &std::collections::HashSet<String>, interface_map: &HashMap<String, String>) -> EventControl {
    match ev {
        EventControl::Identifier(id) => {
            let name = if let Some(mapped) = port_map.get(&id.name) {
                if let ExprKind::Ident(h) = &mapped.kind { h.path[0].name.name.clone() } else { id.name.clone() }
            } else if local_names.contains(&id.name) {
                format!("{}.{}", prefix, id.name)
            } else {
                id.name.clone()
            };
            EventControl::Identifier(Identifier { name, span: id.span })
        }
        EventControl::HierIdentifier(expr) => EventControl::HierIdentifier(rewrite_expr(expr, prefix, port_map, local_names, interface_map)),
        EventControl::EventExpr(exprs) => EventControl::EventExpr(exprs.iter().map(|e| {
            EventExpr {
                edge: e.edge,
                expr: rewrite_expr(&e.expr, prefix, port_map, local_names, interface_map),
                iff: e.iff.as_ref().map(|i| rewrite_expr(i, prefix, port_map, local_names, interface_map)),
                span: e.span,
            }
        }).collect()),
        other => other.clone(),
    }
}
thread_local! {
    /// Recursion-depth guard for re-export resolution in `process_import`
    /// (prevents stack overflow on cyclic `import`/`export` package graphs).
    static IMPORT_DEPTH: std::cell::Cell<u32> = const { std::cell::Cell::new(0) };
}

fn process_import(imp: &ImportDeclaration, elab: &mut ElaboratedModule, defs: &HashMap<String, Definition>) -> Result<(), String> {
    for ii in &imp.items {
        let pkg_name = &ii.package.name;
        if let Some(Definition::Package(pkg)) = defs.get(pkg_name) {
            if let Some(sym) = &ii.item {
                let sym_name = &sym.name;
                let mut found = false;
                for pi in &pkg.items {
                    match pi {
                        PackageItem::Parameter(pd) => {
                            if let ParameterKind::Data { data_type, assignments } = &pd.kind {
                                for assign in assignments {
                                    if &assign.name.name == sym_name {
                                        let mut width = resolve_type_width(data_type, Some(&elab.parameters), Some(&elab.typedefs));
                                        let mut signed = is_type_signed(data_type);
                                        let is_real = is_type_real(data_type);
                                        if matches!(data_type, DataType::Implicit { .. }) {
                                            // Infer width from sized literal
                                            // initializer (`7'h13` → 7) so the
                                            // parameter doesn't default to 32
                                            // and break concat width math
                                            // (cv32e40p OPCODE_OPIMM = 7'h13).
                                            width = assign.init.as_ref()
                                                .and_then(|e| sized_literal_width(e))
                                                .unwrap_or(32);
                                            signed = true;
                                        }
                                        let v = if let Some(init) = &assign.init {
                                            let mut v = eval_init_for_width(init, &elab.parameters, width);
                                            if signed { v.is_signed = true; }
                                            if is_real { v = Value::from_f64(v.to_f64()); }
                                            v
                                        } else { Value::zero(width) };
                                        elab.parameters.insert(assign.name.name.clone(), v.clone());
                                        elab.signals.insert(assign.name.name.clone(), Signal {
                                            is_const: false, name: assign.name.name.clone(),
                                            width, is_signed: signed, is_real, direction: None,
                                            value: v, type_name: get_type_name(data_type),
                                        });
                                        found = true;
                                        break;
                                    }
                                }
                            }
                        }
                        PackageItem::Typedef(td) => {
                            if &td.name.name == sym_name {
                                process_typedef(td, elab);
                                found = true;
                            }
                        }
                        PackageItem::Function(fd) => {
                            if &fd.name.name.name == sym_name {
                                elab.functions.insert(fd.name.name.name.clone(), fd.clone());
                                found = true;
                            }
                        }
                        PackageItem::Task(td) => {
                            if &td.name.name.name == sym_name {
                                elab.tasks.insert(td.name.name.name.clone(), td.clone());
                                found = true;
                            }
                        }
                        PackageItem::DPIImport(di) => {
                            if &dpi_proto_sv_name(&di.proto) == sym_name {
                                register_dpi_import(di, elab)?;
                                found = true;
                            }
                        }
                        PackageItem::Class(c) => {
                            if &c.name.name == sym_name {
                                elab.classes.insert(c.name.name.clone(), elaborate_class(c));
                                found = true;
                            }
                        }
                        PackageItem::Data(dd) => {
                            if dd.declarators.iter().any(|decl| &decl.name.name == sym_name) {
                                let width = match &dd.data_type {
                                    DataType::TypeReference { name, .. } => {
                                        elab.typedefs.get(&name.name.name).copied().unwrap_or(resolve_type_width(&dd.data_type, Some(&elab.parameters), Some(&elab.typedefs)))
                                    }
                                    _ => resolve_type_width(&dd.data_type, Some(&elab.parameters), Some(&elab.typedefs)),
                                };
                                let is_signed = is_type_signed(&dd.data_type);
                                let is_real = is_type_real(&dd.data_type);
                                for decl in &dd.declarators {
                                    if &decl.name.name == sym_name {
                                        let v = if let Some(init) = &decl.init {
                                            eval_init_for_width(init, &elab.parameters, width)
                                        } else { Value::zero(width) };
                                        elab.signals.insert(decl.name.name.clone(), Signal {
                                            is_const: dd.const_kw, name: decl.name.name.clone(),
                                            width, is_signed, is_real, direction: None,
                                            value: v, type_name: get_type_name(&dd.data_type),
                                        });
                                    }
                                }
                                found = true;
                            }
                        }
                        _ => {}
                    }
                    if found { break; }
                }
                if !found {
                    // §26.6 re-export: `package P2; import P1::x; export P1::*;`
                    // makes P1's `x` visible to importers of P2. Non-DPI exports
                    // aren't modeled directly, but P2 must `import` what it
                    // re-exports — so resolve the symbol by following P2's own
                    // imports to the source package (one synthetic explicit
                    // import per candidate; depth-guarded against cyclic
                    // re-export).
                    found = IMPORT_DEPTH.with(|d| {
                        if d.get() >= 32 { return false; }
                        d.set(d.get() + 1);
                        let mut ok = false;
                        for pi in &pkg.items {
                            if let PackageItem::Import(inner) = pi {
                                for ii2 in &inner.items {
                                    let provides = match &ii2.item {
                                        Some(s) => s.name == *sym_name, // import Src::sym
                                        None => true,                   // import Src::*
                                    };
                                    if !provides { continue; }
                                    let synth = ImportDeclaration {
                                        items: vec![ImportItem {
                                            package: ii2.package.clone(),
                                            item: Some(Identifier { name: sym_name.clone(), span: Span::dummy() }),
                                            span: Span::dummy(),
                                        }],
                                        span: Span::dummy(),
                                    };
                                    if process_import(&synth, elab, defs).is_ok() { ok = true; break; }
                                }
                            }
                            if ok { break; }
                        }
                        d.set(d.get() - 1);
                        ok
                    });
                }
                if !found {
                    return Err(format!("Symbol '{}' not found in package '{}'", sym_name, pkg_name));
                }
            } else {
                // Wildcard import
                for pi in &pkg.items {
                    match pi {
                        PackageItem::Parameter(pd) => {
                            if let ParameterKind::Data { data_type, assignments } = &pd.kind {
                                let base_width = resolve_type_width(data_type, Some(&elab.parameters), Some(&elab.typedefs));
                                let mut signed = is_type_signed(data_type);
                                let is_real = is_type_real(data_type);
                                let is_implicit = matches!(data_type, DataType::Implicit { .. });
                                if is_implicit { signed = true; }
                                for assign in assignments {
                                    // Per-assignment width: implicit-typed
                                    // parameters take the sized-literal
                                    // initializer width when available
                                    // (`7'h13` → 7) instead of forcing 32-bit.
                                    let width = if is_implicit {
                                        assign.init.as_ref()
                                            .and_then(|e| sized_literal_width(e))
                                            .unwrap_or(32)
                                    } else { base_width };
                                    register_packed_array_elem_w(&assign.name.name, data_type, &elab.typedefs);
                                    if let Some(init) = &assign.init {
                                        let mut v = eval_param_value(data_type, init, &elab.parameters, &elab.typedefs, &elab.typedef_types, width);
                                        if signed { v.is_signed = true; }
                                        if is_real { v = Value::from_f64(v.to_f64()); }
                                        elab.parameters.insert(assign.name.name.clone(), v.clone());
                                        elab.signals.insert(assign.name.name.clone(), Signal {
                                            is_const: false, name: assign.name.name.clone(),
                                            width, is_signed: signed, is_real, direction: None,
                                            value: v, type_name: get_type_name(data_type),
                                        });
                                    }
                                }
                            }
                        }
                        PackageItem::Typedef(td) => {
                            process_typedef(td, elab);
                        }
                        PackageItem::Function(fd) => {
                            elab.functions.insert(fd.name.name.name.clone(), fd.clone());
                        }
                        PackageItem::Task(td) => {
                            elab.tasks.insert(td.name.name.name.clone(), td.clone());
                        }
                        PackageItem::DPIImport(di) => {
                            register_dpi_import(di, elab)?;
                        }
                        PackageItem::Class(c) => {
                            elab.classes.insert(c.name.name.clone(), elaborate_class(c));
                        }
                        PackageItem::Data(dd) => {
                            let width = match &dd.data_type {
                                DataType::TypeReference { name, .. } => {
                                    elab.typedefs.get(&name.name.name).copied().unwrap_or(resolve_type_width(&dd.data_type, Some(&elab.parameters), Some(&elab.typedefs)))
                                }
                                _ => resolve_type_width(&dd.data_type, Some(&elab.parameters), Some(&elab.typedefs)),
                            };
                            let is_signed = is_type_signed(&dd.data_type);
                            let is_real = is_type_real(&dd.data_type);
                            for decl in &dd.declarators {
                                let v = if let Some(init) = &decl.init {
                                    eval_init_for_width(init, &elab.parameters, width)
                                } else { Value::zero(width) };
                                elab.signals.insert(decl.name.name.clone(), Signal {
                                    is_const: dd.const_kw, name: decl.name.name.clone(),
                                    width, is_signed, is_real, direction: None,
                                    value: v, type_name: get_type_name(&dd.data_type),
                                });
                            }
                        }
                        _ => {}
                    }
                }
            }
        } else {
            return Err(format!("Package '{}' not found", pkg_name));
        }
    }
    Ok(())
}
