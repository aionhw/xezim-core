//! Elaborator: converts parsed AST into a flat simulation model.
//! Resolves net/variable declarations, continuous assigns, always blocks.

use super::value::Value;
use crate::ast::binding::{Bound, DeclId, DeclKind};
use crate::ast::decl::*;
use crate::ast::expr::*;
use crate::ast::module::*;
use crate::ast::stmt::*;
use crate::ast::types::*;
use crate::ast::{Identifier, Span};
use crate::hasher::HashMap;
use crate::hasher::HashSet;
use crate::shared_names::{SharedName, SharedNameMap};
use std::rc::Rc;

pub(crate) mod array_params;
pub mod bind;
mod canonical;
pub(crate) mod class_scope_types;
mod const_context;
mod const_function_scope;
#[cfg(test)]
mod callable_sharing_tests;
pub(crate) mod constructor_forwarding;
mod context_maps;
#[cfg(test)]
mod context_maps_tests;
mod interface_arrays;
pub mod interface_ports;
mod module_class_scope;
mod net_drivers;
use net_drivers::{cont_assign_has_own_delay, cont_assign_net_span, fixed_net_cell};
pub use net_drivers::{
    apply_net_delays, continuous_assign_delay_select, resolve_bidirectional_switches,
    resolve_multi_driver_nets, unify_alias_nets,
};
mod param_prefix_index;
mod param_scope;
mod prepared_bodies;
#[cfg(test)]
mod prepared_bodies_tests;
pub(crate) mod unit_storage;
#[cfg(test)]
mod upward_scopes_tests;
pub(crate) mod relaxed_static;

mod aggregates;
mod array_assigns;
mod bind_inline;
mod body_checks;
mod class_checks;
mod class_constraints;
mod class_links;
mod class_spec_names;
mod class_typedefs;
mod classes;
mod collections;
mod const_exprs;
mod const_functions;
mod const_int;
mod const_tls;
mod const_values;
mod decl_shapes;
mod declaration_order;
mod declared_names;
mod defparams;
mod delays;
mod dpi_covergroups;
mod driver_conflicts;
mod enums;
mod expr_rewrite;
mod gates;
mod gen_renames;
mod generate;
mod hier_names;
mod legacy_initializers;
pub use legacy_initializers::{set_verilog_2005_initializers, verilog_2005_initializers};
pub(crate) use legacy_initializers::lower_verilog_2005_initializers;
mod ident_checks;
mod implicit_nets;
mod imports;
mod inline;
mod instance_arrays;
mod instance_items;
mod items;
mod literal_dims;
mod member_visibility;
mod module_body;
mod nested_scopes;
mod nettypes;
mod package_params;
mod packed_widths;
mod param_values;
mod patterns;
mod port_elision;
mod port_widths;
mod prepare;
mod resolver_state;
mod semantic_checks;
mod spans;
mod specify;
mod stmt_rewrite;
mod streaming_serde;
mod type_param_subst;
mod type_props;
mod type_queries;
mod typedefs;
mod upward_scopes;
mod walkers;

pub use aggregates::*;
pub use array_assigns::*;
use bind_inline::*;
use body_checks::*;
use class_checks::*;
use class_constraints::*;
pub use class_links::*;
pub use class_spec_names::*;
pub use class_typedefs::*;
pub use classes::*;
pub use collections::*;
use const_exprs::*;
pub(crate) use const_functions::*;
pub use const_int::*;
pub use const_tls::*;
pub use const_values::*;
pub use decl_shapes::*;
pub(crate) use declaration_order::*;
use declared_names::*;
use defparams::*;
pub use delays::*;
use dpi_covergroups::*;
pub use driver_conflicts::*;
pub use enums::*;
use expr_rewrite::*;
use gates::*;
pub use gen_renames::*;
pub use generate::*;
pub use hier_names::*;
use ident_checks::*;
use implicit_nets::*;
use imports::*;
pub use inline::*;
use instance_arrays::*;
use instance_items::*;
use items::*;
use literal_dims::*;
use member_visibility::*;
pub use module_body::*;
use nested_scopes::*;
pub use nettypes::*;
use package_params::*;
pub use packed_widths::*;
pub(crate) use param_values::*;
pub use patterns::*;
pub use port_elision::*;
use port_widths::*;
pub use prepare::*;
pub use semantic_checks::*;
pub use spans::*;
pub use specify::*;
pub use stmt_rewrite::*;
pub use type_param_subst::*;
pub use type_props::*;
pub use type_queries::*;
pub use typedefs::*;
use upward_scopes::*;
pub use walkers::*;

struct ScopeGuardLite<F: FnMut()>(F);
impl<F: FnMut()> Drop for ScopeGuardLite<F> {
    fn drop(&mut self) {
        (self.0)();
    }
}
fn scopeguard_lite<F: FnMut()>(f: F) -> ScopeGuardLite<F> {
    ScopeGuardLite(f)
}

thread_local! {
    static IPROF_SECT: std::cell::RefCell<std::collections::BTreeMap<&'static str, f64>> =
        std::cell::RefCell::new(std::collections::BTreeMap::new());
}
fn iprof_enabled() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var("XEZIM_INST_PROF").is_ok())
}
fn iprof_add(k: &'static str, d: std::time::Duration) {
    if !iprof_enabled() {
        return;
    }
    IPROF_SECT.with(|m| *m.borrow_mut().entry(k).or_insert(0.0) += d.as_secs_f64());
}
/// A section start for `iprof_since`: `None` (no clock read) unless
/// `XEZIM_INST_PROF` is set. The per-instance sections below are entered
/// once per instance, so unconditional clock reads cost measurable
/// elaboration time on designs with tens of thousands of instances.
fn iprof_now() -> Option<std::time::Instant> {
    iprof_enabled().then(std::time::Instant::now)
}
fn iprof_since(k: &'static str, t: Option<std::time::Instant>) {
    if let Some(t) = t {
        iprof_add(k, t.elapsed());
    }
}
pub fn iprof_dump() {
    IPROF_SECT.with(|m| {
        for (k, v) in m.borrow().iter() {
            eprintln!("[IPROF-SECT] {:<28} {:>10.3}s", k, v);
        }
    });
}

fn elab_trace_enabled() -> bool {
    // Read once: this is asked for every instantiation item.
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| {
        std::env::var("XEZIM_TRACE_ELAB")
            .map(|v| {
                let v = v.trim();
                !v.is_empty() && v != "0" && !v.eq_ignore_ascii_case("false")
            })
            .unwrap_or(false)
    })
}

/// `XEZIM_PEND_DBG`, read once (asked for every lazy block materialized).
fn pend_dbg_enabled() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var("XEZIM_PEND_DBG").is_ok())
}

/// XEZIM_TRACE_TYPE=name[,name...] — trace every WRITE to the typedef-width
/// tables and every type-width resolution whose key CONTAINS one of the
/// comma-separated substrings. Exists because a wrong width observed mid-
/// elaboration can be overwritten back to the right one before runtime, so
/// only a log of the full writer sequence identifies the offending site.
/// Parsed once; `None` when unset/empty so the untraced path is a single
/// OnceLock load and an early return before any formatting.
fn type_trace_patterns() -> Option<&'static Vec<String>> {
    static PATS: std::sync::OnceLock<Option<Vec<String>>> = std::sync::OnceLock::new();
    PATS.get_or_init(|| {
        let v = std::env::var("XEZIM_TRACE_TYPE").ok()?;
        let pats: Vec<String> = v
            .split(',')
            .map(str::trim)
            .filter(|s| !s.is_empty())
            .map(str::to_string)
            .collect();
        if pats.is_empty() { None } else { Some(pats) }
    })
    .as_ref()
}

/// True when `key` is traced. Callers whose `detail` is expensive to build
/// must check this FIRST — `type_trace` takes an already-formatted &str.
pub(crate) fn type_trace_on(key: &str) -> bool {
    match type_trace_patterns() {
        None => false,
        Some(pats) => pats.iter().any(|p| key.contains(p.as_str())),
    }
}

pub(crate) fn type_trace(site: &str, key: &str, detail: &str) {
    if type_trace_on(key) {
        eprintln!("[xezim][trace-type] {site} key={key} {detail}");
    }
}

/// XEZIM_TRACE_PARAM=name[,name...] — trace every WRITE to the global
/// parameter table and every constant-evaluation MISS (an identifier the
/// const evaluator could not resolve, which callers silently default to 0)
/// whose key CONTAINS one of the comma-separated substrings; `*` traces
/// everything. Exists because a `[N-1:0]` underflow (the "sane cap" clamp)
/// only names the parameter whose VALUE went negative — the actual defect is
/// usually an UPSTREAM name in its defining expression resolving to nothing,
/// and only the write/miss sequence identifies it.
fn param_trace_patterns() -> Option<&'static Vec<String>> {
    static PATS: std::sync::OnceLock<Option<Vec<String>>> = std::sync::OnceLock::new();
    PATS.get_or_init(|| {
        let v = std::env::var("XEZIM_TRACE_PARAM").ok()?;
        let pats: Vec<String> = v
            .split(',')
            .map(str::trim)
            .filter(|s| !s.is_empty())
            .map(str::to_string)
            .collect();
        if pats.is_empty() { None } else { Some(pats) }
    })
    .as_ref()
}

pub(crate) fn param_trace_on(key: &str) -> bool {
    match param_trace_patterns() {
        None => false,
        Some(pats) => pats.iter().any(|p| p == "*" || key.contains(p.as_str())),
    }
}

pub(crate) fn param_trace(site: &str, key: &str, detail: &str) {
    if param_trace_on(key) {
        eprintln!("[xezim][trace-param] {site} key={key} {detail}");
    }
}

/// Insert into a parameter-value table, logging the written value and the
/// value it replaced when the key is traced. Same result as
/// `HashMap::insert`; the untraced path is the plain insert.
/// Register each member of a packed-struct parameter under its dotted name
/// (`Cfg.VLEN`), sliced out of the struct's packed value. Nested members
/// come flattened (`A.B`), so the key is simply `<param>.<member path>`.
fn register_struct_param_members(
    mut insert: impl FnMut(String, Value),
    key: &str,
    val: &Value,
    fields: &[(String, u32, u32)],
) {
    for (member, off, w) in fields {
        if *w == 0 || off + w > val.width {
            continue;
        }
        insert(
            format!("{}.{}", key, member),
            val.range_select((off + w - 1) as usize, *off as usize),
        );
    }
}

fn params_insert_traced(
    map: &mut HashMap<String, Value>,
    site: u32,
    key: String,
    v: Value,
) -> Option<Value> {
    if param_trace_on(&key) {
        let prev = map.get(&key).map(|p| p.to_i64().unwrap_or(0));
        eprintln!(
            "[xezim][trace-param] insert@{site} key={key} value={} prev={:?}",
            v.to_i64().unwrap_or(0),
            prev
        );
    }
    map.insert(key, v)
}

/// Insert into a typedef-width table, logging the written width and the value
/// it replaced when the key is traced. Same result as `HashMap::insert`; the
/// untraced path does no tracing work.
/// A table typedef widths can be recorded in: the design's own
/// `TypedefTable` or a scratch `HashMap`.
trait WidthTable {
    fn insert_width(&mut self, key: String, w: u32) -> Option<u32>;
}

impl WidthTable for HashMap<String, u32> {
    fn insert_width(&mut self, key: String, w: u32) -> Option<u32> {
        self.insert(key, w)
    }
}

impl WidthTable for TypedefTable {
    fn insert_width(&mut self, key: String, w: u32) -> Option<u32> {
        self.insert_if_changed(key, w)
    }
}

/// Process-unique identity of one `TypedefTable` value (a clone or a
/// deserialized copy is a different table).
#[derive(Debug)]
struct TableIdent(u64);

impl Default for TableIdent {
    fn default() -> Self {
        static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(1);
        TableIdent(NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed))
    }
}

/// A name-keyed table that remembers which keys each change touched, so a
/// thread-local snapshot of it (`TYPEDEFS_TLS`, `FUNCS_TLS`) is brought up to
/// date by replaying only the changes since it was taken instead of copying
/// the whole table after every change. Reads go through `Deref` to the map;
/// every write goes through the methods below. Serialized exactly as the
/// plain map.
#[derive(Debug, serde::Serialize, serde::Deserialize)]
#[serde(transparent)]
pub struct LoggedMap<V> {
    map: Rc<HashMap<String, V>>,
    #[serde(skip)]
    ident: TableIdent,
    #[serde(skip)]
    log: Vec<String>,
}

/// A name-keyed table whose copies share one map until one of them is
/// written (copy on write). Reads and writes go through `Deref` and
/// `DerefMut` to the map; serialized exactly as the plain map. Typedef
/// bodies are kept this way so the constant evaluator's snapshot and its
/// per-call shells share the table instead of copying it (#721).
#[derive(Debug, serde::Serialize, serde::Deserialize)]
#[serde(transparent)]
pub struct SharedMap<V>(Rc<HashMap<String, V>>);

impl<V> Default for SharedMap<V> {
    fn default() -> Self {
        Self(Rc::new(HashMap::default()))
    }
}

impl<V> Clone for SharedMap<V> {
    fn clone(&self) -> Self {
        Self(Rc::clone(&self.0))
    }
}

impl<V> std::ops::Deref for SharedMap<V> {
    type Target = HashMap<String, V>;
    fn deref(&self) -> &HashMap<String, V> {
        &self.0
    }
}

impl<V: Clone> std::ops::DerefMut for SharedMap<V> {
    fn deref_mut(&mut self) -> &mut HashMap<String, V> {
        Rc::make_mut(&mut self.0)
    }
}

impl<V> From<HashMap<String, V>> for SharedMap<V> {
    fn from(map: HashMap<String, V>) -> Self {
        Self(Rc::new(map))
    }
}

impl<'a, V> IntoIterator for &'a SharedMap<V> {
    type Item = (&'a String, &'a V);
    type IntoIter = std::collections::hash_map::Iter<'a, String, V>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

/// Typedef name -> width.
pub type TypedefTable = LoggedMap<u32>;
/// Subroutine name -> declaration.
pub type FuncTable = LoggedMap<FunctionDeclaration>;

impl<V: Clone> Default for LoggedMap<V> {
    fn default() -> Self {
        Self::from_map(HashMap::default())
    }
}

impl<V: Clone> Clone for LoggedMap<V> {
    fn clone(&self) -> Self {
        Self::from_shared(Rc::clone(&self.map))
    }
}

impl<V> std::ops::Deref for LoggedMap<V> {
    type Target = HashMap<String, V>;
    fn deref(&self) -> &HashMap<String, V> {
        &self.map
    }
}

impl<V: Clone> LoggedMap<V> {
    pub fn from_map(map: HashMap<String, V>) -> Self {
        Self::from_shared(Rc::new(map))
    }

    /// Read-only constant-evaluation shells share the existing function
    /// snapshot. A later insertion detaches it before mutating (§13.4.3).
    fn from_shared(map: Rc<HashMap<String, V>>) -> Self {
        Self {
            map,
            ident: TableIdent::default(),
            log: Vec::new(),
        }
    }

    pub fn as_map(&self) -> &HashMap<String, V> {
        &self.map
    }

    /// The map itself, shared: a snapshot that costs nothing until this
    /// table is next written (§13.4.3 constant-function shells, #721).
    fn shared_map(&self) -> Rc<HashMap<String, V>> {
        Rc::clone(&self.map)
    }

    /// The plain map, for bulk in-place edits (rewrap with `from_map`).
    pub fn into_map(self) -> HashMap<String, V> {
        Rc::try_unwrap(self.map).unwrap_or_else(|shared| (*shared).clone())
    }

    pub fn insert(&mut self, key: String, value: V) -> Option<V> {
        self.log.push(key.clone());
        Rc::make_mut(&mut self.map).insert(key, value)
    }

    pub fn remove(&mut self, key: &str) -> Option<V> {
        // Avoid detaching a read-only snapshot for an absent-key no-op.
        if !self.map.contains_key(key) {
            return None;
        }
        let prev = Rc::make_mut(&mut self.map).remove(key);
        if prev.is_some() {
            self.log.push(key.to_string());
        }
        prev
    }

    /// `entry(key).or_insert_with(value)`; true when it inserted.
    pub fn insert_if_absent_with(&mut self, key: String, value: impl FnOnce() -> V) -> bool {
        if self.map.contains_key(&key) {
            return false;
        }
        self.insert(key, value());
        true
    }

    /// `entry(key).or_insert(value)`; true when it inserted.
    pub fn insert_if_absent(&mut self, key: String, value: V) -> bool {
        self.insert_if_absent_with(key, || value)
    }

    /// Bring `snap` from this table's state after `seen` logged changes to
    /// its current state (see `LoggedMap`).
    fn replay_into(&self, snap: &mut HashMap<String, V>, seen: usize)
    where
        V: Clone,
    {
        for key in &self.log[seen..] {
            match self.map.get(key) {
                Some(v) => {
                    snap.insert(key.clone(), v.clone());
                }
                None => {
                    snap.remove(key);
                }
            }
        }
    }
}

impl LoggedMap<u32> {
    /// Same return value as `insert`, but an unchanged width leaves both
    /// the table and its change-log position intact. Wildcard imports bind
    /// large package type tables twice per instance (#721); recording those
    /// no-ops retained one key allocation per typedef per instance forever.
    pub fn insert_if_changed(&mut self, key: String, width: u32) -> Option<u32> {
        if self.map.get(&key) == Some(&width) {
            return Some(width);
        }
        self.insert(key, width)
    }
}

fn typedefs_insert_traced(
    map: &mut impl WidthTable,
    site: &str,
    key: String,
    w: u32,
) -> Option<u32> {
    if !type_trace_on(&key) {
        return map.insert_width(key, w);
    }
    let prev = map.insert_width(key.clone(), w);
    let prev_s = prev
        .map(|p| p.to_string())
        .unwrap_or_else(|| "<none>".into());
    type_trace(site, &key, &format!("width={w} prev={prev_s}"));
    prev
}

/// TYPEDEFS_TLS snapshot refreshes: when tracing is enabled, report each
/// traced pattern's EXACT-key width in the map being installed — O(patterns)
/// lookups per refresh, nothing at all when the variable is unset. A stale
/// snapshot is indistinguishable from a bad write without this.
fn type_trace_tls_refresh(at: &str, map: &HashMap<String, u32>) {
    let Some(pats) = type_trace_patterns() else {
        return;
    };
    for p in pats {
        let w_s = map
            .get(p.as_str())
            .map(|w| w.to_string())
            .unwrap_or_else(|| "<absent>".into());
        type_trace("tls:refresh", p, &format!("at={at} width={w_s}"));
    }
}

/// A resolved signal in the simulation model.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct Signal {
    pub name: SharedName,
    pub width: u32,
    pub is_signed: bool,
    pub is_real: bool,
    pub is_const: bool,
    pub direction: Option<PortDirection>,
    pub value: Value,
    /// Name of the data type (e.g. class name).
    pub type_name: Option<SharedName>,
}

/// §28.12: one driver of a net whose drivers carry drive strengths, kept so
/// `%v` (§21.2.1.5) can report the strength the net resolves to.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct StrengthDriver {
    /// The driven value.
    pub value: Expression,
    /// A tristate primitive's control (`ctl ? value : 'z`); `None` when the
    /// driver is always on.
    pub ctl: Option<Expression>,
    /// Strength level, 0 (highz) to 7 (supply), of a driven 0 and of a
    /// driven 1.
    pub s0: u8,
    pub s1: u8,
}

/// Expressions in global ticks for the rise, fall, and turn-off delays.
pub type DelayExpressions = Box<[Option<Expression>; 3]>;

/// Rarely populated delay metadata for a [`ContinuousAssignment`], boxed out
/// of the inline struct so undelayed and single-delay assignments pay nothing
/// for it (aionhw/xezim#721).
#[derive(Debug, Clone, Default, serde::Serialize, serde::Deserialize)]
pub struct ContinuousAssignDelays {
    /// §10.3.3 fall delay (transition to 0) when it differs in form from
    /// `delay`; `None` for the single-delay form.
    pub delay_fall: Option<u64>,
    /// §10.3.3 turn-off delay (transition to z).
    pub delay_off: Option<u64>,
    /// §28.16 fall value of the primitive this assignment was lowered from,
    /// kept for the split of a net's drivers into a stage each. Separate from
    /// `delay_fall`: a primitive that stays the only driver of its net keeps
    /// its fall delay in `gate_fall_delays`, including net-delay lowering.
    pub gate_delay_fall: Option<u64>,
    /// Runtime delay operands when any operand depends on simulation state.
    pub delay_exprs: Option<DelayExpressions>,
    /// §10.3.3 / §28.16: physical (low bit, width, vector shape) before
    /// driver widening. A bit-select is scalar; a width-one part is vector.
    pub delay_select: Option<(u32, u32, bool)>,
}

impl ContinuousAssignDelays {
    fn is_empty(&self) -> bool {
        self.delay_fall.is_none()
            && self.delay_off.is_none()
            && self.gate_delay_fall.is_none()
            && self.delay_exprs.is_none()
            && self.delay_select.is_none()
    }
}

/// Optional source-origin and rare delay metadata for a [`ContinuousAssignment`].
///
/// Synthesized assignments (port connections, gate primitives, delayed nets)
/// have neither an origin nor rare delays and leave `extras` as `None`. Source
/// `assign` statements without rare delays allocate only this 40-byte record
/// rather than the full delay table (aionhw/xezim#721).
#[derive(Debug, Clone, Default, serde::Serialize, serde::Deserialize)]
pub struct ContinuousAssignExtras {
    /// A continuous assignment the source spells out (an `assign`, or a net
    /// declaration assignment): the span of that statement and the instance
    /// scope it was elaborated in (`""` for the top). `None` for the ones
    /// elaboration synthesizes (port connections, gate primitives, delayed
    /// nets). Code coverage counts only the former. The assignments of one
    /// instance hold one scope string between them (aionhw/xezim#721).
    #[serde(default)]
    pub origin: Option<(crate::ast::Span, std::sync::Arc<str>)>,
    #[serde(default)]
    pub delays: Option<Box<ContinuousAssignDelays>>,
}

impl ContinuousAssignExtras {
    fn is_empty(&self) -> bool {
        self.origin.is_none() && self.delays.is_none()
    }
}

/// A continuous assignment: assign lhs = rhs.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct ContinuousAssignment {
    pub lhs: Expression,
    pub rhs: Expression,
    /// Delay in ticks (rise delay of the `#(rise, fall[, turnoff])` form).
    pub delay: u64,
    /// §23.3.3: this assign is an instance PORT CONNECTION emitted at
    /// inline time — its RHS names live in the PARENT scope by
    /// construction. The simulator must not apply the child scope hint to
    /// them: an actual like `.d(d ^ 1)` whose operand shares the FORMAL's
    /// name otherwise resolved to the child's own port net (`u1.d = u1.d
    /// ^ 1`, a self-loop that read x forever).
    pub rhs_parent_scoped: bool,
    #[serde(default)]
    pub extras: Option<Box<ContinuousAssignExtras>>,
}

impl ContinuousAssignment {
    pub fn plain(lhs: Expression, rhs: Expression) -> Self {
        Self {
            lhs,
            rhs,
            delay: 0,
            rhs_parent_scoped: false,
            extras: None,
        }
    }

    pub fn with_delay(lhs: Expression, rhs: Expression, delay: u64) -> Self {
        Self {
            lhs,
            rhs,
            delay,
            rhs_parent_scoped: false,
            extras: None,
        }
    }

    pub fn with_extras(
        lhs: Expression,
        rhs: Expression,
        delay: u64,
        rhs_parent_scoped: bool,
        delay_fall: Option<u64>,
        delay_off: Option<u64>,
        gate_delay_fall: Option<u64>,
        delay_exprs: Option<DelayExpressions>,
        delay_select: Option<(u32, u32, bool)>,
        origin: Option<(crate::ast::Span, std::sync::Arc<str>)>,
    ) -> Self {
        let delays = if delay_fall.is_some()
            || delay_off.is_some()
            || gate_delay_fall.is_some()
            || delay_exprs.is_some()
            || delay_select.is_some()
        {
            Some(Box::new(ContinuousAssignDelays {
                delay_fall,
                delay_off,
                gate_delay_fall,
                delay_exprs,
                delay_select,
            }))
        } else {
            None
        };
        let extras = if origin.is_some() || delays.is_some() {
            Some(Box::new(ContinuousAssignExtras { origin, delays }))
        } else {
            None
        };
        Self {
            lhs,
            rhs,
            delay,
            rhs_parent_scoped,
            extras,
        }
    }

    fn delays(&self) -> Option<&ContinuousAssignDelays> {
        self.extras.as_deref().and_then(|e| e.delays.as_deref())
    }

    fn delays_mut(&mut self) -> &mut ContinuousAssignDelays {
        self.extras
            .get_or_insert_with(|| Box::new(ContinuousAssignExtras::default()))
            .delays
            .get_or_insert_with(|| Box::new(ContinuousAssignDelays::default()))
    }

    fn prune_extras(&mut self) {
        if let Some(extras) = self.extras.as_deref_mut() {
            if extras.delays.as_deref().is_some_and(ContinuousAssignDelays::is_empty) {
                extras.delays = None;
            }
            if extras.is_empty() {
                self.extras = None;
            }
        }
    }

    pub fn delay_fall(&self) -> Option<u64> {
        self.delays().and_then(|d| d.delay_fall)
    }

    pub fn delay_off(&self) -> Option<u64> {
        self.delays().and_then(|d| d.delay_off)
    }

    pub fn gate_delay_fall(&self) -> Option<u64> {
        self.delays().and_then(|d| d.gate_delay_fall)
    }

    pub fn delay_exprs(&self) -> Option<&DelayExpressions> {
        self.delays().and_then(|d| d.delay_exprs.as_ref())
    }

    pub fn delay_select(&self) -> Option<(u32, u32, bool)> {
        self.delays().and_then(|d| d.delay_select)
    }

    pub fn origin(&self) -> Option<&(crate::ast::Span, std::sync::Arc<str>)> {
        self.extras.as_deref().and_then(|e| e.origin.as_ref())
    }

    pub fn set_delay_fall(&mut self, value: Option<u64>) {
        if value.is_some() {
            self.delays_mut().delay_fall = value;
        } else if let Some(d) = self.extras.as_deref_mut().and_then(|e| e.delays.as_deref_mut()) {
            d.delay_fall = None;
            self.prune_extras();
        }
    }

    pub fn set_delay_off(&mut self, value: Option<u64>) {
        if value.is_some() {
            self.delays_mut().delay_off = value;
        } else if let Some(d) = self.extras.as_deref_mut().and_then(|e| e.delays.as_deref_mut()) {
            d.delay_off = None;
            self.prune_extras();
        }
    }

    pub fn set_gate_delay_fall(&mut self, value: Option<u64>) {
        if value.is_some() {
            self.delays_mut().gate_delay_fall = value;
        } else if let Some(d) = self.extras.as_deref_mut().and_then(|e| e.delays.as_deref_mut()) {
            d.gate_delay_fall = None;
            self.prune_extras();
        }
    }

    pub fn set_delay_exprs(&mut self, value: Option<DelayExpressions>) {
        if value.is_some() {
            self.delays_mut().delay_exprs = value;
        } else if let Some(d) = self.extras.as_deref_mut().and_then(|e| e.delays.as_deref_mut()) {
            d.delay_exprs = None;
            self.prune_extras();
        }
    }

    pub fn take_delay_exprs(&mut self) -> Option<DelayExpressions> {
        let taken = self
            .extras
            .as_deref_mut()
            .and_then(|e| e.delays.as_deref_mut())
            .and_then(|d| d.delay_exprs.take());
        if taken.is_some() {
            self.prune_extras();
        }
        taken
    }

    pub fn set_delay_select(&mut self, value: Option<(u32, u32, bool)>) {
        if value.is_some() {
            self.delays_mut().delay_select = value;
        } else if let Some(d) = self.extras.as_deref_mut().and_then(|e| e.delays.as_deref_mut()) {
            d.delay_select = None;
            self.prune_extras();
        }
    }

    pub fn set_origin(&mut self, value: Option<(crate::ast::Span, std::sync::Arc<str>)>) {
        if value.is_some() {
            self.extras
                .get_or_insert_with(|| Box::new(ContinuousAssignExtras::default()))
                .origin = value;
        } else if let Some(extras) = self.extras.as_deref_mut() {
            extras.origin = None;
            self.prune_extras();
        }
    }

    pub fn take_origin(&mut self) -> Option<(crate::ast::Span, std::sync::Arc<str>)> {
        let taken = self.extras.as_deref_mut().and_then(|e| e.origin.take());
        if taken.is_some() {
            self.prune_extras();
        }
        taken
    }
}

impl ContinuousAssignment {
    /// Keep the original driver context on each unpacked array element.
    pub fn inherit_driver_metadata(&mut self, driver: &Self) {
        self.set_delay_fall(driver.delay_fall());
        self.set_delay_off(driver.delay_off());
        self.set_delay_exprs(driver.delay_exprs().cloned());
        self.set_origin(driver.origin().cloned());
        self.rhs_parent_scoped = driver.rhs_parent_scoped;
    }
}

/// The `ContinuousAssignment::origin` scope of the top module, one string
/// for all of its assignments.
fn top_origin_scope() -> std::sync::Arc<str> {
    thread_local! {
        static TOP: std::sync::Arc<str> = std::sync::Arc::from("");
    }
    TOP.with(std::sync::Arc::clone)
}

/// IEEE 1800-2017 §29 User-Defined Primitive instance, flattened during
/// elaboration. Terminal expressions are already rewritten into parent scope,
/// so the simulator resolves them to signal IDs the same way it resolves a
/// continuous-assign LHS/RHS.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct UdpInstance {
    /// Primitive (UDP) name, for diagnostics.
    pub udp_name: String,
    /// Full instance path (e.g. `top.u_dff`), for diagnostics.
    pub inst_path: String,
    /// Output terminal net (the single UDP output).
    pub output: Expression,
    /// Input terminal nets, declaration order.
    pub inputs: Vec<Expression>,
    /// `reg out;` ⇒ sequential UDP.
    pub is_sequential: bool,
    /// §29.6 initial start state ('0'/'1'/'x'); default 'x'.
    pub init: Option<char>,
    /// Truth table.
    pub rows: Vec<crate::ast::decl::UdpTableRow>,
    /// Instance delay in simulation ticks (0 = none): the rise delay, and
    /// every delay when `delay_fall` is None.
    #[serde(default)]
    pub delay: u64,
    /// §28.16/§29.3: the fall delay of a `#(rise, fall)` instance delay;
    /// None when one value was given (it applies to every transition).
    #[serde(default)]
    pub delay_fall: Option<u64>,
    pub span: crate::ast::Span,
}

/// IEEE 1800-2017 §31 timing check of one instance, flattened: terminals,
/// conditions and the notifier are rewritten into the parent namespace (the
/// simulator resolves them like a UDP terminal), and the limit and flag
/// arguments are evaluated.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct TimingCheckInstance {
    /// System task name (`$setuphold`).
    pub name: String,
    /// Instance scope (`u_a.u_b`), empty for the top module.
    pub scope: String,
    /// Module definition (locates its source file for diagnostics).
    pub def_name: String,
    /// Arguments in source order, `None` where omitted.
    pub args: Vec<Option<crate::ast::decl::TimingCheckArg>>,
    /// Per argument: a limit in simulation ticks, or an integer flag
    /// (`timing_check_limit_args` / `timing_check_flag_args`).
    pub consts: Vec<Option<i64>>,
    pub span: crate::ast::Span,
}

/// One §30.4 module path into a destination net, flattened.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct ModulePath {
    /// §30.5 delay per output transition, in ticks, in Table 30-3 order:
    /// 0->1, 1->0, 0->z, z->1, 1->z, z->0, 0->x, x->1, 1->x, x->0, x->z,
    /// z->x (see `path_transition_index`).
    pub delays: [u64; 12],
    /// Input terminals, flat names.
    pub srcs: Vec<String>,
    /// §30.4.4 condition in the flat namespace; `None` = always enabled.
    pub cond: Option<Expression>,
    /// §30.4.4.3 `ifnone`: enabled only while no conditional path from the
    /// same input is.
    pub ifnone: bool,
}

/// An always block for combinatorial logic.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct AlwaysBlock {
    pub kind: AlwaysKind,
    pub stmt: Statement,
    /// Instance scope this block was inlined under (e.g. "u_a.u_b"), empty
    /// for the top module. The simulator uses it to resolve the block's
    /// module timescale for $time/%t — deriving it from a sensitivity
    /// signal's name fails when a port-connected clock collapses to the
    /// parent's signal.
    #[serde(default)]
    pub scope: String,
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
        InitialBlock {
            stmt,
            scope: String::new(),
        }
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
// per instance). port_map is per-instance and shared with the instance's
// input-port actuals; interface_map is per-instance owned.
//
// A streaming consumer (the simulator's bytecode compiler) is expected to
// drain `pending_*` one block at a time via the `drain_pending_*` helpers,
// compile-and-drop, so the materialized AST never co-exists in bulk.
//
// For non-streaming callers, `ElaboratedModule::materialize_pending()`
// performs a non-streaming drain into `always_blocks`/`initial_blocks`/
// `continuous_assigns` — preserving prior semantics at the cost of peak.
// ----------------------------------------------------------------------------

/// §23.3.3: an input port whose reads inside the instance were renamed to
/// its actual. The simulator needs the pair back (`formal` is the port's
/// hierarchical name) to start the processes that read the port at time 0.
///
/// The actual is not copied: it is the entry of the instance's port table
/// (`RewriteCtx::port_map`), which the instance's deferred bodies hold
/// anyway. A design loaded from an artifact owns each actual instead; the
/// serialized form is the `(formal, actual, two_state)` tuple either way.
#[derive(Debug, Clone)]
pub struct InputPortActual {
    formal: String,
    actual: InputActualExpr,
    two_state: bool,
}

#[derive(Debug, Clone)]
enum InputActualExpr {
    Owned(Box<Expression>),
    /// The entry of `ports` for the port name `formal[name_start..]`.
    Shared {
        ports: Rc<HashMap<String, Expression>>,
        name_start: usize,
    },
}

impl InputPortActual {
    /// An actual that belongs to this record alone.
    pub fn owned(formal: String, actual: Expression, two_state: bool) -> Self {
        InputPortActual {
            formal,
            actual: InputActualExpr::Owned(Box::new(actual)),
            two_state,
        }
    }

    /// The actual `ports` holds for the port name `formal[name_start..]`.
    /// The entry must exist.
    fn shared(
        formal: String,
        name_start: usize,
        ports: Rc<HashMap<String, Expression>>,
        two_state: bool,
    ) -> Self {
        debug_assert!(ports.contains_key(&formal[name_start..]));
        InputPortActual {
            formal,
            actual: InputActualExpr::Shared { ports, name_start },
            two_state,
        }
    }

    /// The port's hierarchical name (`u.v.port`).
    pub fn formal(&self) -> &str {
        &self.formal
    }

    /// The connected expression, in the parent's scope.
    pub fn actual(&self) -> &Expression {
        match &self.actual {
            InputActualExpr::Owned(actual) => actual,
            InputActualExpr::Shared { ports, name_start } => &ports[&self.formal[*name_start..]],
        }
    }

    /// Whether the formal starts at 0 (a 2-state type) rather than x/z (§6.8).
    pub fn two_state(&self) -> bool {
        self.two_state
    }

    /// Whether `self` and `other` read their actuals from one port table.
    pub fn shares_table_with(&self, other: &Self) -> bool {
        match (&self.actual, &other.actual) {
            (
                InputActualExpr::Shared { ports: a, .. },
                InputActualExpr::Shared { ports: b, .. },
            ) => Rc::ptr_eq(a, b),
            _ => false,
        }
    }

    /// Whether the actual is the entry of `ports` itself, not a copy of it.
    pub fn reads_table(&self, ports: &Rc<HashMap<String, Expression>>) -> bool {
        matches!(&self.actual, InputActualExpr::Shared { ports: own, .. } if Rc::ptr_eq(own, ports))
    }
}

impl serde::Serialize for InputPortActual {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        (&self.formal, self.actual(), self.two_state).serialize(serializer)
    }
}

impl<'de> serde::Deserialize<'de> for InputPortActual {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let (formal, actual, two_state) =
            <(String, Expression, bool) as serde::Deserialize>::deserialize(deserializer)?;
        Ok(InputPortActual::owned(formal, actual, two_state))
    }
}

/// Per-instance context needed to materialize a deferred procedural body.
/// Held lightweight: cloning is cheap because shared structures sit behind Rc.
#[derive(Debug, Clone)]
pub struct RewriteCtx {
    pub prefix: String,
    /// `prefix` without its trailing dot: the scope every continuous
    /// assignment of the instance records as its origin, held once.
    pub origin_scope: std::sync::Arc<str>,
    /// Port name → connecting expression in the parent scope. Per-instance
    /// (different connections per instantiation). The one table the
    /// instance's own inlining rewrote with, shared rather than copied; the
    /// instance's `InputPortActual`s read the same table (#721).
    pub port_map: Rc<HashMap<String, Expression>>,
    /// Names declared locally inside the submodule. Shared across siblings of
    /// the same submodule via the prepared-items cache. Uses
    /// `std::collections::HashSet` to match `rewrite_expr`/`rewrite_stmt`
    /// signatures (which deliberately don't take ahash for hash determinism
    /// across the rewrite boundary).
    pub local_names: std::rc::Rc<std::collections::HashSet<String>>,
    /// Interface-port substitutions (interface name → parent path). Per-branch
    /// in the recursion tree; cloning the small map is cheap.
    pub interface_map: HashMap<String, String>,
    /// This instance's TYPE-PARAMETER bindings (name → resolved concrete
    /// DataType), overrides and defaults alike. Behavioral items are inlined
    /// per instance, but the global `typedef_types` entry for a type param is
    /// restored after each instance — so a `CLASS_T obj;` in an initial block
    /// had no binding left at run time and `obj = new()` never constructed.
    /// `materialize` substitutes these into cloned statements' declarations.
    pub type_binds: Rc<HashMap<String, DataType>>,
    /// Packed width of each bound type parameter — folded into `$bits(T)`
    /// while this instance's items are rewritten (see `TYPE_BIND_WIDTHS_TLS`).
    pub type_bind_widths: Rc<HashMap<String, u32>>,
    /// What each bound type parameter answers to the §20.7 array queries
    /// (`$left(T)`, `$size(T)`, …), folded alongside `$bits(T)`.
    pub type_bind_queries: Rc<HashMap<String, TypeQueryDims>>,
    /// Name of the module/interface definition this body came from — the
    /// file a diagnostic's span belongs to.
    pub owner: String,
    /// §23.8: the design's scope tree (`ElaboratedModule::upward_scopes`),
    /// installed for `upward_scope_rewrite` while this body is rewritten.
    pub upward: Rc<std::cell::RefCell<UpwardScopes>>,
}

/// Per-instance context needed to materialize a deferred instance-scoped
/// function or task body (#193). Sibling callables of one instance share one `Rc`.
#[derive(Debug, Clone)]
pub struct CallableRewriteCtx {
    pub ctx: Rc<RewriteCtx>,
    /// Unpacked-array typedef names declared locally in this instance that
    /// must be instance-prefixed in local declaration types (§6.18/§23.9).
    pub local_array_typedefs: Option<Rc<std::collections::HashSet<String>>>,
}

impl CallableRewriteCtx {
    /// Rewrite `source_items` into this instance's lexical scope, applying
    /// formal/local shadowing, port/interface substitution, local unpacked-
    /// array typedef scoping, and type-parameter substitution. Respects the
    /// caller's `ast::cache` scope-cache mode (`without_scope_caches` or
    /// `with_fresh_scope_caches`).
    pub fn materialize_body(
        &self,
        ports: &[crate::ast::decl::FunctionPort],
        source_items: &[Statement],
    ) -> Vec<Statement> {
        self.rewrite_body(ports, source_items, false)
    }

    /// The rewrite of `materialize_body` done while the instance is inlined,
    /// for a body `callable_body_names_scopes` keeps out of the shared form:
    /// only the statement rewrite makes private copies, as it always did.
    fn rewrite_body_now(
        &self,
        ports: &[crate::ast::decl::FunctionPort],
        source_items: &[Statement],
    ) -> Vec<Statement> {
        self.rewrite_body(ports, source_items, true)
    }

    fn rewrite_body(
        &self,
        ports: &[crate::ast::decl::FunctionPort],
        source_items: &[Statement],
        private_rewrite: bool,
    ) -> Vec<Statement> {
        let mut fn_locals = (*self.ctx.local_names).clone();
        for p in ports {
            fn_locals.remove(&p.name.name);
        }
        for n in stmt_list_declared_names(source_items) {
            fn_locals.remove(n);
        }
        let formal_names: Vec<&str> = ports.iter().map(|p| p.name.name.as_str()).collect();
        let rewrite = || {
            with_shadowed(
                &formal_names,
                &self.ctx.port_map,
                &fn_locals,
                |ports, locals| {
                    rewrite_stmt_list_scoped(
                        source_items,
                        &self.ctx.prefix,
                        ports,
                        locals,
                        &self.ctx.interface_map,
                    )
                },
            )
        };
        let mut items = with_type_bind_tls(&self.ctx, || {
            if private_rewrite {
                crate::ast::cache::without_scope_caches(rewrite)
            } else {
                rewrite()
            }
        });
        if let Some(lat) = &self.local_array_typedefs {
            let prefix = &self.ctx.prefix;
            let scope_array_typedef = |dt: &DataType| -> Option<DataType> {
                match dt {
                    DataType::TypeReference {
                        name,
                        dimensions,
                        type_args,
                        span,
                    } if name.scopes.is_empty()
                        && dimensions.is_empty()
                        && lat.contains(&name.name.name) =>
                    {
                        let mut nn = name.clone();
                        nn.name.name = cat2(prefix, &name.name.name);
                        Some(DataType::TypeReference {
                            name: nn,
                            dimensions: dimensions.clone(),
                            type_args: type_args.clone(),
                            span: *span,
                        })
                    }
                    _ => None,
                }
            };
            scope_local_decl_types(&mut items, &scope_array_typedef);
        }
        substitute_type_params_stmts(items, &self.ctx.type_binds, &self.ctx.prefix)
    }
}

/// §23.8, §23.8.1: whether rewriting `items` into an instance consults the
/// instance tree: a dotted or rooted name or a member access, which the
/// rewrite may resolve upward or downward through the hierarchy, a call the
/// binder left to the hierarchy, or a hierarchical `disable`. The tree
/// grows while the design is inlined, and an instance joins it only after
/// its own subroutines were rewritten, so such a body is rewritten into its
/// instance right away, against the tree as it stands then (#193).
fn callable_body_names_scopes(items: &[Statement]) -> bool {
    // `for_each_stmt_expr` reaches the expressions of nested statements; a
    // `disable` or a local `typedef` at any depth needs its own walk.
    fn statement_names_scopes(s: &Statement) -> bool {
        use crate::ast::stmt::StatementKind as K;
        let nested = |st: &Statement| statement_names_scopes(st);
        match &s.kind {
            K::Disable(h) => h.path.len() >= 2 || h.root.is_some(),
            K::Typedef(_) => true,
            K::SeqBlock { stmts, .. } | K::ParBlock { stmts, .. } => stmts.iter().any(nested),
            K::If {
                then_stmt,
                else_stmt,
                ..
            } => nested(then_stmt) || else_stmt.as_deref().is_some_and(nested),
            K::Case { items, .. } => items.iter().any(|it| nested(&it.stmt)),
            K::RandCase { items } => items.iter().any(|(_, st)| nested(st)),
            K::Assertion(a) => [&a.action, &a.else_action]
                .into_iter()
                .flatten()
                .any(|st| nested(st)),
            K::WaitOrder { pass, fail, .. } => {
                [pass, fail].into_iter().flatten().any(|st| nested(st))
            }
            K::For { body, .. }
            | K::Foreach { body, .. }
            | K::ForeachTail { body, .. }
            | K::Forever { body }
            | K::ForeverTail { body }
            | K::RsAction { body }
            | K::While { body, .. }
            | K::DoWhile { body, .. }
            | K::Repeat { body, .. }
            | K::TimingControl { stmt: body, .. }
            | K::Wait { stmt: body, .. } => nested(body),
            _ => false,
        }
    }
    items.iter().any(|s| {
        let mut hit = statement_names_scopes(s);
        if !hit {
            for_each_stmt_expr(s, &mut |e| {
                for_each_sub_expr(e, &mut |x| match &x.kind {
                    ExprKind::Ident(h)
                        if h.path.len() >= 2 || h.root.is_some() || h.bound.is_upward() =>
                    {
                        hit = true
                    }
                    ExprKind::MemberAccess { .. } => hit = true,
                    _ => {}
                })
            });
        }
        hit
    })
}

#[derive(Debug, Clone)]
pub struct PendingAlways {
    pub kind: AlwaysKind,
    /// Source Statement, shared with the prepared-items cache so 26 sibling
    /// instances of the same submodule all point at the same Rc<Statement>.
    pub source: std::rc::Rc<Statement>,
    pub ctx: std::rc::Rc<RewriteCtx>,
    /// §21.2.1.7: generate block scope for %m hierarchy. If this always block
    /// was inside a generate block, this contains the generate block's scope name.
    pub gen_scope: String,
}

#[derive(Debug, Clone)]
pub struct PendingInitial {
    pub source: std::rc::Rc<Statement>,
    pub ctx: std::rc::Rc<RewriteCtx>,
    /// §21.2.1.7: generate block scope for %m hierarchy. If this initial block
    /// was inside a generate block, this contains the generate block's scope name.
    pub gen_scope: String,
}

#[derive(Debug, Clone)]
pub struct PendingContAssign {
    pub lhs_source: std::rc::Rc<Expression>,
    /// A net declaration target is qualified locally, without port substitution.
    pub lhs_is_net_initializer: bool,
    pub rhs_source: std::rc::Rc<Expression>,
    pub ctx: std::rc::Rc<RewriteCtx>,
    /// §10.3.1 / §21.2.1.5 drive strength (`(weak0, weak1)`, …) of the
    /// source `assign`; wrapped into the `$__weak`/`$__pull`/… marker at
    /// materialize time, exactly as the top-module path does. Dropping it
    /// left an inlined sub-module driver with no strength marker, so it was
    /// folded as STRONG against the net's other drivers (#1063).
    pub strength: Option<String>,
    /// `assign #N ...` delay expression, unevaluated: parameters it names
    /// resolve per-instance, so it is rewritten with `ctx` and evaluated at
    /// materialize time against the flattened parameter table. Dropping it
    /// (the old behavior) silently ran every inlined delayed assign with
    /// zero delay — a `#3` clock echo inside a DUT tracked undelayed.
    pub delay_source: Option<std::rc::Rc<Expression>>,
    /// §10.3.3 fall / turn-off delays of the `#(rise, fall[, turnoff])` form.
    pub delay_fall_source: Option<std::rc::Rc<Expression>>,
    pub delay_off_source: Option<std::rc::Rc<Expression>>,
    /// Span of the source statement for an `assign` or a net declaration
    /// assignment; see `ContinuousAssignment::origin`.
    pub origin_span: Option<crate::ast::Span>,
}

impl PendingAlways {
    /// Run the rewrite once and produce the owned AlwaysBlock. Drops self.
    pub fn materialize(self) -> AlwaysBlock {
        self.materialize_ref()
    }

    /// Borrowed materializer used by streaming artifact serialization (#721).
    pub fn materialize_ref(&self) -> AlwaysBlock {
        if pend_dbg_enabled() {
            eprintln!(
                "[PEND-MAT] prefix={:?} keys={:?}",
                self.ctx.prefix,
                self.ctx.port_map.keys().collect::<Vec<_>>()
            );
        }
        let stmt = self.rewrite(&self.source);
        AlwaysBlock {
            kind: self.kind,
            stmt,
            scope: self.scope(),
        }
    }

    /// The instance scope `materialize` records: `ctx.prefix` is the
    /// instance path with a trailing dot ("TB.p1."), recorded dot-trimmed,
    /// like PendingInitial. §21.2.1.7: inside a generate block, the generate
    /// block scope is appended to the instance path.
    pub fn scope(&self) -> String {
        let mut scope = self.ctx.prefix.trim_end_matches('.').to_string();
        if !self.gen_scope.is_empty() {
            if !scope.is_empty() {
                scope.push('.');
            }
            scope.push_str(&self.gen_scope);
        }
        scope
    }

    /// For an `@(...) body` block, its header alone, rewritten exactly as
    /// `materialize` rewrites it (the event control is rewritten on its own,
    /// independent of the body): `TimingControl { Event(..), Null }`.
    /// `None` for any other shape.
    pub fn materialize_header(&self) -> Option<Statement> {
        let StatementKind::TimingControl {
            control: control @ crate::ast::stmt::TimingControl::Event(_),
            stmt: body,
        } = &self.source.kind
        else {
            return None;
        };
        let header = Statement::new(
            StatementKind::TimingControl {
                control: control.clone(),
                stmt: Box::new(Statement::new(StatementKind::Null, body.span)),
            },
            self.source.span,
        );
        Some(self.rewrite(&header))
    }

    fn rewrite(&self, stmt: &Statement) -> Statement {
        set_type_bind_tls(&self.ctx);
        let stmt = rewrite_stmt(
            stmt,
            &self.ctx.prefix,
            &self.ctx.port_map,
            &self.ctx.local_names,
            &self.ctx.interface_map,
        );
        clear_type_bind_tls();
        substitute_type_params_stmt(stmt, &self.ctx.type_binds, &self.ctx.prefix)
    }
}

impl PendingInitial {
    /// The instance scope `materialize` records: `ctx.prefix` is the
    /// instance path with a trailing dot ("TB.p1."), recorded dot-trimmed.
    /// §21.2.1.7: inside a generate block, the generate block scope is appended
    /// to the instance path.
    pub fn scope(&self) -> String {
        let mut scope = self.ctx.prefix.trim_end_matches('.').to_string();
        if !self.gen_scope.is_empty() {
            if !scope.is_empty() {
                scope.push('.');
            }
            scope.push_str(&self.gen_scope);
        }
        scope
    }

    pub fn materialize(self) -> InitialBlock {
        self.materialize_ref()
    }

    /// Borrowed materializer used by streaming artifact serialization (#721).
    pub fn materialize_ref(&self) -> InitialBlock {
        set_type_bind_tls(&self.ctx);
        let stmt = rewrite_stmt(
            &self.source,
            &self.ctx.prefix,
            &self.ctx.port_map,
            &self.ctx.local_names,
            &self.ctx.interface_map,
        );
        clear_type_bind_tls();
        let stmt = substitute_type_params_stmt(stmt, &self.ctx.type_binds, &self.ctx.prefix);
        let scope = self.scope();
        InitialBlock { stmt, scope }
    }
}

impl PendingContAssign {
    /// §10.3.1: declaration targets name the instance net before port rewriting.
    /// Keep only the bare source in shared storage; qualify on demand.
    pub fn source_lhs(&self) -> std::borrow::Cow<'_, Expression> {
        if self.lhs_is_net_initializer {
            let name = ident_flat_name(&self.lhs_source).expect("net declaration target");
            std::borrow::Cow::Owned(make_ident_expr(&cat2(&self.ctx.prefix, &name)))
        } else {
            std::borrow::Cow::Borrowed(&self.lhs_source)
        }
    }

    pub fn materialize_lhs(&self) -> Expression {
        rewrite_expr(
            &self.source_lhs(),
            &self.ctx.prefix,
            &self.ctx.port_map,
            &self.ctx.local_names,
            &self.ctx.interface_map,
        )
    }

    pub fn materialize(self, params: &HashMap<String, Value>) -> ContinuousAssignment {
        self.materialize_ref(params)
    }

    /// Borrowed materializer used by streaming artifact serialization (#721).
    pub fn materialize_ref(&self, params: &HashMap<String, Value>) -> ContinuousAssignment {
        set_type_bind_tls(&self.ctx);
        let out = self.materialize_inner(params);
        clear_type_bind_tls();
        out
    }

    fn materialize_inner(&self, params: &HashMap<String, Value>) -> ContinuousAssignment {
        let lhs = self.materialize_lhs();
        let rhs = rewrite_expr(
            &self.rhs_source,
            &self.ctx.prefix,
            &self.ctx.port_map,
            &self.ctx.local_names,
            &self.ctx.interface_map,
        );
        // §10.3.1 / §21.2.1.5: apply the drive-strength marker, exactly as
        // the top-module copy at the `ModuleItem::ContinuousAssign` sites
        // does. Without this an inlined sub-module driver arrived WITHOUT a
        // marker and `resolve_multi_driver_nets` folded it as STRONG, so a
        // `(weak0, weak1)` pull lost to—and fought—the net's real driver
        // (#1063).
        let mut rhs = match self.strength.as_deref().and_then(strength_marker) {
            Some((marker, code)) => make_syscall(
                marker,
                vec![rhs.clone(), strength_code_literal(code, rhs.span)],
                rhs.span,
            ),
            None => rhs,
        };
        // §23.6: a hierarchical-LHS continuous assign in a sub-module writes
        // into a child scope (`lp.v = ~v`), so its RHS names are lexical to
        // the writing scope and must not be re-qualified into the target.
        root_mark_hier_ca_rhs(&self.lhs_source, &mut rhs, &|_| false, &|n| {
            self.ctx.upward.borrow().packages.contains(n)
        });
        let operands = [
            &self.delay_source,
            &self.delay_fall_source,
            &self.delay_off_source,
        ]
        .map(|src| {
            src.as_deref().map(|d| {
                rewrite_expr(
                    d,
                    &self.ctx.prefix,
                    &self.ctx.port_map,
                    &self.ctx.local_names,
                    &self.ctx.interface_map,
                )
            })
        });
        let (delay, delay_fall, delay_off, delay_exprs) =
            cont_assign_delays(operands.each_ref().map(Option::as_ref), params);
        let origin = self
            .origin_span
            .map(|sp| (sp, std::sync::Arc::clone(&self.ctx.origin_scope)));
        ContinuousAssignment::with_extras(
            lhs,
            rhs,
            delay,
            false,
            delay_fall,
            delay_off,
            None,
            delay_exprs,
            None,
            origin,
        )
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
    /// Shared: a class entry copied per specialization (the simulator's
    /// §8.25 type-parameter-base entries) shares the method bodies.
    pub methods: std::sync::Arc<HashMap<String, ClassMethod>>,
    /// Properties marked as 'rand' or 'randc'.
    pub random_properties: HashSet<String>,
    /// Properties declared with the `protected` qualifier (IEEE 1800 §8.2):
    /// visible to the declaring class and its subclasses only. Captured so a
    /// compile-time member-visibility pass can reject illegal out-of-class
    /// accesses (e.g. `t.events` where `events` is `const local`).
    #[serde(default)]
    pub protected_properties: HashSet<String>,
    /// Properties declared with the `local` qualifier (IEEE 1800 §8.2): visible
    /// to the declaring class only. See `protected_properties`.
    #[serde(default)]
    pub local_properties: HashSet<String>,
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
    /// Constraints: name -> constraint declaration. Shared with the class
    /// declaration and with every other elaborated copy of the class that
    /// did not rewrite the block (aionhw/xezim#721): a reader that changes
    /// one, or that keys state by where its items are stored, takes its own
    /// copy first.
    pub constraints: HashMap<String, std::sync::Arc<ClassConstraint>>,
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
    /// §8.23: for a class declared INSIDE another class, the lexically
    /// enclosing class — its statics are visible to this class's methods.
    #[serde(default)]
    pub enclosing: Option<String>,
    /// The MODULE this class is declared inside (`module wrapper; class
    /// proxy_c; ... endclass ... endmodule`), if any. A method of such a
    /// class resolves bare and sibling-instance names in that module's
    /// scope (§23.6); the runtime needs the module to find the instance when
    /// the object was not built inside it.
    #[serde(default)]
    pub declaring_module: Option<String>,
    /// Names listed in the `implements` clause.
    #[serde(default)]
    pub implements: Vec<String>,
    /// Names of type parameters declared on the class.
    #[serde(default)]
    pub type_param_names: Vec<String>,
    /// IEEE 1800-2020 §6.20.2: default type/class for each type parameter that
    /// declares one (`type T = some_class`). Stored as `(name, fragment)`
    /// where `fragment` is the default rendered to its class/identifier text
    /// (e.g. `uvm_callback`). Used to CANONICALIZE specialization signatures
    /// so a specialization that omits a defaulted trailing param
    /// (`C#(arg)` vs `C#(arg, default)`) keys its statics consistently
    /// regardless of whether it was named directly or reached via `extends`.
    /// Without this, `uvm_callbacks#(T,CB=uvm_callback)::m_typeid` was keyed
    /// `uvm_callbacks#a_comp::m_typeid` when named directly but
    /// `uvm_callbacks#a_comp, uvm_callback::m_typeid` via `extends`, so
    /// `register_super_type` read a different (empty) cell and
    /// `m_derived_types` stayed empty.
    #[serde(default)]
    pub type_param_defaults: Vec<(String, String)>,
    /// §6.20.2: the DEFAULT type of each type parameter, kept as AST so a
    /// width that references a VALUE parameter (`parameter type T = logic
    /// [W-1:0]`) can be resolved against the active specialization at
    /// runtime. `type_param_defaults` only keeps a textual fragment, which
    /// cannot be re-sized per specialization.
    #[serde(default)]
    pub type_param_default_types: Vec<(String, crate::ast::types::DataType)>,
    /// IEEE 1800-2017 §8.7: value arguments in the `extends Base(args)` clause,
    /// passed to the implicit `super.new(args)` when the derived constructor
    /// does not call `super.new` explicitly.
    #[serde(default)]
    pub extends_args: Vec<Expression>,
    /// Declared `DataType` of each property, keyed by property name.
    ///
    /// `properties[p].width` is the width under the class's DEFAULT parameter
    /// values, which is all a single `ElaboratedClass` per base-class name can
    /// record. A property whose packed range depends on a class parameter
    /// (`class box #(parameter int W = 8); bit [W-1:0] data;`) has a different
    /// width in every specialization, so the runtime re-resolves this type
    /// against the parameter bindings the instance carries — see
    /// `Simulator::respec_packed_width`.
    #[serde(default)]
    pub property_types: HashMap<String, DataType>,
    /// ALL arguments in the `extends Base#(arg1, arg2, ...)` clause as textual
    /// fragments, preserving order (both type and value params). Used to
    /// resolve ancestor type/value parameters: when a method of
    /// `uvm_registry_common` references `Tregistry`, we match it against the
    /// ancestor's `param_order` to find the extends arg at the same position
    /// (e.g. `this_type`), then resolve it to the concrete specialization.
    #[serde(default)]
    pub extends_type_args: Vec<String>,
    /// ALL parameter names (type and value), in declaration order. Needed to
    /// map positional `#(...)` type-args to the correct param when type and
    /// value params are interleaved (e.g. `uvm_component_registry#(type T,
    /// string Tname)` has the type param FIRST). `type_param_names`/
    /// `param_defaults` alone lose the combined order.
    #[serde(default)]
    pub param_order: Vec<String>,
    /// Declared `#(...)` specialization args for each CLASS PROPERTY typed
    /// with a parameterized type (e.g. `special_comp#(1) a1;` records
    /// `a1 -> [<1>]`). Locals get `var_type_args`; module-level decls get
    /// `ElaboratedModule::class_type_args`; but class properties had neither,
    /// so a later `this.a1 = new(...)` constructed with NO type-args and the
    /// value parameter `N` defaulted — collapsing `#(1)`/`#(2)` properties
    /// to `#(0)` (a UVM callbacks specialization case). Looked up by the runtime at
    /// construction time via the `this` instance's class definition.
    #[serde(default)]
    pub property_type_args: HashMap<String, Vec<Expression>>,
    /// Typedef names declared in the class body.
    #[serde(default)]
    pub typedef_names: Vec<String>,
    /// Typedef name -> its target DataType, captured so a later step can
    /// resolve e.g. `MyClass::type_id` to its target type.
    #[serde(default)]
    pub typedef_targets: HashMap<String, crate::ast::types::DataType>,
    /// Class-local typedef name -> its UNPACKED dimensions (`typedef bit
    /// edges_t[Node];`). Previously computed only transiently for property
    /// width resolution, so the simulator could not tell that a `ref edges_t`
    /// subroutine formal is an associative array (§13.5.2 writeback).
    #[serde(default)]
    pub typedef_unpacked_dims: HashMap<String, Vec<UnpackedDimension>>,
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
    /// §6.19.6: the NAMED key type of an assoc property (`int cnt[sev_e];`)
    /// — property name → type name. Consulted by the simulator's `foreach`
    /// so the index variable carries the enum type when the collection is a
    /// CLASS PROPERTY (the module-scope map cannot see it).
    #[serde(default)]
    pub assoc_key_types: HashMap<String, String>,
    /// Associative-array property INDEX (key) width + signedness: `shortint
    /// aa[shortint]` -> (16, true). Used to narrow a wider index expression
    /// before keying at runtime. String-keyed arrays are excluded (the
    /// `assoc_properties` bool distinguishes them).
    #[serde(default)]
    pub assoc_index_props: HashMap<String, (u32, bool)>,
    /// Properties declared as queues / dynamic arrays (`T m[$];`, `T m[];`) —
    /// name mapped to (element width, optional bounded-queue max+1). Stored
    /// per-instance like associative arrays, so each object's queue is
    /// independent.
    #[serde(default)]
    pub queue_properties: HashMap<String, (u32, Option<u32>)>,
    /// §7.10: queue declarations among queue/dynamic-array properties.
    pub queue_property_names: HashSet<String>,
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
    /// §7.8.2: the KEY type of a STATIC assoc member (`static T map[string];`)
    /// — static member name -> key-type name (a plain `string` is stored as
    /// the literal `"string"`). `static_collections` carries no key type, and
    /// writing statics into `assoc_properties` (which is per-INSTANCE) confused
    /// `is_associative_array`'s `handle#member` dispatch, so without a dedi-
    /// cated map a `static T map[string]` param'd array fell into the NUMERIC
    /// branch of `assoc_key_str` and stored its string keys as hashed integers
    /// (consistent for set/get, but foreach()/first()/next() decoded garbage).
    #[serde(default)]
    pub static_assoc_key_types: HashMap<String, String>,
    /// §7.8.2: the INDEX (key) width + signedness of a STATIC assoc member
    /// (`static int m[int];` -> (32, true)). `assoc_index_props` is per-
    /// INSTANCE (and recording statics there confuses `is_associative_array`'s
    /// `handle#member` dispatch), so statics keep their own map. Consulted by
    /// `assoc_index_width_for` for a per-spec `Class#spec::member` key so
    /// `foreach` binds a SIGNED index with its true width.
    #[serde(default)]
    pub static_assoc_index_props: HashMap<String, (u32, bool)>,
    /// §8.25: the KEY type of an instance assoc member whose packed range
    /// depends on a class parameter (`logic [7:0] m[a_t]` with
    /// `typedef logic [AW-1:0] a_t;`). `assoc_index_props` holds the width at
    /// the DEFAULT parameters; construction re-sizes the key from this type
    /// for the specialization the object actually has.
    #[serde(default)]
    pub assoc_key_decl_types: HashMap<String, DataType>,
    /// Fixed-size `static` array members (`static int S[3]`, `static bit
    /// m[2:0]`): (name, lo, hi, element width). §8.9 gives every instance of
    /// the class ONE shared copy, so — exactly like `static_collections` —
    /// these are kept OUT of the per-instance `array_properties` and are
    /// registered under their bare name at simulator startup instead. They
    /// need their own list because `static_collections` carries no bounds:
    /// a queue/assoc store is unsized, a fixed array is not.
    #[serde(default)]
    pub static_fixed_arrays: Vec<(String, i64, i64, u32)>,
    /// Fixed-size unpacked-array members with a compile-time-constant size
    /// (`rand reg_t gpr[4]`, `int m[2:0]`): name -> (lo, hi, element width).
    /// Stored per-instance as `<handle>#<member>` registered in `module.arrays`
    /// so index access and `foreach` see a real fixed range (and rand elements
    /// can be randomized). Non-constant sizes (`m[NUM_HARTS]`) stay in
    /// `queue_properties` since the size isn't known at class-elaboration time.
    #[serde(default)]
    pub array_properties: HashMap<String, (i64, i64, u32)>,
    /// §8.25: fixed-size unpacked-array members sized by a class VALUE
    /// parameter (`int items[N]`, `int md[N][2]`): name -> the declared
    /// unpacked dimensions. `array_properties` / `array_nd_properties` hold
    /// their shape at the DEFAULT parameter values; the runtime re-sizes each
    /// object's storage from the parameters it was built with.
    #[serde(default)]
    pub param_sized_props: HashMap<String, Vec<UnpackedDimension>>,
    /// MULTI-dimensional fixed-size unpacked-array members whose every
    /// dimension has compile-time-constant bounds (`test_t foo[0:3][0:7]`):
    /// name -> (per-dimension (lo, hi) shape, element width). Registered
    /// per-instance as `<handle>#<member>` in `module.arrays_2d` /
    /// `arrays_nd` so nested index access and multi-var `foreach` resolve —
    /// `array_properties` only ever carried the FIRST dimension, so
    /// `foo[i][j]` writes were dropped and `foreach (foo[i,j])` left `j` at X.
    #[serde(default)]
    pub array_nd_properties: HashMap<String, (Vec<(i64, i64)>, u32)>,
    /// §7.4.5: a fixed-size unpacked array whose ELEMENT is a COLLECTION
    /// (`int q[3][$]`, `int d[3][]`, `int a[2][2][int]`). name -> (outer
    /// fixed shape, element width, element collection kind).
    ///
    /// The trailing collection dimension used to be dropped on the floor.
    /// `array_nd_properties` rejects the shape (a queue dimension has no
    /// constant bounds), so classification fell back to
    /// `effective_dims.first()` and the member became a plain fixed array of
    /// SCALARS. That failed quietly in the worst way: `$size(q)` and
    /// `foreach (q[i])` both answered correctly off the outer shape, while
    /// every element's queue had no storage at all — `q[i].push_back(x)`
    /// resolved to nothing and `q[i].size()` stayed 0 forever.
    #[serde(default)]
    pub array_of_coll_properties: HashMap<String, (Vec<(i64, i64)>, u32, CollDimKind)>,
    /// §7.4.5/§7.5/§7.8: a dynamic outer dimension whose elements are
    /// associative arrays. The tail dimensions retain each declared key type;
    /// each object's rows are registered when new[n] allocates them.
    #[serde(default)]
    pub dynamic_assoc_properties: HashMap<String, Vec<UnpackedDimension>>,
    /// §7.4.5/§7.5: a dynamic or queue outer dimension whose elements are
    /// themselves unpacked arrays (`T a[][N]`, `T a[][]`, `T a[$][N]`): the
    /// tail dimensions after the outer one. The member's leaf width is in
    /// `queue_properties`; the runtime shapes each object's storage from the
    /// tail the way a module-scope declaration of the same shape is shaped.
    #[serde(default)]
    pub dynamic_tail_properties: HashMap<String, Vec<UnpackedDimension>>,
    /// §7.4.5: the declared [`CollShape`] of each collection property; the
    /// class counterpart of `ElaboratedModule::coll_shapes`. Keyed by the
    /// bare property name (statics too). §8.25: a key typed by a class
    /// parameter is resolved at the default specialization (or kept
    /// `Typed`), so a specialized object re-resolves it.
    #[serde(default)]
    pub prop_coll_shapes: HashMap<String, CollShape>,
    /// §7.4.2 / §20.7: the DECLARED `(left, right)` bounds of every unpacked
    /// dimension of a fixed-size array member with at least one descending
    /// dimension (`int ds[3:1]`). `array_properties` / `array_nd_properties`
    /// normalize to `(lo, hi)`, which loses the direction an assignment
    /// pattern, `%p`, `foreach` and `$left`/`$right` follow.
    #[serde(default)]
    pub array_prop_decl_dims: HashMap<String, Vec<(i64, i64)>>,
}

/// The kind of COLLECTION that sits at the innermost dimension of an
/// `array_of_coll_properties` member. Mirrors the three trailing unpacked
/// dimensions that give an element its own independent store.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum CollDimKind {
    /// `m[$]` / `m[$:N]` — the option carries the bounded cap (max + 1).
    Queue(Option<u32>),
    /// `m[]` — dynamic array.
    Dyn,
    /// `m[KEY]` — associative; the flag is `true` for a `string` key.
    Assoc { string_key: bool },
}

/// DPI import metadata used by the simulator for foreign-call dispatch.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct DpiImportSpec {
    pub c_name: String,
    pub property: Option<DPIProperty>,
    pub proto: DPIProto,
}

/// §23.8: what an upward hierarchical name is resolved against — the
/// elaborated instance tree, grouped by parent scope, and per definition the
/// scope names its source declares. Filled while the design is inlined
/// (`inline_module_items`, the `ElabInstance` registration) and read by
/// `upward_scope_rewrite`, both during elaboration and when a deferred body
/// is materialized, by which time the tree is complete.
#[derive(Debug, Default)]
pub struct UpwardScopes {
    /// Parent scope path (`""` = the top module) → the paths of its child
    /// instances, bound instances included. A child's instance name is its
    /// path below the parent's (`child_leaf`).
    children: HashMap<Rc<str>, Vec<Rc<str>>>,
    /// Instance path (`""` = the top module) → definition name.
    defs: HashMap<Rc<str>, Rc<str>>,
    /// Definition name → the scope names its source declares anywhere in
    /// its body (instances of every generate branch, generate and block
    /// labels, subroutines): a reference headed by one of them is a
    /// DOWNWARD reference (§23.8 step a) even before that child is inlined.
    declared: HashMap<String, HashSet<String>>,
    /// §26.3: package names — `pkg.member` is the inliner's spelling of a
    /// package constant, never a scope path.
    packages: HashSet<String>,
    /// §23.8.1: instance path → where its instantiation sits in its parent.
    parents: HashMap<Rc<str>, InstanceParent>,
    /// The definition names in `defs` and `parents`, one string per
    /// definition. An instance path is likewise one string, shared by the
    /// tables that name it (aionhw/xezim#721).
    def_names: HashSet<Rc<str>>,
    /// The scope the last instance was recorded in; the children of one
    /// scope arrive together, so most lookups of a parent end here.
    last_parent: Option<Rc<str>>,
}
/// The scope of the parent definition holding an instantiation.
#[derive(Debug)]
struct InstanceParent {
    /// The instance's own definition.
    def: Rc<str>,
    path: Rc<str>,
    tree: Rc<crate::scope_tree::ScopeTree>,
    scope: crate::ast::binding::ScopeId,
    indices: Vec<i64>,
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
    pub path: SharedName,
    /// The module (or interface) definition this instantiates.
    pub def_name: SharedName,
    /// Dotted path of the containing scope; empty for a child of the top.
    pub parent: SharedName,
    /// Source offset of the instantiation among the parent's items, for the
    /// simulator's time-0 process order. A bound instance (appended to its
    /// host's items by `bind`) sorts after every item that precedes it.
    #[serde(default)]
    pub src_pos: usize,
}

/// Elaborated module ready for simulation.
///
/// `serde::Serialize` is implemented in [`streaming_serde`] so deferred
/// `pending_*` blocks, continuous assignments, and callable bodies stream
/// directly into `.xez` artifacts one element at a time without requiring
/// bulk `materialize_pending()` in memory (aionhw/xezim#721).
#[derive(Debug, serde::Deserialize)]
pub struct ElaboratedModule {
    pub name: String,
    /// Global simulation tick in seconds — the finest `timescale` precision
    /// across the design (default 1e-9 = 1 ns when none is finer). Delays are
    /// pre-scaled to this unit at elaboration; the simulator counts ticks of it.
    #[serde(default = "default_tick_s")]
    pub tick_s: f64,
    pub signals: SharedNameMap<Signal>,
    /// Transient elaboration bookkeeping (not serialized): names that already
    /// received a type-bearing declaration, mapped to whether that type was
    /// *incompatible* (a named/atom/real/struct/enum type, which cannot be
    /// combined with any other type spec). Used to flag §23.2.2.1 conflicting
    /// non-ANSI redeclarations while still permitting the legal split forms.
    #[serde(skip)]
    pub typed_decls: HashMap<String, bool>,
    /// Transient: non-ANSI ports that a separate net or variable declaration
    /// has already completed (§23.2.2.1 allows exactly one such declaration).
    #[serde(skip)]
    pub completed_ports: HashSet<String>,
    /// Transient: width of each non-ANSI port whose port declaration carries
    /// an explicit packed range (`output [7:0] x;`).
    #[serde(skip)]
    pub ranged_port_widths: HashMap<String, u32>,
    /// Transient (§26.3, §6.19): the bare-name parameter and signal entries
    /// of each `$unit` enum member that a package also declares, as the
    /// `$unit` typedefs registered them (`reassert_unit_enum_members`).
    #[serde(skip)]
    pub unit_member_slots: Vec<(String, Value, Signal)>,
    /// Transient (§26.3): bare type entries `rebind_imported_typedefs` hid
    /// for the scope being prepared, because an import of that scope binds
    /// the name as a constant: name, width, type, unpacked dimensions and
    /// element width. The next scope's rebind puts them back.
    #[serde(skip)]
    pub hidden_bare_types: Vec<HiddenBareType>,
    /// §26.3: names that are BOTH brought in by a wildcard package import
    /// (`import pkg::*`) AND re-declared locally in this scope. A local
    /// declaration shadows the imported name — so at such a name the
    /// duplicate-declaration check overrides (drops the imported entry) instead
    /// of erroring. Explicit imports (`import pkg::x`) are never listed here.
    pub wildcard_shadowed: HashSet<String>,
    pub port_order: Vec<String>,
    pub continuous_assigns: Vec<ContinuousAssignment>,
    /// §28.8 bidirectional switches (`tran`/`tranif0`/`tranif1`), pending
    /// resolution against each terminal's own drivers.
    #[serde(default)]
    pub tran_switches: Vec<TranSwitch>,
    /// §29 User-Defined Primitive instances (flattened).
    #[serde(default)]
    pub udp_instances: Vec<UdpInstance>,
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
    /// §26.3 / §21.7.2.3: actual parameter declarations, excluding lookup aliases.
    pub declared_parameters: HashSet<String>,
    /// Typedef name -> width mapping for user-defined types.
    pub typedefs: TypedefTable,
    /// §7.4.1: for a typedef whose target is a packed array of packed
    /// elements (`typedef u8_t [15:0] vec_t`), the ELEMENT width (8 here).
    /// Lets downstream compilers slice `local[i]` on typedef-typed locals.
    pub typedef_elem_widths: HashMap<String, u32>,
    pub typedef_types: SharedMap<DataType>,
    /// §6.6.7 nettype name -> resolution function, for every user-defined
    /// nettype visible at the top module (which is where a nettype shared
    /// across a port boundary must be declared — both sides have to name the
    /// same type, so it lives at $unit or package scope).
    ///
    /// Consumed by `resolve_user_nettype_drivers` AFTER inlining, which is the
    /// first point at which a net driven from several module instances has all
    /// of its drivers. Not serialized: the pass runs before any artifact is
    /// written, so a loaded artifact has the folds already applied.
    #[serde(skip)]
    pub nettype_resolvers: HashMap<String, String>,
    /// §6.18, §26.3, §26.5: nettype names of the compilation unit or a
    /// package that the module hides with its own typedef, class or type
    /// parameter of the same name. A declaration whose type is spelled with
    /// one of these names is a variable of that type, not a nettype net.
    #[serde(skip)]
    pub shadowed_nettypes: HashSet<String>,
    /// Array declarations: base_name -> (lo_index, hi_index, element_width)
    pub arrays: HashMap<String, (i64, i64, u32)>,
    /// Associative arrays: name -> true if string-keyed
    pub associative_arrays: HashMap<String, bool>,
    /// Associative-array ELEMENT width: `logic [3:0] aa [string]` -> 4.
    /// Only `associative_arrays` (a keyed-ness flag) was recorded, so a write
    /// stored the RHS at its own width — `aa["k"] = 8'hEF` kept all 8 bits in
    /// a 4-bit element, and `$bits` reported the stored width rather than the
    /// declared one. Elements live in the runtime `signals` map with no
    /// declared width attached, so the width has to be carried here.
    #[serde(default)]
    pub assoc_elem_widths: HashMap<String, u32>,
    /// Associative-array INDEX (key) width + signedness: `shortint aa[shortint]`
    /// -> (16, true). A key written with a wider expression must be narrowed to
    /// the declared index type before stringifying (`assoc_key_str`), else the
    /// stored key text diverges from a read that correctly narrows. String-keyed
    /// arrays are excluded (handled by the `bool` flag above).
    #[serde(default)]
    pub assoc_index_widths: HashMap<String, (u32, bool)>,
    /// Class definitions: name -> elaborated class.
    pub classes: HashMap<String, std::sync::Arc<ElaboratedClass>>,
    /// Covergroup definitions: name -> AST declaration.
    pub covergroups: HashMap<String, CovergroupDeclaration>,
    /// Module-level function declarations.
    pub functions: FuncTable,
    /// Module-level task declarations.
    pub tasks: HashMap<String, TaskDeclaration>,
    /// Declaring scope (package name) for package-level functions/tasks, so
    /// `%m` inside a package subroutine yields `<pkg>.<name>` — matching
    /// real simulators — instead of the top-module name. Keyed by the
    /// function/task simple name (mirrors the `functions`/`tasks` maps).
    #[serde(default)]
    pub func_decl_scope: HashMap<String, String>,
    /// Declaring package of each package-scope class (`C` -> `pk`), so `%m`
    /// in one of its methods names `pk.C.m` (§21.2.1.7).
    #[serde(default)]
    pub class_decl_pkg: HashMap<String, String>,
    /// DPI imports by SV-visible symbol name.
    pub dpi_imports: HashMap<String, DpiImportSpec>,
    /// §35.5.3: the package an import is declared in, by SV name (the
    /// first one), so a context import called from anywhere runs in it.
    #[serde(default)]
    pub dpi_import_pkg: HashMap<String, String>,
    /// SV names of imports declared in a module, interface, program,
    /// generate block or the compilation unit: such an import runs in the
    /// instance scope it is called from.
    #[serde(default)]
    pub dpi_import_in_design: HashSet<String>,
    /// §35.5.4 exported SV functions/tasks (`export "DPI-C" function f;`), in
    /// declaration order. The index is a stable id the C-callable trampoline
    /// passes back to identify which subroutine to run.
    pub dpi_exports: Vec<String>,
    /// The C linkage name of each entry of `dpi_exports` (same index): the
    /// alias of `export "DPI-C" c_name = task sv_name;` when given, else the
    /// SV name. The alias used to be dropped, so the C side's `c_name` was an
    /// undefined symbol in the loaded library.
    pub dpi_export_c_names: Vec<String>,
    /// Clocking block definitions: name -> AST declaration.
    pub clocking_blocks: HashMap<String, ClockingDeclaration>,
    /// Let declarations visible in the elaborated scope.
    pub lets: HashMap<String, LetDeclaration>,
    /// Bound interface modport views: signal -> (member -> direction).
    pub modport_views: HashMap<String, HashMap<String, PortDirection>>,
    /// Clocking block signals: block name -> (signal -> direction).
    pub clocking_signal_dirs: HashMap<String, HashMap<String, PortDirection>>,
    /// §14.16: a clocking OUTPUT clockvar drives a stage of its own when
    /// the net it is bound to has another driver: (block name, net) ->
    /// stage signal. The clockvar drives the stage, and the stage joins the
    /// net's other drivers in the resolution fold.
    #[serde(default)]
    pub clocking_output_stages: HashMap<(String, String), String>,
    /// Specify path delays: destination signal name -> the largest delay
    /// of its module paths, in ticks (marks the net as path-delayed).
    pub specify_delays: HashMap<String, u64>,
    /// §30.4 module paths by destination signal name.
    #[serde(default)]
    pub module_paths: HashMap<String, Vec<ModulePath>>,
    /// §31 timing checks, one entry per check per instance.
    #[serde(default)]
    pub timing_checks: Vec<TimingCheckInstance>,
    /// §6.6.2/§6.6.3 nets whose MULTI-DRIVER resolution or undriven value is
    /// not plain `wire`: wand/triand, wor/trior, tri0, tri1. Only these kinds
    /// are recorded — a plain wire needs no entry. Consumed by
    /// `resolve_multi_driver_nets` (which picks the fold function) and by the
    /// tri0/tri1 pull driver below.
    #[serde(default)]
    pub resolved_net_kinds: crate::shared_names::SharedNameMap<ResolvedNetKind>,
    /// §28.16 primitive fall delays, keyed by the driven signal (the private
    /// driver stage where a net's drivers were split). This map also lets
    /// the runtime apply primitive delay-mode overrides. Only differing
    /// rise/fall values are recorded.
    #[serde(default)]
    pub gate_fall_delays: HashMap<String, u64>,
    /// Nets driven by a lowered GATE PRIMITIVE (`buf`, `and`, …), by name.
    ///
    /// A gate lowers to an ordinary `ContinuousAssignment`, which makes it
    /// indistinguishable from a user `assign` by the time the simulator fuses
    /// one-bit copies into a buffer op. The two differ on `z`: §28.4's `buf`
    /// truth table maps a `z` input to an `x` output, but §10.3 continuous
    /// assignment passes the value through unchanged. Applying the gate rule
    /// to both silently turned every `assign y = x;` into a z-eater.
    #[serde(default)]
    pub gate_driven_nets: HashSet<String>,
    /// Associative array default values.
    pub assoc_defaults: HashMap<String, Expression>,
    /// Dynamic arrays / queues (size starts at 0, not pre-allocated range).
    pub dynamic_arrays: HashSet<String>,
    /// §10.3.1 drive strength of a continuous assign's target net, keyed by
    /// net name: (strength-when-1, strength-when-0), e.g. ("pull1", "pull0").
    /// Consumed by `%v` (§21.2.1.5); absent nets display as strong.
    #[serde(default)]
    pub net_strengths: HashMap<String, (String, String)>,
    /// §28.12: every driver, with its strengths, of each net that several
    /// drivers resolve and some driver of which carries a drive strength, is
    /// a tristate primitive or a pull (and of each tri0/tri1/trireg net).
    /// Only `%v` reads it; the net's value comes from its folded assign.
    #[serde(default)]
    pub strength_drivers: HashMap<String, Vec<StrengthDriver>>,
    /// `supply0` / `supply1` nets (supply strength, §6.6.6).
    #[serde(default)]
    pub supply_nets: HashSet<String>,
    /// Arrays declared with descending range (e.g. [7:0])
    pub descending_arrays: HashSet<String>,
    /// DECLARED (left, right) bounds per unpacked dimension, outermost first
    /// (§20.7 array queries must report declared order — `[3:1]` has
    /// $left=3/$right=1 and $increment=1; the arrays* tables normalize to
    /// (lo, hi) and lose it).
    pub unpacked_decl_dims: crate::shared_names::SharedSliceMap<(i64, i64)>,
    /// Packed vectors declared with an ASCENDING range (`logic [0:7]`), mapped
    /// to their width. Bit/part selects index these from the MSB end (label 0 =
    /// MSB), so the interpreter remaps `sig[i]` → internal bit `(W-1)-i`
    /// (IEEE 1800-2017 §7.4.1, §11.5.1). Default-declared `[N:0]` vectors are
    /// descending and absent here.
    /// Ascending packed vectors (`logic [3:10] a`): declared `(low, high)`
    /// label bounds. Label `p` lives at physical bit `high - p` (the left
    /// label is the MSB), so both bounds are needed, not just the width.
    pub ascending_packed: HashMap<String, (i64, i64)>,
    /// Unpacked dimensions attached to a typedef (`typedef T A[0:3];`), keyed by
    /// typedef name. A variable `A v;` inherits these dims so it elaborates as
    /// an unpacked array (IEEE 1800-2017 §6.18, §7.4). Empty for scalar typedefs.
    pub typedef_unpacked_dims: HashMap<String, Vec<UnpackedDimension>>,
    /// Bounded queue max sizes: name -> max element count (i.e., $:N means N+1).
    pub queue_max_sizes: HashMap<String, u32>,
    /// Variables declared as QUEUES (`[$]`/`[$:N]`) — distinguishes them from
    /// dynamic arrays inside `dynamic_arrays` (§7.10.1 out-of-range write
    /// semantics differ: a queue write at index==size appends).
    #[serde(default)]
    pub queue_vars: HashSet<String>,
    /// 2D unpacked arrays: name -> ((dim1_lo,dim1_hi),(dim2_lo,dim2_hi),elem_width).
    pub arrays_2d: HashMap<String, ((i64, i64), (i64, i64), u32)>,
    pub packages: HashSet<String>,
    /// §26.3: declaring package of each package-scope subroutine's BARE key
    /// (`name` → `pkg`). Used by the runtime to keep a bare sibling call from
    /// inside a package subroutine in ITS package when two packages contest
    /// the name.
    pub pkg_subr_owner: HashMap<String, String>,
    /// §26.3: every scalar package variable under its QUALIFIED name
    /// (`pkg::name`), with its declared type and initial value. Package
    /// variables are hoisted into `signals` under their bare name, which two
    /// packages declaring the same name — or a module-scope declaration of
    /// it — share; the runtime gives each contested name its own
    /// per-package storage from this table.
    #[serde(default)]
    pub pkg_var_decls: HashMap<String, Signal>,
    /// §26.3: `static_init_blocks` entries that initialize a scalar package
    /// variable from a call (`int x = f();`): (block index, `pkg::name`).
    #[serde(default)]
    pub pkg_var_init_blocks: Vec<(usize, String)>,
    /// §26.3: the package imports of every module / interface / program
    /// definition: (package, explicitly imported item or `None` for `*`).
    #[serde(default)]
    pub def_pkg_imports: HashMap<String, Vec<(String, Option<String>)>>,
    /// Names of bodyless sequences, properties, and checkers (so `@name` event
    /// control resolves). Declarations with bodies live in `property_decls`
    /// alone (#721); query both via [`Self::has_named_sva`].
    pub sequences: crate::shared_names::SharedNameSet,
    /// Packed struct bit-field layout: container_name -> shared slice of
    /// `(member_name, lsb_offset, width)`.
    /// Members are stored by bit offset so MemberAccess can slice the container.
    pub packed_struct_fields: crate::shared_names::SharedSliceMap<(String, u32, u32)>,
    /// For the port width-mismatch diagnostic: typedef name -> (field name ->
    /// identifiers its range expression reads), captured from the ORIGINAL
    /// (pre-fold) struct declaration. The stored `typedef_types` folds these
    /// dimensions away (`[P:0]` becomes `[0:0]`), erasing the parameter the
    /// underflow can be traced to, so we keep the identifier list alongside.
    /// Both levels iterate in a fixed order: the table is serialized.
    pub struct_field_range_idents: HashMap<String, HashMap<String, Vec<String>>>,
    /// Variable -> its declared (element) data type. For an array this is the
    /// ELEMENT type; array-ness comes from `arrays`/`dynamic_arrays`/
    /// `associative_arrays`. Drives the type-directed `%p` renderer
    /// (LRM §21.2.1.7), which must walk nested structs/arrays/enums.
    #[serde(default)]
    pub var_decl_types: crate::decl_types::DeclTypeMap,
    /// Value parameter -> its declared type, for an explicitly typed one
    /// (`localparam e_t RST`), keyed as in `parameters`. The self-determined
    /// type of a parameter (§6.20.2), e.g. for a `default:` key (§10.9.1).
    #[serde(default)]
    pub param_decl_types: crate::decl_types::ParamDeclTypeMap,
    /// Struct variable -> its top-level member names in DECLARATION order, for
    /// packed and unpacked alike. `packed_struct_fields` is ordered by bit
    /// offset (i.e. reversed) and unpacked members live in separate signals, so
    /// neither preserves source order. Used by `%p` (LRM §21.2.1.7), which must
    /// print `'{member:value, ...}` in declaration order.
    #[serde(default)]
    pub struct_members: crate::shared_names::SharedSliceMap<String>,
    /// Packed multi-dimensional signal element width: signal_name -> element_width.
    /// For `logic [3:0][7:0] words;` stores `"words" -> 8` so that `words[i]`
    /// resolves to an 8-bit slice rather than a 1-bit select. Also keyed for
    /// struct fields under `"struct_var.field"` form.
    pub packed_signal_elem_widths: crate::shared_names::SharedNameMap<u32>,
    /// Full packed dimension list (outermost first) for multi-dimensional
    /// packed vectors: `reg [1:0][15:0][7:0] a;` stores
    /// `"a" -> [(1,0),(15,0),(7,0)]`. Each entry is the declared
    /// (left, right) bounds so nested selects (`a[i][j]`) can be resolved to
    /// the correct flat bit slice with index normalization for ascending /
    /// non-zero-based ranges (LRM §7.4.1).
    #[serde(default)]
    pub packed_full_dims: crate::shared_names::SharedSliceMap<(i64, i64)>,
    /// §6.9.1 / §10.3.3: declared vector net shape, including equal bounds.
    /// Keyed by final flat net name; independent of array query/select tables.
    pub vector_nets: crate::shared_names::SharedNameSet,
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
    /// §25.9 / §6.22.1: each interface's header parameters in declaration
    /// order with their default rendered as a specialization fragment (a
    /// literal value or a type name; None when it cannot be reduced here).
    /// Lets the simulator key `virtual I` and `virtual I#(<defaults>)` as
    /// the same type.
    #[serde(default)]
    pub interface_param_defaults: HashMap<String, Vec<(String, Option<String>)>>,
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
    pub property_decls: crate::shared_names::SharedNameMap<Rc<Expression>>,
    /// §16.6: formal port NAMES of each parameterized named property/sequence,
    /// keyed like `property_decls`. Portless declarations are omitted (#721).
    #[serde(default)]
    pub property_params: crate::shared_names::SharedSliceMap<String>,
    /// §16.8, §16.12: the default actual argument of each formal, keyed like
    /// `property_decls` and parallel to `property_params`; absent when no
    /// formal of the declaration has one. A declaration of an inlined
    /// instance has its defaults rewritten into the instance's scope, as its
    /// body is.
    #[serde(default)]
    pub property_param_defaults: HashMap<String, Vec<Option<crate::ast::expr::Expression>>>,
    /// LRM §8.4: for an array-of-class-handles (`T arr[N]`,
    /// `T arr[];`), record the element's class name so runtime
    /// `arr[i] = new(...)` can construct an instance of that class.
    /// Populated at signal-declaration time when the data type is a
    /// `TypeReference` whose name resolves to a known class. Without
    /// this, the assignment falls back to a zero value (null handle).
    #[serde(default)]
    pub array_elem_class: HashMap<String, String>,
    /// Associative-array KEY type name, when the key is a named type
    /// (`int cnt [sev_e];`). `foreach (cnt[s])` binds `s` with this type so
    /// `s.name()` resolves against the RIGHT enum — without it the lookup
    /// scans every enum and picks the largest, printing a member of an
    /// unrelated enum (UVM's report summary showed `UVM_NORADIX` where a
    /// severity belonged).
    pub assoc_key_type_names: HashMap<String, String>,
    /// §7.4.5: the declared [`CollShape`] of every collection of collections
    /// (see [`CollShape::of`]), by storage name.
    #[serde(default)]
    pub coll_shapes: HashMap<String, CollShape>,
    /// N-dimensional unpacked array shapes (N >= 3): name → Vec of (lo, hi) per dim.
    pub arrays_nd: HashMap<String, (Vec<(i64, i64)>, u32)>,
    /// Parameter init expressions that couldn't be evaluated at elaboration time
    /// (e.g. contain function calls). Simulator re-evaluates these during init.
    pub deferred_param_exprs: Vec<(String, Expression)>,
    /// Names declared as nets (wire, supply0/1, tri, etc). Variables are everything else.
    /// Used to enforce §6.5 driver-conflict rules only against variables.
    #[serde(default)]
    pub nets: crate::shared_names::SharedNameSet,
    /// Subset of `nets` that §6.10 created IMPLICITLY (referenced but never
    /// declared). `--primitive-verbose` flags UDP terminals landing on one of
    /// these — the classic signature of a dropped/unresolved vendor cell.
    #[serde(default)]
    pub implicit_nets: HashSet<String>,
    /// §6.6.8 `interconnect` nets: typeless — the net adopts the type of the
    /// port it connects. Declared here so the port-binding pass can shape the
    /// placeholder (1-bit z) signal from the first definitely-typed formal.
    #[serde(default)]
    pub interconnect_nets: HashSet<String>,
    /// Elaboration-time diagnostics (implicit-net warnings, port-width lint,
    /// unresolved-module notes, width-underflow) captured during a cold run so
    /// a warm design-cache HIT — which skips elaboration — can replay them
    /// instead of silently dropping them.
    #[serde(default)]
    pub elab_diagnostics: Vec<String>,
    /// The design's instance tree, in elaboration order. Inlining flattens
    /// every module into this one, so without this the hierarchy is only
    /// implicit in dotted signal names — enough to resolve a name, not
    /// enough to enumerate a scope's children. Drives the VPI object model.
    #[serde(default)]
    pub instances: Vec<ElabInstance>,
    /// §23.8: `instances` as a scope tree for `upward_scope_rewrite`, shared
    /// with every `RewriteCtx` so a body materialized after elaboration
    /// resolves its upward names against the complete design. Not cached:
    /// the artifact stores materialized bodies only.
    #[serde(skip)]
    pub upward_scopes: Rc<std::cell::RefCell<UpwardScopes>>,
    /// §23.11: bind directives selected for each elaborated host path.
    pub resolved_binds: HashMap<String, Vec<crate::ast::decl::BindDirective>>,
    /// Active declarations collected in their elaborated lexical scopes.
    #[serde(skip)]
    pub bind_sites: Vec<(String, crate::ast::decl::BindDirective)>,
    /// §25.10: the sorted dotted keys of `parameters`, for the lookup of an
    /// interface instance's parameters by its path (`param_prefix_index`).
    #[serde(skip)]
    pub(crate) param_index: param_prefix_index::ParamPrefixIndex,
    /// Out-of-class constraint definitions: `(class_name, constraint_name)`.
    #[serde(default)]
    pub out_of_class_constraints: HashSet<(String, String)>,
    /// IEEE 1800-2023 §20.3: $timeunit / $timeprecision encoded as the
    /// power-of-10 exponent in seconds (e.g. 10ns → -8). Defaults to -9.
    #[serde(default = "default_timeunit_exp")]
    pub timeunit_exp: i32,
    #[serde(default = "default_timeunit_exp")]
    pub timeprecision_exp: i32,
    /// Per-module-DEFINITION timescale as `(unit_exp, precision_exp)` powers of
    /// ten in seconds. Covers both `\`timescale` directives and in-body
    /// `timeunit`/`timeprecision` declarations. The simulator scales `$time` /
    /// `$realtime` in each scope to its own module's unit (§20.3) and reports
    /// `$printtimescale` from it. Keyed by module name (= definition name).
    #[serde(default)]
    pub module_timescale_exp: HashMap<String, (i32, i32)>,
    /// Module definitions that carried no `timescale (own, inherited, or
    /// CLI) and therefore run on the 1ns/1ns tool default.
    pub modules_without_timescale: Vec<String>,
    /// IEEE 1800-2017 §6.19: enum typedef members in declaration order.
    /// Keyed by typedef name; each entry is `(member_name, value)`.
    /// Used to resolve `.name()` / `.next()` / `.first()` etc.
    #[serde(default)]
    pub enum_members: HashMap<String, Vec<(String, u64)>>,
    /// IEEE 1800-2017 §26.3: enum members grouped by their declaring PACKAGE,
    /// as `package -> member -> (value, width)`.
    ///
    /// Members are otherwise reachable only through the flat design-wide
    /// name maps, so `pkg::NAME` was answered by stripping the scope and
    /// looking `NAME` up bare. That works right up until a local declaration
    /// legally shadows `NAME`, at which point the qualified form — the one
    /// way §26.3 leaves the member reachable — silently read the LOCAL
    /// instead. This map keeps the package's own view addressable.
    #[serde(default)]
    pub package_enum_members: HashMap<String, HashMap<String, (u64, u32)>>,
    /// Where each name was FIRST declared, as `name -> (span, what it was)`.
    /// Only the first declaration is kept — that is the one a duplicate-
    /// declaration error needs to point at, and it is the one a later
    /// declaration cannot see. `what it was` is a short human phrase
    /// ("parameter", "enum member of state_e", "imported from pkg p") because
    /// the surprise in these errors is usually not WHERE the first declaration
    /// is but WHAT it is.
    #[serde(default)]
    pub decl_sites: HashMap<String, (Span, String, bool)>,
    /// §26.3: names declared in packages this module does NOT import (see
    /// `compute_foreign_package_names`). A local declaration of one of these
    /// is legal and must win — they are only visible at all because package
    /// contents are registered in one flat design-wide namespace.
    #[serde(default)]
    pub foreign_package_names: HashSet<String>,
    /// Foreign-package names a local declaration has already displaced. A
    /// module gets ONE such declaration per name; a second is a real duplicate.
    #[serde(default)]
    pub foreign_displaced: HashSet<String>,
    /// IEEE 1800-2017 §6.2: names of 2-state-typed signals (bit, byte,
    /// shortint, int, longint). Assignments to these coerce X/Z
    /// source bits to 0.
    #[serde(default)]
    pub two_state_signals: crate::shared_names::SharedNameSet,
    /// Names of unpacked arrays whose synthesized element storage initializes
    /// to Z rather than X. This is for arrays of nets and unconnected
    /// input/inout ports; ordinary 4-state variable arrays still default to X.
    #[serde(default)]
    pub z_init_signals: HashSet<String>,
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
    /// Instance-scoped function bodies retained in shared definition syntax
    /// (keyed by `functions` key). Materialized on demand or by
    /// `materialize_pending`. Not serialized: artifact writers call
    /// `materialize_pending()` first.
    #[serde(skip)]
    pub deferred_function_bodies: HashMap<String, Rc<CallableRewriteCtx>>,
    /// Instance-scoped task bodies retained in shared definition syntax
    /// (keyed by `tasks` key).
    #[serde(skip)]
    pub deferred_task_bodies: HashMap<String, Rc<CallableRewriteCtx>>,
    /// §6.7.1 / §28.16 net delays, keyed by flat net name, as (rise, fall,
    /// turn-off) in ticks. A net delay belongs to the NET: it delays every
    /// driver of it, not only a declaration assignment. Recorded where each
    /// net is declared and consumed by `apply_net_delays` before the drivers
    /// are folded, so nothing downstream (and no cached artifact) sees it.
    #[serde(skip)]
    pub net_delays: HashMap<String, (u64, Option<u64>, Option<u64>, Option<DelayExpressions>)>,
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
    /// Instance-port net collapsing, for the dump writers only.
    ///
    /// `<inst>.<formal>` → the parent net the port's actual names, recorded ONLY
    /// when the actual is a SIMPLE WHOLE-NET identifier (`.din(src_bus)`). A
    /// bit-select, part-select, concatenation or expression actual
    /// (`.din(bus[3:0])`, `.din({a,b})`, `.din(w+1)`) is a distinct object and is
    /// NOT recorded — Verilator and a reference simulator keep those separate too.
    ///
    /// Inlining gives the formal its own signal-table entry, kept in step with
    /// the actual by a port continuous-assign, so a dump that treats the two as
    /// independent signals writes every change TWICE and shows one physical net
    /// as two. Both reference tools give the two names ONE identifier code (each
    /// still gets its own `$var` line in its own `$scope`). Chains through
    /// multiple levels (a port bound to a port), so consumers must resolve to a
    /// root.
    #[serde(default)]
    pub port_aliases: crate::shared_names::SharedNameMap<SharedName>,
    /// §23.3.3.7: `(net, bit)` of every bit a tri0 or tri1 port bound to a
    /// select has given its pull, so a second such port on the same bit adds
    /// none (the first connection decides, as on a whole net). Elaboration
    /// state only.
    #[serde(skip)]
    pub tri_select_pulls: HashSet<(String, u32)>,
    /// §25.3 / §23.8: an interface port is a hierarchical alias of its
    /// connected instance, including when reached from outside the module.
    #[serde(default)]
    pub interface_port_aliases: HashMap<String, String>,
    /// IEEE 1800-2023 §23.3.3: `(formal's path, actual, formal is 2-state)`
    /// of every input port whose reads in the instance body were renamed to
    /// its actual; the instance is the path's parent. The port is a
    /// continuous assignment from the actual, so its time-0 value is an
    /// update event in the instance — the simulator replays it for the blocks
    /// there, and for a parent's reference to the port by this path. The
    /// update starts from the formal's own initial value, unknown for a
    /// 4-state type and 0 for a 2-state one (§6.8), which an elided port no
    /// longer records anywhere else.
    #[serde(default)]
    pub input_port_actuals: Vec<InputPortActual>,
    /// §16.5.1: these input formals must keep their own prehistory when the
    /// simulator coalesces whole-net copies after elaboration.
    #[serde(default)]
    pub sampled_input_ports: HashSet<String>,
    /// Input ports whose net was never built (see [`set_port_elision`]): the
    /// [`elided_port_hash`] of each `<inst>.<port>` flat name, sorted. The
    /// simulator checks a failed name lookup against it, so a reference the
    /// elision analysis missed is reported instead of silently reading
    /// nothing. A port whose actual is the top-level net of its own name is
    /// not listed: a scoped lookup of it falls through to that very net.
    #[serde(default)]
    pub elided_port_hashes: Vec<u64>,
    /// How many input-port nets were left out (tracked or not).
    #[serde(default)]
    pub elided_port_count: usize,
    /// The distinct port names (last path segment) among the elided ports.
    #[serde(default)]
    pub elided_port_leaves: HashSet<String>,
    /// §10.11 `alias` net unification: (canonical, other) flat-name pairs.
    /// The simulator repoints `other`'s signal-table id at `canonical`'s so
    /// the names share ONE storage slot.
    #[serde(default)]
    pub alias_pairs: Vec<(String, String)>,
    /// §10.11 `alias` net unification, collected as GROUPS: every name an
    /// alias statement names is ONE physical net. The groups are cumulative
    /// ("The same nets can appear in multiple alias statements. The effects
    /// are cumulative"), so two groups naming a common net are one group.
    ///
    /// The names are the FLAT names of the scope the statement was written
    /// in (`g1`, `g.g1`, `u.p`), so a group's members are resolved against
    /// the elaborated net tables.
    #[serde(default)]
    pub alias_groups: Vec<Vec<String>>,
    /// §10.11: the canonical name of the group every alias member belongs
    /// to — the member names ONE physical net with the canonical's, so a
    /// driver of a member counts for the canonical (the driver count and
    /// the resolution fold of §6.6.1 key their work by it).
    #[serde(default)]
    pub alias_canon: HashMap<String, String>,
    /// §23.3.3.3: an INOUT port and the net it is connected to are ONE
    /// physical net. The map holds the formal name and the actual name of
    /// every such connection, so an alias group that reaches a port can
    /// take the port's net into the group (§10.11's "same physical net").
    /// An input or output port is a COPY, not a merge, and is not listed.
    #[serde(default)]
    pub net_port_merges: HashMap<String, String>,
    /// Preprocessed source text of each input file, in parse order, with
    /// `source_files` carrying the matching file names. A `Statement`'s
    /// `Span` is a byte offset into its OWN file's preprocessed text, so
    /// runtime diagnostics (e.g. the zero-delay stall report) resolve it
    /// against these to print `file:line`. Not serialized: compiled
    /// artifacts carry no sources, so artifact-driven runs simply degrade
    /// to span-less diagnostics.
    #[serde(skip)]
    pub source_texts: Vec<String>,
    /// Serialized (small): the compile-time source paths. Together with
    /// `src_file_of_module` this lets a cache-hit run repopulate
    /// `source_texts` (re-preprocessed by the cache-key pass) so runtime
    /// diagnostics keep their `file:line` resolution instead of degrading.
    #[serde(default)]
    pub source_files: Vec<String>,
    /// Source-file index (into `source_texts`/`source_files`) of each
    /// module/interface/program DEFINITION, by name. Filled by
    /// `parse_and_elaborate_multi`, where the per-file parse boundary still
    /// knows which file produced which definition. Runtime diagnostics map an
    /// offending process's instance scope → defining module (`instances`) →
    /// THIS file, so a span (a per-file byte offset) resolves against the
    /// right file in multi-file designs. Serialized (small name->index map)
    /// so cache-hit runs keep multi-file `file:line` diagnostics.
    #[serde(default)]
    pub src_file_of_module: HashMap<String, u32>,
    /// Line count of each source file BEFORE preprocessing, parallel to
    /// `source_texts`. A `Span` indexes the PREPROCESSED text, where an
    /// `\`include` has been spliced in whole, so a reported line can land far
    /// past the end of the file it names — a 10-line file that includes 3000
    /// lines reports line 3005. Keeping the original count lets a diagnostic
    /// SAY that the number is post-expansion instead of quoting a line that
    /// cannot exist.
    #[serde(default)]
    pub source_orig_lines: Vec<u32>,
    /// Line map of each of `source_texts` back to the original files (the
    /// `include`d file and line a span's text came from, and whether it is
    /// macro text), for `file:line:col` diagnostics. Not serialized, like
    /// `source_texts`.
    #[serde(skip)]
    pub source_line_maps: Vec<Option<sv_parser::source_map::LineMap>>,
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

    /// True when a local declaration of `name` legally displaces whatever the
    /// design-wide maps already hold for it, rather than conflicting with it:
    /// either §26.3 shadowing of a wildcard-imported name, or a name that only
    /// appeared because some package this module never imported declares it.
    /// Both mean "the local wins"; neither is an error.
    ///
    /// Non-consuming — this is also what suppresses the repeated design-wide
    /// re-registration of the displaced name, which has to keep applying for
    /// the whole elaboration. Use `claim_local_decl_displacement` for the
    /// once-per-name decision at a declaration.
    pub fn local_decl_displaces(&self, name: &str) -> bool {
        self.wildcard_shadowed.contains(name) || self.foreign_package_names.contains(name)
    }

    /// `local_decl_displaces`, but true only the FIRST time it is asked about a
    /// foreign-package name. A module is entitled to one declaration that
    /// displaces the package's; a SECOND declaration of the same name is an
    /// ordinary duplicate and must still be reported as one.
    pub fn claim_local_decl_displacement(&mut self, name: &str, span: Span, kind: &str) -> bool {
        let claimed = self.wildcard_shadowed.contains(name)
            || (self.foreign_package_names.contains(name)
                && self.foreign_displaced.insert(name.to_string()));
        if claimed && !(span.start == 0 && span.end == 0) {
            // The displaced declaration is no longer what `name` refers to
            // here, so it must stop being the "first declaration" a later
            // duplicate is blamed on — a second local declaration would
            // otherwise be pointed at a package member it has nothing to do
            // with. This one supersedes it, so overwrite rather than remove:
            // callers record their site at inconsistent points relative to
            // this check, and some never do.
            self.decl_sites
                .insert(name.to_string(), (span, kind.to_string(), true));
        }
        claimed
    }

    /// Remember where `name` was first declared, and as what. Later calls for
    /// the same name are ignored: a duplicate-declaration error has to point at
    /// the ORIGINAL, and overwriting would make it point at the duplicate.
    /// A synthesized (dummy) span records nothing — an entry with no location
    /// would only suppress the fallback description in the error text.
    /// `own_scope` says the span is in the source of the module being
    /// elaborated. That decides whether the span may be resolved with the
    /// "prefer this module's file" hint: for a declaration that came from
    /// somewhere else (a package's enum member, an imported parameter) the
    /// hint would confidently name the wrong file.
    pub fn note_decl_site(&mut self, name: &str, span: Span, kind: &str, own_scope: bool) {
        if own_scope && kind == "parameter/localparam" {
            self.declared_parameters.insert(name.to_string());
        }
        if span.start == 0 && span.end == 0 {
            return;
        }
        self.decl_sites
            .entry(name.to_string())
            .or_insert_with(|| (span, kind.to_string(), own_scope));
    }

    /// §23.2.2.1: a non-ANSI port declared without a net or variable type may
    /// be declared again ONCE, by a net or variable declaration. A second one
    /// (`output x; reg x; reg x;`, `input x; wire x; reg x;`) redeclares it.
    ///
    /// When the port declaration has an explicit range, a completing
    /// declaration that states its own shape must match it ("the range
    /// specification between the two declarations of a port shall be
    /// identical"); a bare `wire x;` takes the port's range.
    fn complete_port(
        &mut self,
        name: &str,
        span: Span,
        dt: &DataType,
        width: u32,
    ) -> Result<(), String> {
        if !self.completed_ports.insert(name.to_string()) {
            if sv_parser::strict_checks() {
                return Err(duplicate_decl_error(self, name, span, "variable/net"));
            }
            eprintln!(
                "[xezim][warning] duplicate declaration of port '{}'; keeping first definition",
                name
            );
            return Ok(());
        }
        let bare = matches!(dt, DataType::Implicit { dimensions, .. } if dimensions.is_empty());
        if let Some(&port_w) = self.ranged_port_widths.get(name)
            && !bare
            && port_w != width
            && sv_parser::strict_checks()
        {
            return Err(span_error(
                self,
                span,
                &format!(
                    "port '{}' is declared {} bits wide but redeclared {} bits wide; the \
                     port and its net/variable declaration must have identical ranges \
                     (IEEE 1800-2017 §23.2.2.1)",
                    name, port_w, width
                ),
            ));
        }
        Ok(())
    }

    fn note_explicit_type(&mut self, name: &str, dt: &DataType, span: Span) -> Result<(), String> {
        // A *bare* implicit type — `output x;` / `wire x;` (no range, no
        // signing) — carries no type; it is the legal half of a non-ANSI split
        // and is ignored here.
        let bare = matches!(dt,
            DataType::Implicit { dimensions, signing: None, .. } if dimensions.is_empty());
        if bare {
            return Ok(());
        }
        // An "incompatible" type cannot be combined with any other type spec:
        // a named type, an integer atom (int/integer/byte/…), real, string/
        // chandle/event, a struct/union, or an enum. A plain range
        // (`[7:0]`/Implicit-with-dims) or a vector keyword (logic/bit/reg) is
        // compatible — e.g. the standard `input [7:0] a; reg [7:0] a;` split is
        // legal. A second type-bearing declaration is a conflict only when one
        // of the two is incompatible.
        let incompat = matches!(
            dt,
            DataType::TypeReference { .. }
                | DataType::IntegerAtom { .. }
                | DataType::Real { .. }
                | DataType::Simple { .. }
                | DataType::Struct(_)
                | DataType::Enum(_)
        );
        if let Some(&prev_incompat) = self.typed_decls.get(name) {
            if incompat || prev_incompat {
                return Err(duplicate_decl_error(self, name, span, "variable/net"));
            }
        }
        self.typed_decls
            .entry(name.to_string())
            .and_modify(|v| *v = *v || incompat)
            .or_insert(incompat);
        self.note_decl_site(name, span, "variable/net", true);
        Ok(())
    }

    pub fn new(name: String) -> Self {
        Self {
            name,
            tick_s: default_tick_s(),
            signals: SharedNameMap::default(),
            typed_decls: HashMap::default(),
            completed_ports: HashSet::default(),
            ranged_port_widths: HashMap::default(),
            wildcard_shadowed: HashSet::default(),
            port_order: Vec::new(),
            continuous_assigns: Vec::new(),
            tran_switches: Vec::new(),
            udp_instances: Vec::new(),
            always_blocks: Vec::new(),
            initial_blocks: Vec::new(),
            final_blocks: Vec::new(),
            static_init_blocks: Vec::new(),
            program_initial_blocks: Vec::new(),
            parameters: HashMap::default(),
            declared_parameters: HashSet::default(),
            typedefs: TypedefTable::default(),
            typedef_types: SharedMap::default(),
            nettype_resolvers: HashMap::default(),
            shadowed_nettypes: HashSet::default(),
            arrays: HashMap::default(),
            associative_arrays: HashMap::default(),
            assoc_elem_widths: HashMap::default(),
            assoc_index_widths: HashMap::default(),
            classes: HashMap::default(),
            covergroups: HashMap::default(),
            functions: FuncTable::default(),
            tasks: HashMap::default(),
            func_decl_scope: HashMap::default(),
            class_decl_pkg: HashMap::default(),
            dpi_imports: HashMap::default(),
            dpi_import_pkg: HashMap::default(),
            dpi_import_in_design: HashSet::default(),
            dpi_exports: Vec::new(),
            dpi_export_c_names: Vec::new(),
            clocking_blocks: HashMap::default(),
            lets: HashMap::default(),
            hidden_bare_types: Vec::new(),
            modport_views: HashMap::default(),
            clocking_signal_dirs: HashMap::default(),
        clocking_output_stages: HashMap::default(),
            specify_delays: HashMap::default(),
            module_paths: HashMap::default(),
            timing_checks: Vec::new(),
            resolved_net_kinds: Default::default(),
            gate_fall_delays: HashMap::default(),
            gate_driven_nets: HashSet::default(),
            assoc_defaults: HashMap::default(),
            dynamic_arrays: HashSet::default(),
            net_strengths: HashMap::default(),
            strength_drivers: HashMap::default(),
            supply_nets: HashSet::default(),
            descending_arrays: HashSet::default(),
            unpacked_decl_dims: Default::default(),
            ascending_packed: HashMap::default(),
            typedef_unpacked_dims: HashMap::default(),
            queue_max_sizes: HashMap::default(),
            queue_vars: HashSet::default(),
            arrays_2d: HashMap::default(),
            packages: HashSet::default(),
            pkg_subr_owner: HashMap::default(),
            pkg_var_decls: HashMap::default(),
            pkg_var_init_blocks: Vec::new(),
            def_pkg_imports: HashMap::default(),
            sequences: Default::default(),
            packed_struct_fields: Default::default(),
            struct_field_range_idents: HashMap::default(),
            var_decl_types: Default::default(),
            param_decl_types: Default::default(),
            struct_members: Default::default(),
            packed_signal_elem_widths: Default::default(),
            typedef_elem_widths: HashMap::default(),
            packed_full_dims: Default::default(),
            vector_nets: Default::default(),
            string_signals: HashSet::default(),
            modport_member_dirs: HashMap::default(),
            class_type_args: HashMap::default(),
            interfaces: HashSet::default(),
            interface_param_defaults: HashMap::default(),
            checker_decls: HashMap::default(),
            property_decls: Default::default(),
            property_params: Default::default(),
            property_param_defaults: HashMap::default(),
            array_elem_class: HashMap::default(),
            assoc_key_type_names: HashMap::default(),
            coll_shapes: HashMap::default(),
            arrays_nd: HashMap::default(),
            deferred_param_exprs: Vec::new(),
            nets: Default::default(),
            implicit_nets: HashSet::default(),
            interconnect_nets: HashSet::default(),
            elab_diagnostics: Vec::new(),
            instances: Vec::new(),
            upward_scopes: Rc::default(),
            resolved_binds: HashMap::default(),
            bind_sites: Vec::new(),
            param_index: Default::default(),
            out_of_class_constraints: HashSet::default(),
            timeunit_exp: default_timeunit_exp(),
            timeprecision_exp: default_timeunit_exp(),
            module_timescale_exp: HashMap::default(),
            modules_without_timescale: Vec::new(),
            enum_members: HashMap::default(),
            package_enum_members: HashMap::default(),
            decl_sites: HashMap::default(),
            foreign_package_names: HashSet::default(),
            foreign_displaced: HashSet::default(),
            unit_member_slots: Vec::new(),
            two_state_signals: Default::default(),
            z_init_signals: HashSet::default(),
            pending_always: Vec::new(),
            pending_initial: Vec::new(),
            pending_cont_assign: Vec::new(),
            deferred_function_bodies: HashMap::default(),
            deferred_task_bodies: HashMap::default(),
            tri_select_pulls: HashSet::default(),
            net_delays: HashMap::default(),
            const_decl_inits: HashSet::default(),
            forward_typedef_names: HashSet::default(),
            events: HashSet::default(),
            port_aliases: Default::default(),
            interface_port_aliases: HashMap::default(),
            input_port_actuals: Vec::new(),
            sampled_input_ports: HashSet::default(),
            elided_port_hashes: Vec::new(),
            elided_port_count: 0,
            elided_port_leaves: HashSet::default(),
            alias_pairs: Vec::new(),
            alias_groups: Vec::new(),
            alias_canon: HashMap::default(),
            net_port_merges: HashMap::default(),
            source_texts: Vec::new(),
            source_files: Vec::new(),
            src_file_of_module: HashMap::default(),
            source_orig_lines: Vec::new(),
            source_line_maps: Vec::new(),
        }
    }

    /// Materialize a deferred function body into a private `SharedVec` using
    /// the caller's current scope-cache mode, or `None` when not deferred.
    pub fn materialize_function_body(
        &self,
        key: &str,
        fd: &FunctionDeclaration,
    ) -> Option<crate::ast::shared_vec::SharedVec<Statement>> {
        self.deferred_function_bodies
            .get(key)
            .map(|ctx| ctx.materialize_body(&fd.ports, &fd.items).into())
    }

    /// Materialize a deferred task body into a private `SharedVec` using
    /// the caller's current scope-cache mode, or `None` when not deferred.
    pub fn materialize_task_body(
        &self,
        key: &str,
        td: &TaskDeclaration,
    ) -> Option<crate::ast::shared_vec::SharedVec<Statement>> {
        self.deferred_task_bodies
            .get(key)
            .map(|ctx| ctx.materialize_body(&td.ports, &td.items).into())
    }

    /// Borrow or materialize a function's instance-rewritten statements for a
    /// read-only pass (keeping scope caches disabled if materialized).
    pub fn resolved_function_items<'a>(
        &self,
        key: &str,
        fd: &'a FunctionDeclaration,
    ) -> std::borrow::Cow<'a, [Statement]> {
        match self.deferred_function_bodies.get(key) {
            Some(ctx) => std::borrow::Cow::Owned(crate::ast::cache::without_scope_caches(|| {
                ctx.materialize_body(&fd.ports, &fd.items)
            })),
            None => std::borrow::Cow::Borrowed(&fd.items),
        }
    }

    /// Borrow or materialize a task's instance-rewritten statements for a
    /// read-only pass (keeping scope caches disabled if materialized).
    pub fn resolved_task_items<'a>(
        &self,
        key: &str,
        td: &'a TaskDeclaration,
    ) -> std::borrow::Cow<'a, [Statement]> {
        match self.deferred_task_bodies.get(key) {
            Some(ctx) => std::borrow::Cow::Owned(crate::ast::cache::without_scope_caches(|| {
                ctx.materialize_body(&td.ports, &td.items)
            })),
            None => std::borrow::Cow::Borrowed(&td.items),
        }
    }

    /// Materialize one deferred function body in place inside `self.functions`.
    /// Returns `true` if `key` was deferred and materialized.
    pub fn materialize_function(&mut self, key: &str) -> bool {
        let Some(ctx) = self.deferred_function_bodies.remove(key) else {
            return false;
        };
        let Some(mut fd) = self.functions.get(key).cloned() else {
            return false;
        };
        fd.items =
            crate::ast::cache::without_scope_caches(|| ctx.materialize_body(&fd.ports, &fd.items))
                .into();
        self.functions.insert(key.to_string(), fd);
        true
    }

    /// Materialize one deferred task body in place inside `self.tasks`.
    /// Returns `true` if `key` was deferred and materialized.
    pub fn materialize_task(&mut self, key: &str) -> bool {
        let Some(ctx) = self.deferred_task_bodies.remove(key) else {
            return false;
        };
        let Some(td) = self.tasks.get_mut(key) else {
            return false;
        };
        td.items =
            crate::ast::cache::without_scope_caches(|| ctx.materialize_body(&td.ports, &td.items))
                .into();
        true
    }

    /// Whether `name` is a declared sequence, property, or checker — either
    /// with a body in `property_decls` or bodyless in `sequences` (#721).
    pub fn has_named_sva(&self, name: &str) -> bool {
        self.property_decls.contains_key(name) || self.sequences.contains(name)
    }

    /// Materialize every deferred instance-scoped function and task body in
    /// place (`self.functions` / `self.tasks`) with scope caches disabled.
    pub fn materialize_pending_callables(&mut self) {
        let deferred_fns = std::mem::take(&mut self.deferred_function_bodies);
        if !deferred_fns.is_empty() {
            let mut functions = std::mem::take(&mut self.functions).into_map();
            for (key, ctx) in deferred_fns {
                if let Some(fd) = functions.get_mut(&key) {
                    fd.items = crate::ast::cache::without_scope_caches(|| {
                        ctx.materialize_body(&fd.ports, &fd.items)
                    })
                    .into();
                }
            }
            self.functions = FuncTable::from_map(functions);
        }
        let deferred_tasks = std::mem::take(&mut self.deferred_task_bodies);
        for (key, ctx) in deferred_tasks {
            if let Some(td) = self.tasks.get_mut(&key) {
                td.items = crate::ast::cache::without_scope_caches(|| {
                    ctx.materialize_body(&td.ports, &td.items)
                })
                .into();
            }
        }
    }

    /// Eager (non-streaming) drain of pending procedural blocks. Materializes
    /// every Pending* into the corresponding always_blocks/initial_blocks/
    /// continuous_assigns vec, and materializes deferred callable bodies. Keeps
    /// semantics identical to pre-#7 elaborate at the cost of high peak memory
    /// — use streaming drains in performance-sensitive paths (see
    /// drain_pending_*_for_each).
    pub fn materialize_pending(&mut self) {
        self.materialize_pending_callables();
        let pending_always = std::mem::take(&mut self.pending_always);
        for p in pending_always {
            self.always_blocks.push(p.materialize());
        }
        let pending_initial = std::mem::take(&mut self.pending_initial);
        for p in pending_initial {
            self.initial_blocks.push(p.materialize());
        }
        self.materialize_pending_cont_assigns();
    }

    fn materialize_pending_cont_assigns(&mut self) {
        let pending_ca = std::mem::take(&mut self.pending_cont_assign);
        // One allocation for the lot: growing the table a push at a time
        // copies it at every doubling, old and new buffer held together,
        // and leaves up to half of the last one unused (aionhw/xezim#721).
        self.continuous_assigns.reserve_exact(pending_ca.len());
        for p in pending_ca {
            let ca = p.materialize(&self.parameters);
            // A sub-module's `assign dst = src;` between unpacked arrays
            // arrives here (inlined bodies bypass the ModuleItem path), so it
            // needs the same per-element expansion — otherwise an array OUTPUT
            // PORT driven that way never propagates and the parent's array
            // stays x for the whole run.
            if !expand_whole_array_assign(&ca, self) {
                self.continuous_assigns.push(ca);
            }
        }
    }

    /// Streaming drain for pending always-blocks. Each block is materialized
    /// just before the callback runs, then dropped. Peak memory is one
    /// materialized AlwaysBlock at a time. Intended consumer: bytecode
    /// compiler — `f` should compile and discard the AST.
    pub fn drain_pending_always_for_each<F: FnMut(AlwaysBlock)>(&mut self, mut f: F) {
        let pending = std::mem::take(&mut self.pending_always);
        for p in pending {
            f(p.materialize());
        }
    }

    /// Streaming drain for pending initial-blocks.
    pub fn drain_pending_initial_for_each<F: FnMut(InitialBlock)>(&mut self, mut f: F) {
        let pending = std::mem::take(&mut self.pending_initial);
        for p in pending {
            f(p.materialize());
        }
    }

    /// Streaming drain for pending continuous-assigns.
    pub fn drain_pending_cont_assign_for_each<F: FnMut(ContinuousAssignment)>(&mut self, mut f: F) {
        let pending = std::mem::take(&mut self.pending_cont_assign);
        for p in pending {
            let ca = p.materialize(&self.parameters);
            // Same unpacked-array expansion the eager drain does; this is the
            // path the bytecode compiler takes, and a sub-module's
            // `assign dst = src;` between arrays reaches only one of the two.
            match self.whole_array_driver_parts(&ca.lhs, &ca.rhs, ca.delay, &self.unpacked_decl_dims)
            .or_else(|| {
                slice_array_assign_parts(
                    &ca.lhs,
                    &ca.rhs,
                    ca.delay,
                    &self.arrays,
                    Some(&self.descending_arrays),
                    Some(&self.unpacked_decl_dims),
                    &self.parameters,
                )
            })
            .or_else(|| {
                self.with_unpacked_array_tables(|t| {
                    concat_array_assign_parts(&ca.lhs, &ca.rhs, ca.delay, t)
                })
            }) {
                Some(parts) => {
                    for mut e in parts {
                        e.inherit_driver_metadata(&ca);
                        f(e);
                    }
                }
                None => f(ca),
            }
        }
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
    /// IEEE 1800-2017 §29 User-Defined Primitive.
    Udp(&'a crate::ast::decl::UdpDecl),
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
            Definition::Udp(u) => &u.name.name,
        }
    }

    pub fn params(&self) -> &[ParameterDeclaration] {
        match self {
            Definition::Module(m) => &m.params,
            Definition::Interface(i) => &i.params,
            Definition::Program(p) => &p.params,
            Definition::Class(c) => &c.params,
            Definition::Covergroup(_)
            | Definition::Package(_)
            | Definition::Typedef(_)
            | Definition::Udp(_) => &[],
        }
    }

    /// §6.20.3: body type parameters bind types like header parameters.
    /// Body value parameters retain their separate fixpoint/override path.
    fn params_and_body_types(&self) -> impl Iterator<Item = &ParameterDeclaration> {
        self.params()
            .iter()
            .chain(self.items().iter().filter_map(|item| {
                let (ModuleItem::ParameterDeclaration(pd) | ModuleItem::LocalparamDeclaration(pd)) =
                    item
                else {
                    return None;
                };
                matches!(pd.kind, ParameterKind::Type { .. }).then_some(pd)
            }))
    }

    pub fn ports(&self) -> &PortList {
        match self {
            Definition::Module(m) => &m.ports,
            Definition::Interface(i) => &i.ports,
            Definition::Program(p) => &p.ports,
            Definition::Class(_)
            | Definition::Covergroup(_)
            | Definition::Package(_)
            | Definition::Typedef(_)
            | Definition::Udp(_) => &PortList::Empty,
        }
    }
    pub fn items(&self) -> &[ModuleItem] {
        match self {
            Definition::Module(m) => &m.items,
            Definition::Interface(i) => &i.items,
            Definition::Program(p) => &p.items,
            Definition::Class(_)
            | Definition::Covergroup(_)
            | Definition::Package(_)
            | Definition::Typedef(_)
            | Definition::Udp(_) => &[],
        }
    }
}

/// Whether a `gated_clk_cell` definition is the OpenC910 pass-through:
/// `clk_in` an input, `clk_out` the only output, driven solely by an
/// undelayed `assign clk_out = clk_in;`, and nothing else in the body but
/// declarations and continuous assignments to internal nets (the dead enable
/// logic). Such an instance behaves as a direct assignment of its
/// connections; anything else (a latch, an `always` block, an instance,
/// another output) is a real cell and must be elaborated as written. So is a
/// cell whose `clk_in` or `clk_out` net has a delay (§6.7.1, §28.16), a drive
/// strength, or a net type that resolves or holds a value (§6.6): the direct
/// assignment would drop it, and clock edges would arrive early or differ.
/// And so is one whose `clk_in` or `clk_out` is not a scalar four-state
/// value: a `bit` port turns an x or z clock into 0 (§6.11.2), and a vector,
/// signed or unpacked port resizes or sign-extends the value it passes
/// (§23.3.3), which the direct assignment of the connections would not.
fn is_clock_passthrough_cell(def: &Definition) -> bool {
    let Definition::Module(_) = def else {
        return false;
    };
    let clock_port = |n: &str| n == "clk_in" || n == "clk_out";
    let plain_net = |t: Option<&NetType>| {
        matches!(t, None | Some(NetType::Wire | NetType::Tri | NetType::Uwire))
    };
    let scalar_4state = |dt: Option<&DataType>, unpacked: &[UnpackedDimension]| {
        unpacked.is_empty()
            && match dt {
                None => true,
                Some(DataType::Implicit {
                    signing: None,
                    dimensions,
                    ..
                })
                | Some(DataType::IntegerVector {
                    kind: IntegerVectorType::Logic | IntegerVectorType::Reg,
                    signing: None,
                    dimensions,
                    ..
                }) => dimensions.is_empty(),
                Some(_) => false,
            }
    };
    let mut dirs: HashMap<&str, PortDirection> = HashMap::default();
    if let PortList::Ansi(ports) = def.ports() {
        // §23.2.2.3: an ANSI port without a direction inherits the previous.
        let mut last = PortDirection::Inout;
        for p in ports {
            if let Some(d) = p.direction {
                last = d;
            }
            if clock_port(&p.name.name)
                && (!plain_net(p.net_type.as_ref())
                    || !scalar_4state(p.data_type.as_ref(), &p.dimensions))
            {
                return false;
            }
            dirs.insert(p.name.name.as_str(), last);
        }
    }
    let is_ident = |e: &Expression, name: &str| {
        matches!(&e.kind, ExprKind::Ident(h)
            if h.root.is_none()
                && h.path.len() == 1
                && h.path[0].selects.is_empty()
                && h.path[0].name.name == name)
    };
    let mut out_drivers = 0usize;
    let mut internal_lhs: Vec<&Expression> = Vec::new();
    for item in def.items() {
        match item {
            ModuleItem::PortDeclaration(pd) => {
                for d in &pd.declarators {
                    if d.init.is_some()
                        || (clock_port(&d.name.name)
                            && (!plain_net(pd.net_type.as_ref())
                                || !scalar_4state(Some(&pd.data_type), &d.dimensions)))
                    {
                        return false;
                    }
                    dirs.insert(d.name.name.as_str(), pd.direction);
                }
            }
            ModuleItem::NetDeclaration(nd) => {
                let shaped = nd.delay.is_some()
                    || nd.delay_fall.is_some()
                    || nd.delay_off.is_some()
                    || nd.strength.is_some()
                    || !plain_net(Some(&nd.net_type));
                if nd.declarators.iter().any(|d| {
                    clock_port(&d.name.name)
                        && (shaped
                            || d.init.is_some()
                            || !scalar_4state(Some(&nd.data_type), &d.dimensions))
                }) {
                    return false;
                }
            }
            ModuleItem::DataDeclaration(dd) => {
                if dd.declarators.iter().any(|d| {
                    clock_port(&d.name.name)
                        && (d.init.is_some() || !scalar_4state(Some(&dd.data_type), &d.dimensions))
                }) {
                    return false;
                }
            }
            ModuleItem::ContinuousAssign(ca) => {
                if ca.delay.is_some() || ca.strength.is_some() {
                    return false;
                }
                for (lhs, rhs) in &ca.assignments {
                    if is_ident(lhs, "clk_out") {
                        if !is_ident(rhs, "clk_in") {
                            return false;
                        }
                        out_drivers += 1;
                    } else {
                        internal_lhs.push(lhs);
                    }
                }
            }
            ModuleItem::ParameterDeclaration(_)
            | ModuleItem::LocalparamDeclaration(_)
            | ModuleItem::TimeunitsDecl(_) => {}
            _ => return false,
        }
    }
    // Every other driven net must be internal: an assignment to a port, or
    // to a part of `clk_out`, is observable outside the cell.
    let internal = |e: &Expression| match &e.kind {
        ExprKind::Ident(h) if h.root.is_none() && h.path.len() == 1 => {
            !dirs.contains_key(h.path[0].name.name.as_str())
        }
        _ => false,
    };
    out_drivers == 1
        && internal_lhs.iter().all(|e| internal(e))
        && dirs.get("clk_in") == Some(&PortDirection::Input)
        && dirs.get("clk_out") == Some(&PortDirection::Output)
        && dirs.iter().all(|(n, d)| {
            *n == "clk_out" || !matches!(d, PortDirection::Output | PortDirection::Inout)
        })
}

/// Elaborate a module or interface declaration into a simulation model.
pub fn elaborate_module(
    module: Definition,
    param_overrides: &HashMap<String, Value>,
) -> Result<ElaboratedModule, String> {
    elaborate_module_with_defs(module, param_overrides, None, &[], &[], &[])
}

/// `XEZIM_TRACE_SIGNAL=<substr>[,<substr>...]` — trace every write to the
/// elaboration signal table for matching names. The type-table tracer proved
/// a declaration can be SIZED correctly (resolve:type_ref logs 292) while the
/// simulated signal ends up narrower: a later plain `signals.insert` silently
/// replaces the entry, and no width-resolution trace can see that. Each hit
/// logs the source line of the insert, the new width, and the width it
/// replaced — `prev_width=Some(292)` with a smaller new width is the smoking
/// gun, and the line number names the guilty path.
fn signal_trace_patterns() -> &'static Option<Vec<String>> {
    static PATS: std::sync::OnceLock<Option<Vec<String>>> = std::sync::OnceLock::new();
    PATS.get_or_init(|| match std::env::var("XEZIM_TRACE_SIGNAL") {
        Ok(v) if !v.trim().is_empty() => Some(
            v.split(',')
                .map(|s| s.trim().to_string())
                .filter(|s| !s.is_empty())
                .collect(),
        ),
        _ => None,
    })
}

pub(crate) fn signals_insert_traced(
    map: &mut SharedNameMap<Signal>,
    line: u32,
    name: String,
    sig: Signal,
) -> Option<Signal> {
    if let Some(pats) = signal_trace_patterns() {
        if pats.iter().any(|p| name.contains(p.as_str())) {
            eprintln!(
                "[xezim][trace-signal] insert@elaborate.rs:{} key={} width={} prev_width={:?}",
                line,
                name,
                sig.width,
                map.get(&name).map(|s| s.width)
            );
        }
    }
    map.insert(name, sig)
}

/// Declaration-order snapshots are immutable inside procedural scopes.
/// Sharing them avoids copying every module declaration for each function,
/// block and condition; module/generate declarations retain copy-on-write
/// isolation (§6.5, §6.21).
#[derive(Clone, Default)]
struct DeclaredModuleNames(Rc<HashSet<String>>);

#[cfg(test)]
mod declaration_order_snapshot_tests;

/// §23.11: the instances the compilation-unit `bind` directives add. A bound
/// instance is instantiated in its target, so the target can start a
/// hierarchical name with it (`a.y`), but the undeclared-name checks run on
/// each definition before those binds are applied. A module-scope bind is in
/// the definitions already (`collect_design_declared_names`).
#[derive(Default)]
pub(crate) struct UnitBindInstances {
    /// Every instance name, for the instance bodies, whose check accepts any
    /// name the design declares.
    names: HashSet<String>,
    /// The names a bind adds to every instance of a module (`bind t c a();`),
    /// by that module: what a top's own processes can name. A bind into an
    /// instance path never targets the top itself.
    by_module: HashMap<String, HashSet<String>>,
}

/// An overlay stacked onto any `&dyn ParamLookup` (`top` wins), used to avoid
/// cloning `base` when materializing package-local bare aliases.
struct StackedParamEnv<'a> {
    base: &'a dyn ParamLookup,
    top: &'a HashMap<String, Value>,
}

struct ParamDeclPolicy<'a> {
    unresolved_call: UnresolvedCallPolicy<'a>,
    promote_implicit_real: bool,
    narrow_implicit_string_lit: bool,
    force_signed_on_override: bool,
    eval_packed_aggregate: bool,
    require_known_idents: bool,
    signed_from_pkg_helper: bool,
}
struct ParamResolution {
    val: Value,
    width: u32,
    is_real: bool,
    signed: bool,
    skipped: bool,
}

/// §10.9.1 / §10.9.2: the type keys and `default:` key of a structure or
/// array pattern, which reach every member or element that no position,
/// name or index key sets, and recursively the members and elements of an
/// aggregate one they reach.
#[derive(Default)]
struct PatternKeys {
    types: Vec<(DataType, Expression)>,
    default: Option<Expression>,
}

/// The elements of one fixed unpacked array member of a structure pattern.
struct ArraySlot<'a> {
    elem_dt: &'a DataType,
    typedef_types: &'a HashMap<String, DataType>,
    params: &'a HashMap<String, Value>,
    /// The instance scope of the assignment (`""` for the top), whose
    /// parameters a `name:` index key names.
    scope: &'a str,
    default_types: Option<&'a ElaboratedModule>,
}

#[derive(Debug, Clone)]
struct PreparedModuleItems {
    interface_array_bounds: Vec<(String, (i64, i64))>,
    effective_items: Vec<ModuleItem>,
    body_sources: Vec<BodySource>,
    has_subroutines: bool,
    local_typedefs: std::collections::HashSet<String>,
    interface_ports: std::collections::HashSet<String>,
    port_directions: HashMap<String, PortDirection>,
    local_names: std::rc::Rc<std::collections::HashSet<String>>,
    /// Port names this module's own body DRIVES: a continuous-assign or
    /// procedural-assignment target, a gate output, or an actual bound to an
    /// output/inout of a sub-instance.
    ///
    /// Driving an `input` is illegal (§23.3.3) but xezim runs such designs,
    /// and it only works because the port is substituted away — the write
    /// then lands on the parent net directly. Such a port must therefore keep
    /// its substitution even when its shape argues against it (see
    /// `no_subst_ports`): routing the write to the port's own signal instead
    /// would leave it fighting the connection assign, and the parent net
    /// would never see the value.
    ///
    /// Deliberately OVER-approximates — an unresolvable sub-instance counts
    /// as driving every actual it is passed. Naming a port here only forgoes
    /// a shape fix; missing one would break a working design.
    body_driven_ports: std::collections::HashSet<String>,
    /// §16.5.1: sampled input ports retain a distinct default from the driver.
    sampled_ports: std::collections::HashSet<String>,
}
/// What the inlining of one design computes once and reuses for each
/// instance.
#[derive(Default)]
struct InlineCache {
    /// Portless compilation-unit binds keyed by target definition (§23.11).
    unit_module_binds: HashMap<String, Vec<crate::ast::decl::BindDirective>>,
    /// Prepared bodies (`prepare_module_items`).
    prepared: prepared_bodies::PreparedBodies,
    /// Whether preparation leaves value-parameter references symbolic.
    value_independent: HashMap<(String, usize), bool>,
    /// §23.10 / §27 (#721): the distinct prepared bodies of each definition,
    /// by content. Parameter values that change no generate choice, range or
    /// declaration (an index passed down a generate loop) yield equal bodies;
    /// those instances share one instead of each retaining its own copy.
    /// It owns no body: one that `prepared` released is gone from here too.
    equal_prepared: HashMap<(String, usize), EqualPrepared>,
    process_bodies: crate::ast_intern::AstInterner<Rc<Statement>>,
    named_sva_bodies: crate::ast_intern::AstInterner<Rc<Expression>>,
    callable_bodies: crate::ast_intern::AstInterner<crate::ast::shared_vec::SharedVec<Statement>>,
    /// Cache-disabled shared source bodies keyed by original `Arc` pointer,
    /// avoiding repeated cloning/interning across sibling instances (#193).
    /// The source is held weakly: a prepared body released after its
    /// instance is freed, and the entry still keeps its address from reuse.
    shared_callable_sources: HashMap<
        usize,
        (
            std::sync::Weak<Vec<Statement>>,
            crate::ast::shared_vec::SharedVec<Statement>,
        ),
    >,
    /// §6.20.3 / §20.7: equal type bindings and their independent width/query
    /// snapshots are immutable. Keep one copy through deferred rewriting.
    type_binds: context_maps::MapInterner<DataType>,
    /// §6.8: one copy of each declared type of each definition, shared by
    /// the signals its instances declare with it.
    decl_types: crate::decl_types::DeclTypeInterner,
    type_widths: context_maps::MapInterner<u32>,
    type_queries: context_maps::MapInterner<TypeQueryDims>,
    /// Per definition, the typedefs its imports bind, one list per import.
    imports: HashMap<(String, usize), Rc<[ImportedTypedefs]>>,
    /// Per package, the typedefs `import P::*` binds.
    wildcards: HashMap<String, ImportedTypedefs>,
    /// Module/interface/program definitions whose `import P::*` bindings
    /// (bare params, functions, tasks) were folded into the elaborated
    /// module. `process_import` has design-wide effects, so it must run once
    /// per definition, not once per instance of the definition.
    param_imports_done: std::collections::HashSet<String>,
}
/// The distinct prepared bodies of one definition that are still held. The
/// first body is kept unencoded: most definitions are prepared under one
/// parameter environment only, and comparison is needed only once a second
/// one appears.
#[derive(Default)]
struct EqualPrepared {
    first: Option<std::rc::Weak<PreparedModuleItems>>,
    by_content: HashMap<(u64, usize), Vec<std::rc::Weak<PreparedModuleItems>>>,
    /// The size of `by_content` at which the released bodies are next
    /// dropped from it.
    sweep_at: usize,
}
/// Everything a prepared body holds, encoded in a fixed order (sets sorted).
struct PreparedView<'a>(&'a PreparedModuleItems);

/// §23.10.1: a `defparam` on its way to its target: the remaining path, the
/// value already evaluated in the declaring scope, and where it is written
/// (the target's span and the definition holding it), so an illegal target
/// is reported at the `defparam` even when the child is in another file.
#[derive(Clone)]
struct PendingDefparam {
    path: Vec<String>,
    value: Value,
    span: Span,
    owner: String,
}

/// Static filter indexing every target that any `bind` directive in the
/// design could ever match. When empty (`collect` returns `None`),
/// non-bind designs retain zero `TargetScope` state.
struct BindTargetFilter {
    target_defs: HashSet<String>,
    target_leaf_names: HashSet<String>,
    can_target_top: bool,
    has_non_plain_bind: bool,
}
/// Elaboration environment captured for a scope that may receive bound
/// instances on a later `bind` fixed-point pass.
struct TargetScope {
    def_name: String,
    local_names: Option<Rc<std::collections::HashSet<String>>>,
    local_typedefs: Option<Box<std::collections::HashSet<String>>>,
    interface_map: HashMap<String, String>,
    port_map: Rc<HashMap<String, Expression>>,
    local_params: HashMap<String, Value>,
    defparams: Vec<PendingDefparam>,
    type_overlay: Option<Box<TargetTypeOverlay>>,
    items_end: usize,
    was_flat_leaf: bool,
}
struct BindWorklistState {
    filter: BindTargetFilter,
    scopes: HashMap<String, TargetScope>,
    needs_full_rebuild: bool,
    /// A target's input ports were kept for a checker or other non-plain
    /// bind: this walk is no longer the one a design without the bind gets.
    kept_bound_ports: bool,
}
struct ModuleInlineMeta {
    items_end: usize,
    was_flat_leaf: bool,
    local_names: Option<Rc<std::collections::HashSet<String>>>,
    local_typedefs: Option<Box<std::collections::HashSet<String>>>,
    defparams: Vec<PendingDefparam>,
}

mod identity_rewrite;

#[cfg(test)]
mod package_shadow_tests;

#[cfg(test)]
mod logged_map_tests {
    use super::*;

    /// §7.8.2: a string key reached through typedef aliases remains unbounded;
    /// its placeholder type width must not become an integral index width.
    #[test]
    fn aliased_string_key_has_no_integral_width() {
        fn alias(name: &str) -> DataType {
            let span = Span::new(0, 0);
            DataType::TypeReference {
                name: crate::ast::types::TypeName {
                    scopes: Vec::new(),
                    name: Identifier {
                        name: name.into(),
                        span,
                    },
                    span,
                    bound: Default::default(),
                },
                dimensions: Vec::new(),
                type_args: Vec::new(),
                span,
            }
        }
        let mut types = HashMap::default();
        types.insert(
            "text_t".into(),
            DataType::Simple {
                kind: SimpleType::String,
                span: Span::new(0, 0),
            },
        );
        types.insert("key_t".into(), alias("text_t"));
        let mut widths = HashMap::default();
        widths.insert("key_t".into(), 32);
        assert_eq!(
            assoc_key_type_info(Some(&alias("key_t")), &HashMap::default(), &widths, &types),
            (None, Some("key_t".into())),
        );
    }

    /// §7.4.5: dynamic rows retain associative key types across artifacts;
    /// fixed rows and scalar dynamic arrays keep their existing metadata.
    #[test]
    fn dynamic_associative_property_metadata_roundtrips() {
        let parsed = crate::parse(
            "class holder; int v[][string]; int deep[][string][int]; int fixed_rows[2][string]; int plain[]; endclass",
        );
        assert!(parsed.errors.is_empty(), "{:?}", parsed.errors);
        let crate::ast::Description::Class(decl) = &parsed.source.descriptions[0] else {
            panic!("class expected");
        };
        let cd = elaborate_class(decl);
        assert_eq!(cd.dynamic_assoc_properties.len(), 2);
        assert_eq!(cd.dynamic_assoc_properties["v"].len(), 1);
        assert_eq!(cd.dynamic_assoc_properties["deep"].len(), 2);
        assert!(cd.queue_properties.contains_key("v"));
        assert!(cd.array_of_coll_properties.contains_key("fixed_rows"));
        assert!(!cd.assoc_properties.contains_key("v"));
        let cfg = crate::xez_bincode_config();
        let encoded = bincode::serde::encode_to_vec(&cd, cfg).unwrap();
        let (restored, _): (ElaboratedClass, usize) =
            bincode::serde::decode_from_slice(&encoded, cfg).unwrap();
        assert!(
            matches!(&restored.dynamic_assoc_properties["v"][0], UnpackedDimension::Associative { data_type: Some(dt), .. }
            if matches!(dt.as_ref(), DataType::Simple { kind: SimpleType::String, .. }))
        );
        assert_eq!(restored.dynamic_assoc_properties["deep"].len(), 2);
    }

    /// §7.4.5: a dynamic or queue outer dimension over unpacked rows keeps
    /// its row dimensions across artifacts; an associative tail, a scalar
    /// dynamic array and a fixed outer shape record none.
    #[test]
    fn dynamic_tail_property_metadata_roundtrips() {
        let parsed = crate::parse(
            "class holder; bit [7:0] raw[][2]; int d[][]; int q3[$][2][3]; int v[][string]; int plain[]; int fixed[2][3]; endclass",
        );
        assert!(parsed.errors.is_empty(), "{:?}", parsed.errors);
        let crate::ast::Description::Class(decl) = &parsed.source.descriptions[0] else {
            panic!("class expected");
        };
        let cd = elaborate_class(decl);
        assert_eq!(cd.dynamic_tail_properties.len(), 3);
        assert_eq!(cd.dynamic_tail_properties["raw"].len(), 1);
        assert!(matches!(
            cd.dynamic_tail_properties["d"][..],
            [UnpackedDimension::Unsized(_)]
        ));
        assert_eq!(cd.dynamic_tail_properties["q3"].len(), 2);
        assert!(cd.queue_properties.contains_key("raw"));
        assert!(!cd.dynamic_tail_properties.contains_key("v"));
        let cfg = crate::xez_bincode_config();
        let encoded = bincode::serde::encode_to_vec(&cd, cfg).unwrap();
        let (restored, _): (ElaboratedClass, usize) =
            bincode::serde::decode_from_slice(&encoded, cfg).unwrap();
        assert_eq!(restored.dynamic_tail_properties["q3"].len(), 2);
    }

    fn tls_snapshot() -> Option<HashMap<String, u32>> {
        TYPEDEFS_TLS.with(|c| c.borrow().clone())
    }

    fn same(a: &HashMap<String, u32>, b: &HashMap<String, u32>) -> bool {
        a.len() == b.len() && a.iter().all(|(k, v)| b.get(k) == Some(v))
    }

    /// #721: no-op width bindings must not grow the retained change log,
    /// and replay positions must still describe actual mutations exactly.
    #[test]
    fn unchanged_typedef_widths_do_not_advance_snapshot_positions() {
        let mut table = TypedefTable::default();
        assert_eq!(table.insert_if_changed("word_t".into(), 8), None);
        let id = table.ident.0;
        sync_typedefs_tls(&table);
        let seen = table.log.len();
        let mut older_snapshot = (*table.map).clone();

        for _ in 0..1000 {
            assert_eq!(table.insert_if_changed("word_t".into(), 8), Some(8));
            assert_eq!(table.log.len(), seen);
            sync_typedefs_tls(&table);
            assert_eq!(TYPEDEFS_TLS_MIRROR.with(|m| m.get()), Some((id, seen)));
        }
        assert_eq!(table.insert_if_changed("word_t".into(), 16), Some(8));
        assert_eq!(table.remove("word_t"), Some(16));
        assert_eq!(table.remove("word_t"), None);
        assert_eq!(table.insert_if_changed("word_t".into(), 32), None);
        assert_eq!(table.insert_if_changed("word_t".into(), 32), Some(32));
        assert_eq!(table.insert_if_changed("other_t".into(), 4), None);
        assert_eq!(table.log.len(), seen + 4);

        // A snapshot may miss a width change, removal and reinsertion:
        // replay still restores the final table, including deleted keys.
        table.replay_into(&mut older_snapshot, seen);
        assert!(same(&older_snapshot, table.as_map()));
        sync_typedefs_tls(&table);
        assert!(same(&tls_snapshot().unwrap(), table.as_map()));
        let seen = table.log.len();
        assert_eq!(table.remove("word_t"), Some(32));
        let mut deleted_snapshot = older_snapshot;
        table.replay_into(&mut deleted_snapshot, seen);
        assert!(same(&deleted_snapshot, table.as_map()));
    }

    /// #721: clones and deserialized tables own fresh identities. Skipping
    /// no-ops must never make their empty logs reuse another table's TLS.
    #[test]
    fn unchanged_widths_preserve_clone_and_roundtrip_snapshot_identity() {
        let mut original = TypedefTable::default();
        original.insert_if_changed("word_t".into(), 8);
        sync_typedefs_tls(&original);
        let mut cloned = original.clone();
        assert_ne!(cloned.ident.0, original.ident.0);
        assert!(cloned.log.is_empty());
        assert_eq!(cloned.insert_if_changed("word_t".into(), 8), Some(8));
        assert!(cloned.log.is_empty());
        cloned.insert_if_changed("word_t".into(), 16);
        sync_typedefs_tls(&cloned);
        assert_eq!(tls_snapshot().unwrap()["word_t"], 16);
        sync_typedefs_tls(&original);
        assert_eq!(tls_snapshot().unwrap()["word_t"], 8);

        let config = crate::xez_bincode_config();
        let encoded = bincode::serde::encode_to_vec(&cloned, config).unwrap();
        let (mut restored, _): (TypedefTable, usize) =
            bincode::serde::decode_from_slice(&encoded, config).unwrap();
        assert_ne!(restored.ident.0, cloned.ident.0);
        assert!(restored.log.is_empty());
        assert_eq!(restored.insert_if_changed("word_t".into(), 16), Some(16));
        assert!(restored.log.is_empty());
        sync_typedefs_tls(&restored);
        assert_eq!(tls_snapshot().unwrap()["word_t"], 16);
        original.insert_if_changed("word_t".into(), 32);
        sync_typedefs_tls(&original);
        assert_eq!(tls_snapshot().unwrap()["word_t"], 32);
        sync_typedefs_tls(&restored);
        assert_eq!(tls_snapshot().unwrap()["word_t"], 16);
    }

    /// §26.3 (#721): repeated transitive wildcard imports share typedef
    /// widths without retaining a log key per typedef per instance.
    #[test]
    fn repeated_wildcard_typedef_imports_keep_a_bounded_change_log() {
        let mut source = String::from("package many_types;\n");
        for i in 0..96 {
            source.push_str(&format!("typedef logic [7:0] word_{i}_t;\n"));
        }
        source.push_str(
            "endpackage\npackage relay; import many_types::*; endpackage\n\
             module leaf; import relay::*; word_0_t q; endmodule\n\
             module top; for (genvar i=0;i<32;i++) begin:g leaf u(); end endmodule\n",
        );
        let (_, design) =
            crate::parse_and_elaborate_multi(&[source], Some("top"), &[], &["top.sv".into()], &[])
                .expect("elaborate repeated imports");
        assert_eq!(design.signals["g[31].u.q"].width, 8);
        assert_eq!(design.typedefs["word_95_t"], 8);
        assert!(
            design.typedefs.log.len() <= design.typedefs.len(),
            "{} retained changes for {} widths",
            design.typedefs.log.len(),
            design.typedefs.len(),
        );
    }

    /// The const-eval snapshot must equal the table after every sync, whether
    /// it was brought up to date by replaying changes or by a full copy.
    #[test]
    fn typedef_snapshot_tracks_the_table() {
        let mut t = TypedefTable::default();
        t.insert("a".into(), 1);
        t.insert("b".into(), 2);
        sync_typedefs_tls(&t);
        assert!(same(&tls_snapshot().unwrap(), t.as_map()));

        // Replay: overwrite, add, remove.
        t.insert("a".into(), 5);
        t.insert("c".into(), 3);
        t.remove("b");
        assert!(!t.insert_if_absent("c".into(), 9));
        sync_typedefs_tls(&t);
        assert!(same(&tls_snapshot().unwrap(), t.as_map()));

        // A scoped replacement is undone, and the next sync is still exact.
        let mut foreign = HashMap::default();
        foreign.insert("z".to_string(), 7);
        with_typedefs_owned(foreign, || {
            assert_eq!(tls_snapshot().unwrap().get("z"), Some(&7));
        });
        t.insert("d".into(), 4);
        sync_typedefs_tls(&t);
        assert!(same(&tls_snapshot().unwrap(), t.as_map()));

        // A different table (a clone has its own identity) is copied whole.
        let mut u = t.clone();
        u.insert("e".into(), 6);
        sync_typedefs_tls(&u);
        assert!(same(&tls_snapshot().unwrap(), u.as_map()));
        sync_typedefs_tls(&t);
        assert!(same(&tls_snapshot().unwrap(), t.as_map()));

        // A snapshot some other writer replaced is copied whole too.
        TYPEDEFS_TLS.with(|c| *c.borrow_mut() = Some(HashMap::default()));
        TYPEDEFS_TLS_MIRROR.with(|m| m.set(None));
        sync_typedefs_tls(&t);
        assert!(same(&tls_snapshot().unwrap(), t.as_map()));
    }
    /// §7.4.2: parsed names can denote parameter sizes or associative types.
    #[test]
    fn declared_array_dimensions_resolve_parameter_names() {
        let parsed = crate::parse(
            "package dim_cfg; parameter int EDGE_COUNT=3; endpackage \
             module dimension_probe #(parameter int EDGE_COUNT=2); \
             typedef int key_t; wire sample[EDGE_COUNT][dim_cfg::EDGE_COUNT]; \
             wire ranges[1:-1][0:2]; int keyed[key_t]; endmodule",
        );
        assert!(parsed.errors.is_empty(), "{:?}", parsed.errors);
        let module = parsed
            .source
            .descriptions
            .iter()
            .find_map(|d| match d {
                crate::ast::Description::Module(m) => Some(m),
                _ => None,
            })
            .unwrap();
        let mut params = HashMap::default();
        params.insert("EDGE_COUNT".into(), Value::from_u64(2, 32));
        params.insert("dim_cfg::EDGE_COUNT".into(), Value::from_u64(3, 32));
        let mut checked = 0;
        for item in &module.items {
            let declarators: Vec<_> = match item {
                ModuleItem::NetDeclaration(d) => d
                    .declarators
                    .iter()
                    .map(|d| (&d.name, &d.dimensions))
                    .collect(),
                ModuleItem::DataDeclaration(d) => d
                    .declarators
                    .iter()
                    .map(|d| (&d.name, &d.dimensions))
                    .collect(),
                _ => continue,
            };
            for (name, dims) in declarators {
                match name.name.as_str() {
                    "sample" => {
                        assert_eq!(
                            declared_unpacked_dims(dims, &params),
                            Some(vec![(0, 1), (0, 2)])
                        );
                        let mut zero = params.clone();
                        zero.insert("EDGE_COUNT".into(), Value::zero(32));
                        assert_eq!(declared_unpacked_dims(dims, &zero), None);
                        assert_eq!(declared_unpacked_dims(dims, &HashMap::default()), None);
                        checked += 1;
                    }
                    "ranges" => {
                        assert_eq!(
                            declared_unpacked_dims(dims, &params),
                            Some(vec![(1, -1), (0, 2)])
                        );
                        checked += 1;
                    }
                    "keyed" => {
                        assert_eq!(declared_unpacked_dims(dims, &params), None);
                        checked += 1;
                    }
                    _ => {}
                }
            }
        }
        assert_eq!(checked, 3);
    }
}

#[cfg(test)]
mod imported_typedef_tests {
    /// §26.3, §26.6 (aionhw/xezim#721): each instance binds the typedefs
    /// its own imports reach, whichever instance came before.
    #[test]
    fn each_instance_binds_its_own_imported_typedefs() {
        let source = "package a; typedef logic [3:0] t; endpackage
package b; typedef logic [7:0] t; endpackage
package c; import a::*; export a::*; endpackage
module via_c; import c::*; t q; endmodule
module via_b; import b::*; t q; endmodule
module via_a; import a::t; t q; endmodule
module top; via_c u0(); via_b u1(); via_c u2(); via_a u3(); via_b u4(); endmodule
";
        let (_, design) = crate::parse_and_elaborate_multi(
            &[source.into()],
            Some("top"),
            &[],
            &["top.sv".into()],
            &[],
        )
        .expect("elaborate imports");
        let widths: Vec<_> = ["u0.q", "u1.q", "u2.q", "u3.q", "u4.q"]
            .iter()
            .map(|n| design.signals[*n].width)
            .collect();
        assert_eq!(widths, [4, 8, 4, 4, 8]);
    }
}

#[cfg(test)]
mod nested_class_method_tests {
    use super::*;

    /// Whether `class`'s method `m` carries the out-of-block body
    /// (`function int x::inner::m()`, a scoped name) rather than its own.
    fn linked_out_of_block(elab: &ElaboratedModule, class: &str) -> bool {
        match &elab.classes[class].methods["m"].kind {
            crate::ast::decl::ClassMethodKind::Function(f) => f.name.has_scope(),
            _ => panic!("{class}::m is not a function"),
        }
    }

    /// §8.24/§8.23: an out-of-block `outer::inner::m` attaches to that nested
    /// class only — not to a top-level `class inner` or another class's
    /// `inner`, whichever holds the bare name `inner`.
    #[test]
    fn nested_method_attaches_only_to_its_own_class() {
        for (source, expected) in [
            (
                "class inner; function int m(); return 1; endfunction endclass
                 class outer; class inner; extern function int m(); endclass endclass
                 function int outer::inner::m(); return 2; endfunction
                 module t; endmodule",
                &[("outer::inner", true), ("inner", false)][..],
            ),
            (
                "class a; class inner; function int m(); return 1; endfunction endclass endclass
                 class b; class inner; extern function int m(); endclass endclass
                 function int b::inner::m(); return 2; endfunction
                 module t; endmodule",
                &[("b::inner", true), ("a::inner", false)][..],
            ),
            (
                "class outer; class inner; extern function int m(); endclass endclass
                 function int outer::inner::m(); return 2; endfunction
                 module t; endmodule",
                &[("outer::inner", true), ("inner", true)][..],
            ),
        ] {
            let (_, elab) = crate::parse_and_elaborate_multi(
                &[source.to_string()],
                Some("t"),
                &[],
                &["t.sv".to_string()],
                &[],
            )
            .expect("elaborate");
            for &(class, linked) in expected {
                assert_eq!(
                    linked_out_of_block(&elab, class),
                    linked,
                    "{class}: {source}"
                );
            }
        }
    }
}

#[cfg(test)]
mod package_net_tests {
    /// §26.2, §26.3: a package net is a net under its qualified name, and
    /// under its bare name unless a local declaration displaces that name —
    /// a module's own `logic w` is not the unimported (or shadowed) `pkg::w`.
    #[test]
    fn package_net_bare_name_yields_to_a_local_declaration() {
        for (source, bare_is_net) in [
            // Not imported: the bare name is the module's variable.
            (
                "package nets; wand w; supply1 s; endpackage
                 module t; logic w, s; initial begin w = 0; s = 0; end endmodule",
                false,
            ),
            // Wildcard-imported but shadowed by the local declaration.
            (
                "package nets; wand w; supply1 s; endpackage
                 module t; import nets::*; logic w, s; endmodule",
                false,
            ),
            (
                "package nets; wand w; supply1 s; endpackage
                 module t; logic w, s; import nets::*; endmodule",
                false,
            ),
            // Referenced only qualified: the bare name is the package's net.
            (
                "package nets; wand w; supply1 s; endpackage
                 module t; assign nets::w = 1'b1; assign nets::w = 1'b0;
                 initial $display(nets::w, nets::s); endmodule",
                true,
            ),
        ] {
            let (_, elab) = crate::parse_and_elaborate_multi(
                &[source.to_string()],
                Some("t"),
                &[],
                &["t.sv".to_string()],
                &[],
            )
            .expect("elaborate");
            assert!(elab.nets.contains("nets::w"), "{source}");
            assert!(elab.supply_nets.contains("nets::s"), "{source}");
            assert_eq!(elab.nets.contains("w"), bare_is_net, "{source}");
            assert_eq!(
                elab.resolved_net_kinds.contains_key("w"),
                bare_is_net,
                "{source}"
            );
            assert_eq!(elab.supply_nets.contains("s"), bare_is_net, "{source}");
        }
    }
}

#[cfg(test)]
mod shared_map_tests {
    use super::*;

    #[test]
    fn copies_share_one_map_until_one_is_written() {
        let mut a = SharedMap::<u32>::default();
        a.insert("t".into(), 4);
        let b = a.clone();
        assert!(Rc::ptr_eq(&a.0, &b.0));
        a.insert("u".into(), 8);
        assert!(!Rc::ptr_eq(&a.0, &b.0));
        assert_eq!(a.get("u"), Some(&8));
        assert_eq!(b.get("u"), None);
        assert_eq!(b.get("t"), Some(&4));
    }

    #[test]
    fn serializes_as_the_plain_map() {
        let mut plain: HashMap<String, u32> = HashMap::default();
        plain.insert("t".into(), 4);
        plain.insert("u".into(), 8);
        let shared = SharedMap::from(plain.clone());
        let cfg = crate::xez_bincode_config();
        let bytes = bincode::serde::encode_to_vec(&shared, cfg).unwrap();
        assert_eq!(bytes, bincode::serde::encode_to_vec(&plain, cfg).unwrap());
        let (back, _): (SharedMap<u32>, usize) =
            bincode::serde::decode_from_slice(&bytes, cfg).unwrap();
        assert_eq!(*back, plain);
    }

    #[test]
    fn constant_function_snapshots_share_the_elaboration_tables() {
        let elab = ElaboratedModule::new("m".into());
        set_typedef_types_tls(&elab.typedef_types);
        set_typedef_widths_tls(&elab.typedefs);
        let types = TYPEDEF_TYPES_TLS.with(|c| c.borrow().clone()).unwrap();
        assert!(Rc::ptr_eq(&types.0, &elab.typedef_types.0));
        let widths = TYPEDEF_WIDTHS_TLS.with(|c| c.borrow().clone()).unwrap();
        assert!(Rc::ptr_eq(&widths, &elab.typedefs.shared_map()));
        reset_const_eval_snapshots();
    }
}
