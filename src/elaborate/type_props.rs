use super::*;

/// A name→`Value` environment a constant-expression evaluator can resolve
/// parameter names against. The plain `&HashMap` is the common case; a
/// `ParamEnv::Overlay` backs a lookup with a second map without copying the
/// first, which is what lets a constant-function call read the whole module
/// parameter table (`base`) with only a small map of locals (`top`) stacked
/// on it.
pub trait ParamLookup {
    fn get(&self, key: &str) -> Option<&Value>;
    #[inline]
    fn contains_key(&self, key: &str) -> bool {
        self.get(key).is_some()
    }
    /// Every key this lookup answers for. Rows underneath an `Overlay` are
    /// reported too, so the rare whole-table scans (`name.starts_with(...)`)
    /// keep seeing every candidate.
    fn keys(&self) -> crate::hasher::HashSet<&str>;

    /// Every `(key, value)` row this lookup answers for, top rows first and
    /// deduplicated (a row shadowed by an overlaid row is dropped). Materializing
    /// the caller scope for a nested constant-function call needs the values,
    /// not just the keys.
    fn rows(&self) -> Vec<(&str, &Value)>;

    /// A complete flat view, only when no overlay needs materialization.
    fn as_hashmap_base(&self) -> Option<&HashMap<String, Value>> {
        None
    }

    /// Preserve all visible bindings at boundaries that require a flat map.
    /// Plain tables remain borrowed; overlay rows retain their precedence.
    fn to_hashmap(&self) -> std::borrow::Cow<'_, HashMap<String, Value>> {
        if let Some(map) = self.as_hashmap_base() {
            std::borrow::Cow::Borrowed(map)
        } else {
            std::borrow::Cow::Owned(self.rows().into_iter()
                .map(|(name, value)| (name.to_owned(), value.clone())).collect())
        }
    }
}

impl ParamLookup for HashMap<String, Value> {
    #[inline]
    fn get(&self, key: &str) -> Option<&Value> {
        self.get(key)
    }
    #[inline]
    fn contains_key(&self, key: &str) -> bool {
        self.contains_key(key)
    }
    #[inline]
    fn keys(&self) -> crate::hasher::HashSet<&str> {
        self.iter().map(|(k, _)| k.as_str()).collect()
    }
    #[inline]
    fn rows(&self) -> Vec<(&str, &Value)> {
        self.iter().map(|(k, v)| (k.as_str(), v)).collect()
    }
    #[inline]
    fn as_hashmap_base(&self) -> Option<&HashMap<String, Value>> {
        Some(self)
    }
}

impl<T: ParamLookup + ?Sized> ParamLookup for &T {
    #[inline]
    fn get(&self, key: &str) -> Option<&Value> {
        (**self).get(key)
    }
    #[inline]
    fn contains_key(&self, key: &str) -> bool {
        (**self).contains_key(key)
    }
    #[inline]
    fn keys(&self) -> crate::hasher::HashSet<&str> {
        (**self).keys()
    }
    #[inline]
    fn rows(&self) -> Vec<(&str, &Value)> {
        (**self).rows()
    }
    #[inline]
    fn as_hashmap_base(&self) -> Option<&HashMap<String, Value>> {
        (**self).as_hashmap_base()
    }
}

impl ParamLookup for StackedParamEnv<'_> {
    #[inline]
    fn get(&self, key: &str) -> Option<&Value> {
        self.top.get(key).or_else(|| self.base.get(key))
    }
    #[inline]
    fn contains_key(&self, key: &str) -> bool {
        self.top.contains_key(key) || self.base.contains_key(key)
    }
    fn keys(&self) -> crate::hasher::HashSet<&str> {
        let mut set = self.base.keys();
        set.extend(self.top.keys().map(String::as_str));
        set
    }
    fn rows(&self) -> Vec<(&str, &Value)> {
        let mut out: Vec<(&str, &Value)> = Vec::new();
        let mut seen: crate::hasher::HashSet<&str> = crate::hasher::HashSet::default();
        for (k, v) in self.top {
            out.push((k.as_str(), v));
            seen.insert(k.as_str());
        }
        for (k, v) in self.base.rows() {
            if !seen.contains(k) {
                out.push((k, v));
            }
        }
        out
    }
    #[inline]
    fn as_hashmap_base(&self) -> Option<&HashMap<String, Value>> {
        None
    }
}

/// A parameter environment: one table, or one laid over a base (top wins).
#[derive(Clone, Copy)]
pub enum ParamEnv<'a> {
    /// Just one table.
    Single(&'a HashMap<String, Value>),
    /// `top` wins; `base` is consulted only for keys `top` lacks.
    Overlay {
        base: &'a HashMap<String, Value>,
        top: &'a HashMap<String, Value>,
    },
}

impl<'a> ParamLookup for ParamEnv<'a> {
    #[inline]
    fn get(&self, key: &str) -> Option<&Value> {
        match self {
            ParamEnv::Single(m) => m.get(key),
            ParamEnv::Overlay { base, top } => top.get(key).or_else(|| base.get(key)),
        }
    }
    #[inline]
    fn contains_key(&self, key: &str) -> bool {
        match self {
            ParamEnv::Single(m) => m.contains_key(key),
            ParamEnv::Overlay { base, top } => top.contains_key(key) || base.contains_key(key),
        }
    }
    #[inline]
    fn keys(&self) -> crate::hasher::HashSet<&str> {
        use crate::hasher::HashSet;
        match self {
            ParamEnv::Single(m) => m.iter().map(|(k, _)| k.as_str()).collect::<HashSet<&str>>(),
            ParamEnv::Overlay { base, top } => base
                .iter()
                .map(|(k, _)| k.as_str())
                .chain(top.iter().map(|(k, _)| k.as_str()))
                .collect(),
        }
    }
    #[inline]
    fn as_hashmap_base(&self) -> Option<&HashMap<String, Value>> {
        match self {
            ParamEnv::Single(m) => Some(m),
            ParamEnv::Overlay { .. } => None,
        }
    }

    #[inline]
    fn rows(&self) -> Vec<(&str, &Value)> {
        use crate::hasher::HashSet;
        match self {
            ParamEnv::Single(m) => m.iter().map(|(k, v)| (k.as_str(), v)).collect(),
            ParamEnv::Overlay { base, top } => {
                let mut out: Vec<(&str, &Value)> = Vec::new();
                let mut seen: HashSet<&str> = HashSet::default();
                // top wins: emit top rows first, then base rows not shadowed.
                for (k, v) in top.iter() {
                    out.push((k.as_str(), v));
                    seen.insert(k.as_str());
                }
                for (k, v) in base.iter() {
                    if !seen.contains(k.as_str()) {
                        out.push((k.as_str(), v));
                    }
                }
                out
            }
        }
    }
}

/// Resolve the width of a data type.
pub fn resolve_type_width(
    dt: &DataType,
    params: Option<&HashMap<String, Value>>,
    typedefs: Option<&HashMap<String, u32>>,
) -> u32 {
    resolve_type_width_env(dt, params, typedefs)
}

/// Generic core of [`resolve_type_width`]: same logic, but `params` may be any
/// [`ParamLookup`] so a constant-function body overlays its small locals on
/// the whole elaboration parameter table instead of cloning it.
pub fn resolve_type_width_env<P: ParamLookup>(
    dt: &DataType,
    params: Option<&P>,
    typedefs: Option<&HashMap<String, u32>>,
) -> u32 {
    match dt {
        DataType::IntegerVector { dimensions, .. } => {
            if dimensions.is_empty() {
                return 1;
            }
            let mut total = 1u64;
            let mut culprit: Option<String> = None;
            let mut dims_desc = String::new();
            let mut first_span: Option<u32> = None;
            for dim in dimensions {
                if let PackedDimension::Range { left, right, .. } = dim {
                    let lv = const_eval_i64_with_params_env(left, params);
                    let rv = const_eval_i64_with_params_env(right, params);
                    if let (Some(l), Some(r)) = (lv, rv) {
                        let w = l.abs_diff(r).saturating_add(1);
                        if w > max_packed_width() as u64 && culprit.is_none() {
                            culprit = Some(describe_packed_range(left, right, l, r, params.map(ParamLookup::to_hashmap).as_deref()));
                        }
                        dims_desc.push_str(&format!("[{}:{}]", l, r));
                        if first_span.is_none() {
                            first_span = Some(left.span.start as u32);
                        }
                        total = total.saturating_mul(w);
                    }
                }
            }
            // A PRODUCT of sane dims can still exceed the cap
            // (`[2047:0][2047:0]`); name the dims and the source byte offset
            // so the offending declaration is findable (grep the
            // --dump-merged-sv output at that offset).
            if total > max_packed_width() as u64 && culprit.is_none() {
                culprit = Some(format!(
                    "dims {} at {}",
                    dims_desc,
                    published_span_location(Span::new(
                        first_span.unwrap_or(0) as usize,
                        first_span.unwrap_or(0) as usize
                    ))
                ));
            }
            clamp_packed_width(total, "IntegerVector", culprit.as_deref().unwrap_or(""))
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
            if dimensions.is_empty() {
                return 1;
            }
            let mut total = 1u64;
            for dim in dimensions {
                if let PackedDimension::Range { left, right, .. } = dim {
                    let lv = const_eval_i64_with_params_env(left, params);
                    let rv = const_eval_i64_with_params_env(right, params);
                    if let (Some(l), Some(r)) = (lv, rv) {
                        let w = l.abs_diff(r).saturating_add(1);
                        total = total.saturating_mul(w);
                    }
                }
            }
            clamp_packed_width(total, "Implicit", "")
        }
        DataType::TypeReference {
            name, dimensions, ..
        } => {
            // XEZIM_TRACE_TYPE: this fn is HOT, so the guard runs before any
            // formatting; `hit` records which table answered for the trace.
            let traced = type_trace_on(&name.name.name);
            let mut hit = "no-table";
            let mut base_width = if let Some(td) = typedefs {
                // §26.3: prefer the package-qualified key for `P::T` so a
                // module-local `typedef ... T` cannot capture it.
                let scoped = lookup_scoped_type(name, td).copied();
                let raw = scoped.or_else(|| td.get(&name.name.name).copied());
                if traced {
                    hit = if scoped.is_some() {
                        "scoped"
                    } else if raw.is_some() {
                        "bare"
                    } else {
                        "miss"
                    };
                }
                raw.map(|w| if w == 0 { 32 } else { w }).unwrap_or(32)
            } else {
                32
            };
            let traced_base = base_width;
            if !dimensions.is_empty() {
                let mut total = base_width as u64;
                for dim in dimensions {
                    if let PackedDimension::Range { left, right, .. } = dim {
                        if let (Some(l), Some(r)) = (
                            const_eval_i64_with_params_env(left, params),
                            const_eval_i64_with_params_env(right, params),
                        ) {
                            let w = l.abs_diff(r).saturating_add(1);
                            total = total.saturating_mul(w);
                        }
                    }
                }
                let detail = format!(
                    "type '{}' at {}",
                    name.name.name,
                    published_span_location(name.span)
                );
                base_width = clamp_packed_width(total, "TypeReference", &detail);
            }
            if traced {
                type_trace(
                    "resolve:type_ref",
                    &name.name.name,
                    &format!(
                        "hit={hit} base={traced_base} dims={} final={base_width}",
                        dimensions.len()
                    ),
                );
            }
            base_width
        }
        DataType::Simple { kind, .. } => match kind {
            SimpleType::String => 1024, // Dynamic string, allocate 128 chars max
            SimpleType::Chandle => 64,
            SimpleType::Event => 1,
        },
        DataType::Enum(e) => {
            let base = if let Some(bt) = &e.base_type {
                resolve_type_width_env(bt, params, typedefs)
            } else {
                32
            };
            // §7.4.2: body-suffix packed dims (`enum {...} [1:0] x;`) make a
            // packed ARRAY of the enum — multiply like the struct arm does.
            let mut total = base as u64;
            for d in &e.dimensions {
                if let PackedDimension::Range { left, right, .. } = d {
                    if let (Some(l), Some(r)) = (
                        const_eval_i64_with_params_env(left, params),
                        const_eval_i64_with_params_env(right, params),
                    ) {
                        total = total.saturating_mul((l - r).unsigned_abs() + 1);
                    }
                }
            }
            clamp_packed_width(total, "Enum", "")
        }
        DataType::Struct(s) => {
            let is_union = matches!(s.kind, StructUnionKind::Union);
            let mut total = 0u32;
            let mut max_w = 0u32;
            let mut member_count = 0u32;
            for member in &s.members {
                let mw = resolve_type_width_env(&member.data_type, params, typedefs);
                for mdecl in &member.declarators {
                    // §7.4.2: an UNPACKED dimension on the member multiplies its
                    // contribution — `logic [7:0] arr [3]` is 24 bits of the
                    // struct, not 8. Counting one element made `$bits` of any
                    // struct with an array member too small, and (worse) that
                    // width sized the variable, so a return value was truncated
                    // and the members laid out above the cut were lost.
                    let n = unpacked_dims_elem_count(&mdecl.dimensions, params);
                    let dw = mw.saturating_mul(n);
                    total += dw;
                    if dw > max_w {
                        max_w = dw;
                    }
                    member_count += 1;
                }
            }
            let elem_w = if is_union {
                if s.tagged {
                    let tag_w = (member_count.max(2) - 1)
                        .next_power_of_two()
                        .trailing_zeros()
                        .max(1);
                    max_w + tag_w
                } else {
                    max_w
                }
            } else {
                total
            };
            // Packed array dimensions after the body (`struct {...} [N-1:0]`)
            // multiply the element width.
            let mut w = elem_w as u64;
            for dim in &s.dimensions {
                if let PackedDimension::Range { left, right, .. } = dim {
                    if let (Some(l), Some(r)) = (
                        const_eval_i64_with_params_env(left, params),
                        const_eval_i64_with_params_env(right, params),
                    ) {
                        w = w.saturating_mul(l.abs_diff(r).saturating_add(1));
                    }
                }
            }
            clamp_packed_width(w, "Struct", "")
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
            if let Some(s) = signing {
                return matches!(s, Signing::Signed);
            }
            match kind {
                IntegerAtomType::Byte
                | IntegerAtomType::ShortInt
                | IntegerAtomType::Int
                | IntegerAtomType::LongInt
                | IntegerAtomType::Integer => true,
                IntegerAtomType::Time => false,
            }
        }
        DataType::Implicit { signing, .. } => matches!(signing, Some(Signing::Signed)),
        DataType::Real { .. } => true,
        DataType::Struct(su) => matches!(su.signing, Some(Signing::Signed)),
        // §6.19: an enum takes the signedness of its BASE type, and the
        // default base is `int` — which is signed. This arm was missing, so
        // every enum was unsigned: `enum shortint {A=-1,...} es;` read `es`
        // as 65534 instead of -2, `es.first()` as 65535 instead of -1, and
        // `es.first() < 0` was false (ivtest enum_method_signed1..4).
        DataType::Enum(e) => e.base_type.as_deref().map(is_type_signed).unwrap_or(true),
        _ => false,
    }
}

/// Look up a §6.6.7 nettype resolution function — by bare name, or as a package
/// member hoisted under a `pkg::name` key.
pub(super) fn lookup_resolver<'a>(
    elab: &'a ElaboratedModule,
    name: &str,
) -> Option<&'a crate::ast::decl::FunctionDeclaration> {
    if let Some(fd) = elab.functions.get(name) {
        return Some(fd);
    }
    let suffix = format!("::{}", name);
    let mut keys: Vec<&String> = elab
        .functions
        .keys()
        .filter(|k| k.ends_with(&suffix))
        .collect();
    keys.sort();
    keys.first().and_then(|k| elab.functions.get(*k))
}

/// §6.6.7 constraints on a nettype resolution function, checked at elaboration
/// where a wrong one can still be reported instead of silently mis-resolving.
pub(super) fn validate_resolver(
    elab: &ElaboratedModule,
    nettype: &str,
    name: &str,
) -> Result<(), String> {
    // A call to a name that resolves to nothing lands on `eval_call_inner`'s
    // terminal fallback, which returns `Value::zero(32)` — a misspelled or
    // out-of-scope resolver would silently drive the net to 0, and
    // single-driver nets (routed through the resolver too) would regress from
    // always-correct to silently wrong.
    let Some(fd) = lookup_resolver(elab, name) else {
        return Err(format!(
            "nettype '{}' names resolution function '{}', which is not declared \
             (IEEE 1800-2017 6.6.7). Note a package-qualified resolver \
             (`nettype T w with pkg::f;`) is not yet representable.",
            nettype, name
        ));
    };

    // §6.6.7: "A resolution function shall be automatic (or preserve no state
    // information)". A static one is accepted when it writes each static
    // variable it reads earlier in the same call, as `res = 0.0;` before the
    // accumulating loop does. One that reads a value left by the previous call
    // would resolve to a stale value rather than an error, so it is rejected.
    if fd.lifetime != Some(crate::ast::types::Lifetime::Automatic)
        && let Err(var) = super::resolver_state::static_carried_variable(elab, fd)
    {
        return Err(format!(
            "nettype '{}' resolution function '{}' is static and reads {} before writing it, \
             so it preserves state between calls; declare it `automatic` or write the variable \
             first (IEEE 1800-2023 6.6.7)",
            nettype, name, var
        ));
    }

    // §6.6.7: the function takes a single input formal that is an UNPACKED
    // ARRAY of the nettype's data type. A scalar formal otherwise falls through
    // to the ordinary scalar call path and receives the drivers concatenated
    // into one packed value, so the body's `foreach` reads stale state and the
    // net resolves to a silently wrong value.
    //
    // Only checked for an ANSI declaration: a non-ANSI `function f; input T d[];`
    // parses its ports into the body, leaving `ports` empty, and rejecting that
    // would be a false positive.
    if !fd.ports.is_empty() {
        if fd.ports.len() != 1 {
            return Err(format!(
                "nettype '{}' resolution function '{}' takes {} formals; it must take exactly one, \
                 an unpacked array of the nettype data type (IEEE 1800-2017 6.6.7)",
                nettype,
                name,
                fd.ports.len()
            ));
        }
        let port = &fd.ports[0];
        if port.dimensions.is_empty() {
            return Err(format!(
                "nettype '{}' resolution function '{}' declares formal '{}' as a scalar; it must be \
                 an unpacked array of the nettype data type, e.g. `input T {} []` \
                 (IEEE 1800-2017 6.6.7)",
                nettype, name, port.name.name, port.name.name
            ));
        }
        if !matches!(port.direction, PortDirection::Input) {
            return Err(format!(
                "nettype '{}' resolution function '{}' declares formal '{}' as {:?}; it must be an \
                 `input` (IEEE 1800-2017 6.6.7)",
                nettype, name, port.name.name, port.direction
            ));
        }
    }

    Ok(())
}

pub fn is_type_real(dt: &DataType) -> bool {
    matches!(dt, DataType::Real { .. })
}

/// `is_type_real` that resolves a type reference through the typedef/nettype
/// table, so `nettype real rn; rn n;` (and `typedef real r_t; r_t v;`) mark the
/// signal `is_real`. Without this a real-typed NET kept `is_real == false` and
/// read back as its raw f64 bit pattern (3.5 printed as 4615063718147915776).
/// Same bounded iterative walk as `is_type_signed_resolved` — a malformed
/// typedef cycle must diagnose, never overflow the stack.
pub fn is_type_real_resolved(dt: &DataType, typedef_types: &HashMap<String, DataType>) -> bool {
    let mut cur = dt;
    for _ in 0..64 {
        if matches!(cur, DataType::Real { .. }) {
            return true;
        }
        let DataType::TypeReference { name, .. } = cur else {
            break;
        };
        let key = &name.name.name;
        let inner = lookup_scoped_type(name, typedef_types);
        match inner {
            Some(next) if !matches!(next, DataType::TypeReference { name: n, .. } if &n.name.name == key) => {
                cur = next
            }
            _ => break,
        }
    }
    is_type_real(cur)
}

/// `is_type_signed` that resolves a typedef reference (`typedef logic signed
/// [7:0] t; t v;`) against the typedef table so `v` inherits the underlying
/// type's signedness. Without this a signed typedef var read as unsigned,
/// e.g. `t'(-16) !== -16` failed on the high bits.
pub fn is_type_signed_resolved(dt: &DataType, typedef_types: &HashMap<String, DataType>) -> bool {
    // Walk the chain ITERATIVELY under the same bound `resolve_typedef_chain`
    // uses. This was recursive with a guard against a DIRECT self-reference
    // only (`typedef T T;`), so a cycle through two names —
    // `typedef T1; typedef T1 T2; typedef T2 T1;` — recursed until the stack
    // overflowed and the process ABORTED (ivtest sv_typedef_circular1/2).
    // Malformed input must be diagnosed, never crash the tool.
    let mut cur = dt;
    for _ in 0..64 {
        let DataType::TypeReference { name, .. } = cur else {
            break;
        };
        let key = &name.name.name;
        // §26.3: scoped `P::T` prefers the qualified registration.
        let inner = lookup_scoped_type(name, typedef_types);
        match inner {
            // Self-referential name: stop here, as before.
            Some(next) if !matches!(next, DataType::TypeReference { name: n, .. } if &n.name.name == key) => {
                cur = next
            }
            _ => break,
        }
    }
    // §6.19: an enum's signedness is its BASE type's, and that base may itself
    // be a typedef (`typedef byte sb_t; typedef enum sb_t {B0=-2,…} eb_t;`).
    // `is_type_signed` cannot resolve it without the table, so the enum read
    // unsigned and `e < 0` was false.
    if let DataType::Enum(e) = cur {
        return match e.base_type.as_deref() {
            Some(bt) => is_type_signed_resolved(bt, typedef_types),
            None => true, // default base is `int` — signed
        };
    }
    is_type_signed(cur)
}

/// Returns the default value for a type: 0 for 2-state types, X for 4-state types.
/// §6.20.2 + §5.7.1: signedness of an UNTYPED parameter, taken from its value.
/// An unsized decimal (`parameter P = 240;`) is a signed int, but a SIZED
/// literal is unsigned unless it carries the `s` designator — so
/// `parameter P = 8'hF0;` is 240, not -16. Untyped parameters were marked
/// signed unconditionally, which made `P > 100` false.
///
/// An expression follows §11.8.1 over the shapes `untyped_param_width` sizes:
/// signed only when every operand is. Now that such a parameter keeps its
/// self-determined width, the old signed default for them would turn
/// `UP + SP` (8-bit, one operand unsigned) into -6 instead of 250. Any other
/// shape keeps the signed default.
pub fn untyped_param_is_signed(init: &Expression, params: &HashMap<String, Value>) -> bool {
    let s = |x: &Expression| untyped_param_is_signed(x, params);
    let lookup = |name: &str| params.get(name).filter(|v| !v.is_real).map(|v| v.is_signed);
    match &init.kind {
        // An unsized decimal is signed, an unsized based literal (`'hFF`)
        // is not unless it carries `s` (§5.7.1) — the parser records both.
        ExprKind::Number(NumberLiteral::Integer { signed, .. }) => *signed,
        ExprKind::Paren(inner) => s(inner),
        ExprKind::StringLiteral(_)
        | ExprKind::Concatenation(_)
        | ExprKind::Replication { .. }
        | ExprKind::RangeSelect { .. } => false,
        ExprKind::Ident(h) if h.root.is_none() && h.path.len() == 1 => {
            if !h.path[0].selects.is_empty() {
                return true;
            }
            let raw = h.path[0].name.name.as_str();
            lookup(raw)
                .or_else(|| lookup(crate::sv_parser::strip_unit_scope_name(raw).unwrap_or(raw)))
                .unwrap_or(true)
        }
        ExprKind::MemberAccess { expr, member } => match &expr.kind {
            ExprKind::Ident(h) if h.root.is_none() && h.path.len() == 1 => {
                lookup(&format!("{}::{}", h.path[0].name.name, member.name)).unwrap_or(true)
            }
            _ => true,
        },
        ExprKind::Unary { op, operand } => match op {
            UnaryOp::Plus | UnaryOp::Minus | UnaryOp::BitNot => s(operand),
            UnaryOp::LogNot
            | UnaryOp::BitAnd
            | UnaryOp::BitNand
            | UnaryOp::BitOr
            | UnaryOp::BitNor
            | UnaryOp::BitXor
            | UnaryOp::BitXnor => false,
            _ => true,
        },
        ExprKind::Binary { op, left, right } => match op {
            BinaryOp::Add
            | BinaryOp::Sub
            | BinaryOp::Mul
            | BinaryOp::Div
            | BinaryOp::Mod
            | BinaryOp::BitAnd
            | BinaryOp::BitOr
            | BinaryOp::BitXor
            | BinaryOp::BitXnor => s(left) && s(right),
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
            | BinaryOp::LogAnd
            | BinaryOp::LogOr
            | BinaryOp::LogImplies
            | BinaryOp::LogEquiv => false,
            BinaryOp::ShiftLeft
            | BinaryOp::ShiftRight
            | BinaryOp::ArithShiftLeft
            | BinaryOp::ArithShiftRight
            | BinaryOp::Power => s(left),
            _ => true,
        },
        ExprKind::Conditional {
            then_expr,
            else_expr,
            ..
        } => s(then_expr) && s(else_expr),
        ExprKind::SystemCall { name, .. } if name == "$unsigned" => false,
        // §11.4.13: `inside` is an unsigned bit; §13.4.1: a call has its
        // function's return type, the same one `untyped_param_width` sizes by.
        ExprKind::Inside { .. } => false,
        ExprKind::Call { func, .. } => const_context::function_type_resolved(func, params)
            .filter(|t| t.integral)
            .is_none_or(|t| t.signed),
        _ => true,
    }
}

/// §6.20.2: a package parameter's DECLARED type fixes its signedness, as a
/// module parameter's does. The package paths only ever SET the flag, so a
/// signed initializer leaked into an unsigned parameter: `parameter bit B = 1`
/// read as a signed 1-bit -1, and `B === 1` was false. Only an untyped,
/// unranged parameter takes the signedness of its value.
pub(super) fn pkg_param_is_signed(
    dt: &DataType,
    init: Option<&Expression>,
    typedef_types: &HashMap<String, DataType>,
    params: &HashMap<String, Value>,
) -> bool {
    match dt {
        DataType::Implicit {
            signing: None,
            dimensions,
            ..
        } if dimensions.is_empty() => init
            .map(|i| untyped_param_is_signed(i, params))
            .unwrap_or(true),
        _ => is_type_signed_resolved(dt, typedef_types),
    }
}

pub(super) fn default_value_for_type_resolved(
    dt: &DataType,
    width: u32,
    typedef_types: &HashMap<String, DataType>,
) -> Value {
    let resolved = resolve_typedef_chain(dt, typedef_types);
    // §7.2.1, §6.8: a packed struct whose members are all 2-state starts at
    // 0, also when a member reaches its type through a typedef
    // (`s_t [1:0] e;`), which `default_value_for_type` does not resolve.
    if matches!(resolved, DataType::Struct(su) if su.packed)
        && is_type_two_state_resolved(resolved, typedef_types)
    {
        return Value::zero(width);
    }
    default_value_for_type(resolved, width)
}

pub(super) fn default_value_for_type(dt: &DataType, width: u32) -> Value {
    if is_type_real(dt) {
        return Value::from_f64(0.0);
    }
    // LRM §6.20.3: `chandle` defaults to null. Module-scope `chandle h;`
    // without explicit init must read as 0 so `if (h == null)` works.
    // Class handles via TypeReference are handled at runtime via the
    // VarDecl/init paths (where module.classes is in scope).
    if matches!(
        dt,
        DataType::Simple {
            kind: SimpleType::Chandle,
            ..
        }
    ) {
        return Value::zero(width);
    }
    // §8.4, §15.3, §15.4: a handle of a built-in class of package `std`
    // (`mailbox`, `semaphore`, `process`) starts null, like a user class's.
    if let DataType::TypeReference { name, .. } = dt
        && name.scopes.iter().all(|s| s.name.name == "std")
        && matches!(name.name.name.as_str(), "mailbox" | "semaphore" | "process")
    {
        return Value::zero(width);
    }
    if is_type_two_state(dt) {
        Value::zero(width)
    } else {
        Value::new(width)
    }
}

/// §23.2.2.3: the net type a port with NO explicit net type still takes.
///
/// A port declared without a data type (`input a`, `output [3:0] y`, or a
/// non-ANSI `input a;` that no net/variable declaration completes) is a net
/// of the default net type, whatever its direction. An ANSI `input` /
/// `inout` whose data type is `logic` (`input logic [3:0] a`) is a net too:
/// the port kind defaults to net for those directions, and `logic` is a
/// valid net data type. Other data types (`int`, `bit`, typedefs, ...) and
/// `var` make a variable, as does an explicitly typed output. A non-ANSI
/// `output d; reg d;` is completed to a variable by the declaration arm,
/// which unregisters the net again.
///
/// Returning None for these left every such port out of `nets`, so VPI
/// reported `vpiReg` for what the standard (and the reference simulator)
/// call a `vpiNet`.
fn implicit_port_net_type(
    direction: Option<PortDirection>,
    var_kw: bool,
    data_type: Option<&DataType>,
    ansi: bool,
) -> Option<NetType> {
    if var_kw || matches!(direction, Some(PortDirection::Ref)) {
        return None;
    }
    match data_type {
        None | Some(DataType::Implicit { .. }) => Some(NetType::Wire),
        Some(DataType::IntegerVector {
            kind: IntegerVectorType::Logic,
            ..
        }) if ansi && matches!(direction, Some(PortDirection::Input | PortDirection::Inout)) => {
            Some(NetType::Wire)
        }
        _ => None,
    }
}

/// The net type of an ANSI port: the declared one, else the §23.2.2.3
/// implicit one (`output o` and `input logic i` are wires).
pub(super) fn ansi_port_net_type(port: &AnsiPort) -> Option<NetType> {
    port.net_type.or_else(|| {
        implicit_port_net_type(port.direction, port.var_kw, port.data_type.as_ref(), true)
    })
}

/// The net type of a non-ANSI port declaration (`output o;` is a wire).
pub(super) fn port_decl_net_type(pd: &PortDeclaration) -> Option<NetType> {
    pd.net_type
        .or_else(|| implicit_port_net_type(Some(pd.direction), false, Some(&pd.data_type), false))
}

/// §6.9 / §6.9.1: whether a declared type is a vector (has a packed
/// dimension, equal bounds included, or is a packed structure) rather than a
/// scalar. Follows typedefs without changing the dimension tables used for
/// §7.4 selects and §20.7 array queries.
pub(super) fn declared_vector_shape(
    data_type: Option<&DataType>,
    typedef_types: &HashMap<String, DataType>,
) -> bool {
    let mut dt = data_type;
    for _ in 0..64 {
        match dt {
            Some(DataType::TypeReference {
                name: ty,
                dimensions,
                ..
            }) if dimensions.is_empty() => {
                dt = lookup_scoped_type(ty, typedef_types);
            }
            Some(
                DataType::IntegerVector { dimensions, .. }
                | DataType::Implicit { dimensions, .. }
                | DataType::TypeReference { dimensions, .. },
            ) => return !dimensions.is_empty(),
            Some(DataType::Struct(st)) => return st.packed,
            Some(DataType::Enum(et)) => {
                // §6.19 / §7.4.1 / §10.3.3: an enum keeps its base's
                // shape, including a one-bit packed vector or scalar logic.
                if !et.dimensions.is_empty() {
                    return true;
                }
                dt = et.base_type.as_deref();
            }
            _ => return false,
        }
    }
    false
}

/// Record every semantic property carried by a built-in net type.  Keeping
/// this in one helper prevents elaboration paths from setting an initial value
/// while forgetting the metadata needed after a driver changes or releases.
pub(super) fn register_net_type(
    elab: &mut ElaboratedModule,
    name: &str,
    net_type: NetType,
    data_type: Option<&DataType>,
) {
    if declared_vector_shape(data_type, &elab.typedef_types) {
        elab.vector_nets.insert(name.to_string());
    }
    elab.nets.insert(name.to_string());
    if matches!(net_type, NetType::Supply0 | NetType::Supply1) {
        elab.supply_nets.insert(name.to_string());
    }
    if let Some(kind) = ResolvedNetKind::from_net_type(net_type) {
        elab.resolved_net_kinds.insert(name.to_string(), kind);
    }
    if matches!(net_type, NetType::Interconnect) {
        elab.interconnect_nets.insert(name.to_string());
    }
}

pub(super) fn unregister_net_type(elab: &mut ElaboratedModule, name: &str) {
    elab.nets.remove(name);
    elab.vector_nets.remove(name);
    elab.supply_nets.remove(name);
    elab.resolved_net_kinds.remove(name);
    elab.interconnect_nets.remove(name);
}

pub(super) fn default_net_value(net_type: NetType, width: u32, is_real: bool) -> Value {
    if is_real {
        return Value::from_f64(0.0);
    }
    match net_type {
        NetType::Supply0 | NetType::Tri0 => Value::zero(width),
        NetType::Supply1 | NetType::Tri1 => Value::ones(width),
        // §6.6.4: charge storage has no retained value until first driven.
        NetType::TriReg => Value::all_x(width),
        NetType::Wire
        | NetType::Tri
        | NetType::Wand
        | NetType::Wor
        | NetType::TriAnd
        | NetType::TriOr
        | NetType::Uwire
        | NetType::Interconnect => Value::all_z(width),
        NetType::Wreal => Value::from_f64(0.0),
    }
}

pub(super) fn default_port_value(
    direction: Option<PortDirection>,
    data_type: Option<&DataType>,
    width: u32,
    is_real: bool,
    net_type: Option<NetType>,
) -> Value {
    if is_real {
        return Value::from_f64(0.0);
    }
    if let Some(net_type) = net_type {
        return default_net_value(net_type, width, false);
    }
    let two_state = data_type.map(is_type_two_state).unwrap_or(false);
    if matches!(direction, Some(PortDirection::Input | PortDirection::Inout)) {
        if two_state {
            Value::zero(width)
        } else {
            Value::all_z(width)
        }
    } else if two_state {
        // §6.8: an `output bit` port is a 2-state variable, 0 until written.
        Value::zero(width)
    } else {
        Value::new(width)
    }
}

/// Returns true for 2-state types (bit, byte, shortint, int, longint) whose default is 0.
/// `is_type_two_state` that resolves a typedef against the type table first.
///
/// §6.8 + Table 6-7: a 2-STATE variable initializes to 0, a 4-state one to x,
/// and §6.18 makes a typedef a pure ALIAS that cannot change that. The plain
/// predicate has no `TypeReference` arm, so a variable reached through a
/// typedef (`typedef bit [7:0] bt8; bt8 a;`) was treated as 4-state and came
/// up x — while the identical direct declaration came up 0. Silent, and it
/// changed which branch of `if (a == 0)` was taken.
pub fn is_type_two_state_resolved(
    dt: &DataType,
    typedef_types: &HashMap<String, DataType>,
) -> bool {
    let resolved = resolve_typedef_chain(dt, typedef_types);
    // §6.19.2: likewise for an enum whose BASE is reached through a typedef.
    if let DataType::Enum(e) = resolved {
        return match e.base_type.as_deref() {
            Some(bt) => is_type_two_state_resolved(bt, typedef_types),
            // §6.19: with NO base type the default is `int`, which is
            // 2-state. Match `is_type_two_state` (`unwrap_or(true)`): a bare
            // `enum {A0,A1} k;` default-initializes to 0, not x.
            None => true,
        };
    }
    // §7.2.1 / §7.3.1: a packed struct or union whose members are all 2-state
    // is 2-state (it starts at 0); one 4-state member makes it 4-state.
    // Members are reached through typedefs here.
    if let DataType::Struct(su) = resolved {
        return su.packed
            && !su.members.is_empty()
            && su
                .members
                .iter()
                .all(|m| is_type_two_state_resolved(&m.data_type, typedef_types));
    }
    is_type_two_state(resolved)
}

pub fn is_type_two_state(dt: &DataType) -> bool {
    match dt {
        DataType::IntegerVector { kind, .. } => matches!(kind, IntegerVectorType::Bit),
        DataType::IntegerAtom { kind, .. } => matches!(
            kind,
            IntegerAtomType::Byte
                | IntegerAtomType::ShortInt
                | IntegerAtomType::Int
                | IntegerAtomType::LongInt
        ),
        DataType::Real { .. } => true,
        // §6.19.2: an enum's state-ness follows its BASE type — `enum bit
        // [3:0] {...} e;` default-initializes to 0, `enum reg [3:0]` to x.
        // §6.19: with NO base type the default is `int` — 2-STATE, so a bare
        // `enum {A0,A1} k;` initializes to 0 (it read x before).
        DataType::Enum(e) => e
            .base_type
            .as_deref()
            .map(is_type_two_state)
            .unwrap_or(true),
        // §7.2.1 / §7.3.1: a packed struct or union is 2-state when every
        // member is (a typedef'd member is not resolved here: 4-state).
        DataType::Struct(su) => {
            su.packed
                && !su.members.is_empty()
                && su.members.iter().all(|m| is_type_two_state(&m.data_type))
        }
        _ => false,
    }
}

/// Ceil-log2 (number of bits to index `n` values): `$clog2(n)`. 0 for n<=1.
pub(super) fn ceil_log2(n: u64) -> u64 {
    if n <= 1 {
        return 0;
    }
    let mut res = 0u64;
    let mut t = n - 1;
    while t > 0 {
        t >>= 1;
        res += 1;
    }
    res
}
