use super::*;

/// Default implementation limit for a single packed declaration, in bits.
/// Packed behavioural memories can legitimately be several megabits wide.
pub const SANE_MAX_PACKED_WIDTH: u32 = 1 << 24;

/// Unreferenced declarations can be dropped below the allocation limit.
const DEAD_DECL_WIDTH_THRESHOLD: u32 = 1 << 20;

pub fn max_packed_width() -> u32 {
    static LIMIT: std::sync::OnceLock<u32> = std::sync::OnceLock::new();
    *LIMIT.get_or_init(|| {
        std::env::var("XEZIM_MAX_PACKED_WIDTH")
            .ok()
            .and_then(|s| s.parse::<u32>().ok())
            .filter(|&n| n > 0 && n <= Value::MAX_WIDTH)
            .unwrap_or(SANE_MAX_PACKED_WIDTH)
    })
}

/// Quiet width probe for the dead-declaration elision below: mirrors
/// `resolve_type_width`'s IntegerVector/TypeReference math WITHOUT the
/// clamp-and-warn side effects. Unresolvable dimensions yield 0 ("don't
/// know" — never elide on a guess).
fn quiet_packed_width_probe(
    dt: &DataType,
    params: &HashMap<String, Value>,
    typedef_widths: &HashMap<String, u32>,
) -> u64 {
    let dims_product = |dims: &[PackedDimension]| -> Option<u64> {
        let mut total = 1u64;
        for dim in dims {
            let PackedDimension::Range { left, right, .. } = dim else {
                return None;
            };
            let l = const_eval_i64_with_params(left, Some(params))?;
            let r = const_eval_i64_with_params(right, Some(params))?;
            total = total.saturating_mul(l.abs_diff(r).saturating_add(1));
        }
        Some(total)
    };
    match dt {
        DataType::IntegerVector { dimensions, .. } => {
            if dimensions.is_empty() {
                return 1;
            }
            dims_product(dimensions).unwrap_or(0)
        }
        DataType::TypeReference {
            name, dimensions, ..
        } => {
            let base = lookup_scoped_type(name, typedef_widths)
                .copied()
                .or_else(|| typedef_widths.get(&name.name.name).copied())
                .unwrap_or(0) as u64;
            if base == 0 {
                return 0;
            }
            match dims_product(dimensions) {
                Some(p) => base.saturating_mul(p),
                None => 0,
            }
        }
        _ => 0,
    }
}

/// Serialize every definition's AST for the byte-level reference probe. A
/// genuine reference to a name — expression ident, hierarchical segment,
/// port connection, even a DPI/`uvm_hdl` path STRING — necessarily carries
/// the name's exact bytes in this stream, so an occurrence count of ONE
/// (the declarator itself) proves the declaration dead. Substring
/// collisions only inflate the count, which merely KEEPS a dead variable —
/// the safe direction. Only runs for beyond-cap declarations, so ordinary
/// designs never pay for it.
fn design_ast_blob(all_defs: &HashMap<String, Definition>) -> Vec<u8> {
    let mut blob: Vec<u8> = Vec::new();
    for def in all_defs.values() {
        let cfg = crate::xez_bincode_config();
        let bytes = match def {
            Definition::Module(m) => bincode::serde::encode_to_vec(m, cfg),
            Definition::Interface(i) => bincode::serde::encode_to_vec(i, cfg),
            Definition::Program(p) => bincode::serde::encode_to_vec(p, cfg),
            Definition::Class(c) => bincode::serde::encode_to_vec(c, cfg),
            Definition::Covergroup(cg) => bincode::serde::encode_to_vec(cg, cfg),
            Definition::Package(p) => bincode::serde::encode_to_vec(p, cfg),
            Definition::Typedef(t) => bincode::serde::encode_to_vec(t, cfg),
            Definition::Udp(u) => bincode::serde::encode_to_vec(u, cfg),
        };
        if let Ok(b) = bytes {
            blob.extend_from_slice(&b);
        }
    }
    blob
}

fn count_byte_occurrences(blob: &[u8], needle: &[u8]) -> usize {
    if needle.is_empty() || blob.len() < needle.len() {
        return 0;
    }
    let mut n = 0usize;
    let mut i = 0usize;
    while i + needle.len() <= blob.len() {
        if &blob[i..i + needle.len()] == needle {
            n += 1;
            i += needle.len();
        } else {
            i += 1;
        }
    }
    n
}

/// Over-cap dead-declaration elision: the reference simulator silently
/// drops variables referenced nowhere, so a leftover multi-megabit debug
/// array (a real customer-BFM pattern) neither warns nor allocates there.
/// Returns Some(filtered copy) when at least one declarator was elided.
/// Guards: a large packed width (probed without recording diagnostics), no initializer, no
/// unpacked dimensions, and the name's serialized-AST occurrence count is
/// exactly the declarator itself.
pub(super) fn filter_dead_giant_declarators(
    dd: &crate::ast::decl::DataDeclaration,
    elab: &ElaboratedModule,
    all_defs: Option<&HashMap<String, Definition>>,
) -> Option<crate::ast::decl::DataDeclaration> {
    let Some(defs) = all_defs else { return None };
    let w = quiet_packed_width_probe(&dd.data_type, &elab.parameters, &elab.typedefs);
    if w <= DEAD_DECL_WIDTH_THRESHOLD.min(max_packed_width()) as u64 {
        return None;
    }
    let candidates: Vec<usize> = dd
        .declarators
        .iter()
        .enumerate()
        .filter(|(_, d)| d.init.is_none() && d.dimensions.is_empty())
        .map(|(i, _)| i)
        .collect();
    if candidates.is_empty() {
        return None;
    }
    let blob = design_ast_blob(defs);
    let mut elide: Vec<usize> = Vec::new();
    for &i in &candidates {
        let name = &dd.declarators[i].name.name;
        if count_byte_occurrences(&blob, name.as_bytes()) == 1 {
            crate::elab_diag(format!(
                "[xezim][note] eliding dead {}-bit declaration '{}' (referenced \
                 nowhere in the design; commercial simulators drop it silently)",
                w, name
            ));
            elide.push(i);
        }
    }
    if elide.is_empty() {
        return None;
    }
    let mut filtered = dd.clone();
    let mut idx = 0usize;
    filtered.declarators.retain(|_| {
        let keep = !elide.contains(&idx);
        idx += 1;
        keep
    });
    Some(filtered)
}

thread_local! {
    // Width queries also run speculatively; report the first over-limit
    // declaration encountered when elaborating the selected hierarchy.
    pub(super) static PACKED_WIDTH_ERROR: std::cell::RefCell<Option<String>> = const { std::cell::RefCell::new(None) };
    static SUPPRESS_WIDTH_WARNINGS: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

pub(crate) fn check_packed_widths() -> Result<(), String> {
    PACKED_WIDTH_ERROR.with(|slot| match slot.take() {
        Some(error) => Err(error),
        None => Ok(()),
    })
}

/// Scoped suppression of `clamp_packed_width` warnings (clamping itself is
/// unaffected). Used by pre-elaboration width scans; see the thread-local.
pub fn with_width_warnings_suppressed<R>(f: impl FnOnce() -> R) -> R {
    SUPPRESS_WIDTH_WARNINGS.with(|c| c.set(true));
    let r = f();
    SUPPRESS_WIDTH_WARNINGS.with(|c| c.set(false));
    r
}

pub(super) fn clamp_packed_width(w: u64, ctx: &str, detail: &str) -> u32 {
    let limit = max_packed_width();
    if w <= u64::from(limit) {
        return w as u32;
    }
    if !SUPPRESS_WIDTH_WARNINGS.with(|c| c.get()) && !crate::elab_diags_muted() {
        PACKED_WIDTH_ERROR.with(|slot| {
            let mut error = slot.borrow_mut();
            if error.is_none() {
                *error = Some(format!(
                    "packed width {w} exceeds implementation limit {limit} ({ctx}, {detail}); \
                     set XEZIM_MAX_PACKED_WIDTH to a supported width up to {} bits",
                    Value::MAX_WIDTH
                ));
            }
        });
    }
    // Width queries also run during tentative scans. Keep temporary storage
    // bounded until the enclosing elaboration returns the captured error.
    1
}

/// Describe an underflowed packed range for `clamp_packed_width` detail:
/// resolved bounds, the parameter identifiers appearing in the bound
/// expressions with their resolved values, and the source byte offset (a
/// span into the preprocessed file — searchable even without file:line).
pub(super) fn describe_packed_range(
    left: &Expression,
    right: &Expression,
    l: i64,
    r: i64,
    params: Option<&HashMap<String, Value>>,
) -> String {
    let mut idents: Vec<String> = Vec::new();
    collect_ident_names(left, &mut idents);
    collect_ident_names(right, &mut idents);
    // Scoped refs (`pkg::P`, parsed as multi-segment Ident or MemberAccess)
    // aren't collected above (that walker also feeds implicit-net creation);
    // gather them here so the diagnostic can resolve their alias keys.
    fn collect_scoped(e: &Expression, out: &mut Vec<String>) {
        match &e.kind {
            ExprKind::Ident(h) if h.path.len() == 2 => {
                out.push(format!("{}::{}", h.path[0].name.name, h.path[1].name.name));
            }
            ExprKind::MemberAccess { expr: base, member } => {
                if let ExprKind::Ident(bh) = &base.kind {
                    if bh.path.len() == 1 {
                        out.push(format!("{}::{}", bh.path[0].name.name, member.name));
                    }
                }
            }
            ExprKind::Unary { operand, .. } => collect_scoped(operand, out),
            ExprKind::Binary { left, right, .. } => {
                collect_scoped(left, out);
                collect_scoped(right, out);
            }
            ExprKind::Paren(i) => collect_scoped(i, out),
            _ => {}
        }
    }
    collect_scoped(left, &mut idents);
    collect_scoped(right, &mut idents);
    idents.sort();
    idents.dedup();
    let mut d = format!("range resolved to [{}:{}]", l, r);
    // Drop a bare scope segment (`cfgp`) when its scoped form
    // (`cfgp::X`) is also listed — the segment alone is never a param.
    let scoped_prefixes: Vec<String> = idents
        .iter()
        .filter(|n| n.contains("::"))
        .filter_map(|n| n.split("::").next().map(|s| s.to_string()))
        .collect();
    let idents: Vec<String> = idents
        .into_iter()
        .filter(|n| n.contains("::") || !scoped_prefixes.contains(n))
        .collect();
    if !idents.is_empty() {
        let vals: Vec<String> = idents
            .iter()
            .take(4)
            .map(|n| match params.and_then(|p| p.get(n)) {
                Some(v) => format!("{}={}", n, v.to_u64().unwrap_or(0)),
                None => format!("{}=<unresolved>", n),
            })
            .collect();
        d.push_str(&format!(" with {}", vals.join(", ")));
        // Owning-scope hint: a package parameter also lives under its
        // `pkg::name` alias, so listing matching aliases names the package
        // that computed the bad value — module-scope params have none.
        // Signed view too: 4294967290 is far more recognizable as -6.
        if let Some(pm) = params {
            let mut owners: Vec<String> = Vec::new();
            for n in idents.iter().take(4) {
                let suffix = format!("::{}", n);
                for (k, v) in pm.iter() {
                    if k.ends_with(&suffix) {
                        owners.push(format!("{}={}", k, v.to_u64().unwrap_or(0) as i64 as i32));
                    }
                }
            }
            owners.sort();
            owners.dedup();
            if owners.is_empty() {
                d.push_str("; no pkg:: alias found (module-scope or unhoisted)");
            } else {
                d.push_str(&format!("; aliases: {}", owners.join(", ")));
            }
        }
        d.push_str(&format!(
            "; rerun --compile with XEZIM_TRACE_PARAM={} for the full write trail",
            idents.iter().take(4).cloned().collect::<Vec<_>>().join(",")
        ));
    }
    d.push_str(&format!(" (source offset {})", left.span.start));
    d
}
