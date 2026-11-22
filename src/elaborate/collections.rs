use super::*;

/// Fully resolve a `DataType` through a chain of typedef aliases
/// (`typedef A B; typedef B C; typedef C struct{…}`). A single
/// `typedef_types.get(name)` only peels one level, so a struct reached through
/// several aliases (black-parrot's CCE types) loses its layout. Follow the chain
/// until a non-`TypeReference` (or an unresolved name) is hit; a small iteration
/// guard prevents looping on recursive typedefs (caught separately at decl time).
/// IEEE 1800-2023 §7.4.5 / §7.8: the dimension at which an unpacked array's
/// ELEMENT becomes a collection of its own, after one or more leading
/// dimensions: the innermost one (`int q[3][$]`, `int a[2][k_t]`), or the
/// FIRST associative one when more dimensions follow it (`int
/// v[2][string][string]`, `int d[][string][string]`: every `v[i]` is an
/// associative array of associative arrays). Requiring the innermost
/// dimension to be the only collection left `v[0]` unregistered, so
/// `v[0]["A"]["B"] = 7` was lost.
pub fn coll_elem_split(dims: &[UnpackedDimension]) -> Option<usize> {
    if dims.len() < 2 {
        return None;
    }
    if let Some(k) = dims
        .iter()
        .position(|d| matches!(d, UnpackedDimension::Associative { .. }))
        && k >= 1
        && k + 1 < dims.len()
    {
        return Some(k);
    }
    matches!(
        dims[dims.len() - 1],
        UnpackedDimension::Unsized(_)
            | UnpackedDimension::Queue { .. }
            | UnpackedDimension::Associative { .. }
    )
    .then_some(dims.len() - 1)
}

pub fn resolve_typedef_chain<'a>(
    dt: &'a DataType,
    typedef_types: &'a HashMap<String, DataType>,
) -> &'a DataType {
    let mut cur = dt;
    for _ in 0..64 {
        let DataType::TypeReference { name, .. } = cur else {
            break;
        };
        // §26.3: a SCOPED reference (`P::T`) names the package's typedef and
        // must not be captured by a same-named local — try the qualified key
        // first (package walks register both spellings).
        let scoped = lookup_scoped_type(name, typedef_types);
        match scoped {
            Some(next) => cur = next,
            None => break,
        }
    }
    cur
}

/// §7.8.4: the index type of one associative dimension.
#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum KeyKind {
    /// `[*]`: any integral index (§7.8.1).
    Wildcard,
    /// `[string]` (§7.8.2).
    String,
    /// An integral index type of the given width and signedness (§7.8.4).
    Integral { width: u32, signed: bool },
    /// A named index type not resolved here — a class (§7.8.5), an enum,
    /// or a type parameter bound per specialization.
    Typed(String),
    /// An index type whose width could not be resolved at elaboration.
    Unknown,
}

/// The kind of one unpacked dimension of a collection (§7.4).
#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum Dim {
    /// `[N]` / `[L:R]` (§7.4.2), with its inclusive `(lo, hi)` index bounds
    /// when they fold at elaboration (`[3:1]` is `(1, 3)`); `None` when a
    /// bound depends on a class parameter, so a specialization's own size
    /// is never checked against the default one.
    Fixed(Option<(i64, i64)>),
    /// `[]` (§7.5).
    Dyn,
    /// `[$]` / `[$:N]` (§7.10).
    Queue,
    /// `[T]` (§7.8).
    Assoc(KeyKind),
}

/// §7.4.5: the declared shape of an unpacked collection — every dimension,
/// outermost first, whatever their kinds — so each level of a nested
/// collection (`int x[string][int][$]`, `int d[][string][$]`) has a declared
/// kind and key type rather than one guessed from its stored elements.
#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct CollShape {
    pub dims: Vec<Dim>,
}

impl CollShape {
    /// The shape of a declaration with unpacked dimensions `dims` when it is
    /// a collection of collections — two or more dimensions, one of them
    /// dynamic, queue or associative — else `None`: a one-dimensional
    /// collection has no rows, and an all-fixed array is laid out by its
    /// bounds. `params` folds fixed bounds (`None` folds literals only);
    /// `key_kind` resolves each associative dimension's index type.
    pub fn of(
        dims: &[UnpackedDimension],
        params: Option<&HashMap<String, Value>>,
        key_kind: impl Fn(Option<&DataType>) -> KeyKind,
    ) -> Option<CollShape> {
        let fixed = |d: &UnpackedDimension| {
            matches!(
                d,
                UnpackedDimension::Range { .. } | UnpackedDimension::Expression { .. }
            )
        };
        if dims.len() < 2 || dims.iter().all(fixed) {
            return None;
        }
        let dims: Vec<Dim> = dims
            .iter()
            .map(|d| match d {
                UnpackedDimension::Range { .. } | UnpackedDimension::Expression { .. } => {
                    Dim::Fixed(const_unpacked_bounds(std::slice::from_ref(d), params))
                }
                UnpackedDimension::Unsized(_) => Dim::Dyn,
                UnpackedDimension::Queue { .. } => Dim::Queue,
                UnpackedDimension::Associative { data_type, .. } => {
                    Dim::Assoc(key_kind(data_type.as_deref()))
                }
            })
            .collect();
        Some(CollShape { dims })
    }
}

/// §7.8.4: the [`KeyKind`] of an associative index type `kdt`. Without a
/// typedef table (a class property) a named type stays `Typed`.
pub fn coll_key_kind(
    kdt: Option<&DataType>,
    params: Option<&HashMap<String, Value>>,
    typedefs: Option<&HashMap<String, u32>>,
    typedef_types: Option<&HashMap<String, DataType>>,
) -> KeyKind {
    let Some(kdt) = kdt else {
        return KeyKind::Wildcard;
    };
    let resolved = typedef_types.map_or(kdt, |t| resolve_typedef_chain(kdt, t));
    match resolved {
        DataType::Simple {
            kind: SimpleType::String,
            ..
        } => KeyKind::String,
        DataType::TypeReference { name, .. } => KeyKind::Typed(name.name.name.clone()),
        dt => match resolve_type_width(dt, params, typedefs) {
            0 => KeyKind::Unknown,
            width => KeyKind::Integral {
                width,
                signed: is_type_signed_resolved(dt, typedef_types.unwrap_or(&HashMap::default())),
            },
        },
    }
}

/// Records the declared [`CollShape`] of a module/package-scope collection.
pub(super) fn record_coll_shape(
    elab: &mut ElaboratedModule,
    name: &str,
    dims: &[UnpackedDimension],
    params: Option<&HashMap<String, Value>>,
) {
    let params = Some(params.unwrap_or(&elab.parameters));
    let shape = CollShape::of(dims, params, |kdt| {
        coll_key_kind(kdt, params, Some(&elab.typedefs), Some(&elab.typedef_types))
    });
    if let Some(shape) = shape {
        elab.coll_shapes.insert(name.to_string(), shape);
    }
}


/// §7.8.2: what the runtime needs about an associative array's KEY type —
/// its (width, signedness) for an integral key, and the typedef name a
/// `TypeReference` key names (enum key rendering). A string or wildcard key
/// has no index width.
pub fn assoc_key_type_info(
    kdt: Option<&DataType>,
    params: &HashMap<String, Value>,
    typedefs: &HashMap<String, u32>,
    typedef_types: &HashMap<String, DataType>,
) -> (Option<(u32, bool)>, Option<String>) {
    let Some(kdt) = kdt else {
        return (None, None);
    };
    let tn = match kdt {
        DataType::TypeReference { name, .. } => Some(name.name.name.clone()),
        _ => None,
    };
    if matches!(
        resolve_typedef_chain(kdt, typedef_types),
        DataType::Simple {
            kind: SimpleType::String,
            ..
        }
    ) {
        return (None, tn);
    }
    let kw = resolve_type_width(kdt, Some(params), Some(typedefs));
    (
        (kw > 0).then(|| (kw, is_type_signed_resolved(kdt, typedef_types))),
        tn,
    )
}

/// A fixed outer array's associative rows have the same declared key type
/// as a standalone associative array (§7.8.4 / §12.7.3).
pub(super) fn register_assoc_element_key_type(
    elab: &mut ElaboratedModule,
    name: String,
    string_key: bool,
    width: u32,
    key_info: &(Option<(u32, bool)>, Option<String>),
) {
    if let Some(index) = key_info.0 {
        elab.assoc_index_widths.insert(name.clone(), index);
    }
    if let Some(key_type) = &key_info.1 {
        elab.assoc_key_type_names
            .insert(name.clone(), key_type.clone());
    }
    if width > 0 {
        elab.assoc_elem_widths.insert(name.clone(), width);
    }
    elab.associative_arrays.insert(name, string_key);
}
