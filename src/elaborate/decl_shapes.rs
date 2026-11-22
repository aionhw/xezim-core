use super::*;

/// IEEE 1800-2023 §20.6.2 / §20.7: the DECLARED shape of one variable, net or
/// port — its data type plus the unpacked dimensions written on the
/// declarator. `$bits` and the array query functions are constant functions
/// of that declared type when it is fixed-size, so a `localparam`, a packed
/// width, a parameter override or a generate condition may use them.
#[derive(Debug, Clone)]
pub struct DeclShape {
    pub data_type: DataType,
    pub unpacked: Vec<UnpackedDimension>,
    /// Typed by one of the module's own TYPE parameters: only the instance's
    /// width binding (TYPEDEFS_TLS) describes it, never a same-named typedef.
    pub by_type_param: bool,
    /// A value parameter's declared type (§20.7 queries a parameter's shape
    /// as it does a variable's).
    pub param: bool,
}

/// The common declaration types do not need the space of a named type in
/// every shape-table bucket. Keep their fields verbatim, including spans;
/// rich types retain the complete AST in the fallback.
#[derive(Debug, Clone)]
enum DeclShapeDataType {
    IntegerVector {
        kind: IntegerVectorType,
        signing: Option<Signing>,
        dimensions: Vec<PackedDimension>,
        span: Span,
    },
    IntegerAtom {
        kind: IntegerAtomType,
        signing: Option<Signing>,
        span: Span,
    },
    Real {
        kind: RealType,
        span: Span,
    },
    Implicit {
        signing: Option<Signing>,
        dimensions: Vec<PackedDimension>,
        span: Span,
    },
    Other(Box<DataType>),
}

impl DeclShapeDataType {
    fn new(dt: &DataType) -> Self {
        match dt {
            DataType::IntegerVector {
                kind,
                signing,
                dimensions,
                span,
            } => Self::IntegerVector {
                kind: *kind,
                signing: *signing,
                dimensions: dimensions.clone(),
                span: *span,
            },
            DataType::IntegerAtom {
                kind,
                signing,
                span,
            } => Self::IntegerAtom {
                kind: *kind,
                signing: *signing,
                span: *span,
            },
            DataType::Real { kind, span } => Self::Real {
                kind: *kind,
                span: *span,
            },
            DataType::Implicit {
                signing,
                dimensions,
                span,
            } => Self::Implicit {
                signing: *signing,
                dimensions: dimensions.clone(),
                span: *span,
            },
            _ => Self::Other(Box::new(dt.clone())),
        }
    }

    fn into_data_type(self) -> DataType {
        match self {
            Self::IntegerVector {
                kind,
                signing,
                dimensions,
                span,
            } => DataType::IntegerVector {
                kind,
                signing,
                dimensions,
                span,
            },
            Self::IntegerAtom {
                kind,
                signing,
                span,
            } => DataType::IntegerAtom {
                kind,
                signing,
                span,
            },
            Self::Real { kind, span } => DataType::Real { kind, span },
            Self::Implicit {
                signing,
                dimensions,
                span,
            } => DataType::Implicit {
                signing,
                dimensions,
                span,
            },
            Self::Other(dt) => *dt,
        }
    }
}

#[derive(Debug, Clone)]
pub(super) struct StoredDeclShape {
    data_type: DeclShapeDataType,
    unpacked: Vec<UnpackedDimension>,
    by_type_param: bool,
    param: bool,
}

impl StoredDeclShape {
    fn new(
        dt: &DataType,
        unpacked: &[UnpackedDimension],
        by_type_param: bool,
        param: bool,
    ) -> Self {
        Self {
            data_type: DeclShapeDataType::new(dt),
            unpacked: unpacked.to_vec(),
            by_type_param,
            param,
        }
    }

    fn into_decl_shape(self) -> DeclShape {
        DeclShape {
            data_type: self.data_type.into_data_type(),
            unpacked: self.unpacked,
            by_type_param: self.by_type_param,
            param: self.param,
        }
    }
}

#[cfg(test)]
mod decl_shape_storage_tests {
    use super::*;

    #[test]
    fn compact_shape_types_preserve_their_ast_fields() {
        let parsed = crate::parse(
            "module shapes; logic signed [3:1] v [2:5]; int unsigned a; realtime r; \
             wire signed [7:0] imp; typedef logic [6:0] word_t; word_t named [1:3]; \
             struct packed { logic [1:0] x; bit y; } aggregate; \
             enum logic [2:0] { A, B } enumeration; endmodule",
        );
        assert!(parsed.errors.is_empty(), "{:?}", parsed.errors);
        let crate::ast::Description::Module(module) = &parsed.source.descriptions[0] else {
            panic!("expected module");
        };
        let (shapes, _) = collect_decl_shapes(
            &module.ports,
            &module.items,
            &module.params,
            &HashSet::default(),
        );
        for item in &module.items {
            let (dt, name, dims) = match item {
                ModuleItem::DataDeclaration(d) => (
                    &d.data_type,
                    &d.declarators[0].name,
                    &d.declarators[0].dimensions,
                ),
                ModuleItem::NetDeclaration(d) => (
                    &d.data_type,
                    &d.declarators[0].name,
                    &d.declarators[0].dimensions,
                ),
                _ => continue,
            };
            let stored = shapes.get(&name.name).expect("fixed declaration shape");
            let shape = stored.clone().into_decl_shape();
            assert_eq!(
                serde_json::to_value(&shape.data_type).unwrap(),
                serde_json::to_value(dt).unwrap()
            );
            assert_eq!(
                serde_json::to_value(&shape.unpacked).unwrap(),
                serde_json::to_value(dims).unwrap()
            );
            assert!(!shape.by_type_param);
            assert!(!shape.param);
        }
        assert!(std::mem::size_of::<StoredDeclShape>() < std::mem::size_of::<DeclShape>());
    }

    #[test]
    fn streamed_scope_items_keep_declaration_order_and_generate_boundaries() {
        let parsed = crate::parse(
            "module shapes #(parameter type T=logic [5:0]); \
             generate logic [3:0] first; T typed; endgenerate \
             logic [9:0] first; \
             if (1) begin : child logic hidden; end \
             localparam logic [4:0] P=0; endmodule",
        );
        assert!(parsed.errors.is_empty(), "{:?}", parsed.errors);
        let crate::ast::Description::Module(module) = &parsed.source.descriptions[0] else {
            panic!("expected module");
        };
        let (shapes, type_params) = collect_decl_shapes(
            &module.ports,
            &module.items,
            &module.params,
            &HashSet::default(),
        );
        assert!(type_params.contains("T"));
        assert!(shapes["typed"].by_type_param);
        assert!(shapes["P"].param);
        assert!(!shapes.contains_key("hidden"));
        let first = shapes["first"].clone().into_decl_shape();
        assert_eq!(resolve_type_width(&first.data_type, None, None), 4);
    }
}

thread_local! {
    /// Declared shapes of the module (or instance) whose body is being
    /// elaborated, keyed by bare name. Installed by `DeclShapesGuard` for that
    /// scope only and restored afterwards, so a name never answers from
    /// another module's declarations, and nothing is installed at run time.
    static DECL_SHAPES_TLS: std::cell::RefCell<Option<std::rc::Rc<HashMap<String, StoredDeclShape>>>>
        = const { std::cell::RefCell::new(None) };
    /// Built declared-shape tables, keyed by definition (name and source
    /// identity) — see `install_decl_shapes`.
    pub(super) static DECL_SHAPES_CACHE: std::cell::RefCell<HashMap<(String, usize, usize), DeclShapeTable>>
        = std::cell::RefCell::new(HashMap::default());
    /// The generate blocks being elaborated in that scope (see
    /// `elaborate_block_items`) and the type parameters visible there.
    static DECL_SHAPE_LAYERS_TLS: std::cell::RefCell<DeclShapeLayers>
        = std::cell::RefCell::new(DeclShapeLayers::default());
    /// Full definitions of the typedefs seen so far (data type and unpacked
    /// dimensions), mirroring `typedef_types` / `typedef_unpacked_dims` for
    /// const-eval, which otherwise only knows a typedef's width.
    pub(super) static TYPEDEF_SHAPES_TLS: std::cell::RefCell<(HashMap<String, DataType>, HashMap<String, Vec<UnpackedDimension>>)>
        = std::cell::RefCell::new((HashMap::default(), HashMap::default()));
}

/// §10.9: the pattern of the typed pattern `T'{...}` when `T` is unpacked;
/// `e` otherwise. An unpacked target has an equivalent type (§6.22.2), so
/// the items place as an untyped pattern's; a packed `T'{...}` is a value.
pub(super) fn peel_unpacked_typed_pattern(e: &Expression) -> &Expression {
    let ExprKind::TypedPattern { ty, pattern } = &e.kind else {
        return e;
    };
    let DataType::TypeReference { name, .. } = ty.as_ref() else {
        return e;
    };
    let unpacked = TYPEDEF_SHAPES_TLS.with(|c| {
        let (types, dims) = &*c.borrow();
        lookup_scoped_type(name, dims).is_some_and(|d| !d.is_empty())
            || lookup_scoped_type(name, types).is_some_and(
                |dt| matches!(resolve_typedef_chain(dt, types), DataType::Struct(su) if !su.packed),
            )
    });
    if unpacked { pattern } else { e }
}

/// §6.20.2: record under `key(name)` the declared type of each explicitly
/// typed value parameter of `pds`. The parameters of one declaration hold
/// one copy of its type.
pub(super) fn record_param_decl_types<'a>(
    elab: &mut ElaboratedModule,
    pds: impl Iterator<Item = &'a ParameterDeclaration>,
    key: impl Fn(&str) -> String,
    mut ty: impl FnMut(&DataType) -> Rc<DataType>,
) {
    for pd in pds {
        let ParameterKind::Data {
            data_type,
            assignments,
        } = &pd.kind
        else {
            continue;
        };
        if matches!(data_type, DataType::Implicit { signing: None, dimensions, .. } if dimensions.is_empty())
        {
            continue;
        }
        let dt = ty(data_type);
        for a in assignments.iter().filter(|a| a.dimensions.is_empty()) {
            elab.param_decl_types
                .insert_shared(key(&a.name.name), Rc::clone(&dt));
        }
    }
}

/// The parameter declarations among `items`, header ones excluded.
pub(super) fn item_param_decls(
    items: &[ModuleItem],
) -> impl Iterator<Item = &ParameterDeclaration> {
    items.iter().filter_map(|item| match item {
        ModuleItem::ParameterDeclaration(pd) | ModuleItem::LocalparamDeclaration(pd) => Some(pd),
        _ => None,
    })
}

/// Record a typedef's full definition for const-eval (see TYPEDEF_SHAPES_TLS).
/// Called whenever a typedef is (re-)registered, so a later same-named typedef
/// replaces the earlier one exactly as it does in `typedef_types`.
pub(super) fn tls_register_typedef_shape(
    name: &str,
    dt: &DataType,
    unpacked: &[UnpackedDimension],
) {
    TYPEDEF_SHAPES_TLS.with(|c| {
        let mut c = c.borrow_mut();
        c.0.insert(name.to_string(), dt.clone());
        if unpacked.is_empty() {
            c.1.remove(name);
        } else {
            c.1.insert(name.to_string(), unpacked.to_vec());
        }
    });
}

/// A TYPEDEF_SHAPES_TLS entry as it stands, for `tls_restore_typedef_shape`.
pub(super) type TypedefShapeSave = (Option<DataType>, Option<Vec<UnpackedDimension>>);

pub(super) fn tls_typedef_shape(name: &str) -> TypedefShapeSave {
    TYPEDEF_SHAPES_TLS.with(|c| {
        let c = c.borrow();
        (c.0.get(name).cloned(), c.1.get(name).cloned())
    })
}

/// §20.7: capture the packed and unpacked shape of a type actual. Its dimensions
/// are folded in `env`, the scope that wrote them, and a bound typedef brings
/// its unpacked dimensions (`typedef logic [3:0] ua_t [0:2]`).
pub(super) fn type_param_shape(
    dt: &DataType,
    mut shape: DataType,
    env: &HashMap<String, Value>,
) -> (DataType, Vec<UnpackedDimension>) {
    lsdd_data_type(&mut shape, env);
    let mut unpacked = match dt {
        DataType::TypeReference {
            name: tn,
            dimensions,
            ..
        } if dimensions.is_empty() && tn.scopes.is_empty() => {
            TYPEDEF_SHAPES_TLS.with(|c| c.borrow().1.get(&tn.name.name).cloned())
        }
        _ => None,
    }
    .unwrap_or_default();
    for d in unpacked.iter_mut() {
        match d {
            UnpackedDimension::Range { left, right, .. } => {
                lsdd_expr(left, env);
                lsdd_expr(right, env);
            }
            UnpackedDimension::Expression { expr, .. } => lsdd_expr(expr, env),
            _ => {}
        }
    }
    (shape, unpacked)
}

pub(super) fn tls_restore_typedef_shape(name: &str, saved: TypedefShapeSave) {
    TYPEDEF_SHAPES_TLS.with(|c| {
        let mut c = c.borrow_mut();
        match saved.0 {
            Some(dt) => c.0.insert(name.to_string(), dt),
            None => c.0.remove(name),
        };
        match saved.1 {
            Some(u) => c.1.insert(name.to_string(), u),
            None => c.1.remove(name),
        };
    });
}

/// Declared shapes layered over a scope's own table: one per generate block
/// being elaborated, innermost last (§27: a block's declarations hide the
/// enclosing ones), and the type parameters a declaration there may name.
#[derive(Default)]
struct DeclShapeLayers {
    type_params: std::rc::Rc<HashSet<String>>,
    blocks: Vec<std::rc::Rc<HashMap<String, StoredDeclShape>>>,
    /// The shapes of the blocks already elaborated in this scope, under
    /// their block keys (`g[0].arr`), for a query from outside (§23.6).
    left: HashMap<String, StoredDeclShape>,
    /// Every generate block's declared shapes as written, under the block
    /// path without loop indices (`g.arr`), for a query from outside a block
    /// not yet elaborated. A shape that reads a genvar does not evaluate.
    by_path: std::rc::Rc<HashMap<String, StoredDeclShape>>,
}

/// A definition's declared shapes, the names of its type parameters, and
/// its generate blocks' shapes by block path.
type DeclShapeTable = (
    std::rc::Rc<HashMap<String, StoredDeclShape>>,
    std::rc::Rc<HashSet<String>>,
    std::rc::Rc<HashMap<String, StoredDeclShape>>,
);

/// Restores the previously installed declared-shape table, and the block
/// layers over it, on drop.
pub struct DeclShapesGuard(
    Option<std::rc::Rc<HashMap<String, StoredDeclShape>>>,
    DeclShapeLayers,
);

impl Drop for DeclShapesGuard {
    fn drop(&mut self) {
        let prev = self.0.take();
        DECL_SHAPES_TLS.with(|c| *c.borrow_mut() = prev);
        let layers = std::mem::take(&mut self.1);
        DECL_SHAPE_LAYERS_TLS.with(|c| *c.borrow_mut() = layers);
    }
}

/// The declared shape of `name` in the scope being elaborated: the innermost
/// generate block that declares it, else the module or instance.
fn decl_shape_of(name: &str) -> Option<DeclShape> {
    DECL_SHAPE_LAYERS_TLS
        .with(|c| {
            c.borrow()
                .blocks
                .iter()
                .rev()
                .find_map(|m| m.get(name).cloned())
        })
        .or_else(|| {
            DECL_SHAPES_TLS.with(|c| c.borrow().as_ref().and_then(|m| m.get(name).cloned()))
        })
        .or_else(|| {
            DECL_SHAPE_LAYERS_TLS.with(|c| {
                let c = c.borrow();
                c.left.get(name).cloned().or_else(|| {
                    let unindexed = strip_block_indices(name)?;
                    c.by_path.get(&unindexed).cloned()
                })
            })
        })
        .map(StoredDeclShape::into_decl_shape)
}

/// `g[0].n.arr` without its loop indices (`g.n.arr`); None for a simple name.
fn strip_block_indices(name: &str) -> Option<String> {
    if !name.contains('.') {
        return None;
    }
    let mut out = String::with_capacity(name.len());
    let mut depth = 0u32;
    for ch in name.chars() {
        match ch {
            '[' => depth += 1,
            ']' => depth = depth.saturating_sub(1),
            _ if depth == 0 => out.push(ch),
            _ => {}
        }
    }
    Some(out)
}

/// §27.5, §27.6: the declared shapes of each generate block in `items`,
/// every arm included, under `<prefix><block>.<name>`. A key two arms
/// declare with different shapes is left out.
fn collect_block_shapes(
    items: &[ModuleItem],
    prefix: &str,
    type_params: &HashSet<String>,
    out: &mut HashMap<String, StoredDeclShape>,
    clash: &mut HashSet<String>,
) {
    let block = |name: &str,
                 block_items: &[ModuleItem],
                 out: &mut HashMap<String, StoredDeclShape>,
                 clash: &mut HashSet<String>| {
        let p = format!("{prefix}{name}.");
        let (shapes, _) = collect_decl_shapes(&PortList::Empty, block_items, &[], type_params);
        for (k, v) in shapes {
            let key = format!("{p}{k}");
            match out.get(&key) {
                Some(old) if format!("{old:?}") != format!("{v:?}") => {
                    clash.insert(key);
                }
                Some(_) => {}
                None => {
                    out.insert(key, v);
                }
            }
        }
        collect_block_shapes(block_items, &p, type_params, out, clash);
    };
    for item in items {
        match item {
            ModuleItem::GenerateRegion(g) => {
                collect_block_shapes(&g.items, prefix, type_params, out, clash)
            }
            ModuleItem::GenerateIf(g) => {
                for (bi, (_, branch)) in g.branches.iter().enumerate() {
                    if g.branch_direct.get(bi) == Some(&true) {
                        collect_block_shapes(branch, prefix, type_params, out, clash);
                        continue;
                    }
                    let label = g.branch_labels.get(bi).and_then(|l| l.as_ref());
                    block(
                        gen_scope_name(label, &g.implicit_name).as_str(),
                        branch,
                        out,
                        clash,
                    );
                }
            }
            ModuleItem::GenerateCase(g) => {
                for arm in &g.arms {
                    if arm.direct {
                        collect_block_shapes(&arm.items, prefix, type_params, out, clash);
                        continue;
                    }
                    let name = gen_scope_name(arm.label.as_ref(), &g.implicit_name);
                    block(name.as_str(), &arm.items, out, clash);
                }
            }
            ModuleItem::GenerateFor(g) => {
                let name = gen_scope_name(g.name.as_ref(), &g.implicit_name);
                block(name.as_str(), &g.items, out, clash);
            }
            _ => {}
        }
    }
}

/// The name a declared-shape operand is keyed by: a simple name, or a path
/// through generate blocks with constant indices (`g[0].arr`, parsed as
/// `Ident` segments or as member selects), as the block's rename keys its
/// declarations.
fn decl_shape_operand_name(e: &Expression) -> Option<String> {
    fn block_path(e: &Expression, out: &mut String) -> Option<()> {
        match &e.kind {
            ExprKind::Ident(h) if h.root.is_none() => {
                for (i, seg) in h.path.iter().enumerate() {
                    if i > 0 {
                        out.push('.');
                    }
                    out.push_str(&seg.name.name);
                    for sel in &seg.selects {
                        let i = const_eval_i64_with_params(sel, None)?;
                        out.push_str(&format!("[{i}]"));
                    }
                }
                Some(())
            }
            ExprKind::Index { expr, index } => {
                block_path(expr, out)?;
                let i = const_eval_i64_with_params(index, None)?;
                out.push_str(&format!("[{i}]"));
                Some(())
            }
            ExprKind::MemberAccess { expr, member } => {
                block_path(expr, out)?;
                out.push('.');
                out.push_str(&member.name);
                Some(())
            }
            _ => None,
        }
    }
    let mut name = String::new();
    match &e.kind {
        ExprKind::Ident(h) if h.path.last().is_some_and(|s| s.selects.is_empty()) => {
            block_path(e, &mut name)?
        }
        ExprKind::MemberAccess { .. } => block_path(e, &mut name)?,
        _ => return None,
    }
    Some(name)
}

/// §20.7, §20.6.2, §27: the array queries and `$bits` over a generate block's
/// own declarations are constant, as over the module's. Elaborate the block's
/// (already renamed) items with their declared shapes layered over the
/// enclosing ones; a nested block adds its own when it is reached.
pub(super) fn elaborate_block_items(
    items: &[ModuleItem],
    elab: &mut ElaboratedModule,
    all_defs: Option<&HashMap<String, Definition>>,
) -> Result<(), String> {
    // §27.5: these parameter names already carry their generate scope.
    record_param_decl_types(elab, item_param_decls(items), str::to_string, |dt| Rc::new(dt.clone()));
    let outer = DECL_SHAPE_LAYERS_TLS.with(|c| c.borrow().type_params.clone());
    let (shapes, type_params) = collect_decl_shapes(&PortList::Empty, items, &[], &outer);
    if shapes.is_empty() && type_params.len() == outer.len() {
        return elaborate_items(items, elab, all_defs);
    }
    let type_params = std::rc::Rc::new(type_params);
    DECL_SHAPE_LAYERS_TLS.with(|c| {
        let mut c = c.borrow_mut();
        c.type_params = type_params;
        c.blocks.push(std::rc::Rc::new(shapes));
    });
    let r = elaborate_items(items, elab, all_defs);
    DECL_SHAPE_LAYERS_TLS.with(|c| {
        let mut c = c.borrow_mut();
        if let Some(block) = c.blocks.pop() {
            let block = std::rc::Rc::try_unwrap(block).unwrap_or_else(|b| (*b).clone());
            c.left.extend(block);
        }
        c.type_params = outer;
    });
    r
}

/// `arr[N]` with `N` a parameter parses as an associative dimension keyed by a
/// type named `N` (see `normalize_unpacked_dims`). The name, when the
/// dimension has that shape; whether it really is a size is decided against
/// the parameters and typedefs in scope.
fn size_param_of_dim(d: &UnpackedDimension) -> Option<&str> {
    match d {
        UnpackedDimension::Associative {
            data_type: Some(dt),
            ..
        } => match dt.as_ref() {
            DataType::TypeReference {
                name, dimensions, ..
            } if name.scopes.is_empty() && dimensions.is_empty() => Some(&name.name.name),
            _ => None,
        },
        _ => None,
    }
}

/// Only a FIXED-SIZE integral or real declaration has a constant shape
/// (§20.7): a dynamic, queue or associative dimension, a string, chandle or
/// event, and an interface port are left to the run-time queries.
fn decl_shape_is_fixed(dt: &DataType, dims: &[UnpackedDimension]) -> bool {
    dims.iter().all(|d| {
        matches!(
            d,
            UnpackedDimension::Range { .. } | UnpackedDimension::Expression { .. }
        ) || size_param_of_dim(d).is_some()
    }) && matches!(
        dt,
        DataType::IntegerVector { .. }
            | DataType::IntegerAtom { .. }
            | DataType::Real { .. }
            | DataType::Struct(_)
            | DataType::Enum(_)
            | DataType::TypeReference { .. }
            | DataType::Implicit { .. }
    )
}

/// Install the declared shapes of a module's ports and body declarations for
/// the lifetime of the returned guard. The table depends only on the
/// definition's source, so it is built once per definition per design (the
/// cache is cleared when a design's elaboration starts).
pub fn install_decl_shapes(def: Definition) -> DeclShapesGuard {
    let items = def.items();
    let key = (def.name().to_string(), items.as_ptr() as usize, items.len());
    let (m, type_params, by_path) = match DECL_SHAPES_CACHE.with(|c| c.borrow().get(&key).cloned())
    {
        Some(e) => e,
        None => {
            let (m, tp) =
                collect_decl_shapes(def.ports(), items, def.params(), &HashSet::default());
            let mut by_path = HashMap::default();
            let mut clash = HashSet::default();
            collect_block_shapes(items, "", &tp, &mut by_path, &mut clash);
            by_path.retain(|k, _| !clash.contains(k));
            let e = (
                std::rc::Rc::new(m),
                std::rc::Rc::new(tp),
                std::rc::Rc::new(by_path),
            );
            DECL_SHAPES_CACHE.with(|c| c.borrow_mut().insert(key, e.clone()));
            e
        }
    };
    let prev = DECL_SHAPES_TLS.with(|c| c.borrow_mut().replace(m));
    // A generate block of the enclosing scope does not reach into this one.
    let layers = DECL_SHAPE_LAYERS_TLS.with(|c| {
        std::mem::replace(
            &mut *c.borrow_mut(),
            DeclShapeLayers {
                type_params,
                blocks: Vec::new(),
                left: HashMap::default(),
                by_path,
            },
        )
    });
    DeclShapesGuard(prev, layers)
}

/// The items of a scope, with those of its `generate` regions in place: a
/// region is not a scope (§27.3).
fn scope_items(items: &[ModuleItem]) -> ScopeItems<'_> {
    ScopeItems {
        pending: vec![items.iter()],
    }
}

struct ScopeItems<'a> {
    pending: Vec<std::slice::Iter<'a, ModuleItem>>,
}

impl<'a> Iterator for ScopeItems<'a> {
    type Item = &'a ModuleItem;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.pending.last_mut()?.next() {
                Some(ModuleItem::GenerateRegion(gr)) => self.pending.push(gr.items.iter()),
                Some(item) => return Some(item),
                None => {
                    self.pending.pop();
                }
            }
        }
    }
}

/// The declared shapes of a scope's ports and declarations, and the type
/// parameters visible in it: `outer_type_params` (an enclosing scope's) and
/// its own.
fn collect_decl_shapes(
    ports: &PortList,
    items: &[ModuleItem],
    header_params: &[ParameterDeclaration],
    outer_type_params: &HashSet<String>,
) -> (HashMap<String, StoredDeclShape>, HashSet<String>) {
    // A variable typed by one of the module's own TYPE parameters takes the
    // instance's binding; it is sized from that width alone, never from a
    // same-named typedef elsewhere.
    let mut type_params: HashSet<String> = outer_type_params.clone();
    let body_params = scope_items(items).filter_map(|it| match it {
        ModuleItem::ParameterDeclaration(pd) | ModuleItem::LocalparamDeclaration(pd) => Some(pd),
        _ => None,
    });
    for pd in header_params.iter().chain(body_params) {
        if let ParameterKind::Type { assignments } = &pd.kind {
            type_params.extend(assignments.iter().map(|a| a.name.name.clone()));
        }
    }
    let by_type_param = |dt: &DataType| {
        matches!(dt, DataType::TypeReference { name, .. }
            if name.scopes.is_empty() && type_params.contains(name.name.name.as_str()))
    };
    let mut m: HashMap<String, StoredDeclShape> = HashMap::default();
    if let PortList::Ansi(ps) = ports {
        for p in ps {
            if let Some(dt) = &p.data_type
                && decl_shape_is_fixed(dt, &p.dimensions)
            {
                m.entry(p.name.name.clone()).or_insert_with(|| {
                    StoredDeclShape::new(dt, &p.dimensions, by_type_param(dt), false)
                });
            }
        }
    }
    // A non-ANSI port is declared twice (direction, then type); the first
    // spelling that carries the shape wins.
    let mut add_decl = |dt: &DataType, name: &Identifier, dims: &[UnpackedDimension]| {
        if decl_shape_is_fixed(dt, dims) {
            m.entry(name.name.clone())
                .or_insert_with(|| StoredDeclShape::new(dt, dims, by_type_param(dt), false));
        }
    };
    for item in scope_items(items) {
        match item {
            ModuleItem::DataDeclaration(dd) => {
                for d in &dd.declarators {
                    add_decl(&dd.data_type, &d.name, &d.dimensions);
                }
            }
            ModuleItem::NetDeclaration(nd) => {
                for d in &nd.declarators {
                    add_decl(&nd.data_type, &d.name, &d.dimensions);
                }
            }
            ModuleItem::PortDeclaration(pd) => {
                for d in &pd.declarators {
                    add_decl(&pd.data_type, &d.name, &d.dimensions);
                }
            }
            _ => {}
        }
    }
    // §20.7, §6.20.2: a value parameter with a declared type or range has
    // that shape (`$size(V)` of `localparam logic [7:0] V` is 8); an untyped
    // one takes its value's, which the parameter table answers.
    let body_params = scope_items(items).filter_map(|it| match it {
        ModuleItem::ParameterDeclaration(pd) | ModuleItem::LocalparamDeclaration(pd) => Some(pd),
        _ => None,
    });
    for pd in header_params.iter().chain(body_params) {
        let ParameterKind::Data {
            data_type,
            assignments,
        } = &pd.kind
        else {
            continue;
        };
        if matches!(data_type, DataType::Implicit { dimensions, .. } if dimensions.is_empty()) {
            continue;
        }
        for a in assignments {
            if decl_shape_is_fixed(data_type, &a.dimensions) {
                m.entry(a.name.name.clone()).or_insert_with(|| {
                    StoredDeclShape::new(data_type, &a.dimensions, by_type_param(data_type), true)
                });
            }
        }
    }
    (m, type_params)
}

/// `[l:r]` / `[n]` bounds of fixed unpacked dimensions, declared order. None
/// for a dynamic, queue or associative dimension (not a constant shape) or a
/// bound that does not fold.
fn fixed_unpacked_bounds<P: ParamLookup>(
    dims: &[UnpackedDimension],
    params: Option<&P>,
) -> Option<Vec<(i64, i64)>> {
    let mut out = Vec::with_capacity(dims.len());
    for d in dims {
        match d {
            UnpackedDimension::Range { left, right, .. } => out.push((
                const_eval_i64_with_params_env(left, params)?,
                const_eval_i64_with_params_env(right, params)?,
            )),
            UnpackedDimension::Expression { expr, .. } => {
                let n = const_eval_i64_with_params_env(expr, params)?;
                if n <= 0 {
                    return None;
                }
                out.push((0, n - 1));
            }
            // `[N]` with `N` a parameter, not a type.
            _ => {
                let pn = size_param_of_dim(d)?;
                if TYPEDEF_SHAPES_TLS.with(|c| c.borrow().0.contains_key(pn)) {
                    return None;
                }
                let n = params?.get(pn)?.to_i64()?;
                if n <= 0 {
                    return None;
                }
                out.push((0, n - 1));
            }
        }
    }
    Some(out)
}

/// §20.7 dimensions and §20.6.2 bit count of a declared fixed-size VARIABLE
/// named `name` in the scope being elaborated. Unpacked dimensions come first
/// (§7.4.5: the declarator's, then a typedef's), then the packed ones.
fn decl_shape_query<P: ParamLookup>(
    name: &str,
    params: Option<&P>,
) -> Option<(TypeQueryDims, Option<i64>)> {
    let shape = decl_shape_of(name)?;
    if !shape.param && params.is_some_and(|p| p.contains_key(name)) {
        return None;
    }
    let mut q = TypeQueryDims {
        dims: fixed_unpacked_bounds(&shape.unpacked, params)?,
        unpacked: shape.unpacked.len(),
        whole: None,
    };
    let (elem_w, inner) = typedefs_snapshot(|td| {
        let elem_w = resolve_type_width_env(&shape.data_type, params, td) as i64;
        let inner = TYPEDEF_SHAPES_TLS.with(|c| {
            let c = c.borrow();
            match &shape.data_type {
                // A type parameter is known by the instance's width alone.
                DataType::TypeReference {
                    name: tn,
                    dimensions,
                    ..
                } if dimensions.is_empty() && shape.by_type_param => {
                    type_query_dims_by_name(&tn.name.name, params, td, None, None)
                }
                // A typedef'd element type contributes its own unpacked dimensions
                // (`typedef int arr_t [3:0][1:5]; arr_t ta;`) and its packed shape.
                DataType::TypeReference {
                    name: tn,
                    dimensions,
                    ..
                } if dimensions.is_empty() => {
                    type_query_dims_by_name(&tn.name.name, params, td, Some(&c.0), Some(&c.1))
                }
                dt => Some(type_query_dims_of(dt, params, td, Some(&c.0))),
            }
        });
        (elem_w, inner)
    });
    let inner = inner?;
    // `elem_w` is one element of the typedef's own unpacked dimensions too,
    // so every unpacked dimension multiplies it.
    q.dims.extend(inner.dims);
    q.unpacked += inner.unpacked;
    q.whole = inner.whole;
    // `real` is not a bit-stream type (§6.24.3), so an array of it has no
    // constant `$bits`; the reference simulator folds it to 0.
    let mut bits =
        (elem_w > 0 && !matches!(shape.data_type, DataType::Real { .. })).then_some(elem_w);
    for &(l, r) in &q.dims[..q.unpacked] {
        bits = bits.and_then(|b| b.checked_mul((l - r).abs() + 1));
    }
    Some((q, bits))
}

/// §7.4.5/§20.6.2: `$bits` of `v[i]…` (index selects only) on a declared
/// variable `v` of the scope: its width over the dimensions, unpacked then
/// packed, that the selects leave. None for any other operand, or when the
/// selects reach past the declared dimensions.
pub(super) fn decl_select_bits<P: ParamLookup>(e: &Expression, params: Option<&P>) -> Option<i64> {
    // A final part-select (`pk[3:2]`, `pk[i +: 2]`) keeps that many elements
    // of the next dimension.
    let (mut cur, slice) = match &e.kind {
        ExprKind::RangeSelect {
            expr,
            kind,
            left,
            right,
        } => {
            let n = match kind {
                crate::ast::expr::RangeKind::Constant => {
                    let l = const_eval_i64_with_params_env(left, params)?;
                    let r = const_eval_i64_with_params_env(right, params)?;
                    (l - r).abs() + 1
                }
                _ => const_eval_i64_with_params_env(right, params)?,
            };
            (expr.as_ref(), Some(n))
        }
        _ => (e, None),
    };
    let mut k = 0usize;
    while let ExprKind::Index { expr, .. } = &cur.kind {
        k += 1;
        cur = expr;
    }
    let ExprKind::Ident(h) = &cur.kind else {
        return None;
    };
    if (k == 0 && slice.is_none())
        || h.path.len() != 1
        || h.root.is_some()
        || !h.path[0].selects.is_empty()
    {
        return None;
    }
    if !is_decl_shape_operand(cur) {
        return None;
    }
    let (q, bits) = decl_shape_query(&h.path[0].name.name, params)?;
    let bits = bits?;
    let sliced = k + usize::from(slice.is_some());
    if sliced > q.dims.len() {
        return None;
    }
    let mut w = bits;
    for &(l, r) in &q.dims[..sliced] {
        w /= (l - r).abs() + 1;
    }
    if let Some(n) = slice {
        w = w.checked_mul(n)?;
    }
    (w > 0).then_some(w)
}

/// §20.6.2 `$bits` and the §20.7 array queries over a declared variable of the
/// scope being elaborated: `$bits(fx)`, `$size(fx2, 2)`, `$increment(pu)`.
/// None when the operand is not such a variable (a parameter or a type keeps
/// its own resolution) or the queried dimension does not exist.
pub(super) fn decl_var_query<P: ParamLookup>(
    fname: &str,
    args: &[Expression],
    params: Option<&P>,
) -> Option<i64> {
    let arg = args.first()?;
    if !is_decl_shape_operand(arg) {
        return None;
    }
    let (q, bits) = decl_shape_query(&decl_shape_operand_name(arg)?, params)?;
    if fname == "$bits" {
        return bits;
    }
    let dim = match args.get(1) {
        Some(d) => const_eval_i64_with_params_env(d, params)?,
        None => 1,
    };
    if dim < 1 {
        return None;
    }
    type_query_bound(fname, &q, dim as usize)
}

/// §20.7 array query over an explicit type operand (`$size(logic [7:0])`,
/// `$left(bit [3:0][7:0], 2)`). None when the dimension does not exist.
pub(super) fn type_literal_query<P: ParamLookup>(
    fname: &str,
    dt: &DataType,
    args: &[Expression],
    params: Option<&P>,
) -> Option<i64> {
    let q = typedefs_snapshot(|td| {
        TYPEDEF_SHAPES_TLS.with(|c| type_query_dims_of(dt, params, td, Some(&c.borrow().0)))
    });
    let dim = match args.get(1) {
        Some(d) => const_eval_i64_with_params_env(d, params)?,
        None => 1,
    };
    if dim < 1 {
        return None;
    }
    type_query_bound(fname, &q, dim as usize)
}

/// §20.6.2 `$bits` of a typedef carrying UNPACKED dimensions
/// (`typedef int arr_t [3:0][1:5]`): the width table records one element, so
/// multiply in every unpacked dimension. None for any other name.
pub(super) fn typedef_unpacked_bits<P: ParamLookup>(name: &str, params: Option<&P>) -> Option<i64> {
    let dims = TYPEDEF_SHAPES_TLS.with(|c| c.borrow().1.get(name).cloned())?;
    let bounds = fixed_unpacked_bounds(&dims, params)?;
    let elem =
        TYPEDEFS_TLS.with(|t| t.borrow().as_ref().and_then(|m| m.get(name).copied()))? as i64;
    let mut bits = elem;
    for (l, r) in bounds {
        bits = bits.checked_mul((l - r).abs() + 1)?;
    }
    Some(bits)
}

/// Does the declared variable `arg` carry UNPACKED dimensions, on its
/// declarator or through its typedef? Only those are mis-sized by the signal
/// table, which records one element.
pub(super) fn decl_has_unpacked_dims(arg: &Expression) -> bool {
    let ExprKind::Ident(h) = &arg.kind else {
        return false;
    };
    let Some(shape) = h.path.last().and_then(|s| decl_shape_of(&s.name.name)) else {
        return false;
    };
    !shape.unpacked.is_empty()
        || (!shape.by_type_param
            && matches!(&shape.data_type, DataType::TypeReference { name, .. }
                if TYPEDEF_SHAPES_TLS.with(|c| c.borrow().1.contains_key(&name.name.name))))
}

/// Is `arg` a declared variable of the scope being elaborated whose shape the
/// array queries can answer at elaboration time?
pub(super) fn is_decl_shape_operand(arg: &Expression) -> bool {
    match &arg.kind {
        ExprKind::Ident(_) | ExprKind::MemberAccess { .. } => {
            let Some(shape) = decl_shape_operand_name(arg).and_then(|n| decl_shape_of(&n)) else {
                return false;
            };
            // `[K]` naming a TYPE is a real associative dimension.
            if shape
                .unpacked
                .iter()
                .filter_map(size_param_of_dim)
                .any(|n| {
                    TYPEDEF_SHAPES_TLS.with(|c| c.borrow().0.contains_key(n))
                        || TYPEDEFS_TLS
                            .with(|t| t.borrow().as_ref().is_some_and(|m| m.contains_key(n)))
                })
            {
                return false;
            }
            // A named element type must be a known typedef whose own
            // unpacked dimensions are fixed too. An instance's local typedefs
            // are known by width only while its parameters resolve.
            match &shape.data_type {
                DataType::TypeReference { name, .. } if shape.by_type_param => {
                    TYPEDEFS_TLS.with(|t| {
                        t.borrow()
                            .as_ref()
                            .is_some_and(|m| m.contains_key(&name.name.name))
                    })
                }
                DataType::TypeReference { name, .. } => TYPEDEF_SHAPES_TLS.with(|c| {
                    let c = c.borrow();
                    (c.0.contains_key(&name.name.name)
                        || TYPEDEFS_TLS.with(|t| {
                            t.borrow()
                                .as_ref()
                                .is_some_and(|m| m.contains_key(&name.name.name))
                        }))
                        && c.1.get(&name.name.name).is_none_or(|d| {
                            d.iter().all(|d| {
                                matches!(
                                    d,
                                    UnpackedDimension::Range { .. }
                                        | UnpackedDimension::Expression { .. }
                                )
                            })
                        })
                }),
                _ => true,
            }
        }
        _ => false,
    }
}

/// Extract array range from unpacked dimensions. Returns Some((lo, hi)) for
/// `[lo:hi]` or `[size]` (which means [0:size-1]).
/// Every `[i]`/`[i][j]` suffix of a fixed shape, in row-major order.
pub(super) fn index_tuples(shape: &[(i64, i64)]) -> Vec<String> {
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

/// DECLARED (left, right) for each unpacked dimension, outermost first —
/// raw order preserved (no lo/hi normalization). `[N]` size form is (0, N-1).
/// Returns None if any dimension is dynamic/associative/unresolvable.
pub fn declared_unpacked_dims(
    dims: &[crate::ast::types::UnpackedDimension],
    params: &HashMap<String, Value>,
) -> Option<Vec<(i64, i64)>> {
    declared_unpacked_dims_env(dims, params)
}

pub(super) fn declared_unpacked_dims_env(
    dims: &[crate::ast::types::UnpackedDimension],
    params: &dyn ParamLookup,
) -> Option<Vec<(i64, i64)>> {
    if dims.is_empty() {
        return None;
    }
    let mut out = Vec::with_capacity(dims.len());
    for d in dims {
        // §7.4.2: `[N]` names a size when N resolves to a parameter,
        // even if the parser initially recorded an associative index type.
        let resolved = scoped_const_dim(d, params);
        let d = resolved.as_ref().unwrap_or(d);
        match d {
            crate::ast::types::UnpackedDimension::Range { left, right, .. } => {
                let p_ref = &params;
                let l = const_eval_i64_with_params_env(left, Some(&p_ref))?;
                let r = const_eval_i64_with_params_env(right, Some(&p_ref))?;
                out.push((l, r));
            }
            crate::ast::types::UnpackedDimension::Expression { expr, .. } => {
                let p_ref = &params;
                let size = const_eval_i64_with_params_env(expr, Some(&p_ref))?;
                if size <= 0 {
                    return None;
                }
                out.push((0, size - 1));
            }
            UnpackedDimension::Associative {
                data_type: Some(dt),
                ..
            } => {
                let DataType::TypeReference {
                    name,
                    dimensions,
                    type_args,
                    ..
                } = dt.as_ref()
                else {
                    return None;
                };
                if name.has_scope() || !dimensions.is_empty() || !type_args.is_empty() {
                    return None;
                }
                let size = params.get(&name.name.name)?.to_i64()?;
                if size <= 0 {
                    return None;
                }
                out.push((0, size - 1));
            }
            _ => return None,
        }
    }
    Some(out)
}

pub fn extract_array_range(
    dims: &[crate::ast::types::UnpackedDimension],
    params: &HashMap<String, Value>,
) -> Option<(i64, i64)> {
    if dims.is_empty() {
        return None;
    }
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
        crate::ast::types::UnpackedDimension::Unsized(_)
        | crate::ast::types::UnpackedDimension::Queue { .. } => {
            // For dynamic arrays and queues, allocate a fixed-size buffer for simulation
            Some((0, 63))
        }
        crate::ast::types::UnpackedDimension::Associative {
            data_type: Some(dt),
            ..
        } => {
            // `[NAME]` is genuinely ambiguous in the grammar (§A.2.5): it is an
            // ASSOCIATIVE index type when NAME is a type, and a SIZED dimension
            // when NAME is a parameter. The parser cannot tell — it has no type
            // table — so it commits to associative and a `wire w [COLS];` came
            // out as a 64-entry dynamic array. Every element past 63 (and the
            // shape of any further dimension) was then wrong, so instances
            // bound to `w[i][j]` drove nothing and the net read z. Reinterpret
            // it here, where the parameter table exists.
            if let Some(n) = scoped_const_dim(&dims[0], params).and_then(|f| match f {
                crate::ast::types::UnpackedDimension::Expression { expr, .. } => {
                    const_eval_i64_with_params(&expr, Some(params))
                }
                _ => None,
            }) {
                return (n > 0).then(|| (0, n - 1));
            }
            if let DataType::TypeReference {
                name, dimensions, ..
            } = &**dt
            {
                if dimensions.is_empty() {
                    if let Some(v) = params.get(&name.name.name) {
                        let size = v.to_u64().unwrap_or(0) as i64;
                        if size > 0 {
                            return Some((0, size - 1));
                        }
                    }
                }
            }
            // A real associative array is purely dynamic.
            None
        }
        crate::ast::types::UnpackedDimension::Associative { .. } => None,
    }
}

pub(super) fn width_with_unpacked_dims(
    dims: &[crate::ast::types::UnpackedDimension],
    base_width: u32,
) -> u32 {
    if dims.is_empty() {
        return base_width;
    }
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
            crate::ast::types::UnpackedDimension::Unsized(_)
            | crate::ast::types::UnpackedDimension::Queue { .. }
            | crate::ast::types::UnpackedDimension::Associative { .. } => {
                total_elements *= 64;
            }
        }
    }
    base_width * total_elements
}

/// Evaluate a constant expression (for enum values, parameter defaults, etc.)
pub(super) fn eval_const_expr(expr: &Expression, params: &HashMap<String, Value>) -> u64 {
    let v = eval_const_expr_val(expr, params);
    if v.is_real {
        // A real result (e.g. a timeunit-scaled delay `5 * 1000.0`) must be
        // converted NUMERICALLY — to_u64 on a real Value returns the raw
        // IEEE-754 bit pattern (5000.0 -> ~4.6e18, a delay parked forever).
        let f = v.to_f64();
        if f.is_finite() && f > 0.0 {
            f.round() as u64
        } else {
            0
        }
    } else {
        v.to_u64().unwrap_or(0)
    }
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
/// `(low, high)` label bounds of a single ascending packed dimension
/// (`[3:10]` gives `(3, 10)`); `None` for descending or multi-dimensional.
pub(super) fn packed_ascending_bounds(
    dt: &DataType,
    params: &HashMap<String, Value>,
) -> Option<(i64, i64)> {
    let dims = match dt {
        DataType::IntegerVector { dimensions, .. } => dimensions,
        DataType::Implicit { dimensions, .. } => dimensions,
        _ => return None,
    };
    if dims.len() != 1 {
        return None;
    }
    if let Some(PackedDimension::Range { left, right, .. }) = dims.first() {
        let l = const_eval_i64_with_params(left, Some(params))?;
        let r = const_eval_i64_with_params(right, Some(params))?;
        if l < r {
            return Some((l, r));
        }
    }
    None
}

/// Packed dimension bounds accumulated ACROSS a typedef chain, outermost
/// first: `typedef logic [7:0] T1; typedef T1 [3:0] T2;` gives
/// `[(3,0),(7,0)]` for `T2`.
///
/// `resolve_typedef_chain` cannot serve here — it walks to the END of the
/// chain and DISCARDS the dimensions carried on the intermediate references,
/// collapsing `T2` to `logic [7:0]`. With no dims recorded, `val[i]` on a
/// `T2` degraded to a one-bit select (ivtest task_nonansi_parray1/2).
pub fn packed_full_dims_chained(
    dt: &DataType,
    params: &HashMap<String, Value>,
    typedef_types: &HashMap<String, DataType>,
) -> Option<Vec<(i64, i64)>> {
    let mut out: Vec<(i64, i64)> = Vec::new();
    let mut cur: DataType = dt.clone();
    for _ in 0..32 {
        match cur {
            DataType::TypeReference {
                ref name,
                ref dimensions,
                ..
            } => {
                for d in dimensions {
                    let PackedDimension::Range { left, right, .. } = d else {
                        return None;
                    };
                    let l = const_eval_i64_with_params(left, Some(params))?;
                    let r = const_eval_i64_with_params(right, Some(params))?;
                    out.push((l, r));
                }
                let next = typedef_types.get(&name.name.name)?.clone();
                cur = next;
            }
            _ => {
                // The base type's own packed dims complete the shape. Take them
                // directly (not via `packed_full_dims_of`, which deliberately
                // reports None for a lone dimension).
                //
                // The chain MUST bottom out in a vector: these "full dims" are
                // read as bit ranges, with the innermost one supplying the bit
                // width. A chain ending in a STRUCT (`parcel_t [0:0][1:0]`)
                // has its element width in the struct, not in a dimension —
                // reporting [(0,0),(1,0)] there made `$bits(nested[0])` read 2
                // instead of 134. Those types are already handled by the
                // struct-array path; leave them to it.
                let base_dims = match &cur {
                    DataType::IntegerVector { dimensions, .. }
                    | DataType::Implicit { dimensions, .. } => dimensions.clone(),
                    _ => return None,
                };
                for d in &base_dims {
                    let PackedDimension::Range { left, right, .. } = d else {
                        return None;
                    };
                    let l = const_eval_i64_with_params(left, Some(params))?;
                    let r = const_eval_i64_with_params(right, Some(params))?;
                    out.push((l, r));
                }
                break;
            }
        }
    }
    // A single dimension is an ordinary vector, not a packed ARRAY — same
    // convention as `packed_full_dims_of`.
    if out.len() < 2 { None } else { Some(out) }
}
