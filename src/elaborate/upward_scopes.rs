use super::*;

thread_local! {
    /// §23.8: the chain of instances being inlined, outermost first —
    /// `(instance prefix, definition name)`. An upward hierarchical name
    /// whose first segment is the DEFINITION name of an enclosing instance
    /// (`dut.gclk_a` written in a module bound into `dut`) resolves to that
    /// instance (`resolve_upward_module_name`).
    pub(super) static INLINE_CHAIN_TLS: std::cell::RefCell<Vec<(String, String)>>
        = const { std::cell::RefCell::new(Vec::new()) };
    /// Class constant declarations by class name (`register_class_consts`).
    pub(super) static CLASS_CONST_DECLS_TLS: std::cell::RefCell<HashMap<String, Rc<ClassConstDecl>>>
        = std::cell::RefCell::new(HashMap::default());
    /// §23.8: the design's scope tree for `upward_scope_rewrite`, shared
    /// with `ElaboratedModule::upward_scopes` and every `RewriteCtx`
    /// (installed by `inline_module_items` and `set_type_bind_tls`).
    pub(super) static UPWARD_SCOPES_TLS: std::cell::RefCell<Option<Rc<std::cell::RefCell<UpwardScopes>>>>
        = const { std::cell::RefCell::new(None) };
    /// §6.21 / §13.3: the names the statement lists and subroutine headers
    /// being rewritten declare themselves (block locals, formals), innermost
    /// last. Such a name is never a scope for `upward_scope_rewrite`: a
    /// block-local handle named like an enclosing instance read null (the
    /// `instance_block_locals_shadow_module_names` regression).
    static STMT_LOCALS_TLS: std::cell::RefCell<Vec<HashSet<String>>>
        = const { std::cell::RefCell::new(Vec::new()) };
    /// The generate renames in progress, innermost last.
    pub(super) static GEN_RENAME_TLS: std::cell::RefCell<Vec<GenRename>>
        = const { std::cell::RefCell::new(Vec::new()) };
}

/// Pops the `STMT_LOCALS_TLS` frame `push_stmt_locals` pushed.
pub(super) struct StmtLocalsFrame;

impl Drop for StmtLocalsFrame {
    fn drop(&mut self) {
        STMT_LOCALS_TLS.with(|s| {
            s.borrow_mut().pop();
        });
    }
}

/// Registers `names` as statement-local for the lifetime of the returned
/// guard; nothing is pushed for an empty set.
pub(super) fn push_stmt_locals(names: HashSet<String>) -> Option<StmtLocalsFrame> {
    if names.is_empty() {
        return None;
    }
    STMT_LOCALS_TLS.with(|s| s.borrow_mut().push(names));
    Some(StmtLocalsFrame)
}

pub(super) fn stmt_local_declared(name: &str) -> bool {
    STMT_LOCALS_TLS.with(|s| s.borrow().iter().any(|frame| frame.contains(name)))
}

/// §26.3: a package of the design being inlined.
pub(super) fn design_package(name: &str) -> bool {
    UPWARD_SCOPES_TLS.with(|c| {
        c.borrow()
            .as_ref()
            .is_some_and(|s| s.borrow().packages.contains(name))
    })
}

impl UpwardScopes {
    /// The one string of the scope path `parent`, an instance recorded
    /// earlier (or the top): the key a table already holds it under.
    fn shared_parent(&mut self, parent: &str) -> Rc<str> {
        if let Some(held) = self.last_parent.as_ref().filter(|p| &***p == parent) {
            return Rc::clone(held);
        }
        let held = self.defs.get_key_value(parent).map(|(k, _)| k);
        let held = held.or_else(|| self.parents.get_key_value(parent).map(|(k, _)| k));
        let held = held.or_else(|| self.children.get_key_value(parent).map(|(k, _)| k));
        let held = held.cloned().unwrap_or_else(|| Rc::from(parent));
        self.last_parent = Some(Rc::clone(&held));
        held
    }

    /// The one string of definition name `def`.
    fn shared_def(&mut self, def: &str) -> Rc<str> {
        if let Some(held) = self.def_names.get(def) {
            return Rc::clone(held);
        }
        let name: Rc<str> = Rc::from(def);
        self.def_names.insert(Rc::clone(&name));
        name
    }

    /// The instance name of the child at `path` in the scope `parent`.
    pub(super) fn child_leaf<'a>(parent: &str, path: &'a str) -> &'a str {
        match parent.is_empty() {
            true => path,
            false => path
                .strip_prefix(parent)
                .map_or(path, |p| p.trim_start_matches('.')),
        }
    }

    /// The child instance of scope `parent` named `name`, by that name.
    pub(super) fn child_named(&self, parent: &str, name: &str) -> Option<&str> {
        self.children
            .get(parent)?
            .iter()
            .map(|path| Self::child_leaf(parent, path))
            .find(|leaf| *leaf == name)
    }

    /// The top module is an instance of `def` at the empty path.
    pub(super) fn set_top(&mut self, def: &str) {
        let (path, def) = (self.shared_parent(""), self.shared_def(def));
        self.defs.insert(path, def);
    }

    pub(super) fn add_instance(&mut self, parent: &str, path: &str, def: &str) {
        let parent = self.shared_parent(parent);
        // `add_parent` recorded the instantiation first, under this path.
        let held = self.parents.get_key_value(path).map(|(k, _)| Rc::clone(k));
        let path = held.unwrap_or_else(|| Rc::from(path));
        let def = self.shared_def(def);
        self.children
            .entry(parent)
            .or_default()
            .push(Rc::clone(&path));
        self.defs.insert(path, def);
    }

    /// Record where instance `path` is declared in its parent `parent`, an
    /// instance of `def`. An instantiation the binder did not visit (a bind
    /// target's, §23.11) sits at the definition scope.
    pub(super) fn add_parent(
        &mut self,
        parent: &str,
        path: &str,
        def: &str,
        inst: &ModuleInstantiation,
        hi: &HierarchicalInstance,
    ) {
        let Some(tree) = crate::scope_tree::tree_of(def) else {
            return;
        };
        let scope = inst.scope.unwrap_or(tree.root);
        if scope.0 as usize >= tree.scopes.len() {
            return;
        }
        let parent = self.shared_parent(parent);
        let def = self.shared_def(&inst.module_name.name);
        // The first record of this instance: its path string starts here.
        self.parents.insert(
            Rc::from(path),
            InstanceParent {
                def,
                path: parent,
                tree,
                scope,
                indices: hi.gen_indices.clone(),
            },
        );
    }

    /// §23.8.1 steps b) and c): the subroutine a bare `name` called in
    /// instance `inst` names, from the scope of the instantiation up through
    /// each enclosing instance. The search is for a scope named `name`, so a
    /// variable of that name does not end it. `None` when a DPI import is
    /// found first (keyed globally), or nothing is. §26.3: imports of an
    /// enclosing scope are not visible to it.
    pub(super) fn subroutine_key(&self, inst: &str, name: &str) -> Option<String> {
        let (up, s, dpi) = self.find_subroutine(inst, name)?;
        if dpi {
            return None;
        }
        let key = up.tree.key(s, name, &up.indices);
        Some(match up.path.is_empty() {
            true => key,
            false => format!("{}.{key}", up.path),
        })
    }

    /// The `subroutine_key` search: the parent and scope declaring `name`,
    /// and whether it is a DPI import.
    pub(super) fn find_subroutine(
        &self,
        inst: &str,
        name: &str,
    ) -> Option<(&InstanceParent, crate::ast::binding::ScopeId, bool)> {
        let mut at = inst;
        while let Some(up) = self.parents.get(at) {
            let mut scope = Some(up.scope);
            while let Some(s) = scope {
                let sc = &up.tree.scopes[s.0 as usize];
                if let Some(d) = sc.by_name.get(name) {
                    match up.tree.decls[d.0 as usize].kind {
                        DeclKind::Function | DeclKind::Task => return Some((up, s, false)),
                        DeclKind::DpiImport => return Some((up, s, true)),
                        _ => {}
                    }
                }
                scope = sc.parent;
            }
            at = &*up.path;
        }
        None
    }

    /// §23.8.1: a bare call of `name` in a body of definition `def` finds a
    /// subroutine upward from every instance of `def`. The top finds none.
    pub(super) fn every_instance_finds(&self, def: &str, name: &str) -> bool {
        let mut insts = self.defs.iter().filter(|(_, d)| &***d == def).peekable();
        insts.peek().is_some() && insts.all(|(p, _)| self.find_subroutine(p, name).is_some())
    }

    pub(super) fn declare(&mut self, def: &Definition) {
        if self.declared.contains_key(def.name()) {
            return;
        }
        let mut names = HashSet::default();
        visit_renamed_decls(def.items(), &mut |n, _, kind| {
            if kind == DeclKind::Instance {
                names.insert(n.to_string());
            }
        });
        collect_scope_labels_in_items(def.items(), &mut names);
        self.declared.insert(def.name().to_string(), names);
    }
}

/// Generate-block labels, named-block labels and subroutine names declared
/// in `items`, nested generate blocks included (the non-instance scopes of
/// §23.8 step a).
fn collect_scope_labels_in_items(items: &[ModuleItem], out: &mut HashSet<String>) {
    for item in items {
        match item {
            ModuleItem::GenerateRegion(gr) => collect_scope_labels_in_items(&gr.items, out),
            ModuleItem::GenerateIf(gi) => {
                out.extend(gi.branch_labels.iter().flatten().cloned());
                for (_, branch) in &gi.branches {
                    collect_scope_labels_in_items(branch, out);
                }
            }
            ModuleItem::GenerateCase(gc) => {
                for arm in &gc.arms {
                    out.extend(arm.label.iter().cloned());
                    collect_scope_labels_in_items(&arm.items, out);
                }
            }
            ModuleItem::GenerateFor(gf) => {
                out.extend(gf.name.iter().cloned());
                collect_scope_labels_in_items(&gf.items, out);
            }
            ModuleItem::AlwaysConstruct(a) => collect_block_labels(&a.stmt, out),
            ModuleItem::InitialConstruct(i) => collect_block_labels(&i.stmt, out),
            ModuleItem::FinalConstruct(f) => collect_block_labels(&f.stmt, out),
            ModuleItem::FunctionDeclaration(f) => {
                out.insert(f.name.name.name.clone());
            }
            ModuleItem::TaskDeclaration(t) => {
                out.insert(t.name.name.name.clone());
            }
            _ => {}
        }
    }
}

pub(super) fn install_upward_scopes(scopes: &Rc<std::cell::RefCell<UpwardScopes>>) {
    UPWARD_SCOPES_TLS.with(|c| {
        let mut slot = c.borrow_mut();
        if !slot.as_ref().is_some_and(|s| Rc::ptr_eq(s, scopes)) {
            *slot = Some(Rc::clone(scopes));
        }
    });
}
