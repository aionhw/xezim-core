//! §23.10.2: a parameter override list on an instance must fit the definition
//! it instantiates. An ordered value needs a parameter to bind to, and a name
//! appears once and names an overridable parameter.
//!
//! This runs as each instance is built, not in the per-file strict pass, so it
//! sees children in other files, generate blocks and bound instances, and
//! leaves alone what is not built. `--no-strict` turns it off.

use crate::ast::Span;
use crate::ast::decl::{
    ModuleInstantiation, ModuleItem, ParamConnection, ParameterDeclaration, ParameterKind,
};
use crate::elaborate::{Definition, ElaboratedModule, span_error_of};
use std::cell::RefCell;
use std::collections::HashSet;
use sv_parser::strict_check::overridable_param_slots;

thread_local! {
    /// Module names defined more than once. One definition survives (the
    /// last, §3.3, and nested modules share the table), so a list written for
    /// another of them cannot be judged against it. Elaboration state, never
    /// part of a compiled artifact.
    static REDEFINED_MODULES: RefCell<HashSet<String>> = RefCell::new(HashSet::new());
}

pub(crate) fn reset_redefined_modules() {
    REDEFINED_MODULES.with(|r| r.borrow_mut().clear());
}

pub(crate) fn note_redefined_module(name: &str) {
    REDEFINED_MODULES.with(|r| {
        r.borrow_mut().insert(name.to_string());
    });
}

/// The kinds of definition an instance's list binds to. A class, package or
/// typedef can share the name table, and has no slots for a list.
fn instantiable_kind(def: Definition) -> Option<&'static str> {
    match def {
        Definition::Module(_) => Some("module"),
        Definition::Interface(_) => Some("interface"),
        Definition::Program(_) => Some("program"),
        _ => None,
    }
}

/// §6.20.1: a body `parameter` that a parameter port list made local.
fn is_local_body_parameter(def: Definition, name: &str) -> bool {
    !def.params().is_empty()
        && def.items().iter().any(|it| {
            matches!(
                it,
                ModuleItem::ParameterDeclaration(_) | ModuleItem::GenerateRegion(_)
            ) && overridable_param_slots(&[], std::slice::from_ref(it)).contains(&name)
        })
}

/// What is wrong with `inst`'s list against `def`, and where. The rules run in
/// a fixed order, so a list with several faults always reports the same one.
fn list_fault(
    inst: &ModuleInstantiation,
    def: Definition,
    bound_into: Option<&str>,
) -> Option<(String, Span)> {
    let list = inst.params.as_ref()?;
    let kind = instantiable_kind(def)?;
    let child = &inst.module_name.name;
    if REDEFINED_MODULES.with(|r| r.borrow().contains(child)) {
        return None;
    }
    let instance = inst.instances.first().map_or("", |h| h.name.name.as_str());
    let subject = match bound_into {
        Some(target) => format!("instance '{instance}' of {kind} '{child}' bound into '{target}'"),
        None => format!("instance '{instance}' of {kind} '{child}'"),
    };
    let slots = overridable_param_slots(def.params(), def.items());
    let fault = |what: String, span: Span| {
        Some((format!("{subject} {what}; --no-strict accepts it"), span))
    };

    let ordered = list
        .iter()
        .filter(|c| matches!(c, ParamConnection::Ordered(_)))
        .count();
    if ordered > slots.len() {
        return fault(
            format!(
                "has {ordered} ordered parameter values, but '{child}' accepts {} \
                 (IEEE 1800-2017 §23.10.2)",
                slots.len()
            ),
            inst.module_name.span,
        );
    }
    let mut seen: HashSet<&str> = HashSet::new();
    for c in list {
        if let ParamConnection::Named { name, .. } = c
            && !seen.insert(name.name.as_str())
        {
            return fault(
                format!(
                    "sets parameter '{}' more than once (IEEE 1800-2017 §23.10.2)",
                    name.name
                ),
                name.span,
            );
        }
    }
    for c in list {
        if let ParamConnection::Named { name, .. } = c
            && !slots.contains(&name.name.as_str())
        {
            let local = if is_local_body_parameter(def, &name.name) {
                ": a parameter declared in the body of a module with a parameter port list \
                 is local (§6.20.1)"
            } else {
                ""
            };
            return fault(
                format!(
                    "names '{}', which is not an overridable parameter \
                     (IEEE 1800-2017 §23.10.2){local}",
                    name.name
                ),
                name.span,
            );
        }
    }
    None
}

/// Check the list of an instance written in `owner`, reporting its location.
pub(crate) fn check_instance(
    elab: &ElaboratedModule,
    inst: &ModuleInstantiation,
    def: Definition,
    owner: &str,
) -> Result<(), String> {
    if !sv_parser::strict_checks() {
        return Ok(());
    }
    match list_fault(inst, def, None) {
        Some((message, span)) => Err(span_error_of(elab, span, owner, &message)),
        None => Ok(()),
    }
}

/// Check the list of an instance bound into `target`. A bind directive keeps a
/// span but not its file, and it is often not in the target's file, so a
/// location could name the wrong line; the message names the bind instead.
pub(crate) fn check_bound_instance(
    inst: &ModuleInstantiation,
    def: Definition,
    target: &str,
) -> Result<(), String> {
    if !sv_parser::strict_checks() {
        return Ok(());
    }
    match list_fault(inst, def, Some(target)) {
        Some((message, _)) => Err(message),
        None => Ok(()),
    }
}

/// §6.20.3: whether `name` is a type parameter of `def`.
fn is_type_parameter(def: Definition, name: &str) -> bool {
    fn declares(pd: &ParameterDeclaration, name: &str) -> bool {
        matches!(&pd.kind, ParameterKind::Type { assignments }
            if assignments.iter().any(|a| a.name.name == name))
    }
    fn in_items(items: &[ModuleItem], name: &str) -> bool {
        items.iter().any(|it| match it {
            ModuleItem::ParameterDeclaration(pd) => declares(pd, name),
            ModuleItem::GenerateRegion(gr) => in_items(&gr.items, name),
            _ => false,
        })
    }
    def.params().iter().any(|pd| declares(pd, name)) || in_items(def.items(), name)
}

/// §23.10.1: a `defparam` written in `owner` sets `param` of an instance of
/// `def`. It can set only an overridable data parameter: not a localparam, not
/// a body `parameter` that a parameter port list made local (§6.20.1), and not
/// a type parameter. The per-file strict pass judges this only when the child
/// is defined in the same file; this runs as each instance is built.
pub(crate) fn check_defparam(
    elab: &ElaboratedModule,
    def: Definition,
    param: &str,
    span: Span,
    owner: &str,
) -> Result<(), String> {
    if !sv_parser::strict_checks() {
        return Ok(());
    }
    let Some(kind) = instantiable_kind(def) else {
        return Ok(());
    };
    let child = def.name();
    if REDEFINED_MODULES.with(|r| r.borrow().contains(child)) {
        return Ok(());
    }
    let message = if !overridable_param_slots(def.params(), def.items()).contains(&param) {
        let local = if is_local_body_parameter(def, param) {
            ": a parameter declared in the body of a module with a parameter port list \
             is local (§6.20.1)"
        } else {
            ""
        };
        format!(
            "defparam cannot override '{param}' of {kind} '{child}' — not an overridable \
             parameter (IEEE 1800-2017 §23.10.1){local}; --no-strict accepts it"
        )
    } else if is_type_parameter(def, param) {
        format!(
            "defparam cannot override type parameter '{param}' of {kind} '{child}' \
             (IEEE 1800-2017 §23.10.1); --no-strict accepts it"
        )
    } else {
        return Ok(());
    };
    Err(span_error_of(elab, span, owner, &message))
}
