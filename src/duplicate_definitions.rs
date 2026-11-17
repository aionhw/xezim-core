//! §3.13, §8.3, §26.2: duplicate class and package definitions in one name space.
//!
//! A scope's name space holds one declaration per name (§3.13), so a second
//! `class C` in the compilation unit, a package, a module or a class, or a
//! second `package P` anywhere in the design (§26.2), is illegal. Nothing
//! checked: the name-keyed tables kept one of the two and silently dropped
//! the rest.
//!
//! The check runs on each file's parsed descriptions, the one point where a
//! declaration's file is still known. All source files share one compilation
//! unit and one package name space, so those tables live across files.

use crate::ast::decl::{ClassDeclaration, ClassItem, ModuleItem, PackageItem};
use crate::ast::{Description, Identifier};
use crate::diagnostics::{self, Diagnostic};
use sv_parser::source_map::LineMap;

/// One file's text, for locating a span.
struct FileText<'a> {
    text: &'a str,
    map: Option<&'a LineMap>,
    file: &'a str,
}

impl FileText<'_> {
    fn locate(&self, name: &Identifier) -> String {
        diagnostics::locate(self.text, self.map, self.file, name.span).short()
    }
}

/// The definitions declared so far in one name space/scope, each with where it is.
type Seen = crate::hasher::HashMap<String, String>;

#[derive(Default)]
pub(crate) struct DuplicateDefinitions {
    /// Compilation-unit classes of the files checked so far.
    unit: Seen,
    /// Packages declared across the files checked so far (§3.13, §26.2).
    packages: Seen,
}

impl DuplicateDefinitions {
    /// The rendered errors for `descriptions`, the parse of one source file.
    pub(crate) fn check_file(
        &mut self,
        descriptions: &[Description],
        text: &str,
        map: Option<&LineMap>,
        file: &str,
    ) -> Vec<String> {
        let ft = FileText { text, map, file };
        let mut diags = Vec::new();
        for d in descriptions {
            match d {
                Description::Class(c) | Description::PackageItem(PackageItem::Class(c)) => {
                    note(
                        &mut self.unit,
                        "class",
                        &c.name,
                        Some("the compilation unit"),
                        "§3.13, §8.3",
                        &ft,
                        &mut diags,
                    );
                    nested(c, &ft, &mut diags);
                }
                Description::Package(p) => {
                    note(
                        &mut self.packages,
                        "package",
                        &p.name,
                        None,
                        "§3.13, §26.2",
                        &ft,
                        &mut diags,
                    );
                    let scope = format!("package '{}'", p.name.name);
                    let mut seen = Seen::default();
                    for it in &p.items {
                        if let PackageItem::Class(c) = it {
                            note(
                                &mut seen,
                                "class",
                                &c.name,
                                Some(&scope),
                                "§3.13, §8.3",
                                &ft,
                                &mut diags,
                            );
                            nested(c, &ft, &mut diags);
                        }
                    }
                }
                Description::Module(m) => items(
                    &m.items,
                    &format!("module '{}'", m.name.name),
                    &ft,
                    &mut diags,
                ),
                Description::Interface(m) => items(
                    &m.items,
                    &format!("interface '{}'", m.name.name),
                    &ft,
                    &mut diags,
                ),
                Description::Program(m) => items(
                    &m.items,
                    &format!("program '{}'", m.name.name),
                    &ft,
                    &mut diags,
                ),
                _ => {}
            }
        }
        diags
            .iter()
            .map(|d| diagnostics::render_diagnostic(d, text, map, file))
            .collect()
    }
}

/// Record `name` in `seen`, or report it when the scope already has the name.
fn note(
    seen: &mut Seen,
    kind: &str,
    name: &Identifier,
    scope: Option<&str>,
    clause: &str,
    ft: &FileText,
    diags: &mut Vec<Diagnostic>,
) {
    match seen.get(&name.name) {
        Some(first) => {
            let where_ = match scope {
                Some(s) => format!(" in {s}"),
                None => String::new(),
            };
            diags.push(Diagnostic::error(
                format!(
                    "duplicate definition of {kind} '{}'{where_}: it is already defined at {first} \
                     (IEEE 1800-2017 {clause})",
                    name.name
                ),
                name.span,
            ));
        }
        None => {
            seen.insert(name.name.clone(), ft.locate(name));
        }
    }
}

/// The classes nested directly in `c` (§8.23), and in those.
fn nested(c: &ClassDeclaration, ft: &FileText, diags: &mut Vec<Diagnostic>) {
    let scope = format!("class '{}'", c.name.name);
    let mut seen = Seen::default();
    for it in &c.items {
        if let ClassItem::Class(inner) = it {
            note(
                &mut seen,
                "class",
                &inner.name,
                Some(&scope),
                "§3.13, §8.3",
                ft,
                diags,
            );
            nested(inner, ft, diags);
        }
    }
}

/// The classes of a module, interface, program or generate block body.
fn items(items: &[ModuleItem], scope: &str, ft: &FileText, diags: &mut Vec<Diagnostic>) {
    let mut seen = Seen::default();
    scope_items(items, scope, &mut seen, ft, diags);
}

fn scope_items(
    list: &[ModuleItem],
    scope: &str,
    seen: &mut Seen,
    ft: &FileText,
    diags: &mut Vec<Diagnostic>,
) {
    for it in list {
        match it {
            ModuleItem::ClassDeclaration(c) => {
                note(
                    seen,
                    "class",
                    &c.name,
                    Some(scope),
                    "§3.13, §8.3",
                    ft,
                    diags,
                );
                nested(c, ft, diags);
            }
            // §27.3: `generate`/`endgenerate` open no scope of their own.
            ModuleItem::GenerateRegion(g) => scope_items(&g.items, scope, seen, ft, diags),
            // §27.6: each generate block is a scope; the alternatives of a
            // conditional construct never coexist.
            ModuleItem::GenerateIf(g) => {
                for (_, its) in &g.branches {
                    items(its, "this generate block", ft, diags);
                }
            }
            ModuleItem::GenerateFor(g) => items(&g.items, "this generate block", ft, diags),
            ModuleItem::GenerateCase(g) => {
                for arm in &g.arms {
                    items(&arm.items, "this generate block", ft, diags);
                }
            }
            ModuleItem::NestedModule(m) => {
                items(&m.items, &format!("module '{}'", m.name.name), ft, diags)
            }
            _ => {}
        }
    }
}
