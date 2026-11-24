//! §3.13, §6.18, §8.3, §26.2: duplicate class, typedef and package definitions.
//!
//! A scope's name space holds one declaration per name (§3.13), so a second
//! `class C` or `typedef ... T` in the compilation unit, a package, a module
//! or a generate block, or a second `package P` anywhere in the design (§26.2),
//! is illegal. Classes and user-defined types share one type-name table per
//! scope. Forward typedefs never count, and identical `typedef` definitions in
//! different command-line files emit a warning and keep the first.
//!
//! The check runs on each file's parsed descriptions, the one point where a
//! declaration's file is still known. All source files share one compilation
//! unit and one package name space, so those tables live across files.

use crate::ast::decl::{ClassDeclaration, ClassItem, ModuleItem, PackageItem, TypedefDeclaration};
use crate::ast::types::DataType;
use crate::ast::{Description, Identifier, Span};
use crate::diagnostics::{self, Diagnostic, Severity};
use crate::lexer::{Lexer, TokenKind};
use sv_parser::source_map::LineMap;

/// One file's text, for locating a span and comparing typedef text.
struct FileText<'a> {
    text: &'a str,
    map: Option<&'a LineMap>,
    file: &'a str,
    file_idx: usize,
}

impl FileText<'_> {
    fn locate(&self, name: &Identifier) -> String {
        diagnostics::locate(self.text, self.map, self.file, name.span).short()
    }
}

/// A declaration already recorded in a scope.
struct Entry {
    loc: String,
    file_idx: usize,
    /// Token-normalized source text for non-forward typedefs (`None` for classes/packages).
    typedef_text: Option<String>,
}

/// The definitions declared so far in one name space/scope.
type Seen = crate::hasher::HashMap<String, Entry>;

/// Rendered errors and warnings for one parsed source file.
#[derive(Default)]
pub(crate) struct CheckDiagnostics {
    pub errors: Vec<String>,
    pub warnings: Vec<String>,
}

#[derive(Default)]
pub(crate) struct DuplicateDefinitions {
    /// Compilation-unit types (classes and typedefs) of the files checked so far.
    unit: Seen,
    /// Packages declared across the files checked so far (§3.13, §26.2).
    packages: Seen,
}

impl DuplicateDefinitions {
    /// Check `descriptions` (parsed from command-line file `file_idx`) for
    /// duplicate definitions against prior scopes and within this file.
    pub(crate) fn check_file(
        &mut self,
        descriptions: &[Description],
        text: &str,
        map: Option<&LineMap>,
        file: &str,
        file_idx: usize,
    ) -> CheckDiagnostics {
        let ft = FileText {
            text,
            map,
            file,
            file_idx,
        };
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
                        None,
                        &ft,
                        &mut diags,
                    );
                    nested(c, &ft, &mut diags);
                }
                Description::TypedefDecl(t) | Description::PackageItem(PackageItem::Typedef(t)) => {
                    note_typedef(&mut self.unit, t, "the compilation unit", &ft, &mut diags);
                }
                Description::Package(p) => {
                    note(
                        &mut self.packages,
                        "package",
                        &p.name,
                        None,
                        "§3.13, §26.2",
                        None,
                        &ft,
                        &mut diags,
                    );
                    let scope = format!("package '{}'", p.name.name);
                    let mut seen = Seen::default();
                    for it in &p.items {
                        match it {
                            PackageItem::Class(c) => {
                                note(
                                    &mut seen,
                                    "class",
                                    &c.name,
                                    Some(&scope),
                                    "§3.13, §8.3",
                                    None,
                                    &ft,
                                    &mut diags,
                                );
                                nested(c, &ft, &mut diags);
                            }
                            PackageItem::Typedef(t) => {
                                note_typedef(&mut seen, t, &scope, &ft, &mut diags);
                            }
                            _ => {}
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
        let mut out = CheckDiagnostics::default();
        for d in &diags {
            let rendered = diagnostics::render_diagnostic(d, text, map, file);
            match d.severity {
                Severity::Warning => out.warnings.push(rendered),
                _ => out.errors.push(rendered),
            }
        }
        out
    }
}

/// Normalize a typedef declaration's source text by tokenizing (ignoring
/// whitespace and comments).
fn normalize_typedef(text: &str, span: Span) -> Option<String> {
    let slice = text.get(span.start as usize..span.end as usize)?;
    let tokens = Lexer::new(slice).tokenize();
    let mut out = String::new();
    for tok in &tokens {
        if tok.kind == TokenKind::Eof {
            continue;
        }
        if !out.is_empty() {
            out.push('\0');
        }
        out.push_str(&tokens.text(tok));
    }
    (!out.is_empty()).then_some(out)
}

/// Record a non-forward typedef in `seen`, or report a duplicate/exemption.
fn note_typedef(
    seen: &mut Seen,
    t: &TypedefDeclaration,
    scope: &str,
    ft: &FileText,
    diags: &mut Vec<Diagnostic>,
) {
    // §6.18: forward typedefs (`typedef class c;`, `typedef struct s;`,
    // `typedef c;`) are placeholders and may repeat before or after the full
    // declaration.
    if t.forward || matches!(t.data_type, DataType::Void(_)) {
        return;
    }
    let norm = normalize_typedef(ft.text, t.span);
    note(
        seen,
        "typedef",
        &t.name,
        Some(scope),
        "§3.13, §6.18",
        norm,
        ft,
        diags,
    );
}

/// Record `name` in `seen`, or report it when the scope already has the name.
#[allow(clippy::too_many_arguments)]
fn note(
    seen: &mut Seen,
    kind: &str,
    name: &Identifier,
    scope: Option<&str>,
    clause: &str,
    typedef_text: Option<String>,
    ft: &FileText,
    diags: &mut Vec<Diagnostic>,
) {
    match seen.get(&name.name) {
        Some(first) => {
            let where_ = match scope {
                Some(s) => format!(" in {s}"),
                None => String::new(),
            };
            let msg = format!(
                "duplicate definition of {kind} '{}'{where_}: it is already defined at {} \
                 (IEEE 1800-2017 {clause})",
                name.name, first.loc
            );
            // Cross-file exemption (§3.12.1): two command-line files with an
            // identical typedef emit a warning and keep the first.
            let identical_cross_file = first.file_idx != ft.file_idx
                && typedef_text.is_some()
                && first.typedef_text == typedef_text;
            let diag = if identical_cross_file {
                Diagnostic::warning(msg, name.span)
            } else {
                Diagnostic::error(msg, name.span)
            };
            diags.push(diag);
        }
        None => {
            seen.insert(
                name.name.clone(),
                Entry {
                    loc: ft.locate(name),
                    file_idx: ft.file_idx,
                    typedef_text,
                },
            );
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
                None,
                ft,
                diags,
            );
            nested(inner, ft, diags);
        }
    }
}

/// The types of a module, interface, program or generate block body.
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
                    None,
                    ft,
                    diags,
                );
                nested(c, ft, diags);
            }
            ModuleItem::TypedefDeclaration(t) => {
                note_typedef(seen, t, scope, ft, diags);
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
