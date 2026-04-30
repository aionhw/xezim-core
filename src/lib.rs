//! xezim-core: shared SystemVerilog elaboration, runtime primitives, and
//! artifact format used by both the `xezim` bytecode interpreter and the
//! `xezim-b` native compiler.

pub mod value;
pub mod elaborate;
pub mod sdf;
pub mod vcd_sink;
pub mod stdout_sink;

pub use sv_parser::{self, parse, lexer, preprocessor, diagnostics, ParseResult, ast};
pub use value::Value;
pub use elaborate::{elaborate_module, ElaboratedModule};

/// Magic bytes identifying a xezim compiled artifact.
pub const XEZIM_BYTECODE_MAGIC: &[u8; 8] = b"XEZIMBC\x01";

/// Serialize a compiled ElaboratedModule to a file.
pub fn write_compiled(elab: &elaborate::ElaboratedModule, path: &str) -> Result<(), String> {
    let bytes = bincode::serialize(elab).map_err(|e| format!("serialize: {}", e))?;
    let mut out = Vec::with_capacity(bytes.len() + 8);
    out.extend_from_slice(XEZIM_BYTECODE_MAGIC);
    out.extend_from_slice(&bytes);
    std::fs::write(path, &out).map_err(|e| format!("write '{}': {}", path, e))
}

/// Read a compiled artifact from a file. Returns Ok(Some(elab)) if the file is
/// a valid artifact, Ok(None) if it lacks the magic header, Err on I/O or
/// deserialization failure.
pub fn read_compiled(path: &str) -> Result<Option<elaborate::ElaboratedModule>, String> {
    let bytes = std::fs::read(path).map_err(|e| format!("read '{}': {}", path, e))?;
    if bytes.len() < 8 || &bytes[..8] != XEZIM_BYTECODE_MAGIC {
        return Ok(None);
    }
    let elab = bincode::deserialize(&bytes[8..]).map_err(|e| format!("deserialize: {}", e))?;
    Ok(Some(elab))
}

use std::rc::Rc;

#[derive(Debug, Clone)]
pub enum SourceDefinition {
    Module(Rc<ast::module::ModuleDeclaration>),
    Interface(Rc<ast::module::InterfaceDeclaration>),
    Program(Rc<ast::module::ProgramDeclaration>),
    Class(Rc<ast::decl::ClassDeclaration>),
    Package(Rc<ast::module::PackageDeclaration>),
    Typedef(Rc<ast::decl::TypedefDeclaration>),
}

impl SourceDefinition {
    pub fn name(&self) -> String {
        match self {
            SourceDefinition::Module(m) => m.name.name.clone(),
            SourceDefinition::Interface(i) => i.name.name.clone(),
            SourceDefinition::Program(p) => p.name.name.clone(),
            SourceDefinition::Class(c) => c.name.name.clone(),
            SourceDefinition::Package(p) => p.name.name.clone(),
            SourceDefinition::Typedef(t) => t.name.name.clone(),
        }
    }

    pub fn items(&self) -> &[ast::decl::ModuleItem] {
        match self {
            SourceDefinition::Module(m) => &m.items,
            SourceDefinition::Interface(i) => &i.items,
            SourceDefinition::Program(p) => &p.items,
            SourceDefinition::Class(_) | SourceDefinition::Package(_) | SourceDefinition::Typedef(_) => &[],
        }
    }
}

/// Tokenize a source string.
pub fn tokenize_file(source: &str, _path: Option<&std::path::Path>) -> Vec<lexer::Token> {
    lexer::Lexer::new(source).tokenize()
}

/// Parse a source string into an AST.
pub fn parse_str(source: &str) -> Result<ParseResult, Vec<diagnostics::Diagnostic>> {
    let result = sv_parser::parse(source);
    if !result.errors.is_empty() {
        Err(result.errors)
    } else {
        Ok(result)
    }
}

pub fn parse_and_elaborate_multi(
    sources: &[String],
    top_module_name: Option<&str>,
    include_dirs: &[String],
    source_files: &[String],
    defines: &[(String, Option<String>)],
) -> Result<(ahash::AHashMap<String, SourceDefinition>, elaborate::ElaboratedModule), String> {
    let mut all_descriptions = Vec::new();
    let mut pp = preprocessor::Preprocessor::new();
    for dir in include_dirs { pp.add_include_dir(std::path::PathBuf::from(dir)); }
    for (name, val) in defines {
        pp.define(name.clone(), preprocessor::MacroDef {
            name: name.clone(), params: None,
            body: val.clone().unwrap_or_default(),
        });
    }

    for (i, source) in sources.iter().enumerate() {
        let source_path = source_files.get(i).map(|p| std::path::PathBuf::from(p));
        let preprocessed = pp.preprocess_file(source, source_path.as_deref());

        let tokens = lexer::Lexer::new(&preprocessed).tokenize();
        let mut parser = sv_parser::parse::Parser::new(tokens);
        let source_ast = parser.parse_source_text();
        let diags = parser.diagnostics().to_vec();

        if diags.iter().any(|d| d.severity == diagnostics::Severity::Error) {
            let errs: Vec<_> = diags.iter()
                .filter(|d| d.severity == diagnostics::Severity::Error)
                .map(|d| d.to_string()).collect();
            return Err(format!("Parse errors in source {}:\n{}", i, errs.join("\n")));
        }
        all_descriptions.extend(source_ast.descriptions);
    }

    let lib_defines = pp.snapshot_defines();
    parse_and_elaborate(all_descriptions, top_module_name, include_dirs, &lib_defines)
}

fn parse_and_elaborate(
    all_descriptions: Vec<ast::Description>,
    top_module_name: Option<&str>,
    include_dirs: &[String],
    lib_defines: &std::collections::HashMap<String, preprocessor::MacroDef>,
) -> Result<(ahash::AHashMap<String, SourceDefinition>, elaborate::ElaboratedModule), String> {
    let mut definitions: ahash::AHashMap<String, SourceDefinition> = ahash::AHashMap::new();
    let mut top_module = None;
    let mut top_level_imports = Vec::new();
    let mut top_level_lets = Vec::new();
    let mut top_level_functions: Vec<ast::decl::FunctionDeclaration> = Vec::new();
    let mut top_level_tasks: Vec<ast::decl::TaskDeclaration> = Vec::new();
    let mut top_level_nettypes: Vec<ast::decl::NettypeDeclaration> = Vec::new();
    for desc in all_descriptions {
        match desc {
            ast::Description::Module(m) => {
                let name = m.name.name.clone();
                top_module = Some(name.clone());
                definitions.insert(name, SourceDefinition::Module(Rc::new(m)));
            }
            ast::Description::Interface(i) => {
                let name = i.name.name.clone();
                definitions.insert(name, SourceDefinition::Interface(Rc::new(i)));
            }
            ast::Description::Program(p) => {
                let name = p.name.name.clone();
                top_module = Some(name.clone());
                definitions.insert(name, SourceDefinition::Program(Rc::new(p)));
            }
            ast::Description::Class(c) => {
                let name = c.name.name.clone();
                definitions.insert(name, SourceDefinition::Class(Rc::new(c)));
            }
            ast::Description::Package(p) => {
                let name = p.name.name.clone();
                definitions.insert(name, SourceDefinition::Package(Rc::new(p)));
            }
            ast::Description::TypedefDecl(t) => {
                let name = t.name.name.clone();
                definitions.insert(name, SourceDefinition::Typedef(Rc::new(t)));
            }
            ast::Description::ImportDecl(id) => {
                top_level_imports.push(id);
            }
            ast::Description::PackageItem(ast::decl::PackageItem::Checker(c)) => {
                let m = ast::module::ModuleDeclaration {
                    attrs: Vec::new(),
                    kind: ast::module::ModuleKind::Module,
                    lifetime: None,
                    name: c.name,
                    params: Vec::new(),
                    ports: c.ports,
                    items: c.items,
                    endlabel: c.endlabel,
                    span: c.span,
                };
                let name = m.name.name.clone();
                definitions.insert(name, SourceDefinition::Module(Rc::new(m)));
            }
            ast::Description::PackageItem(ast::decl::PackageItem::Let(l)) => {
                top_level_lets.push(l);
            }
            ast::Description::PackageItem(ast::decl::PackageItem::Function(f)) => {
                top_level_functions.push(f);
            }
            ast::Description::PackageItem(ast::decl::PackageItem::Task(t)) => {
                top_level_tasks.push(t);
            }
            ast::Description::PackageItem(ast::decl::PackageItem::Nettype(n)) => {
                top_level_nettypes.push(n);
            }
            _ => {}
        }
    }
    if !top_level_functions.is_empty() || !top_level_tasks.is_empty() || !top_level_nettypes.is_empty() {
        for def in definitions.values_mut() {
            if let SourceDefinition::Module(m) = def {
                let m = Rc::make_mut(m);
                for f in top_level_functions.iter().rev() {
                    m.items.insert(0, ast::decl::ModuleItem::FunctionDeclaration(f.clone()));
                }
                for t in top_level_tasks.iter().rev() {
                    m.items.insert(0, ast::decl::ModuleItem::TaskDeclaration(t.clone()));
                }
                for n in top_level_nettypes.iter().rev() {
                    m.items.insert(0, ast::decl::ModuleItem::NettypeDeclaration(n.clone()));
                }
            }
        }
    }
    if !include_dirs.is_empty() { resolve_library_modules(&mut definitions, include_dirs, lib_defines)?; }

    if let Some(name) = top_module_name {
        if definitions.contains_key(name) { top_module = Some(name.to_string()); }
        else { return Err(format!("Top module '{}' not found.", name)); }
    } else {
        let mut instantiated: std::collections::HashSet<String> = std::collections::HashSet::new();
        for m in definitions.values() { collect_instantiated_modules(m.items(), &mut instantiated); }
        let mut candidates: Vec<String> = definitions.keys().filter(|n| !instantiated.contains(n.as_str())).cloned().collect();
        // Sort to make top-module selection deterministic when more than one
        // module is uninstantiated. Without this, ahash's random seed picks
        // arbitrarily between, e.g., openc910's `tb` and `top` testbenches —
        // each iteration runs a different testbench's initial blocks, so the
        // sim either fires up clk/rst correctly or silently picks the
        // verilator variant whose forever-counter logic xezim doesn't model.
        candidates.sort();
        // If the source-order parse already picked a top that's a valid
        // candidate (uninstantiated by anything else), prefer it over the
        // candidate-based heuristic. Otherwise fall through to the heuristic
        // and rely on `candidates.sort()` for determinism.
        let parse_pick_valid = top_module.as_ref()
            .map_or(false, |n| candidates.iter().any(|c| c == n));
        if parse_pick_valid {
            // Keep top_module as-is — deterministic via source order.
        } else if candidates.len() == 1 {
            top_module = Some(candidates[0].clone());
        } else if candidates.len() > 1 {
            for c in &candidates {
                if definitions.get(c).unwrap().items().iter().any(|item| matches!(item, ast::decl::ModuleItem::InitialConstruct(_))) {
                    top_module = Some(c.clone()); break;
                }
            }
        }
    }

    let top_name = top_module.ok_or("No module found")?;
    let top_def = definitions.get(&top_name).ok_or_else(|| format!("Module '{}' not found", top_name))?;
    let params = ahash::AHashMap::new();

    let def_refs: ahash::AHashMap<String, elaborate::Definition> =
        definitions.iter().filter_map(|(k, v)| {
            let def = match v {
                SourceDefinition::Module(m) => elaborate::Definition::Module(&**m),
                SourceDefinition::Interface(i) => elaborate::Definition::Interface(&**i),
                SourceDefinition::Program(p) => elaborate::Definition::Program(&**p),
                SourceDefinition::Class(c) => elaborate::Definition::Class(&**c),
                SourceDefinition::Package(p) => elaborate::Definition::Package(&**p),
                SourceDefinition::Typedef(t) => elaborate::Definition::Typedef(&**t),
            };
            Some((k.clone(), def))
        }).collect();

    let elab_def = match top_def {
        SourceDefinition::Module(m) => elaborate::Definition::Module(&**m),
        SourceDefinition::Interface(i) => elaborate::Definition::Interface(&**i),
        SourceDefinition::Program(p) => elaborate::Definition::Program(&**p),
        SourceDefinition::Class(c) => elaborate::Definition::Class(&**c),
        SourceDefinition::Package(p) => elaborate::Definition::Package(&**p),
        _ => return Err(format!("Top-level element '{}' is not a module or program", top_name)),
    };
    let mut elab = elaborate::elaborate_module_with_defs(
        elab_def,
        &params,
        Some(&def_refs),
        &top_level_imports,
        &top_level_lets,
    )?;

    elaborate::inline_instantiations(&mut elab, &def_refs)?;
    Ok((definitions, elab))
}

fn collect_instantiated_modules(items: &[ast::decl::ModuleItem], set: &mut std::collections::HashSet<String>) {
    for item in items {
        match item {
            ast::decl::ModuleItem::ModuleInstantiation(mi) => { set.insert(mi.module_name.name.clone()); }
            ast::decl::ModuleItem::GenerateIf(gi) => {
                for (_cond, items) in &gi.branches { collect_instantiated_modules(items, set); }
            }
            ast::decl::ModuleItem::GenerateFor(gf) => collect_instantiated_modules(&gf.items, set),
            _ => {}
        }
    }
}

fn resolve_library_modules(
    definitions: &mut ahash::AHashMap<String, SourceDefinition>,
    include_dirs: &[String],
    lib_defines: &std::collections::HashMap<String, preprocessor::MacroDef>,
) -> Result<(), String> {
    fn collect_sv_files(dir: &std::path::Path, out: &mut Vec<std::path::PathBuf>) -> Result<(), String> {
        let entries = std::fs::read_dir(dir)
            .map_err(|e| format!("read_dir '{}': {}", dir.display(), e))?;
        for entry in entries {
            let entry = entry.map_err(|e| format!("read_dir '{}': {}", dir.display(), e))?;
            let path = entry.path();
            if path.is_dir() {
                collect_sv_files(&path, out)?;
                continue;
            }
            let Some(ext) = path.extension().and_then(|s| s.to_str()) else { continue };
            if matches!(ext, "v" | "sv" | "V") {
                out.push(path);
            }
        }
        Ok(())
    }

    let mut files = Vec::new();
    for dir in include_dirs {
        let path = std::path::Path::new(dir);
        if path.is_dir() {
            collect_sv_files(path, &mut files)?;
        }
    }

    for path in files {
        let source = match std::fs::read_to_string(&path) {
            Ok(s) => s,
            Err(_) => continue,
        };
        let mut pp = preprocessor::Preprocessor::new();
        for dir in include_dirs {
            pp.add_include_dir(std::path::PathBuf::from(dir));
        }
        for (name, def) in lib_defines {
            pp.define(name.clone(), def.clone());
        }
        let preprocessed = pp.preprocess_file(&source, Some(&path));
        let result = sv_parser::parse(&preprocessed);
        for desc in result.source.descriptions {
            match desc {
                ast::Description::Module(m) => {
                    let name = m.name.name.clone();
                    definitions.entry(name).or_insert_with(|| SourceDefinition::Module(Rc::new(m)));
                }
                ast::Description::Interface(i) => {
                    let name = i.name.name.clone();
                    definitions.entry(name).or_insert_with(|| SourceDefinition::Interface(Rc::new(i)));
                }
                ast::Description::Program(p) => {
                    let name = p.name.name.clone();
                    definitions.entry(name).or_insert_with(|| SourceDefinition::Program(Rc::new(p)));
                }
                ast::Description::Class(c) => {
                    let name = c.name.name.clone();
                    definitions.entry(name).or_insert_with(|| SourceDefinition::Class(Rc::new(c)));
                }
                ast::Description::Package(p) => {
                    let name = p.name.name.clone();
                    definitions.entry(name).or_insert_with(|| SourceDefinition::Package(Rc::new(p)));
                }
                ast::Description::TypedefDecl(t) => {
                    let name = t.name.name.clone();
                    definitions.entry(name).or_insert_with(|| SourceDefinition::Typedef(Rc::new(t)));
                }
                _ => {}
            }
        }
    }
    Ok(())
}

/// Set the log file for simulation output. Placeholder.
pub fn set_log_file(_path: &str) -> Result<(), String> { Ok(()) }

pub fn log_println(s: &str) { println!("{}", s); }
pub fn log_eprintln(s: &str) { eprintln!("{}", s); }
