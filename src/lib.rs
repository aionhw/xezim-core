//! xezim-core: shared SystemVerilog elaboration, runtime primitives, and
//! artifact format used by both the `xezim` bytecode interpreter and the
//! `xezim-b` native compiler.

pub mod value;
pub mod bits2;
pub mod elaborate;
pub mod sdf;
pub mod vcd_sink;
pub mod stdout_sink;

/// Deterministic hasher for `HashMap`/`HashSet` so iteration order is
/// reproducible across runs. Both `crate::hasher::HashMap` (default `RandomState`)
/// and `std::collections::HashMap` use OS-random seeds, which causes
/// non-deterministic iteration. For simulator correctness debugging
/// (and to make c910 memcpy reproducible at the same cycle each run),
/// we use a fixed-seeded ahash state.
pub mod hasher {
    #[derive(Clone, Debug)]
    pub struct DeterministicState(ahash::RandomState);

    impl Default for DeterministicState {
        fn default() -> Self {
            DeterministicState(ahash::RandomState::with_seeds(
                0xdead_beef_cafe_babe,
                0xfeed_face_0123_4567,
                0xbada_55_b01d_face,
                0x0123_4567_89ab_cdef,
            ))
        }
    }

    impl std::hash::BuildHasher for DeterministicState {
        type Hasher = ahash::AHasher;
        fn build_hasher(&self) -> Self::Hasher {
            <ahash::RandomState as std::hash::BuildHasher>::build_hasher(&self.0)
        }
    }

    pub type HashMap<K, V> = std::collections::HashMap<K, V, DeterministicState>;
    pub type HashSet<T> = std::collections::HashSet<T, DeterministicState>;
}

pub use sv_parser::{self, parse, lexer, preprocessor, diagnostics, ParseResult, ast};
pub use value::Value;
pub use elaborate::{elaborate_module, ElaboratedModule};

/// Magic bytes identifying a xezim compiled artifact.
/// Version byte: \x03 = zstd-compressed varint bincode body
/// (\x02 = uncompressed varint, \x01 = uncompressed fixint).
pub const XEZIM_BYTECODE_MAGIC: &[u8; 8] = b"XEZIMBC\x03";

/// zstd compression level used for `.xez` artifacts. Level 3 is zstd's own
/// default — strong compression at high throughput. Empirically shrinks
/// the elaborated-bincode stream ~27×, which more than pays for the
/// compute via reduced disk I/O.
const XEZIM_ZSTD_LEVEL: i32 = 3;

/// Bincode configuration for xezim compiled artifacts. Variable-int encoding
/// shrinks length tags, enum discriminants, and small integers; the wire
/// format is incompatible with the top-level `bincode::serialize` defaults
/// (which use fixed 8-byte ints), so this is the single source of truth used
/// by both writer and reader.
pub fn xez_bincode_options() -> impl bincode::Options + Copy {
    use bincode::Options;
    bincode::DefaultOptions::new()
        .with_varint_encoding()
        .with_little_endian()
}

fn artifact_version_error(file_magic: &[u8; 8]) -> Option<String> {
    if &file_magic[..7] == &XEZIM_BYTECODE_MAGIC[..7] && file_magic[7] != XEZIM_BYTECODE_MAGIC[7] {
        Some(format!(
            "incompatible xezim artifact version (file v{}, expected v{}); recompile with current xezim",
            file_magic[7], XEZIM_BYTECODE_MAGIC[7]
        ))
    } else {
        None
    }
}

/// Serialize a compiled ElaboratedModule to a file. Streams bincode through
/// a zstd encoder into the file; never holds the full serialized blob in
/// memory, and writes ~27× less to disk than the raw bincode stream.
pub fn write_compiled(elab: &elaborate::ElaboratedModule, path: &str) -> Result<(), String> {
    use bincode::Options;
    use std::io::Write;
    let f = std::fs::File::create(path).map_err(|e| format!("create '{}': {}", path, e))?;
    let mut w = std::io::BufWriter::with_capacity(1 << 20, f);
    w.write_all(XEZIM_BYTECODE_MAGIC).map_err(|e| format!("write '{}': {}", path, e))?;
    let mut enc = zstd::stream::Encoder::new(w, XEZIM_ZSTD_LEVEL)
        .map_err(|e| format!("zstd init: {}", e))?;
    xez_bincode_options()
        .serialize_into(&mut enc, elab)
        .map_err(|e| format!("serialize: {}", e))?;
    let mut w = enc.finish().map_err(|e| format!("zstd finish: {}", e))?;
    w.flush().map_err(|e| format!("flush '{}': {}", path, e))
}

/// Read a compiled artifact from a file. Returns Ok(Some(elab)) if the file is
/// a valid artifact, Ok(None) if it lacks the magic header, Err on I/O,
/// version-mismatch, or deserialization failure.
pub fn read_compiled(path: &str) -> Result<Option<elaborate::ElaboratedModule>, String> {
    use bincode::Options;
    use std::io::Read;
    let f = std::fs::File::open(path).map_err(|e| format!("read '{}': {}", path, e))?;
    let mut r = std::io::BufReader::with_capacity(1 << 20, f);
    let mut magic = [0u8; 8];
    if r.read_exact(&mut magic).is_err() {
        return Ok(None);
    }
    if &magic != XEZIM_BYTECODE_MAGIC {
        if let Some(err) = artifact_version_error(&magic) {
            return Err(err);
        }
        return Ok(None);
    }
    let dec = zstd::stream::Decoder::new(r).map_err(|e| format!("zstd init: {}", e))?;
    let elab = xez_bincode_options()
        .deserialize_from(dec)
        .map_err(|e| format!("deserialize: {}", e))?;
    Ok(Some(elab))
}

/// Like `read_compiled` but reads from an in-memory slice (e.g. an embedded
/// `include_bytes!()` payload in a binary produced by `--emit-native`).
pub fn read_compiled_bytes(bytes: &[u8]) -> Result<elaborate::ElaboratedModule, String> {
    use bincode::Options;
    if bytes.len() < 8 {
        return Err("xezim artifact: payload shorter than magic header".to_string());
    }
    let (magic, body) = bytes.split_at(8);
    if magic != XEZIM_BYTECODE_MAGIC {
        let mut m = [0u8; 8];
        m.copy_from_slice(magic);
        if let Some(err) = artifact_version_error(&m) {
            return Err(err);
        }
        return Err("xezim artifact: missing magic header".to_string());
    }
    let dec = zstd::stream::Decoder::new(body).map_err(|e| format!("zstd init: {}", e))?;
    xez_bincode_options()
        .deserialize_from(dec)
        .map_err(|e| format!("deserialize: {}", e))
}

use std::rc::Rc;

/// Implementation-defined `--module-timescale` command-line extension.
/// `global` applies to every module with no explicit source-level timescale;
/// `named` applies to the listed modules likewise. Exponents are powers of ten
/// in seconds (e.g. `1ns` = -9). Never overrides an explicit timescale.
#[derive(Clone, Default)]
pub struct ModuleTimescaleCli {
    pub global: Option<(i32, i32)>,
    pub named: std::collections::HashMap<String, (i32, i32)>,
}

static MODULE_TIMESCALE_CLI: std::sync::OnceLock<std::sync::Mutex<ModuleTimescaleCli>> =
    std::sync::OnceLock::new();

fn module_timescale_cli_cell() -> &'static std::sync::Mutex<ModuleTimescaleCli> {
    MODULE_TIMESCALE_CLI.get_or_init(|| std::sync::Mutex::new(ModuleTimescaleCli::default()))
}

/// Install the parsed `--module-timescale` configuration before elaboration.
pub fn set_module_timescale_cli(cli: ModuleTimescaleCli) {
    if let Ok(mut g) = module_timescale_cli_cell().lock() {
        *g = cli;
    }
}

fn module_timescale_cli() -> ModuleTimescaleCli {
    module_timescale_cli_cell().lock().map(|g| g.clone()).unwrap_or_default()
}

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
) -> Result<(crate::hasher::HashMap<String, SourceDefinition>, elaborate::ElaboratedModule), String> {
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
        // Second, AST-level strict pass (runs alongside the permissive parser;
        // gated by --strict, on by default). Rejects LRM violations the main
        // parser accepts. See sv_parser::strict_check.
        let strict_viol = sv_parser::strict_check::strict_violations(&source_ast.descriptions);
        if !strict_viol.is_empty() {
            return Err(format!("Strict check failed in source {}:\n{}", i, strict_viol.join("\n")));
        }
        all_descriptions.extend(source_ast.descriptions);
    }

    let lib_defines = pp.snapshot_defines();
    let module_timescales = pp.module_timescales.clone();
    parse_and_elaborate(all_descriptions, top_module_name, include_dirs, &lib_defines, &module_timescales)
}

fn parse_and_elaborate(
    all_descriptions: Vec<ast::Description>,
    top_module_name: Option<&str>,
    include_dirs: &[String],
    lib_defines: &std::collections::HashMap<String, preprocessor::MacroDef>,
    module_timescales: &std::collections::HashMap<String, (f64, f64)>,
) -> Result<(crate::hasher::HashMap<String, SourceDefinition>, elaborate::ElaboratedModule), String> {
    // Effective per-module timescale, unifying `\`timescale` directives (from
    // the preprocessor) with in-body `timeunit`/`timeprecision` declarations
    // (§3.14.2). A `timeunit` decl was previously ignored here, so its module's
    // delays were never scaled — `#5` in a `timeunit 1us` module ran as 5 ns.
    // Precedence, highest first (implementation-defined --module-timescale
    // extension): local timeunit/timeprecision decl > active `\`timescale`
    // directive > named --module-timescale > global --module-timescale >
    // 1 ns / 1 ns default. The command-line forms never override an explicit
    // source-level timescale (a local decl OR an active directive).
    let cli = module_timescale_cli();
    let mut eff_ts: std::collections::HashMap<String, (f64, f64)> = std::collections::HashMap::new();
    let mut named_matched: std::collections::HashSet<String> = std::collections::HashSet::new();
    for desc in &all_descriptions {
        if let ast::Description::Module(m) = desc {
            let name = &m.name.name;
            // Explicit source-level declarations.
            let mut local_u: Option<i32> = None;
            let mut local_p: Option<i32> = None;
            for it in &m.items {
                if let ast::decl::ModuleItem::TimeunitsDecl(td) = it {
                    if let Some(u) = &td.unit {
                        local_u = Some(elaborate::time_literal_to_exp(u));
                    }
                    if let Some(p) = &td.precision {
                        local_p = Some(elaborate::time_literal_to_exp(p));
                    }
                }
            }
            let directive = module_timescales
                .get(name)
                .map(|&(u, p)| (elaborate::secs_to_exp(u), elaborate::secs_to_exp(p)));
            let is_explicit = local_u.is_some() || local_p.is_some() || directive.is_some();
            let named = cli.named.get(name).copied();
            if named.is_some() {
                named_matched.insert(name.clone());
            }

            let eff_exp: Option<(i32, i32)> = if is_explicit {
                // A local decl overrides the directive field by field; a missing
                // field falls back to the directive, then to 1 ns.
                let (du, dp) = directive.unwrap_or((-9, -9));
                let u = local_u.unwrap_or(du);
                let p = local_p.unwrap_or(dp);
                if named.is_some() {
                    eprintln!(
                        "[warn] --module-timescale for module '{}' ignored; it has an explicit source-level timescale",
                        name
                    );
                }
                Some((u, p))
            } else {
                // No explicit timescale: named CLI wins over global CLI.
                named.or(cli.global)
            };
            if let Some((u, p)) = eff_exp {
                eff_ts.insert(name.clone(), (elaborate::exp_to_secs(u), elaborate::exp_to_secs(p)));
            }
        }
    }
    // §10: warn on a named assignment that matched no module definition.
    for name in cli.named.keys() {
        if !named_matched.contains(name) {
            eprintln!("[warn] --module-timescale did not match module '{}'", name);
        }
    }

    // Global simulation tick = the finest precision across the design
    // (default 1 ns). All module delays are then pre-scaled to this unit.
    let tick_s = eff_ts.values().map(|&(_, p)| p).fold(1e-9_f64, f64::min);
    let mut module_timescale_exp: crate::hasher::HashMap<String, (i32, i32)> =
        crate::hasher::HashMap::default();
    for (n, &(u, p)) in &eff_ts {
        module_timescale_exp.insert(n.clone(), (elaborate::secs_to_exp(u), elaborate::secs_to_exp(p)));
    }
    let mut definitions: crate::hasher::HashMap<String, SourceDefinition> = crate::hasher::HashMap::default();
    let mut top_module = None;
    let mut top_level_imports = Vec::new();
    let mut top_level_lets = Vec::new();
    let mut top_level_functions: Vec<ast::decl::FunctionDeclaration> = Vec::new();
    let mut top_level_tasks: Vec<ast::decl::TaskDeclaration> = Vec::new();
    let mut top_level_nettypes: Vec<ast::decl::NettypeDeclaration> = Vec::new();
    let mut top_level_params: Vec<ast::decl::ParameterDeclaration> = Vec::new();
    let mut top_level_vars: Vec<ast::decl::DataDeclaration> = Vec::new();
    let mut top_level_binds: Vec<ast::decl::BindDirective> = Vec::new();
    // §18.5.1 $unit-scope out-of-class constraint definitions (class, name).
    let mut top_level_ooc_constraints: Vec<(String, String, Vec<ast::decl::ConstraintItem>)> =
        Vec::new();
    for desc in all_descriptions {
        match desc {
            ast::Description::Module(mut m) => {
                let name = m.name.name.clone();
                if definitions.contains_key(&name) {
                    return Err(format!(
                        "Duplicate module definition '{}' (IEEE 1800-2017 §3.3)",
                        name
                    ));
                }
                // Pre-scale this module's delays from its own timeunit to the
                // global tick (no-op when both are 1 ns).
                // Every module's delays are pre-scaled to the global tick, even
                // those with no explicit or CLI timescale — the simulator
                // consumes tick-denominated delays. A module with no effective
                // timescale uses the tick unit, making the rewrite a numeric
                // no-op but still converting the delay form.
                let unit_s = eff_ts.get(&name).map(|&(u, _)| u).unwrap_or(tick_s);
                elaborate::rewrite_module_delays_pub(&mut m.items, unit_s, tick_s);
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
                // §6.18: a bare forward typedef (`typedef name;`) must not
                // displace a real definition of the same name — `typedef_test_0`
                // restates the forward name after the full `typedef int name;`.
                // Forward → insert only if absent; real → always (replaces a
                // prior forward placeholder).
                if t.forward {
                    definitions.entry(name).or_insert_with(|| SourceDefinition::Typedef(Rc::new(t)));
                } else {
                    definitions.insert(name, SourceDefinition::Typedef(Rc::new(t)));
                }
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
            ast::Description::PackageItem(ast::decl::PackageItem::Parameter(p)) => {
                top_level_params.push(p);
            }
            ast::Description::PackageItem(ast::decl::PackageItem::Data(d)) => {
                top_level_vars.push(d);
            }
            ast::Description::Bind(b) => {
                top_level_binds.push(b);
            }
            ast::Description::OutOfClassConstraint { class_name, constraint_name, items } => {
                top_level_ooc_constraints.push((class_name, constraint_name, items));
            }
            _ => {}
        }
    }

    // §23.11: a `bind` written as a module item (not at compilation-unit
    // scope) is applied identically. Lift every `ModuleItem::Bind` out of the
    // module bodies (replacing it with `Null` so it is not re-processed as a
    // real instantiation) and fold it into `top_level_binds`.
    let mut inmodule_binds: Vec<ast::decl::BindDirective> = Vec::new();
    for def in definitions.values_mut() {
        if let SourceDefinition::Module(m) = def {
            if !m.items.iter().any(|it| matches!(it, ast::decl::ModuleItem::Bind(_))) {
                continue;
            }
            let m = Rc::make_mut(m);
            for it in m.items.iter_mut() {
                if let ast::decl::ModuleItem::Bind(b) = it {
                    inmodule_binds.push(b.clone());
                    *it = ast::decl::ModuleItem::Null;
                }
            }
        }
    }
    top_level_binds.extend(inmodule_binds);

    // IEEE 1800-2023 §23.11: apply each `bind` by appending the bound
    // instantiation to its target module's items. This runs before
    // top_level_functions/tasks/nettypes injection so a bound monitor module
    // sees the same top-level helpers as native modules.
    for b in &top_level_binds {
        let tname = b.target_module.name.clone();
        let Some(def) = definitions.get_mut(&tname) else { continue };
        if let SourceDefinition::Module(m) = def {
            let m = Rc::make_mut(m);
            m.items.push(ast::decl::ModuleItem::ModuleInstantiation(b.instantiation.clone()));
        }
    }
    if !top_level_functions.is_empty() || !top_level_tasks.is_empty()
        || !top_level_nettypes.is_empty() || !top_level_params.is_empty()
        || !top_level_vars.is_empty() {
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
                // $unit-scope parameters become body localparams (constants):
                // visible inside the module, not part of its override interface.
                // A module-local parameter/localparam of the same name SHADOWS
                // the $unit one (LRM §3.12.1 name resolution) — skip injecting
                // any $unit param the module already declares, else the two
                // collide as a "Duplicate declaration".
                let local_param_names: std::collections::HashSet<String> = m.items.iter()
                    .filter_map(|it| match it {
                        ast::decl::ModuleItem::ParameterDeclaration(pd)
                        | ast::decl::ModuleItem::LocalparamDeclaration(pd) => Some(pd),
                        _ => None,
                    })
                    .flat_map(|pd| match &pd.kind {
                        ast::decl::ParameterKind::Data { assignments, .. } =>
                            assignments.iter().map(|a| a.name.name.clone()).collect::<Vec<_>>(),
                        _ => Vec::new(),
                    })
                    .collect();
                for p in top_level_params.iter().rev() {
                    let shadowed = match &p.kind {
                        ast::decl::ParameterKind::Data { assignments, .. } =>
                            assignments.iter().all(|a| local_param_names.contains(&a.name.name)),
                        _ => false,
                    };
                    if shadowed { continue; }
                    m.items.insert(0, ast::decl::ModuleItem::LocalparamDeclaration(p.clone()));
                }
                // $unit-scope variables (`string label = "X";`) become module
                // signals so references — including from class methods
                // validated against this module — resolve.
                for d in top_level_vars.iter().rev() {
                    m.items.insert(0, ast::decl::ModuleItem::DataDeclaration(d.clone()));
                }
            }
        }
    }
    // Capture the definitions that came from the explicitly-provided source
    // files BEFORE pulling in library (`-y` / `+incdir`) modules. Library
    // modules satisfy instantiations but must NEVER be candidates for the
    // implicit top: otherwise compiling a self-contained file (e.g. a lone
    // `class`) that shares an include dir with sibling testbenches would let
    // one of those testbenches (`module tb; initial run_test(); …`) get picked
    // as the top and run. An include dir is a search path, not a compile list.
    let explicit_def_names: std::collections::HashSet<String> =
        definitions.keys().cloned().collect();
    if !include_dirs.is_empty() { resolve_library_modules(&mut definitions, include_dirs, lib_defines)?; }

    let named_top_found = top_module_name.map_or(false, |n| definitions.contains_key(n));
    if let (Some(name), true) = (top_module_name, named_top_found) {
        top_module = Some(name.to_string());
    } else {
        // No top named, OR the named top wasn't found — auto-detect the
        // hierarchy root (a module instantiated by no other). This recovers
        // from a wrong `:top_module:` in a generated test (e.g. sv-tests'
        // veer-el2 specifies `veer-el2_wrapper`, but the module is
        // `el2_veer_wrapper`).
        if let Some(name) = top_module_name {
            eprintln!("[xezim][warning] top module '{}' not found; auto-detecting the design root", name);
        }
        let mut instantiated: std::collections::HashSet<String> = std::collections::HashSet::new();
        for m in definitions.values() { collect_instantiated_modules(m.items(), &mut instantiated); }
        let mut candidates: Vec<String> = definitions.keys()
            .filter(|n| !instantiated.contains(n.as_str())
                && explicit_def_names.contains(n.as_str())
                // A top-level (`$unit`-scope) typedef is never a hierarchy
                // root. Without this a file like `typedef enum {...} T;
                // module test; ...` wrongly picked `T`, which then fails
                // elaboration ("not a module or program"). Packages stay
                // eligible: a package-only design (e.g. uvm_pkg) legitimately
                // elaborates the package as the root.
                && !matches!(definitions.get(n.as_str()), Some(SourceDefinition::Typedef(_))))
            .cloned().collect();
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
        // No candidate carried an `initial` (e.g. a file of several `class`
        // declarations with no module — common in §18 constrained-random
        // tests). Rather than failing with "No module found", fall back to the
        // first candidate so the design still elaborates: a single-class file
        // already behaved this way, and a multi-class file should too.
        if top_module.is_none() && !candidates.is_empty() {
            top_module = Some(candidates[0].clone());
        }
    }

    let top_name = top_module.ok_or("No module found")?;
    let top_def = definitions.get(&top_name).ok_or_else(|| format!("Module '{}' not found", top_name))?;
    let params = crate::hasher::HashMap::default();

    let def_refs: crate::hasher::HashMap<String, elaborate::Definition> =
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
        &top_level_ooc_constraints,
    )?;
    elab.tick_s = tick_s;
    elab.module_timescale_exp = module_timescale_exp;
    // The top module's own unit/precision drives the default $time scaling and
    // $printtimescale when no per-scope entry is found.
    if let Some(&(u, p)) = elab.module_timescale_exp.get(&elab.name) {
        elab.timeunit_exp = u;
        elab.timeprecision_exp = p;
    }

    elaborate::inline_instantiations(&mut elab, &def_refs)?;
    // §28.8: bidirectional switches need every terminal's drivers in hand.
    elaborate::resolve_bidirectional_switches(&mut elab);
    // §6.6.1: a net with several continuous drivers resolves them all.
    elaborate::resolve_multi_driver_nets(&mut elab);
    // Link `function ClassName::m(); ...` out-of-class bodies into their
    // classes — must run after inline_instantiations repopulates classes.
    elaborate::link_extern_methods(&mut elab, &def_refs);
    if std::env::var("XEZIM_ELAB_STATS").is_ok() {
        eprintln!("[elab-stats] always_blocks={} initial_blocks={} cont_assigns={} pending_always={} pending_initial={} pending_cont_assign={} signals={} parameters={} arrays={} arrays_2d={} arrays_nd={} packed_struct_fields={}",
            elab.always_blocks.len(),
            elab.initial_blocks.len(),
            elab.continuous_assigns.len(),
            elab.pending_always.len(),
            elab.pending_initial.len(),
            elab.pending_cont_assign.len(),
            elab.signals.len(),
            elab.parameters.len(),
            elab.arrays.len(),
            elab.arrays_2d.len(),
            elab.arrays_nd.len(),
            elab.packed_struct_fields.len(),
        );
        // Bytewise breakdown via bincode serialize. Approximation only —
        // bincode is more compact than in-memory layout (no Vec capacity
        // slack, no padding, no String header) but the per-section relative
        // sizes correctly identify hot spots. On c910 hello this revealed
        // continuous_assigns at 394 MB, always_blocks at 193 MB, signals at
        // 173 MB — the three to target for memory work.
        use bincode::Options;
        let opts = xez_bincode_options();
        let try_size = |label: &str, bytes: Result<Vec<u8>, _>| match bytes {
            Ok(b) => eprintln!("[elab-bytes-bincode] {}: {:>10} bytes", label, b.len()),
            Err(_) => eprintln!("[elab-bytes-bincode] {}: <serialize failed>", label),
        };
        try_size("always_blocks    ", opts.serialize(&elab.always_blocks));
        try_size("initial_blocks   ", opts.serialize(&elab.initial_blocks));
        try_size("continuous_assigns", opts.serialize(&elab.continuous_assigns));
        try_size("signals          ", opts.serialize(&elab.signals));
        try_size("parameters       ", opts.serialize(&elab.parameters));
        try_size("arrays           ", opts.serialize(&elab.arrays));
        try_size("arrays_2d        ", opts.serialize(&elab.arrays_2d));
        try_size("arrays_nd        ", opts.serialize(&elab.arrays_nd));
        try_size("functions        ", opts.serialize(&elab.functions));
        try_size("tasks            ", opts.serialize(&elab.tasks));
        try_size("typedefs         ", opts.serialize(&elab.typedefs));
        try_size("typedef_types    ", opts.serialize(&elab.typedef_types));
        try_size("classes          ", opts.serialize(&elab.classes));
        try_size("specify_delays   ", opts.serialize(&elab.specify_delays));
    }
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
    definitions: &mut crate::hasher::HashMap<String, SourceDefinition>,
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

    // Index every library file's module/interface/program definitions (and
    // non-forward typedefs) by name WITHOUT adopting them yet. §23.3.2: a
    // library directory supplies definitions only to satisfy *unresolved*
    // instantiations. Adopting everything poisons the primary design's global
    // scope — sv-tests points `-I` at ivltests/ (~1000 unrelated single-file
    // tests), whose modules carry internal typedefs/enums (e.g. an unrelated
    // `typedef word word_darray[];`) that then fail the §6.18 base-type check
    // in a test that never mentions them.
    let mut lib: crate::hasher::HashMap<String, SourceDefinition> = Default::default();
    let mut lib_typedefs: Vec<Rc<ast::decl::TypedefDeclaration>> = Vec::new();
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
                    lib.entry(m.name.name.clone())
                        .or_insert_with(|| SourceDefinition::Module(Rc::new(m)));
                }
                ast::Description::Interface(i) => {
                    lib.entry(i.name.name.clone())
                        .or_insert_with(|| SourceDefinition::Interface(Rc::new(i)));
                }
                ast::Description::Program(p) => {
                    lib.entry(p.name.name.clone())
                        .or_insert_with(|| SourceDefinition::Program(Rc::new(p)));
                }
                // A non-forward typedef may fill a forward typedef the primary
                // design actually declared; adopted below, never blanket. A
                // forward typedef, class or package is never pulled from a
                // library dir (that is the scope-poisoning we avoid).
                ast::Description::TypedefDecl(t) if !t.forward => {
                    lib_typedefs.push(Rc::new(t));
                }
                _ => {}
            }
        }
    }

    // Instantiated module/interface/program names inside a definition's body.
    fn instantiations(def: &SourceDefinition, out: &mut std::collections::HashSet<String>) {
        let items = match def {
            SourceDefinition::Module(m) => &m.items,
            SourceDefinition::Interface(i) => &i.items,
            SourceDefinition::Program(p) => &p.items,
            _ => return,
        };
        collect_instantiated_modules(items, out);
    }

    // Adopt only library modules that satisfy an unresolved instantiation
    // reachable from the explicitly-compiled design, transitively (a pulled-in
    // library module may itself instantiate further library modules).
    let mut seed = std::collections::HashSet::new();
    for def in definitions.values() {
        instantiations(def, &mut seed);
    }
    let mut work: Vec<String> = seed.into_iter().collect();
    while let Some(name) = work.pop() {
        if definitions.contains_key(&name) {
            continue;
        }
        if let Some(def) = lib.get(&name) {
            let mut more = std::collections::HashSet::new();
            instantiations(def, &mut more);
            definitions.insert(name.clone(), def.clone());
            for n in more {
                if !definitions.contains_key(&n) {
                    work.push(n);
                }
            }
        }
    }

    // §6.18: fill a forward typedef the primary design declared (`typedef
    // name;`) from a library file's real typedef — only those, never blanket.
    for t in lib_typedefs {
        let name = t.name.name.clone();
        let replace_forward = matches!(
            definitions.get(&name),
            Some(SourceDefinition::Typedef(e)) if e.forward);
        if replace_forward {
            definitions.insert(name, SourceDefinition::Typedef(t));
        }
    }
    Ok(())
}

/// Set the log file for simulation output. Placeholder.
pub fn set_log_file(_path: &str) -> Result<(), String> { Ok(()) }

pub fn log_println(s: &str) { println!("{}", s); }
pub fn log_eprintln(s: &str) { eprintln!("{}", s); }
