//! VHDL (IEEE Std 1076-2008) simulation.
//!
//! VHDL sources are parsed with the `vhdl_syntax` crate (`cst`, the only
//! module that uses it). What the parser leaves to the tool — design
//! libraries, name resolution, types, overload resolution, static
//! evaluation and elaboration — is done here, and the elaborated design is
//! lowered to SystemVerilog AST descriptions that join the design before
//! elaboration, the same hook as UPF (`upf.rs`). The standard packages
//! (`std`, `ieee`) are vendored sources (`libraries`).
//!
//! Status: parsing and located syntax errors. Analysis and simulation of
//! VHDL designs are not implemented yet.

pub mod ast;
mod cst;
mod foreign;
pub mod libraries;
mod lower;
pub mod sema;

pub use lower::real_image;

use std::sync::Mutex;

use crate::ast::Description;

/// A VHDL source file and the design library it is analysed into.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct VhdlFile {
    pub path: String,
    pub library: String,
}

#[derive(Clone, Default)]
struct Config {
    files: Vec<VhdlFile>,
}

static CONFIG: Mutex<Option<Config>> = Mutex::new(None);

/// Whether `path` names a VHDL source (`.vhd`, `.vhdl`).
pub fn is_vhdl_path(path: &str) -> bool {
    let lower = path.to_ascii_lowercase();
    lower.ends_with(".vhd") || lower.ends_with(".vhdl")
}

/// The VHDL sources of the design, in command-line order. Call before
/// elaboration; an empty list clears the configuration.
pub fn configure(files: Vec<VhdlFile>) {
    *CONFIG.lock().unwrap_or_else(|e| e.into_inner()) = if files.is_empty() {
        None
    } else {
        Some(Config { files })
    };
}

pub fn configured() -> bool {
    CONFIG.lock().unwrap_or_else(|e| e.into_inner()).is_some()
}

/// A digest of the VHDL sources (names, libraries and contents) for the
/// compile cache, or `None` without VHDL sources.
pub fn cache_digest() -> Option<u64> {
    use std::hash::{BuildHasher, Hash, Hasher};
    let cfg = CONFIG.lock().unwrap_or_else(|e| e.into_inner()).clone()?;
    let mut h = crate::hasher::DeterministicState::default().build_hasher();
    for f in &cfg.files {
        f.hash(&mut h);
        std::fs::read(&f.path).ok().hash(&mut h);
    }
    Some(h.finish())
}

/// Parse the configured VHDL sources and add the lowered design to
/// `descriptions`. Returns the top module to use when none was named.
///
/// In a mixed-language design the SV instances of VHDL entities are
/// pointed at modules lowered for them, and the VHDL top level is the top
/// only when no SV module is left uninstantiated.
pub fn inject(
    descriptions: &mut Vec<Description>,
    top: Option<&str>,
) -> Result<Option<String>, String> {
    let Some(cfg) = CONFIG.lock().unwrap_or_else(|e| e.into_inner()).clone() else {
        return Ok(None);
    };
    let mut msgs = Vec::new();
    let mut parsed = Vec::new();
    for f in &cfg.files {
        let text =
            std::fs::read(&f.path).map_err(|e| format!("VHDL: cannot read '{}': {}", f.path, e))?;
        let p = cst::parse(cst::SourceFile::new(f.path.clone(), text));
        msgs.extend(p.errors.iter().map(|d| p.file.render(d)));
        debug_assert!(!p.errors.is_empty() || p.ast.is_some());
        parsed.push(p);
    }
    if !msgs.is_empty() {
        return Err(format!(
            "{}\nVHDL: {} syntax error(s)",
            msgs.join("\n"),
            msgs.len()
        ));
    }
    if std::env::var_os("XEZIM_VHDL_DUMP").is_some() {
        for (f, p) in cfg.files.iter().zip(&parsed) {
            for u in cst::unit_summary(p) {
                eprintln!("{} [{}]: {}", f.path, f.library, u);
            }
        }
    }
    // The SV side: its modules, and its instances of VHDL entities.
    let mut entities = std::collections::BTreeSet::new();
    for p in &parsed {
        for u in p.ast.iter().flat_map(|a| &a.units) {
            if let ast::LibraryUnit::Entity(e) = &u.unit {
                entities.insert(e.name.name.clone());
            }
        }
    }
    let sv_modules = foreign::sv_modules(descriptions);
    let roots = foreign::root_requests(descriptions, &entities)?;
    // A named VHDL top; SV tops are named as SV modules.
    let vhdl_top = top
        .map(|t| t.to_ascii_lowercase())
        .filter(|t| entities.contains(t) && !sv_modules.contains_key(t));
    let mixed = sema::Mixed {
        roots: roots.clone(),
        sv_modules: sv_modules.clone(),
    };
    let files = cfg
        .files
        .iter()
        .map(|f| f.library.clone())
        .zip(parsed)
        .collect();
    let mut analysed = sema::analyze(files, vhdl_top.as_deref(), &mixed)
        .map_err(|e| format!("{}\nVHDL: {} error(s)", e.join("\n"), e.len()))?;
    // An SV top (named, or an SV module nothing instantiates) leaves the
    // VHDL top level out unless that is named.
    let from_vhdl: std::collections::HashSet<String> = analysed
        .design
        .archs
        .iter()
        .flat_map(|a| a.foreign.iter().map(|f| f.module.clone()))
        .collect();
    if vhdl_top.is_none() && (top.is_some() || has_sv_top(descriptions, &from_vhdl)) {
        analysed.top = None;
    }
    // A module per root, named after its entity (with a suffix for a
    // second binding, or a clash with an SV module).
    let mut names: Vec<String> = Vec::new();
    for r in &roots {
        let base = lower_ident(&r.entity);
        let mut name = base.clone();
        let mut k = 1;
        while sv_modules.contains_key(&name.to_ascii_lowercase()) || names.contains(&name) {
            name = format!("{}__vh{}", base, k);
            k += 1;
        }
        names.push(name);
    }
    let lowered = lower::lower(&analysed, &names)
        .map_err(|e| format!("{}\nVHDL: {} error(s)", e.join("\n"), e.len()))?;
    if std::env::var_os("XEZIM_VHDL_DUMP").is_some() {
        eprintln!("{}", lowered.sv);
    }
    foreign::rewrite(descriptions, &roots, &names);
    descriptions.extend(parse_generated(&lowered.sv)?);
    Ok(lowered.top)
}

/// Whether some SV module is a top: neither an SV module nor the VHDL
/// design (`from_vhdl`) instantiates it.
fn has_sv_top(descs: &[Description], from_vhdl: &std::collections::HashSet<String>) -> bool {
    let mut inst = from_vhdl.clone();
    for d in descs {
        if let Description::Module(m) = d {
            crate::collect_instantiated_modules(&m.items, &mut inst);
        }
    }
    descs
        .iter()
        .any(|d| matches!(d, Description::Module(m) if !inst.contains(&m.name.name)))
}

/// The SV name of a VHDL identifier.
fn lower_ident(s: &str) -> String {
    lower::sv_ident(&s.to_ascii_lowercase())
}

/// Base of the spans of generated SystemVerilog, far above any source
/// file's, so span-keyed simulator caches never collide with them.
const GENERATED_SPAN_BASE: usize = 1 << 41;

/// Parse the lowered design's SystemVerilog text.
fn parse_generated(text: &str) -> Result<Vec<Description>, String> {
    let mut tokens = crate::sv_parser::lexer::Lexer::new(text).tokenize();
    for t in &mut tokens {
        t.span.start += GENERATED_SPAN_BASE;
        t.span.end += GENERATED_SPAN_BASE;
    }
    let mut parser = crate::sv_parser::parse::Parser::new(tokens);
    let source = parser.parse_source_text();
    let errors: Vec<String> = parser
        .diagnostics()
        .iter()
        .filter(|d| matches!(d.severity, crate::sv_parser::diagnostics::Severity::Error))
        .take(5)
        .map(|e| {
            let at = e.span.start.saturating_sub(GENERATED_SPAN_BASE);
            let line = text[..at.min(text.len())].matches('\n').count() + 1;
            format!("line {}: {}", line, e.message)
        })
        .collect();
    if !errors.is_empty() {
        return Err(format!(
            "VHDL: internal error: the lowered SystemVerilog does not parse (XEZIM_VHDL_DUMP=1 shows it):\n{}",
            errors.join("\n")
        ));
    }
    Ok(source.descriptions)
}

/// Analyse VHDL sources (a test hook): the rendered errors.
pub fn check_design(sources: &[(&str, &str, &[u8])]) -> Vec<String> {
    let mut files = Vec::new();
    for (lib, path, text) in sources {
        let p = cst::parse(cst::SourceFile::new(path.to_string(), text.to_vec()));
        if !p.errors.is_empty() {
            return p.errors.iter().map(|d| p.file.render(d)).collect();
        }
        files.push((lib.to_string(), p));
    }
    match sema::analyze(files, None, &sema::Mixed::default()) {
        Ok(_) => Vec::new(),
        Err(e) => e,
    }
}

/// Parse a VHDL source (a test hook): the syntax errors, rendered.
pub fn check_syntax(path: &str, text: &[u8]) -> Vec<String> {
    let p = cst::parse(cst::SourceFile::new(path.to_string(), text.to_vec()));
    p.errors.iter().map(|d| p.file.render(d)).collect()
}
