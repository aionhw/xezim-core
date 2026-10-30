//! VHDL (IEEE Std 1076-2008, and 1076-2019 with `--std=19`) simulation.
//!
//! VHDL sources are parsed with rust_hdl's `vhdl_lang` parser, vendored with
//! xezim's patches in `vhdl-lang/` (`cst`, the only module that uses it).
//! What the parser leaves to the tool — design
//! libraries, name resolution, types, overload resolution, static
//! evaluation and elaboration — is done here, and the elaborated design is
//! lowered to SystemVerilog AST descriptions that join the design before
//! elaboration, the same hook as UPF (`upf.rs`). The standard packages
//! (`std`, `ieee`) are vendored sources (`libraries`).
//!
//! A design may mix VHDL with SystemVerilog (`foreign`, `lower::mixed`):
//! SV modules instantiate VHDL entities, VHDL components bind to SV modules.

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

/// What the tool reports itself as: the values of the conditional analysis
/// identifiers TOOL_TYPE, TOOL_VENDOR, TOOL_NAME, TOOL_EDITION and
/// TOOL_VERSION (VHDL-2019 §24.2) and of the STD.ENV functions of the same
/// names (§16.5).
pub const TOOL_TYPE: &str = "SIMULATION";
pub const TOOL_VENDOR: &str = "xezim";
pub const TOOL_NAME: &str = "xezim";
pub const TOOL_EDITION: &str = "";
pub const TOOL_VERSION: &str = env!("CARGO_PKG_VERSION");

/// The operating-system services of STD.ENV (VHDL-2019 §16.5), for the
/// simulator's `$__vh_os(op, arg)`: each result is a string (numbers and
/// booleans in decimal). Unknown operations give "".
pub fn os_call(op: &str, arg: &str) -> String {
    use std::path::Path;
    let b = |x: bool| (x as u8).to_string();
    match op {
        "getenv" => std::env::var(arg).unwrap_or_default(),
        // Seconds since the epoch, with a fraction.
        "epoch" => std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| format!("{:.6}", d.as_secs_f64()))
            .unwrap_or_else(|_| "0".into()),
        // The local time's offset from UTC in seconds at time `arg`.
        "tzoffset" => tz_offset(arg.trim().parse::<f64>().unwrap_or(0.0) as i64).to_string(),
        "cwd" => std::env::current_dir()
            .map(|p| p.to_string_lossy().into_owned())
            .unwrap_or_default(),
        "chdir" => {
            let p = Path::new(arg);
            if !p.exists() {
                return "notfound".into();
            }
            if !p.is_dir() {
                return "notdir".into();
            }
            io_status(std::env::set_current_dir(p))
        }
        "exists" => b(Path::new(arg).exists()),
        "isdir" => b(Path::new(arg).is_dir()),
        "isfile" => b(Path::new(arg).is_file()),
        "canonical" => std::fs::canonicalize(arg)
            .map(|p| p.to_string_lossy().into_owned())
            .unwrap_or_default(),
        // The names in a directory, sorted (with "." and ".."), one per line.
        "list" => match std::fs::read_dir(arg) {
            Ok(rd) => {
                let mut names: Vec<String> = rd
                    .filter_map(|e| e.ok())
                    .map(|e| e.file_name().to_string_lossy().into_owned())
                    .collect();
                names.push(".".into());
                names.push("..".into());
                names.sort();
                names.join("\n")
            }
            Err(_) => String::new(),
        },
        // Statuses: "ok", "exists", "notfound", "notdir", "notempty",
        // "denied", "error" (each STD.ENV status type has some of them).
        "mkdir" | "mkdirs" => {
            let p = Path::new(arg);
            if p.exists() {
                return "exists".into();
            }
            let r = if op == "mkdirs" {
                std::fs::create_dir_all(p)
            } else {
                std::fs::create_dir(p)
            };
            io_status(r)
        }
        "rmdir" | "rmdirs" => {
            let p = Path::new(arg);
            if !p.is_dir() {
                return "notdir".into();
            }
            if op == "rmdir" && std::fs::read_dir(p).is_ok_and(|mut d| d.next().is_some()) {
                return "notempty".into();
            }
            let r = if op == "rmdirs" {
                std::fs::remove_dir_all(p)
            } else {
                std::fs::remove_dir(p)
            };
            io_status(r)
        }
        "rm" => {
            let p = Path::new(arg);
            if !p.is_file() {
                return "notfound".into();
            }
            io_status(std::fs::remove_file(p))
        }
        _ => String::new(),
    }
}

fn io_status(r: std::io::Result<()>) -> String {
    match r {
        Ok(()) => "ok".into(),
        Err(e) if e.kind() == std::io::ErrorKind::PermissionDenied => "denied".into(),
        Err(_) => "error".into(),
    }
}

/// The local time zone's offset from UTC in seconds at Unix time `t`
/// (`localtime_r`'s `tm_gmtoff`; 0 where it is not known).
fn tz_offset(t: i64) -> i64 {
    #[cfg(unix)]
    {
        // SAFETY: localtime_r writes only the `tm` it is given.
        unsafe {
            let tt = t as libc::time_t;
            let mut tm: libc::tm = std::mem::zeroed();
            if !libc::localtime_r(&tt, &mut tm).is_null() {
                return i64::from(tm.tm_gmtoff);
            }
        }
    }
    let _ = t;
    0
}

/// The VHDL revision a design is analysed as (`--std=08`, `--std=19`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum VhdlStd {
    #[default]
    V2008,
    V2019,
}

impl VhdlStd {
    /// The revision named by a `--std=` value (`08`, `2008`, `19`, `2019`).
    pub fn from_arg(v: &str) -> Option<VhdlStd> {
        match v {
            "08" | "2008" => Some(VhdlStd::V2008),
            "19" | "2019" => Some(VhdlStd::V2019),
            _ => None,
        }
    }
}

/// Run options, as GHDL's `--std=`, `--ieee-asserts=` and `--assert-level=`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct VhdlOptions {
    /// Assertions of the IEEE library: 0 shown, 1 not shown, 2 not shown
    /// at time 0.
    pub ieee_asserts: u8,
    /// The severity (0 note .. 3 failure; 4 none) from which an assertion
    /// stops the simulation.
    pub assert_level: u8,
    /// The revision of the language.
    pub std: VhdlStd,
}

impl Default for VhdlOptions {
    fn default() -> Self {
        VhdlOptions {
            ieee_asserts: 0,
            assert_level: 3,
            std: VhdlStd::V2008,
        }
    }
}

#[derive(Clone, Default)]
struct Config {
    files: Vec<VhdlFile>,
    options: VhdlOptions,
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
    configure_with(files, VhdlOptions::default());
}

/// `configure`, with run options.
pub fn configure_with(files: Vec<VhdlFile>, options: VhdlOptions) {
    *CONFIG.lock().unwrap_or_else(|e| e.into_inner()) = if files.is_empty() {
        None
    } else {
        Some(Config { files, options })
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
    cfg.options.hash(&mut h);
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
        let p = cst::parse_std(cst::SourceFile::new(f.path.clone(), text), cfg.options.std);
        for w in &p.warnings {
            crate::log_eprintln(&p.file.render_warning(w));
        }
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
    let mut analysed = sema::analyze(files, vhdl_top.as_deref(), &mixed, cfg.options.std)
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
    let lowered = lower::lower(&analysed, &names, cfg.options)
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

/// Analyse VHDL-2008 sources (a test hook): the rendered errors.
pub fn check_design(sources: &[(&str, &str, &[u8])]) -> Vec<String> {
    check_design_std(sources, VhdlStd::V2008)
}

/// Analyse VHDL sources of revision `std` (a test hook): the rendered errors.
pub fn check_design_std(sources: &[(&str, &str, &[u8])], std: VhdlStd) -> Vec<String> {
    let mut files = Vec::new();
    for (lib, path, text) in sources {
        let p = cst::parse_std(cst::SourceFile::new(path.to_string(), text.to_vec()), std);
        if !p.errors.is_empty() {
            return p.errors.iter().map(|d| p.file.render(d)).collect();
        }
        files.push((lib.to_string(), p));
    }
    match sema::analyze(files, None, &sema::Mixed::default(), std) {
        Ok(_) => Vec::new(),
        Err(e) => e,
    }
}

/// Parse a VHDL source (a test hook): the syntax errors, rendered.
pub fn check_syntax(path: &str, text: &[u8]) -> Vec<String> {
    let p = cst::parse(cst::SourceFile::new(path.to_string(), text.to_vec()));
    p.errors.iter().map(|d| p.file.render(d)).collect()
}
