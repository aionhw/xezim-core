//! # sv-parser
//!
//! A SystemVerilog parser targeting IEEE 1800-2017/2023.
//!
//! Provides lexing, preprocessing, and parsing of SystemVerilog source into a
//! typed AST. No simulation or elaboration — just parsing.
//!
//! The [`systemc`] module is a second front end for SystemC (C++) designs,
//! RTL and TLM-2.0, with an AST of its own.
//!
//! ## Quick start
//!
//! ```rust
//! use sv_parser::{parse, parse_file};
//!
//! // Parse a source string
//! let result = parse("module top; endmodule");
//! assert!(result.errors.is_empty());
//! assert_eq!(result.source.descriptions.len(), 1);
//!
//! // Parse with preprocessing (include dirs, defines)
//! let result = parse_file("design.sv", &["./includes"], &[("SYNTHESIS", "1")]);
//! ```

pub mod ast;
pub mod diagnostics;
pub mod lexer;
pub mod parse;
pub mod preprocessor;
pub mod source_map;
pub mod strict_check;
pub mod systemc;

use std::sync::atomic::{AtomicBool, Ordering};

/// Process-wide gate for IEEE 1800-2023 syntax extensions. Off by default.
/// Enabled by the `--sv2023` CLI flag; tests opt in via `set_sv2023`.
static SV2023_ENABLED: AtomicBool = AtomicBool::new(false);

/// Enable or disable IEEE 1800-2023 syntax extensions for subsequent
/// lex/parse/simulate calls in this process.
/// min:typ:max delay selection for specify-path triplets (`(2:5:9)`).
/// 0 = min, 1 = typ (default, commercial default), 2 = max. Set from the CLI's
/// `+mindelays`/`+typdelays`/`+maxdelays` before parsing.
static DELAY_SELECT: std::sync::atomic::AtomicU8 = std::sync::atomic::AtomicU8::new(1);

pub fn set_delay_select(sel: u8) {
    DELAY_SELECT.store(sel.min(2), std::sync::atomic::Ordering::Relaxed);
}

pub fn delay_select() -> u8 {
    DELAY_SELECT.load(std::sync::atomic::Ordering::Relaxed)
}

/// What the parsed sources can name through a path, collected from the token
/// streams of every file parsed in this process (see [`reference_census`]).
///
/// The elaborator substitutes an instance's input port by its actual inside
/// the child, so afterwards only a DOTTED reference (`u.p`, `$root.t.u.p`,
/// `u[3].v.p`), a string-keyed lookup (VPI, a DPI backdoor, a dump) or an SDF
/// annotation can still reach the port's own net. The census is what lets it
/// drop a port net nobody can reach.
#[derive(Debug, Default, Clone)]
pub struct ReferenceCensus {
    /// Every identifier written right after a `.` (`a.b.c` adds `b` and `c`),
    /// except the `.name(` of a named port, parameter or argument binding.
    /// Over-approximates on purpose: struct members, methods and interface
    /// signals land here too.
    pub dotted: CensusSet,
    /// Every identifier spelled in code that runs in the scope of whatever
    /// instance calls it rather than an instance of its own: class bodies,
    /// packages, and the compilation unit outside any design unit. A bare
    /// name there that the enclosing code does not declare resolves at run
    /// time under the calling instance's scope, so it can reach that
    /// instance's own port nets.
    pub unit_idents: CensusSet,
    /// Every system task or function name spelled (`$dumpvars`).
    pub system_names: CensusSet,
    /// An `import "DPI…"` or `export "DPI…"` declaration was seen.
    pub dpi: bool,
}

/// FNV-1a: the census hashes every dotted name the sources spell, where
/// SipHash cost more than the scan itself; membership only, so no ordering
/// or flooding concern applies.
#[derive(Default, Clone, Copy)]
pub struct CensusHasher(u64);

impl std::hash::Hasher for CensusHasher {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, bytes: &[u8]) {
        let mut h = if self.0 == 0 {
            0xcbf2_9ce4_8422_2325
        } else {
            self.0
        };
        for &b in bytes {
            h ^= b as u64;
            h = h.wrapping_mul(0x0000_0100_0000_01b3);
        }
        self.0 = h;
    }
}

/// A string set keyed by [`CensusHasher`].
pub type CensusSet = std::collections::HashSet<String, std::hash::BuildHasherDefault<CensusHasher>>;

static REFERENCE_CENSUS: std::sync::Mutex<Option<ReferenceCensus>> = std::sync::Mutex::new(None);

/// Add one token stream to the process-wide [`ReferenceCensus`]. Called for
/// every stream the parser is built over, so nothing parsed escapes it.
pub fn record_reference_census(tokens: &[lexer::Token]) {
    use lexer::token::TokenKind as K;
    let mut guard = REFERENCE_CENSUS.lock().unwrap_or_else(|e| e.into_inner());
    let census = guard.get_or_insert_with(ReferenceCensus::default);
    // A DPI declaration anywhere rules the elision out for the whole design,
    // so nothing else the census could learn matters any more: stop
    // scanning (a UVM testbench declares its DPI imports before its
    // thousands of classes).
    if census.dpi {
        return;
    }
    fn bare(t: &str) -> &str {
        t.strip_prefix('\\').unwrap_or(t).trim_end()
    }
    // Enclosing regions for `unit_idents`: design units (module, interface,
    // program, checker, primitive, config) versus classes and packages.
    // Recording too much only keeps more ports, so every uncertain case
    // leans that way: an end keyword closes EVERY open design unit, and a
    // keyword that may not open one (`virtual interface`, `extern module`,
    // `interface class`, a forward `typedef class`) opens nothing.
    #[derive(Clone, Copy, PartialEq)]
    enum Region {
        Unit,
        Class,
        Package,
    }
    let mut regions: Vec<Region> = Vec::new();
    fn close(regions: &mut Vec<Region>, kind: Region) {
        if let Some(at) = regions.iter().rposition(|r| *r == kind) {
            regions.truncate(at);
        }
    }
    for (i, tok) in tokens.iter().enumerate() {
        let prev = i.checked_sub(1).map(|p| tokens[p].kind);
        match tok.kind {
            K::KwModule
            | K::KwMacromodule
            | K::KwProgram
            | K::KwChecker
            | K::KwPrimitive
            | K::KwConfig => {
                if prev != Some(K::KwExtern) {
                    regions.push(Region::Unit);
                }
            }
            K::KwInterface => {
                let next = tokens.get(i + 1).map(|t| t.kind);
                if !matches!(prev, Some(K::KwVirtual | K::KwExtern))
                    && next != Some(K::KwClass)
                    && !regions.contains(&Region::Unit)
                {
                    regions.push(Region::Unit);
                }
            }
            K::KwClass => {
                if prev != Some(K::KwTypedef) {
                    regions.push(Region::Class);
                }
            }
            K::KwPackage => regions.push(Region::Package),
            K::KwEndmodule
            | K::KwEndprogram
            | K::KwEndinterface
            | K::KwEndchecker
            | K::KwEndprimitive
            | K::KwEndconfig => {
                if let Some(at) = regions.iter().position(|r| *r == Region::Unit) {
                    regions.truncate(at);
                }
            }
            K::KwEndclass => close(&mut regions, Region::Class),
            K::KwEndpackage => close(&mut regions, Region::Package),
            K::Identifier | K::EscapedIdentifier => {
                let unit_level =
                    regions.last() != Some(&Region::Unit) || regions.contains(&Region::Class);
                if unit_level {
                    let n = bare(&tok.text);
                    if !census.unit_idents.contains(n) {
                        census.unit_idents.insert(n.to_string());
                    }
                }
            }
            _ => {}
        }
        match tok.kind {
            K::Dot => {
                let named_binding = i > 0 && matches!(tokens[i - 1].kind, K::LParen | K::Comma);
                if named_binding {
                    continue;
                }
                if let Some(next) = tokens.get(i + 1) {
                    if matches!(next.kind, K::Identifier | K::EscapedIdentifier) {
                        let n = bare(&next.text);
                        if !census.dotted.contains(n) {
                            census.dotted.insert(n.to_string());
                        }
                    }
                }
            }
            // `\a.b ` is ONE identifier whose name holds a dot; the flat
            // namespace cannot tell it from the path `a.b`, so count every
            // component after a dot as dotted too.
            K::EscapedIdentifier if tok.text.contains('.') => {
                for part in bare(&tok.text).split('.').skip(1) {
                    census.dotted.insert(part.to_string());
                }
            }
            K::SystemIdentifier => {
                if !census.system_names.contains(tok.text.as_str()) {
                    census.system_names.insert(tok.text.clone());
                }
            }
            K::KwImport | K::KwExport => {
                if let Some(next) = tokens.get(i + 1) {
                    if matches!(next.kind, K::StringLiteral) && next.text.contains("DPI") {
                        census.dpi = true;
                        return;
                    }
                }
            }
            _ => {}
        }
    }
}

/// A copy of the process-wide [`ReferenceCensus`] (empty when nothing has
/// been parsed).
pub fn reference_census() -> ReferenceCensus {
    REFERENCE_CENSUS
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .clone()
        .unwrap_or_default()
}

/// Reserved storage name for a compilation-unit (`$unit`) declaration that a
/// module SHADOWS with a declaration of its own (§3.12.1). The two are
/// distinct objects, but the elaborated namespace is flat, so the $unit copy
/// is kept under this name — which no user identifier can spell — and
/// `$unit::name` resolves to it.
pub fn unit_scope_name(name: &str) -> String {
    format!("$unit::{}", name)
}

/// The bare name behind [`unit_scope_name`], or `None` for anything else.
pub fn strip_unit_scope_name(name: &str) -> Option<&str> {
    name.strip_prefix("$unit::")
}

pub fn set_sv2023(enabled: bool) {
    SV2023_ENABLED.store(enabled, Ordering::Relaxed);
}

/// Whether IEEE 1800-2023 syntax extensions are currently enabled.
pub fn is_sv2023() -> bool {
    SV2023_ENABLED.load(Ordering::Relaxed)
}

/// Process-wide gate for "strict" negative-test diagnostics — the extra
/// validation that lets xezim *reject* illegal constructs the LRM forbids
/// (bad `\`line`/`\`define`/`\`pragma` directives, illegal sized-literal
/// signs, enum type-checking violations, etc.). ON by default; the
/// `--no-strict` CLI flag turns it off (lenient: accept and move on).
static STRICT_CHECKS_ENABLED: AtomicBool = AtomicBool::new(true);

/// Enable or disable strict negative-test diagnostics for subsequent
/// lex/parse/preprocess/elaborate calls in this process.
pub fn set_strict_checks(enabled: bool) {
    STRICT_CHECKS_ENABLED.store(enabled, Ordering::Relaxed);
}

/// Whether strict negative-test diagnostics are currently enabled (default true).
pub fn strict_checks() -> bool {
    STRICT_CHECKS_ENABLED.load(Ordering::Relaxed)
}

thread_local! {
    /// Stack of enclosing class names, maintained by the parser while
    /// parsing class bodies. Used to resolve `type(this)` (IEEE
    /// 1800-2023 §6.20.2.1) to the current class at parse time.
    static CLASS_CONTEXT: std::cell::RefCell<Vec<String>> =
        std::cell::RefCell::new(Vec::new());

    /// Sticky flag set by the preprocessor when it sees
    /// `` `default_nettype none ``. The elaborator's implicit-net
    /// auto-creation pass consults it to reject implicit-net
    /// usage inside the `none` region.
    static DEFAULT_NETTYPE_NONE_SEEN: std::cell::Cell<bool> =
        std::cell::Cell::new(false);
}

pub(crate) fn push_class_context(name: String) {
    CLASS_CONTEXT.with(|s| s.borrow_mut().push(name));
}

pub(crate) fn pop_class_context() {
    CLASS_CONTEXT.with(|s| {
        s.borrow_mut().pop();
    });
}

pub(crate) fn current_class_name() -> Option<String> {
    CLASS_CONTEXT.with(|s| s.borrow().last().cloned())
}

thread_local! {
    /// §22.9 `unconnected_drive`: modules declared while the directive is
    /// active, mapped to `true` for pull1 / `false` for pull0. Recorded by
    /// the preprocessor, consumed by elaboration when an INPUT port is left
    /// unconnected (which then reads the pulled value instead of Z).
    static UNCONNECTED_DRIVE_MODULES: std::cell::RefCell<std::collections::HashMap<String, bool>> =
        std::cell::RefCell::new(std::collections::HashMap::new());
}

pub fn record_unconnected_drive(module: &str, pull1: bool) {
    UNCONNECTED_DRIVE_MODULES.with(|m| {
        m.borrow_mut().entry(module.to_string()).or_insert(pull1);
    });
}

pub fn unconnected_drive_for(module: &str) -> Option<bool> {
    UNCONNECTED_DRIVE_MODULES.with(|m| m.borrow().get(module).copied())
}

/// Every module the preprocessor recorded under `unconnected_drive` on this
/// thread, so a design preprocessed on one thread can be elaborated on
/// another (see `record_unconnected_drive`).
pub fn unconnected_drive_snapshot() -> Vec<(String, bool)> {
    UNCONNECTED_DRIVE_MODULES.with(|m| m.borrow().iter().map(|(k, v)| (k.clone(), *v)).collect())
}

pub fn set_default_nettype_none_seen(v: bool) {
    DEFAULT_NETTYPE_NONE_SEEN.with(|c| c.set(v));
}

pub fn default_nettype_none_seen() -> bool {
    DEFAULT_NETTYPE_NONE_SEEN.with(|c| c.get())
}

#[cfg(feature = "serde")]
pub mod serde;

#[cfg(test)]
mod tests;

use std::path::{Path, PathBuf};

/// Result of parsing a SystemVerilog source.
pub struct ParseResult {
    /// The original (preprocessed) source text.
    pub source_text: String,
    /// The parsed AST.
    pub source: ast::SourceText,
    /// Parse errors (empty if successful).
    pub errors: Vec<diagnostics::Diagnostic>,
    /// Parse warnings.
    pub warnings: Vec<diagnostics::Diagnostic>,
    /// Preprocessor errors (missing `include files, illegal directives),
    /// each already rendered with its location.
    pub preprocess_errors: Vec<String>,
    /// Where each line of `source_text` came from; see
    /// [`diagnostics::render_diagnostic`].
    pub line_map: Option<source_map::LineMap>,
}

/// Parse a SystemVerilog source string.
///
/// Returns the parsed AST and any diagnostics.
pub fn parse(source: &str) -> ParseResult {
    parse_with_options(source, &[], &[])
}

/// Parse a SystemVerilog source string with preprocessor options.
///
/// `include_dirs`: directories to search for `include files.
/// `defines`: predefined macros as (name, value) pairs.
pub fn parse_with_options(
    source: &str,
    include_dirs: &[&str],
    defines: &[(&str, &str)],
) -> ParseResult {
    parse_impl(source, None, include_dirs, defines)
}

fn parse_impl(
    source: &str,
    path: Option<&Path>,
    include_dirs: &[&str],
    defines: &[(&str, &str)],
) -> ParseResult {
    // Preprocess
    let mut pp = preprocessor::Preprocessor::new();
    for dir in include_dirs {
        pp.add_include_dir(PathBuf::from(dir));
    }
    for (name, value) in defines {
        pp.define(
            name.to_string(),
            preprocessor::MacroDef {
                name: name.to_string(),
                params: None,
                body: value.to_string(),
            },
        );
    }
    let processed = match path {
        Some(p) => pp.preprocess_file(source, Some(p)),
        None => pp.preprocess(source),
    };
    let line_map = pp.take_line_map();

    // Lex
    let tokens = lexer::Lexer::new(&processed).tokenize();

    // Parse
    let mut parser = parse::Parser::new(tokens);
    let source_text = parser.parse_source_text();

    let (errors, warnings) = partition_diagnostics(parser.diagnostics());

    ParseResult {
        source_text: processed,
        source: source_text,
        errors,
        warnings,
        preprocess_errors: pp.errors().to_vec(),
        line_map,
    }
}

/// Parse a SystemVerilog file from disk.
///
/// Resolves `include directives relative to the file's directory and `include_dirs`.
/// `defines`: predefined macros as (name, value) pairs.
pub fn parse_file(
    path: &str,
    include_dirs: &[&str],
    defines: &[(&str, &str)],
) -> Result<ParseResult, String> {
    let content =
        std::fs::read_to_string(path).map_err(|e| format!("cannot read '{}': {}", path, e))?;

    // Add the file's parent directory to include dirs
    let mut dirs: Vec<&str> = include_dirs.to_vec();
    let parent = Path::new(path)
        .parent()
        .and_then(|p| p.to_str())
        .unwrap_or(".");
    dirs.push(parent);

    Ok(parse_impl(&content, Some(Path::new(path)), &dirs, defines))
}

/// Parse multiple SystemVerilog source strings.
///
/// All sources are preprocessed and parsed independently, then their
/// descriptions are collected into a single `SourceText`.
pub fn parse_multi(sources: &[&str]) -> ParseResult {
    let mut all_descriptions = Vec::new();
    let mut all_errors = Vec::new();
    let mut all_warnings = Vec::new();
    let mut all_pp_errors = Vec::new();
    let mut all_source = String::new();

    for source in sources {
        let result = parse(source);
        all_descriptions.extend(result.source.descriptions);
        all_errors.extend(result.errors);
        all_warnings.extend(result.warnings);
        all_pp_errors.extend(result.preprocess_errors);
        all_source.push_str(&result.source_text);
    }

    ParseResult {
        source_text: all_source,
        source: ast::SourceText {
            descriptions: all_descriptions,
            span: ast::Span::dummy(),
        },
        errors: all_errors,
        warnings: all_warnings,
        preprocess_errors: all_pp_errors,
        // Spans index each source's own text; there is no one map.
        line_map: None,
    }
}

/// Tokenize a SystemVerilog source string (lex only, no parsing).
pub fn tokenize(source: &str) -> Vec<lexer::Token> {
    let mut pp = preprocessor::Preprocessor::new();
    let processed = pp.preprocess(source);
    lexer::Lexer::new(&processed).tokenize()
}

/// Preprocess a SystemVerilog source string (macro expansion, include handling).
pub fn preprocess(source: &str) -> String {
    let mut pp = preprocessor::Preprocessor::new();
    pp.preprocess(source)
}

fn partition_diagnostics(
    diags: &[diagnostics::Diagnostic],
) -> (Vec<diagnostics::Diagnostic>, Vec<diagnostics::Diagnostic>) {
    let mut errors = Vec::new();
    let mut warnings = Vec::new();
    for d in diags {
        match d.severity {
            diagnostics::Severity::Error => errors.push(d.clone()),
            diagnostics::Severity::Warning | diagnostics::Severity::Info => {
                warnings.push(d.clone())
            }
        }
    }
    (errors, warnings)
}
