//! # sv-parser
//!
//! A SystemVerilog parser targeting IEEE 1800-2017/2023.
//!
//! Provides lexing, preprocessing, and parsing of SystemVerilog source into a
//! typed AST. No simulation or elaboration — just parsing.
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
pub mod strict_check;

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
    CLASS_CONTEXT.with(|s| { s.borrow_mut().pop(); });
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
    let processed = pp.preprocess(source);

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
    let content = std::fs::read_to_string(path)
        .map_err(|e| format!("cannot read '{}': {}", path, e))?;

    // Add the file's parent directory to include dirs
    let mut dirs: Vec<&str> = include_dirs.to_vec();
    let parent = Path::new(path)
        .parent()
        .and_then(|p| p.to_str())
        .unwrap_or(".");
    dirs.push(parent);

    Ok(parse_with_options(&content, &dirs, defines))
}

/// Parse multiple SystemVerilog source strings.
///
/// All sources are preprocessed and parsed independently, then their
/// descriptions are collected into a single `SourceText`.
pub fn parse_multi(sources: &[&str]) -> ParseResult {
    let mut all_descriptions = Vec::new();
    let mut all_errors = Vec::new();
    let mut all_warnings = Vec::new();
    let mut all_source = String::new();

    for source in sources {
        let result = parse(source);
        all_descriptions.extend(result.source.descriptions);
        all_errors.extend(result.errors);
        all_warnings.extend(result.warnings);
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

fn partition_diagnostics(diags: &[diagnostics::Diagnostic]) -> (Vec<diagnostics::Diagnostic>, Vec<diagnostics::Diagnostic>) {
    let mut errors = Vec::new();
    let mut warnings = Vec::new();
    for d in diags {
        match d.severity {
            diagnostics::Severity::Error => errors.push(d.clone()),
            diagnostics::Severity::Warning | diagnostics::Severity::Info => warnings.push(d.clone()),
        }
    }
    (errors, warnings)
}
