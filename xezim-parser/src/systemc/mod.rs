//! # SystemC front end
//!
//! Parses SystemC designs — the RTL subset and TLM-2.0 (IEEE 1666-2023) —
//! into a typed SystemC AST ([`ast`]). Parse-only, like the rest of this
//! crate: names and types are not resolved and nothing is elaborated.
//!
//! SystemC is a C++ class library, so the input is C++. The front end
//! accepts the C++ subset SystemC designs and testbenches are written in
//! (classes, templates, overloaded operators, lambdas, the usual statements)
//! and recognizes the SystemC registration macros — `SC_MODULE`, `SC_CTOR`,
//! `SC_HAS_PROCESS`, `SC_METHOD`/`SC_THREAD`/`SC_CTHREAD`, `sensitive`,
//! `dont_initialize`, `reset_signal_is`, `SC_NAMED` — as syntax of their
//! own. The SystemC/TLM library headers are therefore never read:
//! `#include <systemc>` is skipped, while a design's own headers are
//! included and macro-expanded normally ([`preprocess`]).
//!
//! ```rust
//! use sv_parser::systemc;
//!
//! let r = systemc::parse(r#"
//!     #include <systemc>
//!     SC_MODULE(dff) {
//!         sc_core::sc_in<bool> clk, d;
//!         sc_core::sc_out<bool> q;
//!         void run() { q.write(d.read()); }
//!         SC_CTOR(dff) { SC_METHOD(run); sensitive << clk.pos(); }
//!     };
//! "#);
//! assert!(r.errors.is_empty());
//! let dff = r.unit.find_class("dff").unwrap();
//! assert_eq!(dff.ports().len(), 3);
//! assert_eq!(dff.processes()[0].func.name, "run");
//! ```

pub mod ast;
pub mod classify;
pub mod lexer;
pub mod parser;
pub mod preprocess;
pub mod token;

use crate::diagnostics::{Location, Severity, locate, render};
use token::ScSpan;

/// A file that contributed source: the main file, an included header or a
/// command-line definition. Indexed by [`ScSpan::file`].
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ScFile {
    pub path: String,
    pub text: String,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ScDiagnostic {
    pub severity: Severity,
    pub message: String,
    pub span: ScSpan,
}

impl ScDiagnostic {
    pub fn error(message: impl Into<String>, span: ScSpan) -> Self {
        Self {
            severity: Severity::Error,
            message: message.into(),
            span,
        }
    }

    pub fn warning(message: impl Into<String>, span: ScSpan) -> Self {
        Self {
            severity: Severity::Warning,
            message: message.into(),
            span,
        }
    }
}

/// Result of parsing a SystemC source.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ScParseResult {
    /// Every file read, in the order first seen; spans index into these.
    pub files: Vec<ScFile>,
    pub unit: ast::TranslationUnit,
    /// Preprocessor and parse errors (empty if successful).
    pub errors: Vec<ScDiagnostic>,
    pub warnings: Vec<ScDiagnostic>,
}

impl ScParseResult {
    /// Where `span` is: file, line and column, plus the source line for
    /// context.
    pub fn locate(&self, span: ScSpan) -> Location {
        match self.files.get(span.file as usize) {
            Some(f) => locate(&f.text, None, &f.path, span.bytes()),
            None => locate("", None, "<unknown>", span.bytes()),
        }
    }

    /// Render `diag` like every other diagnostic of this crate:
    /// `file:line:col: severity: message`, the source line and a caret.
    pub fn render(&self, diag: &ScDiagnostic) -> String {
        render(
            diag.severity.as_str(),
            &diag.message,
            &self.locate(diag.span),
        )
    }
}

/// Parse a SystemC source string.
pub fn parse(source: &str) -> ScParseResult {
    parse_with_options(source, &[], &[])
}

/// Parse a SystemC source string with preprocessor options: `#include`
/// search directories and predefined object-like macros (`-D name=value`).
pub fn parse_with_options(
    source: &str,
    include_dirs: &[&str],
    defines: &[(&str, &str)],
) -> ScParseResult {
    parse_impl("<input>", source.to_string(), include_dirs, defines)
}

/// Parse a SystemC file from disk. Quoted `#include`s resolve against the
/// file's own directory first, then `include_dirs`.
pub fn parse_file(
    path: &str,
    include_dirs: &[&str],
    defines: &[(&str, &str)],
) -> Result<ScParseResult, String> {
    let bytes = std::fs::read(path).map_err(|e| format!("cannot read '{}': {}", path, e))?;
    let text = String::from_utf8_lossy(&bytes).into_owned();
    Ok(parse_impl(path, text, include_dirs, defines))
}

/// Preprocess and tokenize a SystemC source string (no parsing).
pub fn tokenize(source: &str) -> Vec<token::ScToken> {
    preprocess::Preprocessor::new(&[], &[]).run("<input>", source.to_string())
}

/// Whether `path` has a C++ source or header extension, i.e. names a file
/// for this front end rather than the SystemVerilog one.
pub fn is_systemc_path(path: &str) -> bool {
    let ext = std::path::Path::new(path)
        .extension()
        .and_then(|e| e.to_str())
        .unwrap_or("");
    matches!(
        ext.to_ascii_lowercase().as_str(),
        "cpp" | "cc" | "cxx" | "c++" | "h" | "hpp" | "hh" | "hxx" | "h++" | "ipp" | "tpp"
    )
}

fn parse_impl(
    path: &str,
    text: String,
    include_dirs: &[&str],
    defines: &[(&str, &str)],
) -> ScParseResult {
    let mut pp = preprocess::Preprocessor::new(include_dirs, defines);
    let tokens = pp.run(path, text);
    let mut p = parser::Parser::new(tokens);
    let unit = p.parse_translation_unit();
    let mut errors = Vec::new();
    let mut warnings = Vec::new();
    for d in pp.diags.into_iter().chain(p.diags) {
        match d.severity {
            Severity::Error => errors.push(d),
            Severity::Warning | Severity::Info => warnings.push(d),
        }
    }
    ScParseResult {
        files: pp.files,
        unit,
        errors,
        warnings,
    }
}
