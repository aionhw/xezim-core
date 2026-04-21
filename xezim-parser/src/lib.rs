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
