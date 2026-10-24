//! The one module that touches `vhdl_syntax` (the parser). Everything else
//! in `vhdl` works on what this module produces, so a change of the parser
//! crate's API stays here.

use std::ops::Range;

mod convert;

use vhdl_syntax::parser;
use vhdl_syntax::syntax::{AstNode, DesignFileSyntax};

use crate::vhdl::ast;

/// A VHDL source file: its name (as given) and bytes (VHDL is Latin-1).
pub struct SourceFile {
    pub path: String,
    pub text: Vec<u8>,
    line_starts: Vec<usize>,
}

impl SourceFile {
    pub fn new(path: String, text: Vec<u8>) -> Self {
        let mut line_starts = vec![0];
        line_starts.extend(
            text.iter()
                .enumerate()
                .filter(|(_, b)| **b == b'\n')
                .map(|(i, _)| i + 1),
        );
        SourceFile {
            path,
            text,
            line_starts,
        }
    }

    /// 1-based line and column of a byte offset.
    pub fn line_col(&self, offset: usize) -> (usize, usize) {
        let line = self.line_starts.partition_point(|&s| s <= offset) - 1;
        (line + 1, offset - self.line_starts[line] + 1)
    }

    fn line_text(&self, line: usize) -> String {
        let start = self.line_starts[line - 1];
        let end = self
            .line_starts
            .get(line)
            .map_or(self.text.len(), |&e| e.saturating_sub(1));
        // Latin-1: every byte is the character of the same code.
        self.text[start..end.max(start)]
            .iter()
            .map(|&b| b as char)
            .collect::<String>()
            .trim_end_matches('\r')
            .to_string()
    }

    /// `file:line:col: error: msg`, the source line and a caret under the
    /// span (on its first line).
    pub fn render(&self, d: &Diagnostic) -> String {
        let (line, col) = self.line_col(d.span.start);
        let src = self.line_text(line);
        let width = d
            .span
            .len()
            .clamp(1, src.chars().count().saturating_sub(col - 1).max(1));
        let gutter = line.to_string().len();
        format!(
            "{}:{}:{}: error: {}\n{:>g$} |\n{} | {}\n{:>g$} | {}^{}",
            self.path,
            line,
            col,
            d.message,
            "",
            line,
            src,
            "",
            " ".repeat(col - 1),
            "~".repeat(width - 1),
            g = gutter
        )
    }
}

/// An error at a byte range of a source file.
pub struct Diagnostic {
    pub span: Range<usize>,
    pub message: String,
}

/// A parsed file: the concrete syntax tree, its syntax errors, and (when
/// there are none) the converted design (`ast`).
pub struct Parsed {
    pub file: SourceFile,
    pub design: DesignFileSyntax,
    pub errors: Vec<Diagnostic>,
    pub ast: Option<ast::DesignFile>,
}

/// Parse a VHDL-2008 file. One syntax error makes the parser report many
/// follow-on errors in the same design unit, so only the first error of
/// each design unit is kept.
pub fn parse(file: SourceFile) -> Parsed {
    let (design, errs) = parser::parse(file.text.clone());
    let units: Vec<Range<usize>> = design.design_units().map(|u| u.raw().range()).collect();
    let mut seen = std::collections::BTreeSet::new();
    let mut errors = Vec::new();
    for e in errs {
        let span = e.span().clone();
        let unit = units.iter().position(|u| u.contains(&span.start));
        if seen.insert(unit) {
            errors.push(Diagnostic {
                span,
                message: format!("VHDL: syntax error: {}", e.err()),
            });
        }
    }
    let ast = if errors.is_empty() {
        let mut cv = convert::Converter::new();
        let df = cv.design_file(&design.raw());
        errors.extend(cv.errors);
        Some(df)
    } else {
        None
    };
    Parsed {
        file,
        design,
        errors,
        ast,
    }
}

/// The kind and name of each design unit (for `XEZIM_VHDL_DUMP`), e.g.
/// `entity foo`, `architecture rtl of foo`, `package body bar`.
pub fn unit_summary(p: &Parsed) -> Vec<String> {
    p.design
        .design_units()
        .map(|u| {
            let mut out = Vec::new();
            u.raw().write_to(&mut out).ok();
            let text: String = out.iter().map(|&b| b as char).collect();
            let words: Vec<&str> = text
                .lines()
                .map(|l| l.split("--").next().unwrap_or(""))
                .flat_map(|l| l.split_whitespace())
                .skip_while(|w| {
                    !matches!(
                        w.to_ascii_lowercase().as_str(),
                        "entity" | "architecture" | "package" | "configuration" | "context"
                    )
                })
                .collect();
            let n = match words.first().map(|w| w.to_ascii_lowercase()).as_deref() {
                Some("architecture" | "configuration") => 4,
                Some("package") if words.get(1).is_some_and(|w| w.eq_ignore_ascii_case("body")) => {
                    3
                }
                _ => 2,
            };
            words[..n.min(words.len())].join(" ")
        })
        .collect()
}
