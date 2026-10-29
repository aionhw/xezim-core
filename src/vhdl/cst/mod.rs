//! The one module that touches the parser (`vhdl_lang`, vendored in
//! `vhdl-lang/`). Everything else in `vhdl` works on what this module
//! produces, so a change of the parser crate's API stays here.

use std::ops::Range;
use std::sync::OnceLock;

mod convert;

use vhdl_lang::{Severity, SeverityMap, Source, VHDLParser, VHDLStandard};

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

/// A parsed file: its syntax errors, the byte ranges of its design units,
/// and (when there are no errors) the converted design (`ast`).
pub struct Parsed {
    pub file: SourceFile,
    pub units: Vec<Range<usize>>,
    pub errors: Vec<Diagnostic>,
    pub ast: Option<ast::DesignFile>,
}

/// Parse a VHDL-2008 file.
pub fn parse(file: SourceFile) -> Parsed {
    parse_std(file, super::VhdlStd::V2008)
}

/// The parser of a revision (its keyword tables are built once).
fn parser(std: super::VhdlStd) -> &'static VHDLParser {
    static P08: OnceLock<VHDLParser> = OnceLock::new();
    static P19: OnceLock<VHDLParser> = OnceLock::new();
    match std {
        super::VhdlStd::V2008 => P08.get_or_init(|| VHDLParser::new(VHDLStandard::VHDL2008)),
        super::VhdlStd::V2019 => P19.get_or_init(|| VHDLParser::new(VHDLStandard::VHDL2019)),
    }
}

/// Parse a file of revision `std`. One syntax error makes the parser report
/// follow-on errors in the same design unit, so only the first error of
/// each design unit is kept.
pub fn parse_std(file: SourceFile, std: super::VhdlStd) -> Parsed {
    // Latin-1: each byte is the character of the same code, so a column the
    // parser reports is a byte offset in its line.
    let text: String = file.text.iter().map(|&b| b as char).collect();
    let source = Source::inline(std::path::Path::new(&file.path), &text);
    let mut diags: Vec<vhdl_lang::Diagnostic> = Vec::new();
    let design = parser(std).parse_design_source(&source, &mut diags);
    let lines = convert::Lines::new(&file.text);
    let units: Vec<Range<usize>> = design
        .design_units
        .iter()
        .map(|(tokens, _)| match (tokens.first(), tokens.last()) {
            (Some(a), Some(b)) => lines.offset(a.pos.range.start)..lines.offset(b.pos.range.end),
            _ => 0..0,
        })
        .collect();
    let severities = SeverityMap::default();
    let mut seen = std::collections::BTreeSet::new();
    let mut errors = Vec::new();
    for d in &diags {
        if severities[d.code] != Some(Severity::Error) {
            continue;
        }
        let r = d.pos.range();
        let span = lines.offset(r.start)..lines.offset(r.end);
        let unit = units.iter().position(|u| u.contains(&span.start));
        if seen.insert(unit) {
            errors.push(Diagnostic {
                span,
                message: format!("VHDL: syntax error: {}", d.message),
            });
        }
    }
    let ast = if errors.is_empty() {
        let mut out = Vec::new();
        for ((tokens, unit), span) in design.design_units.iter().zip(&units) {
            let mut cv = convert::Converter::new(tokens, &lines, &file.text);
            if let Some(u) = cv.design_unit(unit, span.clone()) {
                out.push(u);
            }
            errors.extend(cv.errors);
        }
        Some(ast::DesignFile { units: out })
    } else {
        None
    };
    Parsed {
        file,
        units,
        errors,
        ast,
    }
}

/// The kind and name of each design unit (for `XEZIM_VHDL_DUMP`), e.g.
/// `entity foo`, `architecture rtl of foo`, `package body bar`.
pub fn unit_summary(p: &Parsed) -> Vec<String> {
    p.units
        .iter()
        .map(|u| {
            let text: String = p.file.text[u.clone()].iter().map(|&b| b as char).collect();
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
