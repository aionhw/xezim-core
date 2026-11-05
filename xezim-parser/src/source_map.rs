//! Line map from preprocessed text back to the original sources.
//!
//! The preprocessor splices `include`d files in whole, expands macros (whose
//! bodies may span lines) and splits inline conditional directives onto
//! lines of their own, so a line of preprocessed text can come from another
//! file, from a macro body, or from the middle of an original line. Every
//! span the parser produces indexes the preprocessed text; this map is what
//! turns one back into `file:line:col` for a diagnostic.

use std::sync::OnceLock;

use crate::ast::Span;
use crate::diagnostics::Location;

/// A file (or `line-directive name) that contributed text.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MapFile {
    pub path: String,
    /// `(file index, line)` of the `include that pulled this file in.
    pub included_from: Option<(u32, u32)>,
}

/// Where one line of preprocessed output came from.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct LineOrigin {
    pub file: u32,
    /// 1-based line in `file`.
    pub line: u32,
    /// 0-based character column in the original line where this output
    /// line starts (non-zero only for a line split off an original line).
    pub col: u32,
    /// 1 + index into `LineMap::macros` for macro-expanded text, else 0.
    pub mac: u32,
    /// Macro-expanded text: column of the invocation, relative to `col`.
    pub mcol: u32,
    /// Macro-expanded text: the output line still starts with the original
    /// text before the invocation (the first line of an expansion).
    pub mfirst: bool,
    /// Macro-expanded text: column (relative to `col`) where the FIRST
    /// line's substituted text ends, exclusive. Ordinary tokens that merely
    /// FOLLOW a macro call on the same line sit at `>= mcol + mend` and are
    /// original text, not macro text. On `mfirst == false` (continuation
    /// lines of a multi-line expansion) every token is macro text and this
    /// value is ignored. When both `mend` and `mcall` are zero the extent is
    /// unknown; a known empty expansion has zero `mend` and nonzero `mcall`.
    pub mend: u32,
    /// Macro-expanded text: character length of the FIRST macro invocation
    /// (`` `NAME `` plus any balanced `(...)`) in the ORIGINAL line. When a
    /// token after the substitution keeps its own column, the substitution
    /// may change length (`mcall` input chars became `mend` output chars), so
    /// the OFFSET of the following original text is shifted by `mcall - mend`.
    /// Zero means unknown (no adjustment).
    pub mcall: u32,
    /// One-based index into the map's exact same-line expansion columns.
    pub columns: u32,
}

impl LineOrigin {
    pub(crate) fn plain(file: u32, line: u32, col: u32) -> Self {
        LineOrigin {
            file,
            line,
            col,
            mac: 0,
            mcol: 0,
            mfirst: false,
            mend: 0,
            mcall: 0,
            columns: 0,
        }
    }
}

/// A run of output lines whose origins advance by `step` lines each (`None`
/// until a second line joins the run).
#[derive(Debug, Clone, Copy)]
struct Seg {
    out: u32,
    origin: LineOrigin,
    step: Option<u32>,
}

/// One expansion and its invocation, in character columns on the same line.
#[derive(Debug, Clone)]
pub(crate) struct MacroColumn {
    pub start: u32,
    pub end: u32,
    pub source_start: u32,
    pub source_end: u32,
    pub mac: u32,
}

/// Maps each line of one preprocessed text to its origin.
#[derive(Debug, Clone, Default)]
pub struct LineMap {
    pub files: Vec<MapFile>,
    macros: Vec<String>,
    segs: Vec<Seg>,
    columns: Vec<Vec<MacroColumn>>,
    /// Where each line of the text starts, taken from the first text
    /// `locate` is given, so that finding a span's line is a binary search
    /// rather than a count of the newlines before it: a design can locate
    /// the spans of a cell library once per cell instance (#898).
    line_starts: OnceLock<LineStarts>,
}

/// Byte offsets at which the lines of one text start.
#[derive(Clone)]
struct LineStarts {
    /// Length of the text the offsets were taken from.
    len: usize,
    starts: Vec<usize>,
}

impl LineStarts {
    fn new(text: &str) -> Self {
        let mut starts = vec![0];
        starts.extend(
            text.bytes()
                .enumerate()
                .filter(|&(_, b)| b == b'\n')
                .map(|(i, _)| i + 1),
        );
        LineStarts {
            len: text.len(),
            starts,
        }
    }
}

impl std::fmt::Debug for LineStarts {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "LineStarts({} lines)", self.starts.len())
    }
}

/// 0-based line of `text` holding byte `start`, and the byte range of that
/// line without its newline, found by scanning the text.
fn line_at_by_scan(text: &str, start: usize) -> (usize, usize, usize) {
    let line = text.as_bytes()[..start]
        .iter()
        .filter(|&&b| b == b'\n')
        .count();
    let line_start = text[..start].rfind('\n').map_or(0, |p| p + 1);
    let line_end = text[start..].find('\n').map_or(text.len(), |p| start + p);
    (line, line_start, line_end)
}

impl LineMap {
    pub(crate) fn new(
        files: Vec<MapFile>,
        macros: Vec<String>,
        origins: &[LineOrigin],
        columns: Vec<Vec<MacroColumn>>,
    ) -> Self {
        let mut segs: Vec<Seg> = Vec::new();
        for (i, o) in origins.iter().enumerate() {
            let i = i as u32;
            if let Some(last) = segs.last_mut() {
                let n = i - last.out;
                let o_at = LineOrigin {
                    line: last.origin.line,
                    ..*o
                };
                if o_at == last.origin {
                    match last.step {
                        None if n == 1 && o.line == last.origin.line + 1 => {
                            last.step = Some(1);
                            continue;
                        }
                        None if n == 1 && o.line == last.origin.line => {
                            last.step = Some(0);
                            continue;
                        }
                        Some(step) if o.line == last.origin.line + n * step => continue,
                        _ => {}
                    }
                }
            }
            segs.push(Seg {
                out: i,
                origin: *o,
                step: None,
            });
        }
        LineMap {
            files,
            macros,
            segs,
            columns,
            line_starts: OnceLock::new(),
        }
    }

    /// `line_at_by_scan` by binary search over the line starts. A text of
    /// another length than the first one located in is scanned instead.
    fn line_at(&self, text: &str, start: usize) -> (usize, usize, usize) {
        let index = self.line_starts.get_or_init(|| LineStarts::new(text));
        if index.len != text.len() {
            return line_at_by_scan(text, start);
        }
        let line = index.starts.partition_point(|&s| s <= start) - 1;
        let line_end = index.starts.get(line + 1).map_or(text.len(), |&s| s - 1);
        (line, index.starts[line], line_end)
    }

    /// Origin of output line `out` (0-based).
    pub(crate) fn origin(&self, out: usize) -> Option<LineOrigin> {
        let out = u32::try_from(out).ok()?;
        let k = self.segs.partition_point(|s| s.out <= out).checked_sub(1)?;
        let s = &self.segs[k];
        let mut o = s.origin;
        o.line += (out - s.out) * s.step.unwrap_or(0);
        Some(o)
    }

    /// Original file and 1-based line of output line `out` (0-based); for
    /// macro-expanded text, the line of the invocation. Lets a caller that
    /// resolves many spans count output lines itself, once per text.
    pub fn file_line(&self, out: usize) -> Option<(&str, u32)> {
        let o = self.origin(out)?;
        Some((self.files.get(o.file as usize)?.path.as_str(), o.line))
    }

    /// Include chain of file `f`, innermost first.
    fn include_chain(&self, mut f: u32) -> Vec<(String, u32)> {
        let mut chain = Vec::new();
        while let Some((parent, line)) = self.files.get(f as usize).and_then(|m| m.included_from) {
            let Some(p) = self.files.get(parent as usize) else {
                break;
            };
            chain.push((p.path.clone(), line));
            if chain.len() > 64 {
                break;
            }
            f = parent;
        }
        chain
    }

    /// Resolve `span` (a byte range of the preprocessed `text` this map was
    /// built for) to the original source position.
    pub fn locate(&self, text: &str, span: Span) -> Option<Location> {
        let start = span.start.min(text.len());
        let (out_line, line_start, line_end) = self.line_at(text, start);
        let o = self.origin(out_line)?;
        let file = self.files.get(o.file as usize)?;
        let out_col = text[line_start..start].chars().count() as u32;
        let end = span.end.clamp(start, line_end);
        let len = text[start..end].chars().count().max(1) as u32;
        let mut loc = Location {
            file: file.path.clone(),
            line: o.line,
            col: o.col + out_col + 1,
            len,
            macro_name: None,
            included_from: self.include_chain(o.file),
            fallback_text: None,
        };
        if let Some(columns) = o
            .columns
            .checked_sub(1)
            .and_then(|index| self.columns.get(index as usize))
        {
            // §22.5: each expansion maps to its own invocation; plain text
            // between or after expansions keeps its original source column.
            let count = columns.partition_point(|column| column.start <= out_col);
            if let Some(column) = count.checked_sub(1).map(|index| &columns[index]) {
                if out_col < column.end {
                    let name = self.macros[column.mac as usize - 1].clone();
                    loc.col = o.col + column.source_start + 1;
                    loc.len = name.chars().count() as u32 + 1;
                    loc.macro_name = Some(name);
                } else {
                    loc.col = (o.col as i64 + out_col as i64 + column.source_end as i64
                        - column.end as i64
                        + 1)
                    .max(1) as u32;
                }
            }
            return Some(loc);
        }
        // Canonical macro-text predicate on the expansion's first line: a
        // token is macro text only while its column lies within the
        // substituted run [mcol, mcol+mend). Ordinary tokens before the call
        // (out_col < mcol) and -- crucially -- ordinary tokens that merely
        // FOLLOW the call on the same line (out_col >= mcol+mend) are
        // original text and keep their real column. That second bound was the
        // defect: the old code redirected every token at/after the invocation
        // to the macro, so `logic [`W-1:0] data;` misreported `data` (which
        // comes after the expansion) at the invocation column.
        let in_macro_text = o.mac != 0
            && (!o.mfirst
                || (out_col >= o.mcol
                    && ((o.mend == 0 && o.mcall == 0) || out_col < o.mcol + o.mend)));
        if in_macro_text {
            // Macro text: point at the invocation (text left of it on the
            // expansion's first line is still the original).
            let name = self
                .macros
                .get(o.mac as usize - 1)
                .cloned()
                .unwrap_or_default();
            loc.col = o.col + o.mcol + 1;
            loc.len = name.chars().count() as u32 + 1;
            loc.macro_name = Some(name);
        } else {
            // Ordinary text. If this is an expansion line and the token lies
            // AFTER the macro substitution (out_col >= mcol + mend), the
            // expansion may have changed the line's length: the substitution
            // replaced `mcall` input chars with `mend` output chars, so the
            // original offset is `out_col + (mcall as i64 - mend as i64)`.
            // Without this the token keeps its preprocessed column, which is
            // wrong when the expansion shrank/grew (`` `W `` -> `8` moves
            // `data` left by one). Several same-line expansions use the
            // exact columns above; this is the single-expansion path.
            let mid = o.mcol + o.mend;
            if o.mac != 0 && o.mfirst && out_col >= mid && o.mcall != 0 {
                let shift = o.mcall as i64 - o.mend as i64;
                loc.col = (o.col as i64 + out_col as i64 + shift + 1).max(0) as u32;
            }
            if o.mac == 0 {
                loc.fallback_text = Some(text[line_start..line_end].to_string());
            }
        }
        Some(loc)
    }

    /// `file:line:col` of `span`, or `None` when the map does not cover it.
    pub fn location_string(&self, text: &str, span: Span) -> Option<String> {
        self.locate(text, span).map(|l| l.short())
    }
}
