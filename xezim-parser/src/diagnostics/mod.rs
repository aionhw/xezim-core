//! Diagnostics: errors and warnings for the SystemVerilog parser, and the
//! one renderer every parser/preprocessor/elaboration message goes through:
//!
//! ```text
//! In file included from top.sv:2:
//! body.svh:4:11: error: expected expression, found Semicolon ';'
//!     4 |   x = 3 +;
//!       |          ^
//! ```

use crate::ast::Span;
use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Severity {
    Error,
    Warning,
    Info,
}

impl Severity {
    pub fn as_str(&self) -> &'static str {
        match self {
            Severity::Error => "error",
            Severity::Warning => "warning",
            Severity::Info => "info",
        }
    }
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Diagnostic {
    pub severity: Severity,
    pub message: String,
    pub span: Span,
}

impl Diagnostic {
    pub fn error(message: impl Into<String>, span: Span) -> Self {
        Self {
            severity: Severity::Error,
            message: message.into(),
            span,
        }
    }

    pub fn warning(message: impl Into<String>, span: Span) -> Self {
        Self {
            severity: Severity::Warning,
            message: message.into(),
            span,
        }
    }
}

/// Bare `severity: message`. A span only means something together with the
/// text it indexes; render located diagnostics with [`render_diagnostic`].
impl fmt::Display for Diagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.severity.as_str(), self.message)
    }
}

/// One-line `<source>:line:col: severity: message` against `source` itself
/// (no file name, no context). Kept for callers without a line map; prefer
/// [`render_diagnostic`].
pub fn format_diagnostic(source: &str, diag: &Diagnostic) -> String {
    let loc = locate(source, None, "<source>", diag.span);
    format!(
        "{}: {}: {}",
        loc.short(),
        diag.severity.as_str(),
        diag.message
    )
}

/// A resolved source position: what a diagnostic prints in front of its
/// message, plus the context lines under it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Location {
    /// The file the text came from (an `include`d file, not the file that
    /// included it).
    pub file: String,
    /// 1-based line in `file`.
    pub line: u32,
    /// 1-based column, in characters.
    pub col: u32,
    /// Characters to underline, at least 1.
    pub len: u32,
    /// The text sits inside the expansion of this macro; `line`/`col` then
    /// point at the macro's invocation.
    pub macro_name: Option<String>,
    /// Include sites, innermost first: `(file, line)` of each `include that
    /// led to `file`.
    pub included_from: Vec<(String, u32)>,
    /// Text of `line`, when the file cannot be read back (e.g. a source that
    /// was never on disk). The file's own copy wins when it is readable.
    pub fallback_text: Option<String>,
}

impl Location {
    /// `file:line:col`.
    pub fn short(&self) -> String {
        format!("{}:{}:{}", self.file, self.line, self.col)
    }
}

/// Render `severity: message` at `loc`: the include chain, the
/// `file:line:col:` header, the source line and a caret underline, and a
/// note when the text came from a macro expansion. No trailing newline.
pub fn render(severity: &str, message: &str, loc: &Location) -> String {
    let mut out = String::new();
    for (k, (file, line)) in loc.included_from.iter().enumerate() {
        let sep = if k + 1 == loc.included_from.len() {
            ':'
        } else {
            ','
        };
        if k == 0 {
            out.push_str(&format!("In file included from {}:{}{}\n", file, line, sep));
        } else {
            out.push_str(&format!("                 from {}:{}{}\n", file, line, sep));
        }
    }
    out.push_str(&format!("{}: {}: {}", loc.short(), severity, message));
    let text = source_line(&loc.file, loc.line).or_else(|| loc.fallback_text.clone());
    if let Some(text) = text {
        let text = text.trim_end_matches(['\r', '\n']);
        let gutter = loc.line.to_string();
        let pad = " ".repeat(gutter.len());
        out.push_str(&format!("\n    {} | {}", gutter, text));
        // Keep tabs so the caret lines up under the same glyphs.
        let mut marker: String = text
            .chars()
            .take(loc.col.saturating_sub(1) as usize)
            .map(|c| if c == '\t' { '\t' } else { ' ' })
            .collect();
        let avail = text
            .chars()
            .count()
            .saturating_sub(loc.col.saturating_sub(1) as usize);
        let len = (loc.len as usize).clamp(1, avail.max(1));
        marker.push('^');
        marker.push_str(&"~".repeat(len - 1));
        out.push_str(&format!("\n    {} | {}", pad, marker));
    }
    if let Some(m) = &loc.macro_name {
        out.push_str(&format!(
            "\n{}: note: in expansion of macro `{}`",
            loc.short(),
            m
        ));
    }
    out
}

/// Render a parser diagnostic whose span indexes `text` (a preprocessed
/// source). With `map` the location is the ORIGINAL file/line/column the
/// text came from; without one it is `text`'s own line, named `file`.
pub fn render_diagnostic(
    diag: &Diagnostic,
    text: &str,
    map: Option<&crate::source_map::LineMap>,
    file: &str,
) -> String {
    let loc = locate(text, map, file, diag.span);
    render(diag.severity.as_str(), &diag.message, &loc)
}

/// Resolve `span` (a byte range of `text`) to a [`Location`] — through
/// `map` when there is one, else against `text` itself under the name `file`.
pub fn locate(
    text: &str,
    map: Option<&crate::source_map::LineMap>,
    file: &str,
    span: Span,
) -> Location {
    if let Some(loc) = map.and_then(|m| m.locate(text, span)) {
        return loc;
    }
    let start = (span.start as usize).min(text.len());
    let line_start = text[..start].rfind('\n').map_or(0, |p| p + 1);
    let line_end = text[start..].find('\n').map_or(text.len(), |p| start + p);
    let line = 1 + text.as_bytes()[..start]
        .iter()
        .filter(|&&b| b == b'\n')
        .count() as u32;
    let col = 1 + text[line_start..start].chars().count() as u32;
    let end = (span.end as usize).clamp(start, line_end);
    Location {
        file: if file.is_empty() {
            "<input>".to_string()
        } else {
            file.to_string()
        },
        line,
        col,
        len: text[start..end].chars().count().max(1) as u32,
        macro_name: None,
        included_from: Vec::new(),
        fallback_text: Some(text[line_start..line_end].to_string()),
    }
}

/// A file's lines as read back for context, stamped with the metadata they
/// were read under.
type CachedLines = (
    Option<(u64, std::time::SystemTime)>,
    std::rc::Rc<Vec<String>>,
);

thread_local! {
    /// Files read back for context lines, so a burst of diagnostics against
    /// one file reads it once. Revalidated by size and mtime, so a file
    /// rewritten in the same process is read again.
    static LINE_CACHE: std::cell::RefCell<std::collections::HashMap<String, CachedLines>> =
        std::cell::RefCell::new(std::collections::HashMap::new());
}

/// Line `line` (1-based) of `file` as it is on disk, if readable.
fn source_line(file: &str, line: u32) -> Option<String> {
    if file.is_empty() || line == 0 {
        return None;
    }
    let meta = std::fs::metadata(file).ok()?;
    let stamp = meta.modified().ok().map(|m| (meta.len(), m));
    let lines = LINE_CACHE.with(|c| {
        let mut c = c.borrow_mut();
        if let Some((st, lines)) = c.get(file) {
            if stamp.is_some() && *st == stamp {
                return Some(lines.clone());
            }
        }
        let bytes = std::fs::read(file).ok()?;
        let lines = std::rc::Rc::new(
            String::from_utf8_lossy(&bytes)
                .lines()
                .map(str::to_string)
                .collect::<Vec<_>>(),
        );
        c.insert(file.to_string(), (stamp, lines.clone()));
        Some(lines)
    })?;
    lines.get(line as usize - 1).cloned()
}
