//! Conditional analysis (VHDL-2019 §24.2): the tool directives `` `if ``,
//! `` `elsif ``, `` `else ``, `` `end [if] ``, `` `warning `` and `` `error ``.
//!
//! This runs on the source text before parsing. Directive lines and the
//! lines of regions whose condition is false are blanked byte by byte (line
//! breaks kept), so every byte offset the parser reports stays the offset of
//! the same character in the file. A directive is recognised where a line's
//! first non-blank character is a grave accent, outside delimited comments.
//!
//! Conditions compare the values of the predefined conditional analysis
//! identifiers (§24.2: VHDL_VERSION, TOOL_TYPE, TOOL_VENDOR, TOOL_NAME,
//! TOOL_EDITION, TOOL_VERSION) with string literals; `and`, `or`, `xor`,
//! `xnor`, `not (...)` and parentheses combine them.

use std::ops::Range;

use super::Diagnostic;
use crate::vhdl::VhdlStd;

/// The value of a conditional analysis identifier (case-insensitive), or
/// `None` when it is not one.
fn identifier_value(name: &str, std: VhdlStd) -> Option<String> {
    Some(match name.to_ascii_uppercase().as_str() {
        "VHDL_VERSION" => match std {
            VhdlStd::V2008 => "2008".into(),
            VhdlStd::V2019 => "2019".into(),
        },
        "TOOL_TYPE" => crate::vhdl::TOOL_TYPE.into(),
        "TOOL_VENDOR" => crate::vhdl::TOOL_VENDOR.into(),
        "TOOL_NAME" => crate::vhdl::TOOL_NAME.into(),
        "TOOL_EDITION" => crate::vhdl::TOOL_EDITION.into(),
        "TOOL_VERSION" => crate::vhdl::TOOL_VERSION.into(),
        _ => return None,
    })
}

/// The result of conditional analysis: the text to parse, its errors and
/// its warnings.
pub struct Output {
    pub text: Vec<u8>,
    pub errors: Vec<Diagnostic>,
    pub warnings: Vec<Diagnostic>,
}

/// One `` `if `` being analysed.
struct Frame {
    /// The `` `if `` directive (for "not closed").
    span: Range<usize>,
    /// The region enclosing this `` `if `` is analysed.
    outer: bool,
    /// A branch of this `` `if `` was taken.
    taken: bool,
    /// The current branch is analysed.
    active: bool,
    /// The `` `else `` was seen.
    in_else: bool,
}

/// Apply the tool directives of `text` (VHDL-2019 only; earlier revisions
/// have none and keep their text).
pub fn preprocess(text: &[u8], std: VhdlStd) -> Option<Output> {
    if std == VhdlStd::V2008 || !text.contains(&b'`') {
        return None;
    }
    let mut out = text.to_vec();
    let mut errors = Vec::new();
    let mut warnings = Vec::new();
    let mut stack: Vec<Frame> = Vec::new();
    let mut in_comment = false;
    let mut start = 0;
    while start < text.len() {
        let end = text[start..]
            .iter()
            .position(|&b| b == b'\n' || b == b'\r')
            .map_or(text.len(), |i| start + i);
        let line = &text[start..end];
        let active = stack.last().is_none_or(|f| f.active);
        let lead = line
            .iter()
            .position(|b| !b.is_ascii_whitespace())
            .unwrap_or(line.len());
        if !in_comment && line.get(lead) == Some(&b'`') {
            let at = start + lead;
            let mut lx = Lexer {
                s: line,
                i: lead + 1,
                base: start,
            };
            let word = lx.ident().map(|w| w.to_ascii_lowercase());
            let span = at..start + lx.i;
            let r = directive(
                word.as_deref(),
                &mut lx,
                span,
                std,
                active,
                &mut stack,
                &mut errors,
                &mut warnings,
            );
            if let Err(d) = r {
                errors.push(d);
            }
            blank(&mut out[start..end]);
        } else {
            if !active {
                blank(&mut out[start..end]);
            }
            in_comment = scan_comments(line, in_comment);
        }
        // Past the line break (`\r\n` is one).
        start = end;
        if text.get(start) == Some(&b'\r') {
            start += 1;
        }
        if text.get(start) == Some(&b'\n') {
            start += 1;
        }
    }
    for f in stack {
        errors.push(Diagnostic {
            span: f.span,
            message: "VHDL: `if without `end".into(),
        });
    }
    Some(Output {
        text: out,
        errors,
        warnings,
    })
}

#[allow(clippy::too_many_arguments)]
fn directive(
    word: Option<&str>,
    lx: &mut Lexer,
    span: Range<usize>,
    std: VhdlStd,
    active: bool,
    stack: &mut Vec<Frame>,
    errors: &mut Vec<Diagnostic>,
    warnings: &mut Vec<Diagnostic>,
) -> Result<(), Diagnostic> {
    let err = |span: &Range<usize>, m: &str| Diagnostic {
        span: span.clone(),
        message: format!("VHDL: {}", m),
    };
    match word {
        // A malformed condition still opens (or continues) the `if, as a
        // false one, so its `end is not reported too.
        Some("if") => {
            let c = condition(lx, std).unwrap_or_else(|d| {
                errors.push(d);
                false
            });
            stack.push(Frame {
                span,
                outer: active,
                taken: active && c,
                active: active && c,
                in_else: false,
            });
        }
        Some("elsif") => {
            let c = condition(lx, std).unwrap_or_else(|d| {
                errors.push(d);
                false
            });
            let Some(f) = stack.last_mut() else {
                return Err(err(&span, "`elsif without `if"));
            };
            if f.in_else {
                return Err(err(&span, "`elsif after `else"));
            }
            f.active = f.outer && !f.taken && c;
            f.taken |= f.active;
        }
        Some("else") => {
            lx.end()?;
            let Some(f) = stack.last_mut() else {
                return Err(err(&span, "`else without `if"));
            };
            if f.in_else {
                return Err(err(&span, "a second `else"));
            }
            f.in_else = true;
            f.active = f.outer && !f.taken;
            f.taken = true;
        }
        Some("end") => {
            if lx.ident().is_some_and(|w| !w.eq_ignore_ascii_case("if")) {
                return Err(lx.error("`if was expected after `end"));
            }
            lx.end()?;
            if stack.pop().is_none() {
                return Err(err(&span, "`end without `if"));
            }
        }
        Some(w @ ("warning" | "error")) => {
            let msg = match lx.token()? {
                Some((Tok::Str(s), _)) => s,
                _ => return Err(lx.error("a string literal was expected")),
            };
            lx.end()?;
            if active {
                let d = Diagnostic {
                    span,
                    message: format!("VHDL: {}", msg),
                };
                if w == "error" {
                    errors.push(d);
                } else {
                    warnings.push(d);
                }
            }
        }
        // §24.1: a tool directive a tool does not define is ignored.
        Some(w) => {
            if active {
                warnings.push(err(&span, &format!("tool directive `{} ignored", w)));
            }
        }
        None => return Err(err(&span, "a tool directive name was expected")),
    }
    Ok(())
}

/// A condition up to `then`.
fn condition(lx: &mut Lexer, std: VhdlStd) -> Result<bool, Diagnostic> {
    let v = expression(lx, std)?;
    match lx.token()? {
        Some((Tok::Word(w), _)) if w == "then" => {}
        _ => return Err(lx.error("then was expected")),
    }
    lx.end()?;
    Ok(v)
}

/// relation { op relation }, one logical operator kind without parentheses.
fn expression(lx: &mut Lexer, std: VhdlStd) -> Result<bool, Diagnostic> {
    let mut v = relation(lx, std)?;
    let mut op: Option<String> = None;
    loop {
        let save = lx.i;
        match lx.token()? {
            Some((Tok::Word(w), span)) if matches!(w.as_str(), "and" | "or" | "xor" | "xnor") => {
                if op.as_ref().is_some_and(|o| *o != w) {
                    return Err(Diagnostic {
                        span,
                        message: "VHDL: different logical operators need parentheses".into(),
                    });
                }
                let r = relation(lx, std)?;
                v = match w.as_str() {
                    "and" => v && r,
                    "or" => v || r,
                    "xor" => v != r,
                    _ => v == r,
                };
                op = Some(w);
            }
            _ => {
                lx.i = save;
                return Ok(v);
            }
        }
    }
}

/// `( expression )`, `not ( expression )` or `identifier op "string"`.
fn relation(lx: &mut Lexer, std: VhdlStd) -> Result<bool, Diagnostic> {
    match lx.token()? {
        Some((Tok::LPar, _)) => {
            let v = expression(lx, std)?;
            lx.expect_rpar()?;
            Ok(v)
        }
        Some((Tok::Word(w), _)) if w == "not" => {
            match lx.token()? {
                Some((Tok::LPar, _)) => {}
                _ => return Err(lx.error("( was expected after not")),
            }
            let v = expression(lx, std)?;
            lx.expect_rpar()?;
            Ok(!v)
        }
        Some((Tok::Word(w), span)) => {
            let Some(value) = identifier_value(&w, std) else {
                return Err(Diagnostic {
                    span,
                    message: format!("VHDL: '{}' is not a conditional analysis identifier", w),
                });
            };
            let op = match lx.token()? {
                Some((Tok::Op(o), _)) => o,
                _ => return Err(lx.error("a relational operator was expected")),
            };
            let s = match lx.token()? {
                Some((Tok::Str(s), _)) => s,
                _ => return Err(lx.error("a string literal was expected")),
            };
            let (a, b) = (value.as_bytes(), s.as_bytes());
            Ok(match op {
                "=" => a == b,
                "/=" => a != b,
                "<" => a < b,
                "<=" => a <= b,
                ">" => a > b,
                _ => a >= b,
            })
        }
        _ => Err(lx.error("a condition was expected")),
    }
}

enum Tok {
    Word(String),
    Str(String),
    Op(&'static str),
    LPar,
    RPar,
}

/// The tokens of one directive line.
struct Lexer<'a> {
    s: &'a [u8],
    i: usize,
    /// The offset of the line in the file.
    base: usize,
}

impl Lexer<'_> {
    fn skip_blanks(&mut self) {
        while self.s.get(self.i).is_some_and(|b| b.is_ascii_whitespace()) {
            self.i += 1;
        }
    }

    fn error(&self, m: &str) -> Diagnostic {
        let at = self.base + self.i.min(self.s.len());
        Diagnostic {
            span: at..at + 1,
            message: format!("VHDL: {}", m),
        }
    }

    /// An identifier directly at the position (the directive name).
    fn ident(&mut self) -> Option<String> {
        self.skip_blanks();
        let st = self.i;
        while self
            .s
            .get(self.i)
            .is_some_and(|b| b.is_ascii_alphanumeric() || *b == b'_')
        {
            self.i += 1;
        }
        (self.i > st).then(|| String::from_utf8_lossy(&self.s[st..self.i]).into_owned())
    }

    /// The next token, or `None` at the end of the line or a comment.
    fn token(&mut self) -> Result<Option<(Tok, Range<usize>)>, Diagnostic> {
        self.skip_blanks();
        let st = self.i;
        let Some(&c) = self.s.get(self.i) else {
            return Ok(None);
        };
        let next = self.s.get(self.i + 1).copied();
        let tok = match c {
            b'-' if next == Some(b'-') => return Ok(None),
            b'(' => {
                self.i += 1;
                Tok::LPar
            }
            b')' => {
                self.i += 1;
                Tok::RPar
            }
            b'"' => {
                let mut v = Vec::new();
                self.i += 1;
                loop {
                    match self.s.get(self.i) {
                        None => return Err(self.error("the string literal is not closed")),
                        Some(b'"') if self.s.get(self.i + 1) == Some(&b'"') => {
                            v.push(b'"');
                            self.i += 2;
                        }
                        Some(b'"') => {
                            self.i += 1;
                            break;
                        }
                        Some(&b) => {
                            v.push(b);
                            self.i += 1;
                        }
                    }
                }
                Tok::Str(v.iter().map(|&b| b as char).collect())
            }
            b'=' => {
                self.i += 1;
                Tok::Op("=")
            }
            b'/' if next == Some(b'=') => {
                self.i += 2;
                Tok::Op("/=")
            }
            b'<' | b'>' => {
                let eq = next == Some(b'=');
                self.i += 1 + eq as usize;
                Tok::Op(match (c, eq) {
                    (b'<', false) => "<",
                    (b'<', true) => "<=",
                    (_, false) => ">",
                    _ => ">=",
                })
            }
            c if c.is_ascii_alphabetic() => {
                let w = self.ident().unwrap_or_default();
                Tok::Word(w.to_ascii_lowercase())
            }
            _ => return Err(self.error("unexpected character in a tool directive")),
        };
        Ok(Some((tok, self.base + st..self.base + self.i)))
    }

    fn expect_rpar(&mut self) -> Result<(), Diagnostic> {
        match self.token()? {
            Some((Tok::RPar, _)) => Ok(()),
            _ => Err(self.error(") was expected")),
        }
    }

    /// Nothing but a comment may follow.
    fn end(&mut self) -> Result<(), Diagnostic> {
        match self.token()? {
            None => Ok(()),
            Some(_) => Err(self.error("unexpected text after the tool directive")),
        }
    }
}

/// Spaces for the bytes of a line (its length kept).
fn blank(line: &mut [u8]) {
    for b in line {
        *b = b' ';
    }
}

/// Whether a delimited comment (`/* */`) is open at the end of the line.
fn scan_comments(line: &[u8], mut in_comment: bool) -> bool {
    let mut i = 0;
    while i < line.len() {
        if in_comment {
            if line[i..].starts_with(b"*/") {
                in_comment = false;
                i += 2;
            } else {
                i += 1;
            }
            continue;
        }
        match line[i] {
            b'-' if line.get(i + 1) == Some(&b'-') => break,
            b'/' if line.get(i + 1) == Some(&b'*') => {
                in_comment = true;
                i += 2;
            }
            // A character literal ('"' must not open a string).
            b'\'' if line.get(i + 2) == Some(&b'\'') => i += 3,
            b'"' => {
                i += 1;
                while i < line.len() && line[i] != b'"' {
                    i += 1;
                }
                i += 1;
            }
            _ => i += 1,
        }
    }
    in_comment
}

#[cfg(test)]
mod tests {
    use super::*;

    fn run(src: &str) -> Output {
        preprocess(src.as_bytes(), VhdlStd::V2019).expect("has directives")
    }

    fn kept(o: &Output) -> Vec<String> {
        String::from_utf8_lossy(&o.text)
            .lines()
            .map(|l| l.trim().to_string())
            .filter(|l| !l.is_empty())
            .collect()
    }

    #[test]
    fn branches_and_nesting() {
        let o = run("a\n`if VHDL_VERSION = \"2019\" then\nb\n`if TOOL_TYPE /= \"SIMULATION\" then\nc\n`else\nd\n`end if\n`elsif VHDL_VERSION < \"2019\" then\ne\n`else\nf\n`end\ng\n");
        assert!(o.errors.is_empty(), "{:?}", o.errors.iter().map(|d| &d.message).collect::<Vec<_>>());
        assert_eq!(kept(&o), ["a", "b", "d", "g"]);
    }

    #[test]
    fn offsets_are_kept() {
        let src = "x\r\n  `if not (VHDL_VERSION = \"2019\") then\r\ny\r\n`end\r\nz";
        let o = run(src);
        assert_eq!(o.text.len(), src.len());
        assert_eq!(&o.text[o.text.len() - 1..], b"z");
        assert_eq!(kept(&o), ["x", "z"]);
    }

    #[test]
    fn logical_operators() {
        let o = run("`if (VHDL_VERSION = \"2019\" or TOOL_NAME = \"x\") and TOOL_EDITION /= \"y\" then\na\n`end\n`if VHDL_VERSION = \"2019\" xor VHDL_VERSION = \"2019\" then\nb\n`end\n");
        assert!(o.errors.is_empty());
        assert_eq!(kept(&o), ["a"]);
        let o = run("`if VHDL_VERSION = \"1\" and VHDL_VERSION = \"2\" or VHDL_VERSION = \"3\" then\n`end\n");
        assert_eq!(o.errors.len(), 1);
    }

    #[test]
    fn warnings_and_errors_in_taken_branches_only() {
        let o = run("`warning \"w1\"\n`if VHDL_VERSION = \"2008\" then\n`error \"e1\"\n`else\n`error \"e2\"\n`end if\n");
        let w: Vec<&str> = o.warnings.iter().map(|d| d.message.as_str()).collect();
        let e: Vec<&str> = o.errors.iter().map(|d| d.message.as_str()).collect();
        assert_eq!(w, ["VHDL: w1"]);
        assert_eq!(e, ["VHDL: e2"]);
        assert_eq!(o.errors[0].span.start, "`warning \"w1\"\n`if VHDL_VERSION = \"2008\" then\n`error \"e1\"\n`else\n".len());
    }

    #[test]
    fn malformed_directives() {
        for src in [
            "`if FOO = \"1\" then\n`end\n",
            "`if VHDL_VERSION = \"1\"\n`end\n",
            "`end\n",
            "`if VHDL_VERSION = \"1\" then\n",
            "`else\n",
            "`if VHDL_VERSION = \"1\" then\n`else\n`else\n`end\n",
        ] {
            assert!(!run(src).errors.is_empty(), "{src}");
        }
    }

    #[test]
    fn grave_accents_in_comments_and_strings() {
        let o = run("/* start\n`if junk\n*/ x\ns := \"`\";\n");
        assert!(o.errors.is_empty());
        assert_eq!(o.text, b"/* start\n`if junk\n*/ x\ns := \"`\";\n");
    }

    #[test]
    fn vhdl_2008_is_unchanged() {
        assert!(preprocess(b"`if x then\n", VhdlStd::V2008).is_none());
    }
}
