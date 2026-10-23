//! C++ lexer for the SystemC front end (ISO/IEC 14882:2017 §5).
//!
//! Produces preprocessing tokens for one file. Comments become whitespace,
//! a backslash-newline splices lines (so a `#define` may continue), and
//! every token records whether it starts a line (for directives) and
//! whether whitespace precedes it (for function-like macro definitions).

use super::ScDiagnostic;
use super::token::{ScSpan, ScToken, ScTokenKind, alternative_token, is_keyword};

/// Punctuators, longest first so the scan takes the maximal munch (§5.4).
const PUNCTUATORS: &[&str] = &[
    "<<=", ">>=", "...", "->*", "<=>", "::", "->", "++", "--", "<<", ">>", "<=", ">=", "==", "!=",
    "&&", "||", "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", ".*", "##", "{", "}", "[", "]",
    "(", ")", "<", ">", ";", ":", ",", ".", "?", "+", "-", "*", "/", "%", "^", "&", "|", "~", "!",
    "=", "#",
];

/// String and character literal encoding prefixes (§5.13.3, §5.13.5).
fn is_literal_prefix(s: &str) -> bool {
    matches!(s, "L" | "u" | "U" | "u8")
}

fn is_raw_prefix(s: &str) -> bool {
    matches!(s, "R" | "LR" | "uR" | "UR" | "u8R")
}

fn is_ident_start(b: u8) -> bool {
    b.is_ascii_alphabetic() || b == b'_' || b == b'$' || b >= 0x80
}

fn is_ident_continue(b: u8) -> bool {
    is_ident_start(b) || b.is_ascii_digit()
}

/// Lex `text` (the contents of file `file`) into tokens. Lexical errors
/// are pushed to `diags`; the offending character is skipped.
pub fn lex(text: &str, file: u32, diags: &mut Vec<ScDiagnostic>) -> Vec<ScToken> {
    let bytes = text.as_bytes();
    let mut tokens = Vec::new();
    let mut i = 0;
    let mut line_start = true;
    let mut space_before = false;

    while i < bytes.len() {
        let b = bytes[i];
        // Whitespace and line structure.
        if b == b'\n' {
            line_start = true;
            space_before = true;
            i += 1;
            continue;
        }
        if b == b' ' || b == b'\t' || b == b'\r' || b == 0x0b || b == 0x0c {
            space_before = true;
            i += 1;
            continue;
        }
        if b == b'\\' {
            // Line splice (§5.2 phase 2): backslash, optional trailing
            // blanks (a common editor accident GCC also accepts), newline.
            let mut j = i + 1;
            while j < bytes.len() && (bytes[j] == b' ' || bytes[j] == b'\t' || bytes[j] == b'\r') {
                j += 1;
            }
            if j < bytes.len() && bytes[j] == b'\n' {
                space_before = true;
                i = j + 1;
                continue;
            }
        }
        // Comments (§5.7) are whitespace. A newline inside a block comment
        // does not end a directive line: the comment is ONE space.
        if b == b'/' && bytes.get(i + 1) == Some(&b'/') {
            while i < bytes.len() && bytes[i] != b'\n' {
                // A spliced `//` comment continues on the next line.
                if bytes[i] == b'\\' && bytes.get(i + 1) == Some(&b'\n') {
                    i += 1;
                }
                i += 1;
            }
            space_before = true;
            continue;
        }
        if b == b'/' && bytes.get(i + 1) == Some(&b'*') {
            let start = i;
            match text[i + 2..].find("*/") {
                Some(p) => i = i + 2 + p + 2,
                None => {
                    diags.push(ScDiagnostic::error(
                        "unterminated block comment",
                        ScSpan::new(file, start, start + 2),
                    ));
                    i = bytes.len();
                }
            }
            space_before = true;
            continue;
        }

        let start = i;
        let (kind, end) = if is_ident_start(b) {
            let mut j = i;
            while j < bytes.len() && is_ident_continue(bytes[j]) {
                j += 1;
            }
            let word = &text[i..j];
            match bytes.get(j) {
                Some(b'"') if is_raw_prefix(word) => {
                    (ScTokenKind::StringLit, raw_string(text, j, file, diags))
                }
                Some(b'"') if is_literal_prefix(word) => {
                    (ScTokenKind::StringLit, quoted(text, j, b'"', file, diags))
                }
                Some(b'\'') if is_literal_prefix(word) => {
                    (ScTokenKind::CharLit, quoted(text, j, b'\'', file, diags))
                }
                _ => {
                    let kind = if is_keyword(word) {
                        ScTokenKind::Keyword
                    } else if alternative_token(word).is_some() {
                        ScTokenKind::Punct
                    } else {
                        ScTokenKind::Ident
                    };
                    (kind, j)
                }
            }
        } else if b.is_ascii_digit()
            || (b == b'.' && bytes.get(i + 1).is_some_and(|c| c.is_ascii_digit()))
        {
            number(bytes, i)
        } else if b == b'"' {
            (ScTokenKind::StringLit, quoted(text, i, b'"', file, diags))
        } else if b == b'\'' {
            (ScTokenKind::CharLit, quoted(text, i, b'\'', file, diags))
        } else if let Some(p) = PUNCTUATORS.iter().find(|p| text[i..].starts_with(**p)) {
            (ScTokenKind::Punct, i + p.len())
        } else {
            let ch = text[i..].chars().next().map_or(1, char::len_utf8);
            diags.push(ScDiagnostic::error(
                format!("unexpected character '{}'", &text[i..i + ch]),
                ScSpan::new(file, i, i + ch),
            ));
            i += ch;
            space_before = true;
            continue;
        };

        let mut tok_text = text[start..end].to_string();
        if kind == ScTokenKind::Punct
            && let Some(op) = alternative_token(&tok_text)
        {
            tok_text = op.to_string();
        }
        tokens.push(ScToken {
            kind,
            text: tok_text,
            span: ScSpan::new(file, start, end),
            line_start,
            space_before,
        });
        line_start = false;
        space_before = false;
        i = end;
    }
    tokens
}

/// A pp-number (§5.9) classified as an integer or floating literal.
/// Returns the kind and the end offset.
fn number(bytes: &[u8], start: usize) -> (ScTokenKind, usize) {
    let hex = bytes[start] == b'0' && matches!(bytes.get(start + 1), Some(b'x' | b'X'));
    let mut j = start;
    let mut float = false;
    while j < bytes.len() {
        let c = bytes[j];
        let exp = if hex {
            matches!(c, b'p' | b'P')
        } else {
            matches!(c, b'e' | b'E')
        };
        if exp && matches!(bytes.get(j + 1), Some(b'+' | b'-')) {
            float = true;
            j += 2;
        } else if c == b'\'' && bytes.get(j + 1).is_some_and(|d| d.is_ascii_alphanumeric()) {
            // Digit separator (§5.13.2).
            j += 1;
        } else if c.is_ascii_alphanumeric() || c == b'_' || c == b'.' {
            if c == b'.' || exp {
                float = true;
            }
            j += 1;
        } else {
            break;
        }
    }
    let kind = if float {
        ScTokenKind::FloatLit
    } else {
        ScTokenKind::IntLit
    };
    (kind, j)
}

/// A `"…"` or `'…'` literal whose opening quote is at `open`. Returns the
/// end offset (past the closing quote, plus any user-defined suffix).
fn quoted(text: &str, open: usize, quote: u8, file: u32, diags: &mut Vec<ScDiagnostic>) -> usize {
    let bytes = text.as_bytes();
    let mut j = open + 1;
    while j < bytes.len() {
        match bytes[j] {
            b'\\' => j += 2,
            b'\n' => break,
            c if c == quote => {
                j += 1;
                // User-defined literal suffix (§5.13.8), e.g. `"x"s`.
                while j < bytes.len() && is_ident_continue(bytes[j]) {
                    j += 1;
                }
                return j;
            }
            _ => j += 1,
        }
    }
    let what = if quote == b'"' { "string" } else { "character" };
    diags.push(ScDiagnostic::error(
        format!("unterminated {} literal", what),
        ScSpan::new(file, open, j.min(bytes.len())),
    ));
    j.min(bytes.len())
}

/// A raw string `R"delim( … )delim"` whose `"` is at `open` (§5.13.5).
fn raw_string(text: &str, open: usize, file: u32, diags: &mut Vec<ScDiagnostic>) -> usize {
    let rest = &text[open + 1..];
    let Some(paren) = rest
        .find('(')
        .filter(|&p| p <= 16 && !rest[..p].contains(['\n', ' ', ')', '\\']))
    else {
        diags.push(ScDiagnostic::error(
            "invalid raw string delimiter",
            ScSpan::new(file, open, open + 1),
        ));
        return open + 1;
    };
    let close = format!("){}\"", &rest[..paren]);
    match rest[paren..].find(&close) {
        Some(p) => open + 1 + paren + p + close.len(),
        None => {
            diags.push(ScDiagnostic::error(
                "unterminated raw string literal",
                ScSpan::new(file, open, open + 1),
            ));
            text.len()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn kinds(src: &str) -> Vec<(ScTokenKind, String)> {
        let mut d = Vec::new();
        let toks = lex(src, 0, &mut d);
        assert!(d.is_empty(), "{:?}", d);
        toks.into_iter().map(|t| (t.kind, t.text)).collect()
    }

    #[test]
    fn maximal_munch_punctuators() {
        let t = kinds("a<<=b>>c->*d::e");
        let texts: Vec<_> = t.iter().map(|(_, s)| s.as_str()).collect();
        assert_eq!(texts, ["a", "<<=", "b", ">>", "c", "->*", "d", "::", "e"]);
    }

    #[test]
    fn numbers() {
        use ScTokenKind::*;
        let t = kinds("42 0x1F 0b1010'0101 1'000'000ull 3.14 1e-9 .5f 0x1p+3 10_ns");
        let k: Vec<_> = t.iter().map(|(k, _)| *k).collect();
        assert_eq!(
            k,
            [
                IntLit, IntLit, IntLit, IntLit, FloatLit, FloatLit, FloatLit, FloatLit, IntLit
            ]
        );
        assert_eq!(t[3].1, "1'000'000ull");
    }

    #[test]
    fn strings_and_chars() {
        use ScTokenKind::*;
        let t = kinds(r#""a\"b" u8"x" L'c' '\n' R"xy(a)"b)xy" s"#);
        let k: Vec<_> = t.iter().map(|(k, _)| *k).collect();
        assert_eq!(
            k,
            [StringLit, StringLit, CharLit, CharLit, StringLit, Ident]
        );
        assert_eq!(t[4].1, r#"R"xy(a)"b)xy""#);
    }

    #[test]
    fn comments_splices_and_line_starts() {
        let mut d = Vec::new();
        let toks = lex("#define X \\\n  1 /* a\nb */ 2\n  # y // c\nz", 0, &mut d);
        let starts: Vec<_> = toks
            .iter()
            .map(|t| (t.text.as_str(), t.line_start))
            .collect();
        assert_eq!(
            starts,
            [
                ("#", true),
                ("define", false),
                ("X", false),
                ("1", false),
                ("2", false),
                ("#", true),
                ("y", false),
                ("z", true)
            ]
        );
    }

    #[test]
    fn alternative_tokens_and_keywords() {
        use ScTokenKind::*;
        let t = kinds("a and not b class");
        assert_eq!(t[1], (Punct, "&&".to_string()));
        assert_eq!(t[2], (Punct, "!".to_string()));
        assert_eq!(t[4].0, Keyword);
    }

    #[test]
    fn errors_do_not_stop_lexing() {
        let mut d = Vec::new();
        let toks = lex("a @ b \"open\nc", 0, &mut d);
        assert_eq!(d.len(), 2);
        assert_eq!(toks.last().unwrap().text, "c");
    }
}
