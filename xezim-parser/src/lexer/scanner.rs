//! Lexer/Scanner for SystemVerilog (IEEE 1800-2017 §5)

use super::token::{Token, TokenKind, ams_keyword, keyword};
use crate::ast::Span;

pub struct Lexer<'a> {
    input: &'a [u8],
    pos: usize,
    /// IEEE 1800-2023 §22.14: stack of active `begin_keywords` regions; each
    /// entry is `true` for a `1364-*` (legacy Verilog) keyword set. The
    /// innermost region wins — while its top is `true`, SystemVerilog-only
    /// keywords (`logic`, `bit`, …) lex as ordinary identifiers.
    kw_stack: Vec<bool>,
}

impl<'a> Lexer<'a> {
    pub fn new(source: &'a str) -> Self {
        Self { input: source.as_bytes(), pos: 0, kw_stack: Vec::new() }
    }

    pub fn tokenize(mut self) -> Vec<Token> {
        let mut tokens = Vec::new();
        loop {
            self.skip_whitespace();
            if self.pos >= self.input.len() {
                tokens.push(Token::new(TokenKind::Eof, String::new(), Span::new(self.pos, self.pos)));
                break;
            }
            // Skip comments
            if self.pos + 1 < self.input.len() && self.input[self.pos] == b'/' {
                if self.input[self.pos + 1] == b'/' {
                    while self.pos < self.input.len() && self.input[self.pos] != b'\n' { self.pos += 1; }
                    continue;
                }
                if self.input[self.pos + 1] == b'*' {
                    self.pos += 2;
                    while self.pos + 1 < self.input.len() {
                        if self.input[self.pos] == b'*' && self.input[self.pos + 1] == b'/' {
                            self.pos += 2;
                            break;
                        }
                        self.pos += 1;
                    }
                    if self.pos >= self.input.len() {
                        // Unclosed block comment - just stop
                    }
                    continue;
                }
            }
            tokens.push(self.scan_token());
        }
        tokens
    }

    fn peek(&self) -> Option<u8> {
        self.input.get(self.pos + 1).copied()
    }

    fn skip_whitespace(&mut self) {
        while self.pos < self.input.len() {
            let ch = self.input[self.pos];
            if ch.is_ascii_whitespace() {
                self.pos += 1;
                continue;
            }
            // Handle line continuation: \ followed by optional spaces and then newline
            if ch == b'\\' && self.pos + 1 < self.input.len() {
                let mut p = self.pos + 1;
                while p < self.input.len() && (self.input[p] == b' ' || self.input[p] == b'\t' || self.input[p] == b'\r') {
                    p += 1;
                }
                if p < self.input.len() && self.input[p] == b'\n' {
                    self.pos = p + 1;
                    continue;
                }
            }
            break;
        }
    }

    fn make_token(&mut self, start: usize, kind: TokenKind) -> Token {
        self.pos += 1;
        let text = String::from_utf8_lossy(&self.input[start..self.pos]).to_string();
        Token::new(kind, text, Span::new(start, self.pos))
    }

    fn scan_token(&mut self) -> Token {
        let start = self.pos;
        let ch = self.input[self.pos];
        match ch {
            // String literal
            b'"' => self.scan_string(start),
            // Compiler directive
            b'`' => self.scan_directive(start),
            // System identifier
            b'$' => {
                if self.peek().map_or(false, |c| c.is_ascii_alphabetic() || c == b'_') {
                    self.scan_system_id(start)
                } else {
                    self.make_token(start, TokenKind::Dollar)
                }
            }
            // Escaped identifier
            b'\\' => self.scan_escaped_id(start),
            // Number starting with apostrophe: 'b, 'h, 'o, 'd, 's, '0, '1, 'x, 'z
            b'\'' => {
                if self.peek().map_or(false, |c| matches!(c, b'{')) {
                    self.pos += 2;
                    Token::new(TokenKind::ApostropheLBrace, "'{".into(), Span::new(start, self.pos))
                } else if self.peek().map_or(false, |c| matches!(c, b'0' | b'1' | b'x' | b'X' | b'z' | b'Z')) {
                    self.pos += 2;
                    let text = String::from_utf8_lossy(&self.input[start..self.pos]).to_string();
                    Token::new(TokenKind::UnbasedUnsizedLiteral, text, Span::new(start, self.pos))
                } else {
                    self.scan_based_number(start)
                }
            }
            // Numbers
            b'0'..=b'9' => self.scan_number(start),
            // Identifiers / keywords
            b'a'..=b'z' | b'A'..=b'Z' | b'_' => self.scan_identifier(start),
            // Operators and punctuation
            b'(' => self.make_token(start, TokenKind::LParen),
            b')' => self.make_token(start, TokenKind::RParen),
            b'[' => self.make_token(start, TokenKind::LBracket),
            b']' => self.make_token(start, TokenKind::RBracket),
            b'{' => self.make_token(start, TokenKind::LBrace),
            b'}' => self.make_token(start, TokenKind::RBrace),
            b';' => self.make_token(start, TokenKind::Semicolon),
            b',' => self.make_token(start, TokenKind::Comma),
            b'.' => self.make_token(start, TokenKind::Dot),
            b'@' => self.make_token(start, TokenKind::At),
            b'?' => self.make_token(start, TokenKind::Question),
            b'~' => {
                self.pos += 1;
                match self.input.get(self.pos) {
                    Some(b'&') => { self.pos += 1; Token::new(TokenKind::BitNand, "~&".into(), Span::new(start, self.pos)) }
                    Some(b'|') => { self.pos += 1; Token::new(TokenKind::BitNor, "~|".into(), Span::new(start, self.pos)) }
                    Some(b'^') => { self.pos += 1; Token::new(TokenKind::BitXnor, "~^".into(), Span::new(start, self.pos)) }
                    _ => Token::new(TokenKind::BitNot, "~".into(), Span::new(start, self.pos))
                }
            }
            b'+' => {
                self.pos += 1;
                match self.input.get(self.pos) {
                    Some(b'+') => { self.pos += 1; Token::new(TokenKind::Increment, "++".into(), Span::new(start, self.pos)) }
                    Some(b'=') => { self.pos += 1; Token::new(TokenKind::PlusAssign, "+=".into(), Span::new(start, self.pos)) }
                    Some(b':') => { self.pos += 1; Token::new(TokenKind::PlusColon, "+:".into(), Span::new(start, self.pos)) }
                    _ => Token::new(TokenKind::Plus, "+".into(), Span::new(start, self.pos))
                }
            }
            b'-' => {
                self.pos += 1;
                match self.input.get(self.pos) {
                    Some(b'-') => { self.pos += 1; Token::new(TokenKind::Decrement, "--".into(), Span::new(start, self.pos)) }
                    Some(b'=') => { self.pos += 1; Token::new(TokenKind::MinusAssign, "-=".into(), Span::new(start, self.pos)) }
                    Some(b'>') => {
                        self.pos += 1;
                        if self.input.get(self.pos) == Some(&b'>') {
                            self.pos += 1; Token::new(TokenKind::DoubleArrow, "->>".into(), Span::new(start, self.pos))
                        } else {
                            Token::new(TokenKind::Arrow, "->".into(), Span::new(start, self.pos))
                        }
                    }
                    Some(b':') => { self.pos += 1; Token::new(TokenKind::MinusColon, "-:".into(), Span::new(start, self.pos)) }
                    _ => Token::new(TokenKind::Minus, "-".into(), Span::new(start, self.pos))
                }
            }
            b'*' => {
                self.pos += 1;
                match self.input.get(self.pos) {
                    Some(b'*') => { self.pos += 1; Token::new(TokenKind::DoubleStar, "**".into(), Span::new(start, self.pos)) }
                    Some(b'=') => { self.pos += 1; Token::new(TokenKind::StarAssign, "*=".into(), Span::new(start, self.pos)) }
                    _ => Token::new(TokenKind::Star, "*".into(), Span::new(start, self.pos))
                }
            }
            b'/' => {
                self.pos += 1;
                match self.input.get(self.pos) {
                    Some(b'=') => { self.pos += 1; Token::new(TokenKind::SlashAssign, "/=".into(), Span::new(start, self.pos)) }
                    _ => Token::new(TokenKind::Slash, "/".into(), Span::new(start, self.pos))
                }
            }
            b'%' => {
                self.pos += 1;
                if self.input.get(self.pos) == Some(&b'=') { self.pos += 1; Token::new(TokenKind::PercentAssign, "%=".into(), Span::new(start, self.pos)) }
                else { Token::new(TokenKind::Percent, "%".into(), Span::new(start, self.pos)) }
            }
            b'!' => {
                self.pos += 1;
                match self.input.get(self.pos) {
                    Some(b'=') => {
                        self.pos += 1;
                        match self.input.get(self.pos) {
                            Some(b'=') => { self.pos += 1; Token::new(TokenKind::CaseNeq, "!==".into(), Span::new(start, self.pos)) }
                            Some(b'?') => { self.pos += 1; Token::new(TokenKind::WildcardNeq, "!=?".into(), Span::new(start, self.pos)) }
                            _ => Token::new(TokenKind::Neq, "!=".into(), Span::new(start, self.pos))
                        }
                    }
                    _ => Token::new(TokenKind::LogNot, "!".into(), Span::new(start, self.pos))
                }
            }
            b'=' => {
                self.pos += 1;
                match self.input.get(self.pos) {
                    Some(b'=') => {
                        self.pos += 1;
                        match self.input.get(self.pos) {
                            Some(b'=') => { self.pos += 1; Token::new(TokenKind::CaseEq, "===".into(), Span::new(start, self.pos)) }
                            Some(b'?') => { self.pos += 1; Token::new(TokenKind::WildcardEq, "==?".into(), Span::new(start, self.pos)) }
                            _ => Token::new(TokenKind::Eq, "==".into(), Span::new(start, self.pos))
                        }
                    }
                    Some(b'>') => { self.pos += 1; Token::new(TokenKind::FatArrow, "=>".into(), Span::new(start, self.pos)) }
                    _ => Token::new(TokenKind::Assign, "=".into(), Span::new(start, self.pos))
                }
            }
            b'<' => {
                self.pos += 1;
                match self.input.get(self.pos) {
                    Some(b'=') => { self.pos += 1; Token::new(TokenKind::Leq, "<=".into(), Span::new(start, self.pos)) }
                    Some(b'<') => {
                        self.pos += 1;
                        match self.input.get(self.pos) {
                            Some(b'<') => { self.pos += 1;
                                if self.input.get(self.pos) == Some(&b'=') { self.pos += 1; Token::new(TokenKind::ArithShiftLeftAssign, "<<<=".into(), Span::new(start, self.pos)) }
                                else { Token::new(TokenKind::ArithShiftLeft, "<<<".into(), Span::new(start, self.pos)) }
                            }
                            Some(b'=') => { self.pos += 1; Token::new(TokenKind::ShiftLeftAssign, "<<=".into(), Span::new(start, self.pos)) }
                            _ => Token::new(TokenKind::ShiftLeft, "<<".into(), Span::new(start, self.pos))
                        }
                    }
                    Some(b'-') => {
                        self.pos += 1;
                        if self.input.get(self.pos) == Some(&b'>') { self.pos += 1; Token::new(TokenKind::LogEquiv, "<->".into(), Span::new(start, self.pos)) }
                        else { self.pos -= 1; Token::new(TokenKind::Lt, "<".into(), Span::new(start, self.pos)) }
                    }
                    _ => Token::new(TokenKind::Lt, "<".into(), Span::new(start, self.pos))
                }
            }
            b'>' => {
                self.pos += 1;
                match self.input.get(self.pos) {
                    Some(b'=') => { self.pos += 1; Token::new(TokenKind::Geq, ">=".into(), Span::new(start, self.pos)) }
                    Some(b'>') => {
                        self.pos += 1;
                        match self.input.get(self.pos) {
                            Some(b'>') => { self.pos += 1;
                                if self.input.get(self.pos) == Some(&b'=') { self.pos += 1; Token::new(TokenKind::ArithShiftRightAssign, ">>>=".into(), Span::new(start, self.pos)) }
                                else { Token::new(TokenKind::ArithShiftRight, ">>>".into(), Span::new(start, self.pos)) }
                            }
                            Some(b'=') => { self.pos += 1; Token::new(TokenKind::ShiftRightAssign, ">>=".into(), Span::new(start, self.pos)) }
                            _ => Token::new(TokenKind::ShiftRight, ">>".into(), Span::new(start, self.pos))
                        }
                    }
                    _ => Token::new(TokenKind::Gt, ">".into(), Span::new(start, self.pos))
                }
            }
            b'&' => {
                self.pos += 1;
                match self.input.get(self.pos) {
                    Some(b'&') => { self.pos += 1; Token::new(TokenKind::LogAnd, "&&".into(), Span::new(start, self.pos)) }
                    Some(b'=') => { self.pos += 1; Token::new(TokenKind::AndAssign, "&=".into(), Span::new(start, self.pos)) }
                    _ => Token::new(TokenKind::BitAnd, "&".into(), Span::new(start, self.pos))
                }
            }
            b'|' => {
                self.pos += 1;
                match self.input.get(self.pos) {
                    Some(b'|') => { self.pos += 1; Token::new(TokenKind::LogOr, "||".into(), Span::new(start, self.pos)) }
                    Some(b'=') => {
                        self.pos += 1;
                        if self.input.get(self.pos) == Some(&b'>') {
                            self.pos += 1;
                            Token::new(TokenKind::OrFatArrow, "|=>".into(), Span::new(start, self.pos))
                        } else {
                            Token::new(TokenKind::OrAssign, "|=".into(), Span::new(start, self.pos))
                        }
                    }
                    Some(b'-') => {
                        self.pos += 1;
                        if self.input.get(self.pos) == Some(&b'>') {
                            self.pos += 1;
                            Token::new(TokenKind::OrMinusArrow, "|->".into(), Span::new(start, self.pos))
                        } else {
                            // Backtrack or just bitwise or and minus. Since `-` isn't assignment, return `|` and leave `-`
                            self.pos -= 1;
                            Token::new(TokenKind::BitOr, "|".into(), Span::new(start, self.pos))
                        }
                    }
                    _ => Token::new(TokenKind::BitOr, "|".into(), Span::new(start, self.pos))
                }
            }
            b'^' => {
                self.pos += 1;
                match self.input.get(self.pos) {
                    Some(b'~') => { self.pos += 1; Token::new(TokenKind::BitXnor, "^~".into(), Span::new(start, self.pos)) }
                    Some(b'=') => { self.pos += 1; Token::new(TokenKind::XorAssign, "^=".into(), Span::new(start, self.pos)) }
                    _ => Token::new(TokenKind::BitXor, "^".into(), Span::new(start, self.pos))
                }
            }
            b'#' => {
                self.pos += 1;
                if self.input.get(self.pos) == Some(&b'#') {
                    self.pos += 1; Token::new(TokenKind::HashHash, "##".into(), Span::new(start, self.pos))
                } else {
                    Token::new(TokenKind::Hash, "#".into(), Span::new(start, self.pos))
                }
            }
            b':' => {
                self.pos += 1;
                match self.input.get(self.pos) {
                    Some(b':') => { self.pos += 1; Token::new(TokenKind::DoubleColon, "::".into(), Span::new(start, self.pos)) }
                    Some(b'/') => { self.pos += 1; Token::new(TokenKind::ColonSlash, ":/".into(), Span::new(start, self.pos)) }
                    Some(b'=') => { self.pos += 1; Token::new(TokenKind::ColonAssign, ":=".into(), Span::new(start, self.pos)) }
                    _ => Token::new(TokenKind::Colon, ":".into(), Span::new(start, self.pos))
                }
            }
            _ => self.make_token(start, TokenKind::Unknown),
        }
    }

    fn scan_string(&mut self, start: usize) -> Token {
        // IEEE 1800-2023 §5.9: triple-quoted string literal (""" ... """).
        // Newlines are preserved and a lone `"` (or `""`) inside does not
        // terminate the literal — only `"""` does. Gated on the SV-2023
        // mode flag; in 2017 mode `"""x"""` lexes as two empty strings.
        if crate::is_sv2023()
            && self.input.get(self.pos + 1) == Some(&b'"')
            && self.input.get(self.pos + 2) == Some(&b'"')
        {
            self.pos += 3; // skip opening """
            while self.pos < self.input.len() {
                if self.input[self.pos] == b'\\' && self.pos + 1 < self.input.len() {
                    self.pos += 2;
                    continue;
                }
                if self.input[self.pos] == b'"'
                    && self.input.get(self.pos + 1) == Some(&b'"')
                    && self.input.get(self.pos + 2) == Some(&b'"')
                {
                    self.pos += 3;
                    break;
                }
                self.pos += 1;
            }
            let text = String::from_utf8_lossy(&self.input[start..self.pos]).to_string();
            return Token::new(TokenKind::TripleStringLiteral, text, Span::new(start, self.pos));
        }

        self.pos += 1; // skip opening "
        while self.pos < self.input.len() {
            if self.input[self.pos] == b'\\' { self.pos += 2; continue; }
            if self.input[self.pos] == b'"' { self.pos += 1; break; }
            self.pos += 1;
        }
        let text = String::from_utf8_lossy(&self.input[start..self.pos]).to_string();
        Token::new(TokenKind::StringLiteral, text, Span::new(start, self.pos))
    }

    fn scan_directive(&mut self, start: usize) -> Token {
        self.pos += 1; // skip `
        while self.pos < self.input.len() && (self.input[self.pos].is_ascii_alphanumeric() || self.input[self.pos] == b'_') {
            self.pos += 1;
        }
        let text = String::from_utf8_lossy(&self.input[start..self.pos]).to_string();
        // §22.14: track `begin_keywords "<version>"` / `end_keywords` so the
        // identifier scanner can downgrade SV-only keywords in legacy regions.
        // The version string is consumed here (not emitted as a separate token).
        if text == "`begin_keywords" {
            let save = self.pos;
            while self.pos < self.input.len()
                && (self.input[self.pos] == b' ' || self.input[self.pos] == b'\t') {
                self.pos += 1;
            }
            if self.pos < self.input.len() && self.input[self.pos] == b'"' {
                self.pos += 1; // opening quote
                let vstart = self.pos;
                while self.pos < self.input.len() && self.input[self.pos] != b'"' {
                    self.pos += 1;
                }
                let ver = String::from_utf8_lossy(&self.input[vstart..self.pos]).to_string();
                if self.pos < self.input.len() { self.pos += 1; } // closing quote
                self.kw_stack.push(ver.starts_with("1364"));
            } else {
                // Malformed (no version) — keep the stack balanced anyway.
                self.pos = save;
                self.kw_stack.push(false);
            }
            return Token::new(TokenKind::Directive, text, Span::new(start, self.pos));
        }
        if text == "`end_keywords" {
            self.kw_stack.pop();
            return Token::new(TokenKind::Directive, text, Span::new(start, self.pos));
        }
        Token::new(TokenKind::Directive, text, Span::new(start, self.pos))
    }

    fn scan_system_id(&mut self, start: usize) -> Token {
        self.pos += 1; // skip $
        while self.pos < self.input.len() && (self.input[self.pos].is_ascii_alphanumeric() || self.input[self.pos] == b'_' || self.input[self.pos] == b'$') {
            self.pos += 1;
        }
        let text = String::from_utf8_lossy(&self.input[start..self.pos]).to_string();
        Token::new(TokenKind::SystemIdentifier, text, Span::new(start, self.pos))
    }

    fn scan_escaped_id(&mut self, start: usize) -> Token {
        self.pos += 1; // skip backslash
        while self.pos < self.input.len() && !self.input[self.pos].is_ascii_whitespace() {
            self.pos += 1;
        }
        let text = String::from_utf8_lossy(&self.input[start..self.pos]).to_string();
        Token::new(TokenKind::EscapedIdentifier, text, Span::new(start, self.pos))
    }

    fn scan_identifier(&mut self, start: usize) -> Token {
        while self.pos < self.input.len() && (self.input[self.pos].is_ascii_alphanumeric() || self.input[self.pos] == b'_' || self.input[self.pos] == b'$') {
            self.pos += 1;
        }
        let text = String::from_utf8_lossy(&self.input[start..self.pos]).to_string();
        let mut kind = keyword(&text).unwrap_or(TokenKind::Identifier);
        // Verilog-AMS adds reserved words that are legal SV identifiers, so
        // they are keywords only under `--ams` (see `sv_parser::is_ams`).
        // Checked after the IEEE 1800 table and only on a would-be identifier,
        // so AMS mode can never shadow a SystemVerilog keyword.
        if kind == TokenKind::Identifier && crate::is_ams() {
            if let Some(k) = ams_keyword(&text) {
                kind = k;
            }
        }
        // §22.14: inside a `begin_keywords "1364-*"` region, a SystemVerilog-
        // only keyword is a legal identifier (e.g. `reg logic;` declares a reg
        // named `logic` in Verilog-2001).
        if self.kw_stack.last().copied().unwrap_or(false) && is_sv_only_keyword(&text) {
            kind = TokenKind::Identifier;
        }
        Token::new(kind, text, Span::new(start, self.pos))
    }

    fn scan_number(&mut self, start: usize) -> Token {
        // Consume decimal digits (and underscores)
        while self.pos < self.input.len() && (self.input[self.pos].is_ascii_digit() || self.input[self.pos] == b'_') {
            self.pos += 1;
        }
        // Check for based literal: <size>'<base><value>. IEEE 1800-2017
        // §5.7.1 permits whitespace between the size and the base specifier
        // (`32 'h ff`), so probe past spaces/tabs before the apostrophe and
        // only commit if a real base specifier follows.
        let mut probe = self.pos;
        while probe < self.input.len() && (self.input[probe] == b' ' || self.input[probe] == b'\t') {
            probe += 1;
        }
        if probe < self.input.len() && self.input[probe] == b'\'' {
            let next = self.input.get(probe + 1).copied().unwrap_or(0);
            if matches!(next, b's' | b'S' | b'b' | b'B' | b'o' | b'O' | b'd' | b'D' | b'h' | b'H') {
                self.pos = probe; // consume the inter-token whitespace
                self.pos += 1; // skip '
                if matches!(self.input.get(self.pos), Some(b's' | b'S')) { self.pos += 1; }
                if self.pos < self.input.len() && matches!(self.input[self.pos], b'b' | b'B' | b'o' | b'O' | b'd' | b'D' | b'h' | b'H') {
                    self.pos += 1;
                }
                // IEEE 1800-2017 §5.7.1: whitespace allowed between base and value
                while self.pos < self.input.len() && (self.input[self.pos] == b' ' || self.input[self.pos] == b'\t') {
                    self.pos += 1;
                }
                while self.pos < self.input.len() && (self.input[self.pos].is_ascii_alphanumeric() || self.input[self.pos] == b'_' || self.input[self.pos] == b'?' || self.input[self.pos] == b'x' || self.input[self.pos] == b'X' || self.input[self.pos] == b'z' || self.input[self.pos] == b'Z') {
                    self.pos += 1;
                }
                let text = String::from_utf8_lossy(&self.input[start..self.pos]).to_string();
                return Token::new(TokenKind::IntegerLiteral, text, Span::new(start, self.pos));
            }
        }
        // Check for real literal: digits.digits or digitsEexp
        if self.pos < self.input.len() && self.input[self.pos] == b'.' && self.input.get(self.pos + 1).map_or(false, |c| c.is_ascii_digit()) {
            self.pos += 1;
            while self.pos < self.input.len() && (self.input[self.pos].is_ascii_digit() || self.input[self.pos] == b'_') { self.pos += 1; }
            // Optional exponent. IEEE 1800-2017 §5.7.2: the exponent REQUIRES
            // at least one digit after `e[+-]`. Mirror the no-dot path below and
            // backtrack when it is missing, so `1.0e+`/`1.0e`/`1.0e-` do not
            // silently consume `e[+-]` into a token that later parses to 0.
            // Leaving `e...` unconsumed re-lexes it as an identifier, yielding a
            // real syntax error rather than silent garbage.
            if self.pos < self.input.len() && matches!(self.input[self.pos], b'e' | b'E') {
                let exp_start = self.pos;
                self.pos += 1;
                if self.pos < self.input.len() && matches!(self.input[self.pos], b'+' | b'-') { self.pos += 1; }
                if self.pos < self.input.len() && self.input[self.pos].is_ascii_digit() {
                    while self.pos < self.input.len() && (self.input[self.pos].is_ascii_digit() || self.input[self.pos] == b'_') { self.pos += 1; }
                } else {
                    self.pos = exp_start; // malformed exponent: no digits after e[+-]
                }
            }
            // Time-unit suffix on a real (1800-2017 §3.14.2): treat
            // `1.250ns` as a single TimeLiteral, not Real + Ident.
            if self.pos + 1 < self.input.len() {
                let rest = &self.input[self.pos..];
                for suffix in &[b"ns" as &[u8], b"us", b"ms", b"ps", b"fs", b"s"] {
                    if rest.starts_with(suffix)
                        && !rest.get(suffix.len()).map_or(false, |c| c.is_ascii_alphanumeric())
                    {
                        self.pos += suffix.len();
                        let text = String::from_utf8_lossy(&self.input[start..self.pos]).to_string();
                        return Token::new(TokenKind::TimeLiteral, text, Span::new(start, self.pos));
                    }
                }
            }
            let text = String::from_utf8_lossy(&self.input[start..self.pos]).to_string();
            return Token::new(TokenKind::RealLiteral, text, Span::new(start, self.pos));
        }
        // Exponent without decimal point
        if self.pos < self.input.len() && matches!(self.input[self.pos], b'e' | b'E') {
            let saved = self.pos;
            self.pos += 1;
            if self.pos < self.input.len() && matches!(self.input[self.pos], b'+' | b'-') { self.pos += 1; }
            if self.pos < self.input.len() && self.input[self.pos].is_ascii_digit() {
                while self.pos < self.input.len() && (self.input[self.pos].is_ascii_digit() || self.input[self.pos] == b'_') { self.pos += 1; }
                let text = String::from_utf8_lossy(&self.input[start..self.pos]).to_string();
                return Token::new(TokenKind::RealLiteral, text, Span::new(start, self.pos));
            }
            self.pos = saved;
        }
        // Time literal check
        if self.pos + 1 < self.input.len() {
            let rest = &self.input[self.pos..];
            for suffix in &[b"ns" as &[u8], b"us", b"ms", b"ps", b"fs", b"s"] {
                if rest.starts_with(suffix) && !rest.get(suffix.len()).map_or(false, |c| c.is_ascii_alphanumeric()) {
                    self.pos += suffix.len();
                    let text = String::from_utf8_lossy(&self.input[start..self.pos]).to_string();
                    return Token::new(TokenKind::TimeLiteral, text, Span::new(start, self.pos));
                }
            }
        }
        let text = String::from_utf8_lossy(&self.input[start..self.pos]).to_string();
        Token::new(TokenKind::IntegerLiteral, text, Span::new(start, self.pos))
    }

    fn scan_based_number(&mut self, start: usize) -> Token {
        self.pos += 1; // skip '
        let mut p = self.pos;
        if p < self.input.len() && matches!(self.input[p], b's' | b'S') { p += 1; }
        let has_base = p < self.input.len()
            && matches!(self.input[p], b'b' | b'B' | b'o' | b'O' | b'd' | b'D' | b'h' | b'H');
        if !has_base {
            // No base specifier after `'` — this is a cast operator (`expr'(…)`)
            // or an assignment pattern, NOT a based literal. Emit a bare `'`
            // token WITHOUT consuming any following whitespace, so a spaced
            // cast like `(w) ' (v)` still has `text == "'"` for the parser's
            // cast handler. (Consuming the space here was tokenizing `"' "`,
            // breaking real-world RTL such as basejump's `(nodes_p) ' (0)`.)
            return Token::new(TokenKind::IntegerLiteral, "'".into(), Span::new(start, self.pos));
        }
        self.pos = p + 1; // consume optional sign + base specifier
        // IEEE 1800-2017 §5.7.1: whitespace allowed between base and value
        while self.pos < self.input.len() && (self.input[self.pos] == b' ' || self.input[self.pos] == b'\t') {
            self.pos += 1;
        }
        while self.pos < self.input.len() && (self.input[self.pos].is_ascii_alphanumeric() || self.input[self.pos] == b'_' || self.input[self.pos] == b'?' || self.input[self.pos] == b'x' || self.input[self.pos] == b'X' || self.input[self.pos] == b'z' || self.input[self.pos] == b'Z') {
            self.pos += 1;
        }
        let text = String::from_utf8_lossy(&self.input[start..self.pos]).to_string();
        Token::new(TokenKind::IntegerLiteral, text, Span::new(start, self.pos))
    }
}

/// IEEE 1800-2023 §B.1 vs §22.14: a keyword that SystemVerilog adds over
/// Verilog-1364 (2001). Inside a `begin_keywords "1364-*"` region these are not
/// reserved and lex as ordinary identifiers. Verilog-2001 keywords (`reg`,
/// `wire`, `module`, `begin`, `if`, …) are deliberately excluded so they stay
/// reserved. The set is generous — it only ever applies inside a (rare) legacy
/// keyword region, so over-inclusion is harmless while under-inclusion would
/// leave a legacy identifier wrongly reserved.
fn is_sv_only_keyword(s: &str) -> bool {
    matches!(s,
        // data types
        "logic" | "bit" | "byte" | "shortint" | "int" | "longint"
        | "shortreal" | "void" | "chandle" | "string" | "var" | "type"
        | "enum" | "struct" | "union" | "packed" | "tagged" | "const"
        // classes / OOP
        | "class" | "endclass" | "extends" | "implements" | "super" | "this"
        | "virtual" | "pure" | "local" | "protected" | "rand" | "randc"
        | "constraint" | "solve" | "before" | "null" | "new" | "extern"
        | "forkjoin" | "interface" | "endinterface" | "modport"
        // procedural / control additions
        | "always_comb" | "always_ff" | "always_latch" | "final" | "do"
        | "return" | "break" | "continue" | "unique" | "unique0" | "priority"
        | "iff" | "inside" | "dist" | "with" | "throughout" | "within"
        | "first_match" | "matches" | "ref" | "context" | "import" | "export"
        // assertions / coverage
        | "assert" | "assume" | "cover" | "property" | "endproperty"
        | "sequence" | "endsequence" | "expect" | "covergroup" | "endgroup"
        | "coverpoint" | "cross" | "bins" | "binsof" | "intersect" | "wildcard"
        | "ignore_bins" | "illegal_bins"
        // clocking / programs / packages
        | "clocking" | "endclocking" | "program" | "endprogram" | "package"
        | "endpackage" | "timeunit" | "timeprecision"
    )
}
