//! Parser helpers: token stream navigation and error recovery.

use super::Parser;
use crate::ast::{Identifier, Span};
use crate::lexer::token::{Token, TokenKind};
use crate::diagnostics::Diagnostic;

impl Parser {
    pub(super) fn current(&self) -> &Token {
        &self.tokens[self.pos.min(self.tokens.len() - 1)]
    }

    pub(super) fn current_kind(&self) -> TokenKind {
        self.current().kind
    }

    pub(super) fn peek_kind(&self) -> TokenKind {
        self.tokens.get(self.pos + 1).map(|t| t.kind).unwrap_or(TokenKind::Eof)
    }

    #[allow(dead_code)]
    pub(super) fn peek_kind_n(&self, n: usize) -> TokenKind {
        self.tokens.get(self.pos + n).map(|t| t.kind).unwrap_or(TokenKind::Eof)
    }

    pub(super) fn at(&self, kind: TokenKind) -> bool {
        self.current_kind() == kind
    }

    pub(super) fn at_any(&self, kinds: &[TokenKind]) -> bool {
        kinds.contains(&self.current_kind())
    }

    pub(super) fn bump(&mut self) -> Token {
        let tok = self.tokens[self.pos.min(self.tokens.len() - 1)].clone();
        if self.pos < self.tokens.len() { self.pos += 1; }
        tok
    }

    pub(super) fn expect(&mut self, kind: TokenKind) -> Token {
        if self.at(kind) {
            self.bump()
        } else {
            let tok = self.current().clone();
            self.diagnostics.push(Diagnostic::error(
                format!("expected {:?}, found {:?} '{}'", kind, tok.kind, tok.text),
                tok.span,
            ));
            tok
        }
    }

    pub(super) fn eat(&mut self, kind: TokenKind) -> Option<Token> {
        if self.at(kind) { Some(self.bump()) } else { None }
    }

    pub(super) fn span_from(&self, start: usize) -> Span {
        let end = if self.pos > 0 {
            self.tokens[self.pos - 1].span.end
        } else { start };
        Span::new(start, end)
    }

    pub(super) fn error(&mut self, msg: impl Into<String>) {
        let span = self.current().span;
        self.diagnostics.push(Diagnostic::error(msg, span));
    }

    #[allow(dead_code)]
    pub(super) fn skip_to_semi(&mut self) {
        while !self.at(TokenKind::Semicolon) && !self.at(TokenKind::Eof) {
            self.bump();
        }
        if self.at(TokenKind::Semicolon) { self.bump(); }
    }

    pub(super) fn parse_identifier(&mut self) -> Identifier {
        let tok = self.current().clone();
        match tok.kind {
            TokenKind::Identifier | TokenKind::EscapedIdentifier => {
                self.bump();
                Identifier { name: tok.text, span: tok.span }
            }
            _ => {
                self.error(format!("expected identifier, found {:?} '{}'", tok.kind, tok.text));
                Identifier { name: String::from("<e>"), span: tok.span }
            }
        }
    }

    pub(super) fn parse_end_label(&mut self) -> Option<Identifier> {
        if self.eat(TokenKind::Colon).is_some() {
            if self.at(TokenKind::KwNew) {
                let tok = self.bump();
                Some(Identifier { name: tok.text, span: tok.span })
            } else {
                Some(self.parse_identifier())
            }
        } else { None }
    }

    /// Check if the current identifier is followed by #(...) :: or just ::
    /// which indicates a class scope (expression) rather than a type declaration.
    pub(super) fn peek_is_class_scope(&self) -> bool {
        if !self.at(TokenKind::Identifier) { return false; }
        let mut p = self.pos + 1;
        if let Some(t) = self.tokens.get(p) {
            if t.kind == TokenKind::DoubleColon {
                p += 1;
                // Peek after ::
                if let Some(t2) = self.tokens.get(p) {
                    if t2.kind == TokenKind::Identifier {
                        p += 1;
                        if let Some(t3) = self.tokens.get(p) {
                            // If followed by another identifier, it's pkg::Type var (declaration)
                            return t3.kind != TokenKind::Identifier;
                        }
                    }
                }
                return true;
            }
            if t.kind == TokenKind::Hash {
                p += 1;
                if let Some(t2) = self.tokens.get(p) {
                    if t2.kind == TokenKind::LParen {
                        p += 1;
                        let mut depth = 1;
                        while depth > 0 && p < self.tokens.len() {
                            if self.tokens[p].kind == TokenKind::LParen { depth += 1; }
                            else if self.tokens[p].kind == TokenKind::RParen { depth -= 1; }
                            p += 1;
                        }
                        if let Some(t3) = self.tokens.get(p) {
                            // If it has :: after #(...) it's a class scope
                            return t3.kind == TokenKind::DoubleColon;
                        }
                    }
                }
            }
        }
        false
    }
}
