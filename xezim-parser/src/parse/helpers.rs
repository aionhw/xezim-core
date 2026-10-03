//! Parser helpers: token stream navigation and error recovery.

use super::Parser;
use crate::ast::{Identifier, Span};
use crate::diagnostics::Diagnostic;
use crate::lexer::token::{Token, TokenKind};

impl Parser {
    pub(super) fn current(&self) -> &Token {
        &self.tokens[self.pos.min(self.tokens.len() - 1)]
    }

    pub(super) fn current_kind(&self) -> TokenKind {
        self.current().kind
    }

    pub(super) fn peek_kind(&self) -> TokenKind {
        self.tokens
            .get(self.pos + 1)
            .map(|t| t.kind)
            .unwrap_or(TokenKind::Eof)
    }

    #[allow(dead_code)]
    pub(super) fn peek_kind_n(&self, n: usize) -> TokenKind {
        self.tokens
            .get(self.pos + n)
            .map(|t| t.kind)
            .unwrap_or(TokenKind::Eof)
    }

    pub(super) fn at(&self, kind: TokenKind) -> bool {
        self.current_kind() == kind
    }

    pub(super) fn at_any(&self, kinds: &[TokenKind]) -> bool {
        kinds.contains(&self.current_kind())
    }

    pub(super) fn bump(&mut self) -> Token {
        let tok = self.tokens[self.pos.min(self.tokens.len() - 1)].clone();
        if self.pos < self.tokens.len() {
            self.pos += 1;
        }
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
        if self.at(kind) {
            Some(self.bump())
        } else {
            None
        }
    }

    pub(super) fn span_from(&self, start: usize) -> Span {
        let end = if self.pos > 0 {
            self.tokens[self.pos - 1].span.end
        } else {
            start
        };
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
        if self.at(TokenKind::Semicolon) {
            self.bump();
        }
    }

    pub(super) fn parse_identifier(&mut self) -> Identifier {
        let tok = self.current().clone();
        match tok.kind {
            TokenKind::EscapedIdentifier => {
                self.bump();
                // IEEE 1800-2017 §5.6.1: an escaped identifier (`\cpu3 `) is the
                // same identifier as the nonescaped spelling (`cpu3`). Strip the
                // leading backslash so both forms resolve to one symbol.
                let name = tok.text.strip_prefix('\\').unwrap_or(&tok.text).to_string();
                Identifier {
                    name,
                    span: tok.span,
                }
            }
            TokenKind::Identifier => {
                self.bump();
                Identifier {
                    name: tok.text,
                    span: tok.span,
                }
            }
            _ => {
                self.error(format!(
                    "expected identifier, found {:?} '{}'",
                    tok.kind, tok.text
                ));
                Identifier {
                    name: String::from("<e>"),
                    span: tok.span,
                }
            }
        }
    }

    pub(super) fn parse_end_label(&mut self) -> Option<Identifier> {
        if self.eat(TokenKind::Colon).is_some() {
            let id = if self.at(TokenKind::KwNew) {
                let tok = self.bump();
                Identifier {
                    name: tok.text,
                    span: tok.span,
                }
            } else {
                self.parse_identifier()
            };
            // Some sources spell `endpackage : name;` with a trailing `;`
            // (lenient over strict SV §22.4.2 grammar — accepted by other
            // simulators). Eat it here so the outer description
            // loop doesn't trip on the lone semicolon.
            let _ = self.eat(TokenKind::Semicolon);
            Some(id)
        } else {
            None
        }
    }

    /// IEEE 1800-2023 §8.20.5: optional `:final` / `:extends` / `:initial`
    /// specifier on a method/class. Consumes the colon and keyword together
    /// only when (a) SV-2023 is enabled and (b) the next two tokens form a
    /// valid specifier; otherwise leaves the cursor untouched.
    pub(super) fn parse_optional_method_specifier(
        &mut self,
    ) -> Option<crate::ast::decl::MethodSpecifier> {
        use crate::ast::decl::MethodSpecifier;
        if !crate::is_sv2023() {
            return None;
        }
        if !self.at(TokenKind::Colon) {
            return None;
        }
        let next = self.peek_kind();
        let spec = match next {
            TokenKind::KwFinal => MethodSpecifier::Final,
            TokenKind::KwExtends => MethodSpecifier::Extends,
            TokenKind::KwInitial => MethodSpecifier::Initial,
            _ => return None,
        };
        self.bump(); // ':'
        self.bump(); // keyword
        Some(spec)
    }

    /// Parse an optional `: <name>` end-label on a named `begin`/`fork` block
    /// and, under strict checks, reject a label that disagrees with the block
    /// name (IEEE 1800-2017 §9.3.4). Unlike `parse_end_label_checked` this is
    /// gated on `strict_checks()` (on by default) rather than SV-2023, because
    /// block end-label matching is not a 2023-only rule.
    pub(super) fn parse_block_end_label_checked(&mut self, expected: &str) -> Option<Identifier> {
        let label = self.parse_end_label();
        if crate::strict_checks() {
            if let Some(ref l) = label {
                if l.name != expected && l.name != "<e>" {
                    self.error(format!(
                        "block end label '{}' does not match block name '{}' (IEEE 1800-2017 §9.3.4)",
                        l.name, expected
                    ));
                }
            }
        }
        label
    }

    /// True when the `begin`/`fork` at the cursor follows a `label :` prefix,
    /// which names the block (§9.3.5). Also true after a case-item label; an
    /// end label is then simply not checked.
    pub(super) fn after_block_label(&self) -> bool {
        self.pos >= 2
            && self.tokens[self.pos - 1].kind == TokenKind::Colon
            && matches!(
                self.tokens[self.pos - 2].kind,
                TokenKind::Identifier | TokenKind::EscapedIdentifier
            )
    }

    /// §9.3.4 / §27.3: only a named block may carry an end label.
    pub(super) fn unnamed_block_end_label(&mut self, label: &Identifier) {
        if crate::strict_checks() {
            self.diagnostics.push(crate::diagnostics::Diagnostic::error(
                format!(
                    "end label '{}' on an unnamed block; only a named block may have an \
                     end label (IEEE 1800-2017 §9.3.4)",
                    label.name
                ),
                label.span,
            ));
        }
    }

    /// Parse an optional `: <name>` end-label and, when SV-2023 is enabled,
    /// emit a diagnostic if the label disagrees with the enclosing decl's
    /// name (IEEE 1800-2023 §27.2.1).
    pub(super) fn parse_end_label_checked(&mut self, expected: &str) -> Option<Identifier> {
        let label = self.parse_end_label();
        if crate::is_sv2023() {
            if let Some(ref l) = label {
                if l.name != expected && l.name != "<e>" {
                    self.error(format!(
                        "end-label '{}' does not match declared name '{}' (IEEE 1800-2023 §27.2.1)",
                        l.name, expected
                    ));
                }
            }
        }
        label
    }

    /// Check if the current identifier begins a class-scope EXPRESSION
    /// rather than a type declaration. Walks the full `::`-chained scope
    /// prefix — `pkg::cls::member` (IEEE 1800-2017 §8.23) and
    /// `cls#(N)::member` (§8.25.1) — then classifies by what follows the
    /// chain: an identifier, directly or after balanced `[...]` groups or a
    /// `#(...)` specialization, means a TYPE declaration
    /// (`pkg::cls::TYPE var;`); anything else (`=`, `;`, `(`, `'`, `.`)
    /// means a scoped expression (`pkg::cls::member = 1;`).
    ///
    /// The walk used to stop after ONE `::` link, so a legal
    /// `pkg::cls::TYPE var;` statement looked like a scoped expression and
    /// was routed to the expression parser, which died on the trailing
    /// declarator.
    pub(super) fn peek_is_class_scope(&self) -> bool {
        if !self.at(TokenKind::Identifier) {
            return false;
        }
        let mut p = self.pos + 1;
        let mut guard = 0;
        loop {
            guard += 1;
            if guard > 512 {
                return true;
            }
            match self.tokens.get(p).map(|t| t.kind) {
                // `x ::` — the chain continues with the next link (which
                // may itself carry a `#(...)` before ITS `::`).
                Some(TokenKind::DoubleColon) => {
                    p += 1;
                    match self.tokens.get(p).map(|t| t.kind) {
                        Some(TokenKind::Identifier) => p += 1,
                        // Malformed (`pkg::;`) — let the expression path
                        // report it, as the old single-link walk did.
                        _ => return true,
                    }
                }
                // `x #(...)` — a specialization of the link just consumed.
                // `::` after it continues the chain (class scope,
                // `cls#(N)::member`); an identifier means a declaration
                // (`cls#(N) var;`); anything else is an expression.
                Some(TokenKind::Hash)
                    if self.tokens.get(p + 1).map(|t| t.kind) == Some(TokenKind::LParen) =>
                {
                    p = self.peek_past_balanced_parens(p + 1);
                    match self.tokens.get(p).map(|t| t.kind) {
                        Some(TokenKind::DoubleColon) => {}
                        Some(TokenKind::Identifier) => return false,
                        _ => return true,
                    }
                }
                // `Type var` — a declaration.
                Some(TokenKind::Identifier) => return false,
                // `Type [dims] var` — a declaration with packed dimensions
                // (§7.4.1: possibly several consecutive bracket groups).
                // Balance them all, then decide.
                Some(TokenKind::LBracket) => {
                    let mut depth: i32 = 0;
                    while p < self.tokens.len() {
                        match self.tokens[p].kind {
                            TokenKind::LBracket => depth += 1,
                            TokenKind::RBracket => {
                                depth -= 1;
                                if depth == 0 {
                                    p += 1;
                                    if self.tokens.get(p).map(|t| t.kind)
                                        != Some(TokenKind::LBracket)
                                    {
                                        break;
                                    }
                                    continue;
                                }
                            }
                            TokenKind::Eof => break,
                            _ => {}
                        }
                        p += 1;
                    }
                    return self.tokens.get(p).map(|t| t.kind) != Some(TokenKind::Identifier);
                }
                // `=`, `;`, `(`, `'`, `.`, … — a scoped expression.
                _ => return true,
            }
        }
    }

    /// Index just past the `)` matching the `(` at `open_idx` (or the end
    /// of the token stream if unbalanced). Pure lookahead helper.
    fn peek_past_balanced_parens(&self, open_idx: usize) -> usize {
        let mut p = open_idx;
        // Start at 0 so the `(` at `open_idx` itself brings the depth to 1;
        // starting at 1 double-counted it and the walk then overshot the
        // matching `)` (to the next `)` or EOF), misclassifying
        // `Alpha#(int) a;` as a scoped expression.
        let mut depth = 0;
        while p < self.tokens.len() {
            match self.tokens[p].kind {
                TokenKind::LParen => depth += 1,
                TokenKind::RParen => depth -= 1,
                _ => {}
            }
            p += 1;
            if depth == 0 {
                break;
            }
        }
        p
    }
}