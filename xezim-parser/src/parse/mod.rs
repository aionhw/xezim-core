//! Recursive descent parser for SystemVerilog IEEE 1800-2017/2023.

mod helpers;
mod types;
mod expressions;
mod statements;
mod declarations;
mod items;

use crate::ast::*;
use crate::ast::decl::{ModuleItem, PackageItem};
use crate::lexer::token::{Token, TokenKind};
use crate::diagnostics::Diagnostic;

pub struct Parser {
    tokens: Vec<Token>,
    pos: usize,
    diagnostics: Vec<Diagnostic>,
}

impl Parser {
    pub fn new(tokens: Vec<Token>) -> Self {
        Self { tokens, pos: 0, diagnostics: Vec::new() }
    }

    pub fn diagnostics(&self) -> &[Diagnostic] { &self.diagnostics }

    pub fn has_errors(&self) -> bool {
        self.diagnostics.iter().any(|d| d.severity == crate::diagnostics::Severity::Error)
    }

    /// source_text ::= { description }
    pub fn parse_source_text(&mut self) -> SourceText {
        let start = self.current().span.start;
        let mut descriptions = Vec::new();
        while !self.at(TokenKind::Eof) {
            if let Some(desc) = self.parse_description() {
                descriptions.push(desc);
            } else {
                self.error(format!("unexpected token: {:?}", self.current().text));
                self.bump();
            }
        }
        SourceText { descriptions, span: self.span_from(start) }
    }

    fn parse_description(&mut self) -> Option<Description> {
        match self.current_kind() {
            TokenKind::KwModule | TokenKind::KwMacromodule =>
                Some(Description::Module(self.parse_module_declaration())),
            TokenKind::KwInterface =>
                Some(Description::Interface(self.parse_interface_declaration())),
            TokenKind::KwProgram =>
                Some(Description::Program(self.parse_program_declaration())),
            TokenKind::KwPackage =>
                Some(Description::Package(self.parse_package_declaration())),
            TokenKind::KwNettype => {
                if let Some(ModuleItem::NettypeDeclaration(n)) = self.parse_module_item() {
                    Some(Description::PackageItem(PackageItem::Nettype(n)))
                } else { None }
            }
            TokenKind::KwClass =>
                Some(Description::Class(self.parse_class_declaration())),
            TokenKind::KwChecker => {
                if let Some(ModuleItem::CheckerDeclaration(c)) = self.parse_module_item() {
                    Some(Description::PackageItem(PackageItem::Checker(c)))
                } else { None }
            }
            TokenKind::KwVirtual if self.peek_kind() == TokenKind::KwClass =>
                Some(Description::Class(self.parse_class_declaration())),
            TokenKind::KwLet => {
                if let Some(ModuleItem::LetDeclaration(l)) = self.parse_module_item() {
                    Some(Description::PackageItem(PackageItem::Let(l)))
                } else { None }
            }
            TokenKind::KwTypedef =>
                Some(Description::TypedefDecl(self.parse_typedef_declaration())),
            TokenKind::KwImport => {
                if self.peek_kind() == TokenKind::StringLiteral {
                    Some(Description::DPIImport(self.parse_dpi_import()))
                } else {
                    Some(Description::ImportDecl(self.parse_import_declaration()))
                }
            }
            TokenKind::KwExport => {
                if self.peek_kind() == TokenKind::StringLiteral {
                    Some(Description::DPIExport(self.parse_dpi_export()))
                } else {
                    self.bump();
                    while !self.at(TokenKind::Semicolon) && !self.at(TokenKind::Eof) { self.bump(); }
                    self.expect(TokenKind::Semicolon);
                    self.parse_description()
                }
            }
            TokenKind::KwExtern => {
                self.bump();
                self.parse_description()
            }
            TokenKind::KwConstraint => {
                // Out-of-class constraint definition at $unit scope:
                // `constraint ClassName::name { ... }[;]`. Parse and discard.
                self.bump();
                let _ = self.parse_hierarchical_identifier();
                if self.at(TokenKind::LBrace) {
                    self.bump();
                    let mut depth = 1;
                    while depth > 0 && !self.at(TokenKind::Eof) {
                        match self.current_kind() {
                            TokenKind::LBrace => depth += 1,
                            TokenKind::RBrace => depth -= 1,
                            _ => {}
                        }
                        self.bump();
                    }
                }
                if self.at(TokenKind::Semicolon) { self.bump(); }
                self.parse_description()
            }
            TokenKind::KwTimeunit | TokenKind::KwTimeprecision =>
                Some(Description::TimeunitsDecl(self.parse_timeunits_declaration())),
            TokenKind::KwFunction =>
                Some(Description::PackageItem(self.parse_package_item().unwrap())),
            TokenKind::KwTask =>
                Some(Description::PackageItem(self.parse_package_item().unwrap())),
            TokenKind::Directive => { self.bump(); self.parse_description() }
            _ => {
                // Top-level data declaration like `string label = "...";` —
                // xezim doesn't model $unit-scope vars, so skip past it.
                if self.is_data_type_keyword() || self.at(TokenKind::KwVar) || self.at(TokenKind::KwConst) {
                    let mut depth = 0i32;
                    while !self.at(TokenKind::Eof) {
                        match self.current_kind() {
                            TokenKind::LBrace | TokenKind::LParen | TokenKind::LBracket => depth += 1,
                            TokenKind::RBrace | TokenKind::RParen | TokenKind::RBracket => depth -= 1,
                            TokenKind::Semicolon if depth <= 0 => { self.bump(); break; }
                            _ => {}
                        }
                        self.bump();
                    }
                    return self.parse_description();
                }
                None
            }
        }
    }
}
