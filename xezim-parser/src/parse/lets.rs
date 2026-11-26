//! IEEE 1800-2023 §11.13 `let` declarations: parsing and scoped expansion.
//!
//! A let instance is expanded where it is written: the parser keeps a stack
//! of the scopes it is inside (design element, generate block, class,
//! subroutine, sequential or parallel block) with the lets each declares, and
//! a reference to a visible let becomes the let body with its actuals
//! substituted (`LetDeclaration::expand`). A name declared in an inner scope
//! (a variable, port, class member) hides an outer let of that name. Lets of
//! the compilation-unit scope, and package lets reached through an import or
//! `pkg::`, are not in the stack; the simulator expands those at run time.

use super::Parser;
use crate::ast::Identifier;
use crate::ast::decl::LetDeclaration;
use crate::ast::expr::Expression;
use crate::ast::module::{AnsiPort, PortList};
use crate::ast::types::DataType;
use crate::lexer::token::TokenKind;
use std::collections::HashMap;
use std::sync::Arc;

/// One lexical scope: each declared name maps to its let, or to None when
/// the name is declared there as something else (hiding outer lets).
pub(super) type LetScope = HashMap<String, Option<Arc<LetDeclaration>>>;

impl<'a> Parser<'a> {
    pub(super) fn push_let_scope(&mut self) {
        self.let_scopes.push(LetScope::new());
    }

    pub(super) fn pop_let_scope(&mut self) {
        if let Some(sc) = self.let_scopes.pop() {
            self.let_live -= sc.values().filter(|v| v.is_some()).count();
        }
    }

    /// `name` is declared in the current scope as something other than a
    /// let, so it hides any outer let of that name. Only tracked while a let
    /// is visible.
    pub(super) fn hide_let_name(&mut self, name: &str) {
        if self.let_live == 0 {
            return;
        }
        if let Some(sc) = self.let_scopes.last_mut() {
            sc.entry(name.to_string()).or_insert(None);
        }
    }

    /// Hide outer lets behind the names a block statement declares.
    pub(super) fn hide_let_names_of_stmt(&mut self, st: &crate::ast::stmt::Statement) {
        if self.let_live == 0 {
            return;
        }
        if let crate::ast::stmt::StatementKind::VarDecl { declarators, .. }
        | crate::ast::stmt::StatementKind::ParamDecl { declarators, .. } = &st.kind
        {
            for d in declarators {
                self.hide_let_name(&d.name.name);
            }
        }
    }

    /// Hide outer lets behind the names a module or generate item declares.
    pub(super) fn hide_let_names_of_item(&mut self, it: &crate::ast::decl::ModuleItem) {
        use crate::ast::decl::{ModuleItem, ParameterKind};
        if self.let_live == 0 {
            return;
        }
        let mut names: Vec<String> = Vec::new();
        match it {
            ModuleItem::DataDeclaration(d) => {
                names.extend(d.declarators.iter().map(|v| v.name.name.clone()))
            }
            ModuleItem::NetDeclaration(n) => {
                names.extend(n.declarators.iter().map(|v| v.name.name.clone()))
            }
            ModuleItem::ParameterDeclaration(p) | ModuleItem::LocalparamDeclaration(p) => {
                if let ParameterKind::Data { assignments, .. } = &p.kind {
                    names.extend(assignments.iter().map(|a| a.name.name.clone()))
                }
            }
            ModuleItem::FunctionDeclaration(f) => names.push(f.name.name.name.clone()),
            ModuleItem::TaskDeclaration(t) => names.push(t.name.name.name.clone()),
            _ => {}
        }
        for n in names {
            self.hide_let_name(&n);
        }
    }

    /// Hide outer lets behind a class member's name.
    pub(super) fn hide_let_names_of_class_item(&mut self, it: &crate::ast::decl::ClassItem) {
        use crate::ast::decl::{ClassItem, ClassMethodKind};
        if self.let_live == 0 {
            return;
        }
        match it {
            ClassItem::Property(p) => {
                for d in &p.declarators {
                    self.hide_let_name(&d.name.name);
                }
            }
            ClassItem::Method(m) => {
                let n = match &m.kind {
                    ClassMethodKind::Function(f)
                    | ClassMethodKind::PureVirtual(f)
                    | ClassMethodKind::Extern(f) => f.name.name.name.clone(),
                    ClassMethodKind::Task(t) => t.name.name.name.clone(),
                };
                self.hide_let_name(&n);
            }
            _ => {}
        }
    }

    /// The let a plain identifier names here, if any.
    pub(super) fn visible_let(&self, name: &str) -> Option<Arc<LetDeclaration>> {
        if self.let_live == 0 {
            return None;
        }
        for sc in self.let_scopes.iter().rev() {
            if let Some(e) = sc.get(name) {
                return e.clone();
            }
        }
        None
    }

    /// Expand a let instance whose name was just consumed; the argument list
    /// (if any) is next.
    pub(super) fn parse_let_instance(
        &mut self,
        ld: &LetDeclaration,
        name: &Identifier,
        start: usize,
    ) -> Expression {
        let args = if self.at(TokenKind::LParen) {
            self.parse_call_args()
        } else {
            Vec::new()
        };
        let span = self.span_from(start);
        match ld.expand(&args, span) {
            Ok(e) => e,
            Err(msg) => {
                self.diagnostics.push(crate::diagnostics::Diagnostic::error(
                    format!("{} (IEEE 1800-2023 §11.13)", msg),
                    name.span,
                ));
                Expression::new(crate::ast::expr::ExprKind::Empty, span)
            }
        }
    }

    /// `let_declaration ::= let let_identifier [ ( [ let_port_list ] ) ] =
    /// expression ;` (A.2.12). The declaration becomes visible in the current
    /// scope once parsed.
    pub(super) fn parse_let_declaration(&mut self) -> LetDeclaration {
        let start = self.current_span().start;
        self.expect(TokenKind::KwLet);
        let name = self.parse_identifier();
        let ports = self.parse_let_port_list();
        self.expect(TokenKind::Assign);
        // The formals hide same-named outer lets inside the body; the body's
        // other references to visible lets are expanded here, in the scope of
        // the declaration (§11.13).
        self.push_let_scope();
        if let PortList::Ansi(ps) = &ports {
            for p in ps {
                if let Some(sc) = self.let_scopes.last_mut() {
                    sc.insert(p.name.name.clone(), None);
                }
            }
        }
        let expr = self.parse_expression();
        self.pop_let_scope();
        self.expect(TokenKind::Semicolon);
        let ld = LetDeclaration {
            name,
            ports,
            expr,
            span: self.span_from(start),
        };
        if let Some(sc) = self.let_scopes.last_mut() {
            let prev = sc.insert(ld.name.name.clone(), Some(Arc::new(ld.clone())));
            if !matches!(prev, Some(Some(_))) {
                self.let_live += 1;
            }
        }
        ld
    }

    /// `let_port_list ::= let_port_item { , let_port_item }` with
    /// `let_port_item ::= { attribute_instance } let_formal_type
    /// formal_port_identifier { variable_dimension } [ = expression ]` and
    /// `let_formal_type ::= data_type_or_implicit | untyped`. A formal with
    /// no type is untyped.
    fn parse_let_port_list(&mut self) -> PortList {
        if self.eat(TokenKind::LParen).is_none() {
            return PortList::Empty;
        }
        let mut ports = Vec::new();
        while !self.at(TokenKind::RParen) && !self.at(TokenKind::Eof) {
            let start = self.current_span().start;
            let data_type: Option<DataType> = if self.eat(TokenKind::KwUntyped).is_some() {
                None
            } else if self.is_data_type_keyword() {
                Some(self.parse_data_type())
            } else if self.at(TokenKind::LBracket) {
                let dims = self.parse_packed_dimensions();
                Some(DataType::Implicit {
                    signing: None,
                    dimensions: dims,
                    span: self.span_from(start),
                })
            } else if self.at(TokenKind::Identifier)
                && (matches!(
                    self.peek_kind(),
                    TokenKind::Identifier | TokenKind::DoubleColon | TokenKind::Hash
                ) || (self.peek_kind() == TokenKind::LBracket && self.type_name_then_dims()))
            {
                Some(self.parse_data_type())
            } else {
                None
            };
            let pname = self.parse_identifier();
            let dimensions = if self.at(TokenKind::LBracket) {
                self.parse_unpacked_dimensions()
            } else {
                Vec::new()
            };
            let default = if self.eat(TokenKind::Assign).is_some() {
                Some(self.parse_expression())
            } else {
                None
            };
            ports.push(AnsiPort {
                attrs: Vec::new(),
                direction: None,
                net_type: None,
                var_kw: false,
                data_type,
                name: pname,
                dimensions,
                default,
                span: self.span_from(start),
            });
            if self.eat(TokenKind::Comma).is_none() {
                break;
            }
        }
        self.expect(TokenKind::RParen);
        if ports.is_empty() {
            PortList::Empty
        } else {
            PortList::Ansi(ports)
        }
    }

    /// At `id [ ... ]`: is it a typedef name with packed dimensions followed
    /// by the formal's name (`word_t [1:0] w`), rather than a formal with an
    /// unpacked dimension (`w [2]`)?
    fn type_name_then_dims(&self) -> bool {
        let mut i = self.pos + 1;
        while self.tokens.get(i).map(|t| t.kind) == Some(TokenKind::LBracket) {
            let mut depth = 0i32;
            while let Some(t) = self.tokens.get(i) {
                match t.kind {
                    TokenKind::LBracket => depth += 1,
                    TokenKind::RBracket => depth -= 1,
                    TokenKind::Eof => return false,
                    _ => {}
                }
                i += 1;
                if depth == 0 {
                    break;
                }
            }
        }
        matches!(
            self.tokens.get(i).map(|t| t.kind),
            Some(TokenKind::Identifier | TokenKind::EscapedIdentifier)
        )
    }
}
