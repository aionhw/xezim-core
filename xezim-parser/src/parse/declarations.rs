//! Declaration parsing (IEEE 1800-2017 §A.2)

use super::Parser;
use crate::ast::decl::*;
use crate::ast::types::*;
use crate::ast::stmt::VarDeclarator;
use crate::ast::Identifier;
use crate::lexer::token::TokenKind;

impl Parser {
    pub(super) fn parse_parameter_port_list(&mut self) -> Vec<ParameterDeclaration> {
        let mut params = Vec::new();
        if self.eat(TokenKind::Hash).is_none() { return params; }
        if self.eat(TokenKind::LParen).is_none() { return params; }
        loop {
            if self.at(TokenKind::RParen) || self.at(TokenKind::Eof) { break; }
            params.push(self.parse_parameter_declaration());
            if self.eat(TokenKind::Comma).is_none() { break; }
        }
        self.expect(TokenKind::RParen);
        params
    }

    pub(super) fn parse_parameter_declaration(&mut self) -> ParameterDeclaration {
        let start = self.current().span.start;
        let local = match self.current_kind() {
            TokenKind::KwParameter => { self.bump(); false }
            TokenKind::KwLocalparam => { self.bump(); true }
            _ => false,
        };
        if self.at(TokenKind::KwType) {
            self.bump();
            let mut assignments = Vec::new();
            let name = self.parse_identifier();
            let init = if self.eat(TokenKind::Assign).is_some() {
                Some(self.parse_data_type())
            } else { None };
            assignments.push(TypeParamAssignment { name, init, span: self.span_from(start) });
            return ParameterDeclaration { local, kind: ParameterKind::Type { assignments }, span: self.span_from(start) };
        }
        // Check if there's an explicit data type keyword or just an implicit type
        // "parameter integer X = ..." has explicit type
        // "parameter WIDTH = ..." has implicit type (identifier followed by =)
        // "parameter [7:0] X = ..." has implicit type with range
        let data_type = if self.is_data_type_keyword() {
            self.parse_data_type()
        } else if self.looks_like_parameter_type_reference() {
            self.parse_data_type()
        } else if self.at(TokenKind::LBracket) {
            // Implicit type with packed dimensions
            let dimensions = self.parse_packed_dimensions();
            DataType::Implicit { signing: None, dimensions, span: self.span_from(start) }
        } else {
            // No explicit type - implicit
            DataType::Implicit { signing: None, dimensions: Vec::new(), span: self.span_from(start) }
        };
        let mut assignments = Vec::new();
        loop {
            let astart = self.current().span.start;
            let name = self.parse_identifier();
            let dimensions = self.parse_unpacked_dimensions();
            let init = if self.eat(TokenKind::Assign).is_some() {
                Some(self.parse_expression())
            } else { None };
            assignments.push(ParamAssignment { name, dimensions, init, span: self.span_from(astart) });
            // Don't consume comma if next token after comma is parameter/localparam
            // (those belong to the parameter port list, not this declaration)
            if self.at(TokenKind::Comma) {
                let next = self.peek_kind();
                if next == TokenKind::KwParameter || next == TokenKind::KwLocalparam {
                    break;
                }
                self.bump(); // consume comma
            } else {
                break;
            }
        }
        ParameterDeclaration { local, kind: ParameterKind::Data { data_type, assignments }, span: self.span_from(start) }
    }

    fn looks_like_parameter_type_reference(&self) -> bool {
        matches!(self.current_kind(), TokenKind::Identifier | TokenKind::EscapedIdentifier) &&
            matches!(
                self.peek_kind(),
                TokenKind::Identifier | TokenKind::EscapedIdentifier | TokenKind::DoubleColon | TokenKind::Hash | TokenKind::LBracket
            )
    }

    pub(super) fn parse_parameter_decl_stmt(&mut self) -> ParameterDeclaration {
        let decl = self.parse_parameter_declaration();
        self.expect(TokenKind::Semicolon);
        decl
    }

    pub(super) fn parse_typedef_declaration(&mut self) -> TypedefDeclaration {
        let start = self.current().span.start;
        self.expect(TokenKind::KwTypedef);
        if self.eat(TokenKind::KwClass).is_some() {
            let name = self.parse_identifier();
            self.expect(TokenKind::Semicolon);
            return TypedefDeclaration {
                data_type: DataType::Void(self.span_from(start)), // Placeholder for forward class
                name,
                dimensions: Vec::new(),
                span: self.span_from(start),
            };
        }
        let data_type = self.parse_data_type();
        let name = self.parse_identifier();
        let dimensions = self.parse_unpacked_dimensions();
        self.expect(TokenKind::Semicolon);
        TypedefDeclaration { data_type, name, dimensions, span: self.span_from(start) }
    }

    pub(super) fn parse_import_declaration(&mut self) -> ImportDeclaration {
        let start = self.current().span.start;
        self.expect(TokenKind::KwImport);
        let mut items = Vec::new();
        loop {
            let item_start = self.current().span.start;
            let package = self.parse_identifier();
            self.expect(TokenKind::DoubleColon);
            let item = if self.eat(TokenKind::Star).is_some() { None }
            else { Some(self.parse_identifier()) };
            items.push(ImportItem { package, item, span: self.span_from(item_start) });
            if self.eat(TokenKind::Comma).is_none() { break; }
        }
        self.expect(TokenKind::Semicolon);
        ImportDeclaration { items, span: self.span_from(start) }
    }

    pub(super) fn parse_dpi_import(&mut self) -> DPIImport {
        let start = self.current().span.start;
        self.expect(TokenKind::KwImport);
        self.expect(TokenKind::StringLiteral); // "DPI-C" etc
        let property = match self.current_kind() {
            TokenKind::KwContext => { self.bump(); Some(DPIProperty::Context) }
            TokenKind::KwPure => { self.bump(); Some(DPIProperty::Pure) }
            _ => None,
        };
        // optional [c_identifier =]
        let mut c_name = None;
        if self.at(TokenKind::Identifier) && self.peek_kind() == TokenKind::Assign {
            c_name = Some(self.parse_identifier().name);
            self.expect(TokenKind::Assign);
        }
        let proto = if self.at(TokenKind::KwFunction) {
            DPIProto::Function(self.parse_function_prototype())
        } else {
            DPIProto::Task(self.parse_task_prototype())
        };
        DPIImport { property, c_name, proto, span: self.span_from(start) }
    }

    pub(super) fn parse_dpi_export(&mut self) -> DPIExport {
        let start = self.current().span.start;
        self.expect(TokenKind::KwExport);
        self.expect(TokenKind::StringLiteral);
        let mut c_name = None;
        if self.at(TokenKind::Identifier) && self.peek_kind() == TokenKind::Assign {
            c_name = Some(self.parse_identifier().name);
            self.expect(TokenKind::Assign);
        }
        let proto = if self.at(TokenKind::KwFunction) {
            DPIProto::Function(self.parse_function_prototype())
        } else {
            DPIProto::Task(self.parse_task_prototype())
        };
        DPIExport { c_name, proto, span: self.span_from(start) }
    }

    pub(super) fn parse_timeunits_declaration(&mut self) -> TimeunitsDeclaration {
        let start = self.current().span.start;
        let mut unit = None;
        let mut precision = None;
        if self.eat(TokenKind::KwTimeunit).is_some() {
            unit = Some(self.bump().text.clone());
            if self.eat(TokenKind::Slash).is_some() {
                precision = Some(self.bump().text.clone());
            }
        } else if self.eat(TokenKind::KwTimeprecision).is_some() {
            precision = Some(self.bump().text.clone());
        }
        self.expect(TokenKind::Semicolon);
        TimeunitsDeclaration { unit, precision, span: self.span_from(start) }
    }

    pub(super) fn parse_data_declaration(&mut self) -> DataDeclaration {
        let start = self.current().span.start;
        let const_kw = self.eat(TokenKind::KwConst).is_some();
        let var_kw = self.eat(TokenKind::KwVar).is_some();
        let lifetime = self.parse_optional_lifetime();
        let data_type = self.parse_data_type();
        let declarators = self.parse_var_declarator_list();
        self.expect(TokenKind::Semicolon);
        DataDeclaration { const_kw, var_kw, lifetime, data_type, declarators, span: self.span_from(start) }
    }

    pub(super) fn parse_var_declarator_list(&mut self) -> Vec<VarDeclarator> {
        let mut decls = Vec::new();
        loop {
            let start = self.current().span.start;
            let name = self.parse_identifier();
            let dimensions = self.parse_unpacked_dimensions();
            let init = if self.eat(TokenKind::Assign).is_some() {
                Some(self.parse_expression())
            } else { None };
            decls.push(VarDeclarator { name, dimensions, init, span: self.span_from(start) });
            if self.eat(TokenKind::Comma).is_none() { break; }
        }
        decls
    }

    pub(super) fn parse_function_declaration(&mut self) -> FunctionDeclaration {
        let start = self.current().span.start;
        let _virt = self.eat(TokenKind::KwVirtual).is_some();
        self.expect(TokenKind::KwFunction);
        let lifetime = self.parse_optional_lifetime();
        let return_type = if self.is_data_type_keyword() || self.at(TokenKind::KwVoid) ||
                            (self.at(TokenKind::Identifier) && (
                                self.peek_kind() == TokenKind::Identifier ||
                                (self.peek_kind() == TokenKind::DoubleColon && self.peek_kind_n(2) != TokenKind::KwNew) ||
                                self.peek_kind() == TokenKind::Hash ||
                                // `function automatic typedef_t [7:0] name(...)` — packed
                                // dimension on a typedef-named return type.
                                self.peek_kind() == TokenKind::LBracket
                            )) {
            self.parse_data_type()
        } else if self.at(TokenKind::LBracket) {
            // `function automatic [PtrW-1:0] name(...)` — implicit type
            // (just packed dimensions, no leading type name).
            let dims = self.parse_packed_dimensions();
            DataType::Implicit { signing: None, dimensions: dims, span: self.span_from(start) }
        } else {
            DataType::Implicit { signing: None, dimensions: Vec::new(), span: self.span_from(start) }
        };
        // Name can be 'new', a regular identifier, or class::method
        let name = self.parse_method_name();
        let ports = self.parse_function_ports();
        self.expect(TokenKind::Semicolon);
        let mut items = Vec::new();
        while !self.at(TokenKind::KwEndfunction) && !self.at(TokenKind::Eof) {
            items.push(self.parse_statement());
        }
        self.expect(TokenKind::KwEndfunction);
        let endlabel = self.parse_end_label();
        FunctionDeclaration { lifetime, return_type, name, ports, items, endlabel, span: self.span_from(start) }
    }

    pub(super) fn parse_task_declaration(&mut self) -> TaskDeclaration {
        let start = self.current().span.start;
        let _virt = self.eat(TokenKind::KwVirtual).is_some();
        self.expect(TokenKind::KwTask);
        let lifetime = self.parse_optional_lifetime();
        // Name can be 'new', a regular identifier, or class::method
        let name = self.parse_method_name();
        let ports = self.parse_function_ports();
        self.expect(TokenKind::Semicolon);
        let mut items = Vec::new();
        while !self.at(TokenKind::KwEndtask) && !self.at(TokenKind::Eof) {
            items.push(self.parse_statement());
        }
        self.expect(TokenKind::KwEndtask);
        let endlabel = self.parse_end_label();
        TaskDeclaration { lifetime, name, ports, items, endlabel, span: self.span_from(start) }
    }

    /// Parse a method name: handles 'new', regular identifiers, and class_scope::name.
    pub(super) fn parse_method_name(&mut self) -> TypeName {
        let start = self.current().span.start;
        let first = if self.at(TokenKind::KwNew) {
            let tok = self.bump();
            Identifier { name: tok.text.clone(), span: tok.span }
        } else {
            self.parse_identifier()
        };

        if self.at(TokenKind::DoubleColon) {
            self.bump();
            let second = if self.at(TokenKind::KwNew) {
                let tok = self.bump();
                Identifier { name: tok.text.clone(), span: tok.span }
            } else {
                self.parse_identifier()
            };
            TypeName { scope: Some(first), name: second, span: self.span_from(start) }
        } else {
            TypeName { scope: None, name: first, span: self.span_from(start) }
        }
    }
    /// Parse a function prototype (no body, no endfunction). Used for pure virtual.
    /// Syntax: `function [lifetime] [type] name(ports);`
    pub(super) fn parse_function_prototype(&mut self) -> FunctionDeclaration {
        let start = self.current().span.start;
        let _virt = self.eat(TokenKind::KwVirtual).is_some();
        self.expect(TokenKind::KwFunction);

        let lifetime = self.parse_optional_lifetime();
        let return_type = if self.is_data_type_keyword() || self.at(TokenKind::KwVoid) ||
                            (self.at(TokenKind::Identifier) && (
                                self.peek_kind() == TokenKind::Identifier ||
                                (self.peek_kind() == TokenKind::DoubleColon && self.peek_kind_n(2) != TokenKind::KwNew) ||
                                self.peek_kind() == TokenKind::Hash
                            )) {
            self.parse_data_type()
        } else {
            DataType::Implicit { signing: None, dimensions: Vec::new(), span: self.span_from(start) }
        };
        let name = self.parse_method_name();
        let ports = self.parse_function_ports();
        self.expect(TokenKind::Semicolon);
        FunctionDeclaration { lifetime, return_type, name, ports, items: Vec::new(), endlabel: None, span: self.span_from(start) }
    }

    pub(super) fn parse_task_prototype(&mut self) -> TaskDeclaration {
        let start = self.current().span.start;
        self.expect(TokenKind::KwTask);
        let lifetime = self.parse_optional_lifetime();
        let name = self.parse_method_name();
        let ports = self.parse_function_ports();
        self.expect(TokenKind::Semicolon);
        TaskDeclaration { lifetime, name, ports, items: Vec::new(), endlabel: None, span: self.span_from(start) }
    }

    pub(super) fn parse_param_value(&mut self) -> ParamValue {
        // `.NAME(int'(...))` etc. — a type-keyword followed by `'` (apostrophe
        // tokenized as IntegerLiteral with text "'") is a casting expression,
        // not a type-parameter override. Defer to parse_expression in that case.
        let is_type_cast = (self.is_data_type_keyword() || self.at(TokenKind::KwVoid))
            && self.peek_kind() == TokenKind::IntegerLiteral
            && self.tokens.get(self.pos + 1).map(|t| t.text.as_str()).unwrap_or("") == "'";
        if (self.is_data_type_keyword() || self.at(TokenKind::KwVoid)) && !is_type_cast {
            ParamValue::Type(self.parse_data_type())
        } else {
            ParamValue::Expr(self.parse_expression())
        }
    }

    pub(super) fn parse_param_args(&mut self) -> Vec<ParamValue> {
        let mut args = Vec::new();
        let _has_hash = self.eat(TokenKind::Hash).is_some();
        if self.eat(TokenKind::LParen).is_none() { return args; }
        if self.at(TokenKind::RParen) { self.bump(); return args; }
        loop {
            if self.at(TokenKind::RParen) || self.at(TokenKind::Eof) { break; }
            args.push(self.parse_param_value());
            if self.eat(TokenKind::Comma).is_none() { break; }
        }
        self.expect(TokenKind::RParen);
        args
    }
    pub(super) fn parse_function_ports(&mut self) -> Vec<FunctionPort> {
        let mut ports = Vec::new();
        if self.eat(TokenKind::LParen).is_none() { return ports; }
        if self.at(TokenKind::RParen) { self.bump(); return ports; }
        loop {
            if self.at(TokenKind::RParen) || self.at(TokenKind::Eof) { break; }
            let start = self.current().span.start;
            let mut var_kw = self.eat(TokenKind::KwVar).is_some();
            let _const_kw = self.eat(TokenKind::KwConst).is_some();
            if !var_kw && self.at(TokenKind::KwVar) { var_kw = self.eat(TokenKind::KwVar).is_some(); } // Handle var after const
            let direction = self.parse_optional_direction().unwrap_or(PortDirection::Input);

            // Handle 'virtual interface <name>' port type
            if self.at(TokenKind::KwVirtual) && self.peek_kind() == TokenKind::KwInterface {
                self.bump(); // virtual
                self.bump(); // interface
                let iface_name = self.parse_identifier();
                let name = self.parse_identifier();
                let data_type = DataType::TypeReference { name: TypeName { scope: None, name: iface_name, span: self.span_from(start) }, dimensions: Vec::new(), type_args: Vec::new(), span: self.span_from(start) };
                let dimensions = self.parse_unpacked_dimensions();
                let default = if self.eat(TokenKind::Assign).is_some() {
                    Some(self.parse_expression())
                } else { None };
                ports.push(FunctionPort { direction, var_kw, data_type, name, dimensions, default, span: self.span_from(start) });
                if self.eat(TokenKind::Comma).is_none() { break; }
                continue;
            }

            let data_type = if self.is_data_type_keyword() || self.at(TokenKind::KwVoid) {
                self.parse_data_type()
            } else if self.at(TokenKind::Identifier) && matches!(self.peek_kind(), TokenKind::Identifier | TokenKind::Hash | TokenKind::DoubleColon) {
                self.parse_data_type()
            } else if self.at(TokenKind::Identifier) && self.peek_kind() == TokenKind::LBracket {
                // `typedef_t [7:0] port_name` — user-defined type with packed
                // dimensions. Look ahead past the [..] balanced brackets: if
                // the next token after the close-bracket is an identifier
                // (the port name), this is a typedef-with-packed-dims; parse
                // it as a full data type. Otherwise it's the legacy
                // implicit-name-with-unpacked-dims fallback.
                let mut depth: i32 = 0;
                let mut k: usize = 0;
                let mut next_after = TokenKind::Eof;
                loop {
                    let kind = self.peek_kind_n(k + 1);
                    match kind {
                        TokenKind::LBracket => depth += 1,
                        TokenKind::RBracket => {
                            depth -= 1;
                            if depth == 0 {
                                next_after = self.peek_kind_n(k + 2);
                                break;
                            }
                        }
                        TokenKind::Eof => break,
                        _ => {}
                    }
                    k += 1;
                    if k > 64 { break; }
                }
                if matches!(next_after, TokenKind::Identifier) {
                    self.parse_data_type()
                } else {
                    let type_name = self.parse_identifier();
                    DataType::TypeReference { name: TypeName { scope: None, name: type_name, span: self.span_from(start) }, dimensions: Vec::new(), type_args: Vec::new(), span: self.span_from(start) }
                }
            } else if self.at(TokenKind::LBracket) {
                let dims = self.parse_packed_dimensions();
                DataType::Implicit { signing: None, dimensions: dims, span: self.span_from(start) }
            } else {
                DataType::Implicit { signing: None, dimensions: Vec::new(), span: self.span_from(start) }
            };
            let name = self.parse_identifier();
            let dimensions = self.parse_unpacked_dimensions();
            let default = if self.eat(TokenKind::Assign).is_some() {
                Some(self.parse_expression())
            } else { None };
            ports.push(FunctionPort { direction, var_kw, data_type, name, dimensions, default, span: self.span_from(start) });
            if self.eat(TokenKind::Comma).is_none() { break; }
        }
        self.expect(TokenKind::RParen);
        ports
    }

    pub(super) fn parse_package_item(&mut self) -> Option<PackageItem> {
        match self.current_kind() {
            TokenKind::KwParameter => Some(PackageItem::Parameter(self.parse_parameter_decl_stmt())),
            TokenKind::KwLocalparam => Some(PackageItem::Parameter(self.parse_parameter_decl_stmt())),
            TokenKind::KwTypedef => Some(PackageItem::Typedef(self.parse_typedef_declaration())),
            TokenKind::KwFunction => Some(PackageItem::Function(self.parse_function_declaration())),
            TokenKind::KwTask => Some(PackageItem::Task(self.parse_task_declaration())),
            TokenKind::KwImport => {
                if self.peek_kind() == TokenKind::StringLiteral {
                    Some(PackageItem::DPIImport(self.parse_dpi_import()))
                } else {
                    Some(PackageItem::Import(self.parse_import_declaration()))
                }
            }
            TokenKind::KwExport => {
                if self.peek_kind() == TokenKind::StringLiteral {
                    Some(PackageItem::DPIExport(self.parse_dpi_export()))
                } else {
                    // Non-DPI export declarations are not modeled; consume statement.
                    // Return PackageItem::Null (not None) so the package-decl loop
                    // doesn't fall through to its `else { self.bump(); }` recovery
                    // and accidentally swallow the next token (e.g. `endpackage`).
                    self.bump();
                    while !self.at(TokenKind::Semicolon) && !self.at(TokenKind::Eof) { self.bump(); }
                    self.expect(TokenKind::Semicolon);
                    Some(PackageItem::Null)
                }
            }
            TokenKind::KwClass => Some(PackageItem::Class(self.parse_class_declaration())),
            TokenKind::KwChecker => {
                if let Some(ModuleItem::CheckerDeclaration(c)) = self.parse_module_item() {
                    Some(PackageItem::Checker(c))
                } else { None }
            }
            TokenKind::KwLet => {
                if let Some(ModuleItem::LetDeclaration(l)) = self.parse_module_item() {
                    Some(PackageItem::Let(l))
                } else { None }
            }
            TokenKind::KwNettype => {
                if let Some(ModuleItem::NettypeDeclaration(n)) = self.parse_module_item() {
                    Some(PackageItem::Nettype(n))
                } else { None }
            }
            TokenKind::KwExtern => {
                self.bump();
                if self.at(TokenKind::KwFunction) {
                    Some(PackageItem::Function(self.parse_function_prototype()))
                } else if self.at(TokenKind::KwTask) {
                    Some(PackageItem::Task(self.parse_task_prototype()))
                } else {
                    // Could be extern module etc, but UVM uses it for methods
                    self.parse_package_item()
                }
            }
            TokenKind::KwVirtual => {
                if self.peek_kind() == TokenKind::KwClass {
                    Some(PackageItem::Class(self.parse_class_declaration()))
                } else if self.peek_kind() == TokenKind::KwFunction {
                    let mut func = self.parse_function_declaration();
                    // Mark as virtual if we had the keyword (though PackageItem doesn't track it)
                    Some(PackageItem::Function(func))
                } else if self.peek_kind() == TokenKind::KwTask {
                    let mut task = self.parse_task_declaration();
                    Some(PackageItem::Task(task))
                } else {
                    // This shouldn't happen at package level in valid SV, but let's be safe.
                    self.error("expected 'class', 'function', or 'task' after 'virtual'");
                    self.bump();
                    self.parse_package_item()
                }
            }
            _ if self.is_data_type_keyword() || self.at(TokenKind::KwVar) || self.at(TokenKind::KwConst) =>
                Some(PackageItem::Data(self.parse_data_declaration())),
            TokenKind::Identifier => Some(PackageItem::Data(self.parse_data_declaration())),
            TokenKind::Directive => { self.bump(); self.parse_package_item() }
            TokenKind::Semicolon => { self.bump(); self.parse_package_item() }
            _ => None,
        }
    }
}
