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
            // §6.20.3: a single `parameter type` may declare several comma-
            // separated type assignments — `parameter type A = int, B = X;`.
            loop {
                let astart = self.current().span.start;
                let name = self.parse_identifier();
                // IEEE 1800-2023 §6.20.2.1: `type T extends Base` constrains the
                // type argument to a class derived from `Base`. Gated on
                // --sv2023; in 2017 mode an `extends` here is a parse error.
                let extends = if crate::is_sv2023() && self.eat(TokenKind::KwExtends).is_some() {
                    Some(self.parse_identifier())
                } else {
                    None
                };
                let init = if self.eat(TokenKind::Assign).is_some() {
                    Some(self.parse_data_type())
                } else { None };
                assignments.push(TypeParamAssignment { name, extends, init, span: self.span_from(astart) });
                // A comma followed by a new parameter/localparam/type keyword
                // OR a data-type keyword ends this `type` declaration — e.g.
                // `#(type TYPE = int, string FIELD = "x")` (UVM uvm_utils): the
                // `string` begins a new typed value parameter, not another type
                // assignment. A comma followed by a bare identifier stays a
                // type-assignment continuation (`type A = int, B = bit`).
                if self.at(TokenKind::Comma)
                    && !matches!(self.peek_kind(),
                        TokenKind::KwParameter | TokenKind::KwLocalparam | TokenKind::KwType
                        | TokenKind::KwBit | TokenKind::KwLogic | TokenKind::KwReg
                        | TokenKind::KwByte | TokenKind::KwShortint | TokenKind::KwInt
                        | TokenKind::KwLongint | TokenKind::KwInteger | TokenKind::KwTime
                        | TokenKind::KwReal | TokenKind::KwShortreal | TokenKind::KwRealtime
                        | TokenKind::KwString | TokenKind::KwChandle | TokenKind::KwEvent
                        | TokenKind::KwVoid | TokenKind::KwStruct | TokenKind::KwUnion
                        | TokenKind::KwEnum)
                {
                    self.bump();
                } else {
                    break;
                }
            }
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
            // Don't consume comma if next token after comma starts a NEW
            // parameter declaration rather than another same-type assignment:
            //  - `parameter`/`localparam` keyword, or
            //  - an explicit data-type keyword (`#(int N, int P)` — each is its
            //    own typed param; `#(int A, B)` keeps B as a same-type assign
            //    because B is a bare identifier, handled by the default path).
            if self.at(TokenKind::Comma) {
                let next = self.peek_kind();
                if next == TokenKind::KwParameter || next == TokenKind::KwLocalparam
                    || next == TokenKind::KwType
                    || matches!(next,
                        TokenKind::KwBit | TokenKind::KwLogic | TokenKind::KwReg |
                        TokenKind::KwByte | TokenKind::KwShortint | TokenKind::KwInt |
                        TokenKind::KwLongint | TokenKind::KwInteger | TokenKind::KwTime |
                        TokenKind::KwReal | TokenKind::KwShortreal | TokenKind::KwRealtime |
                        TokenKind::KwString | TokenKind::KwChandle | TokenKind::KwEvent |
                        TokenKind::KwVoid | TokenKind::KwStruct | TokenKind::KwUnion |
                        TokenKind::KwEnum)
                {
                    break;
                }
                // A USER-DEFINED type also begins a new typed parameter:
                //   #(parameter int N = 1, u32_t A[N] = '{0}, pkg::t B = 0)
                // `Ident Ident` / `Ident ::` can only be `<type> <name>`, never a
                // continuation assignment (`#(int A, B)` has `)` after `B`).
                if matches!(next, TokenKind::Identifier | TokenKind::EscapedIdentifier)
                    && matches!(
                        self.peek_kind_n(2),
                        TokenKind::Identifier | TokenKind::EscapedIdentifier | TokenKind::DoubleColon
                    )
                {
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
                forward: false, // forward CLASS — resolved via a class decl, not checked here
            };
        }
        // §6.18: KEYWORD-qualified forward form — `typedef struct T;`,
        // `typedef union T;`, `typedef enum T;`. Falling through to
        // parse_data_type read `struct` and found no body, registering a
        // bodyless width-0 type under T that CLOBBERED the real definition
        // when the item was re-processed. Only the exact keyword-ident-semi
        // shape is taken; `typedef struct {...} T;` still parses normally.
        if matches!(
            self.current_kind(),
            TokenKind::KwStruct | TokenKind::KwUnion | TokenKind::KwEnum
        ) && matches!(
            self.peek_kind(),
            TokenKind::Identifier | TokenKind::EscapedIdentifier
        ) && self
            .tokens
            .get(self.pos + 2)
            .is_some_and(|t| t.kind == TokenKind::Semicolon)
        {
            self.bump(); // the struct/union/enum keyword
            let name = self.parse_identifier();
            self.expect(TokenKind::Semicolon);
            return TypedefDeclaration {
                data_type: DataType::Void(self.span_from(start)),
                name,
                dimensions: Vec::new(),
                span: self.span_from(start),
                forward: true,
            };
        }
        // IEEE 1800-2017 §6.18: bare forward type declaration `typedef name;`
        // (no type body) — promises a later full typedef. Multiple are legal.
        if (self.at(TokenKind::Identifier) || self.at(TokenKind::EscapedIdentifier))
            && self.peek_kind() == TokenKind::Semicolon {
            let name = self.parse_identifier();
            self.expect(TokenKind::Semicolon);
            return TypedefDeclaration {
                data_type: DataType::Void(self.span_from(start)),
                name, dimensions: Vec::new(), span: self.span_from(start),
                forward: true,
            };
        }
        let data_type = self.parse_data_type();
        let name = self.parse_identifier();
        let dimensions = self.parse_unpacked_dimensions();
        self.expect(TokenKind::Semicolon);
        TypedefDeclaration { data_type, name, dimensions, span: self.span_from(start), forward: false }
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
        // §6.8: `var name;` — the `var` keyword with no explicit type means the
        // identifier is the declarator (implicit `logic`), not a type name.
        let data_type = if var_kw && self.at(TokenKind::Identifier)
            && matches!(self.peek_kind(), TokenKind::Semicolon | TokenKind::Comma | TokenKind::Assign) {
            DataType::Implicit { signing: None, dimensions: Vec::new(), span: self.span_from(start) }
        } else {
            self.parse_data_type()
        };
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
        let specifier = self.parse_optional_method_specifier();
        let lifetime = self.parse_optional_lifetime();
        // §25.9: `virtual` at the RETURN-TYPE position can only start a
        // virtual-interface type (`function automatic virtual bus_if #(4).drv
        // get(...)`) — a virtual METHOD's keyword sits BEFORE `function` and
        // was consumed above.
        let return_type = if self.is_data_type_keyword() || self.at(TokenKind::KwVoid)
            || self.at(TokenKind::KwVirtual) ||
                            (self.at(TokenKind::Identifier) && (
                                self.peek_kind() == TokenKind::Identifier ||
                                (self.peek_kind() == TokenKind::DoubleColon
                                    && self.peek_kind_n(2) != TokenKind::KwNew
                                    && !self.scoped_name_is_the_method_name()) ||
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
        let mut ports = self.parse_function_ports();
        self.expect(TokenKind::Semicolon);
        let mut items = Vec::new();
        let mut strict_body_ports = Vec::new();
        while !self.at(TokenKind::KwEndfunction) && !self.at(TokenKind::Eof) {
            if matches!(self.current_kind(),
                TokenKind::KwInput | TokenKind::KwOutput | TokenKind::KwInout | TokenKind::KwRef) {
                // §13.4.2 non-ANSI body ports fill `ports` for arg binding
                // (ANSI functions already have a non-empty `ports` here).
                self.parse_tf_body_ports(&mut ports, &mut strict_body_ports);
            } else {
                items.push(self.parse_statement());
            }
        }
        self.expect(TokenKind::KwEndfunction);
        let endlabel = self.parse_end_label_checked(&name.name.name);
        Self::merge_nonansi_port_types(&mut ports, &mut items);
        FunctionDeclaration { lifetime, specifier, return_type, name, ports, items, endlabel, strict_body_ports, span: self.span_from(start) }
    }

    /// Consume a non-ANSI task/function body port declaration
    /// (`input integer x, y;`), recording the declared names for the
    /// strict-check pass. Consumes exactly through the terminating `;` — the
    /// same tokens the main path would have discarded into a `Null` statement,
    /// so dropping the statement is behavior-neutral for elaboration.
    pub(super) fn capture_tf_body_port(&mut self, out: &mut Vec<Identifier>) {
        self.bump(); // direction keyword (input/output/inout/ref)
        let mut bdepth = 0i32;
        while !self.at(TokenKind::Semicolon) && !self.at(TokenKind::Eof) {
            match self.current_kind() {
                TokenKind::LBracket => { bdepth += 1; self.bump(); }
                TokenKind::RBracket => { bdepth -= 1; self.bump(); }
                TokenKind::Identifier | TokenKind::EscapedIdentifier if bdepth == 0 => {
                    // A declared name is an identifier at bracket-depth 0
                    // immediately followed by a declarator terminator.
                    if matches!(self.peek_kind(),
                        TokenKind::Comma | TokenKind::Semicolon | TokenKind::Assign) {
                        let tok = self.current();
                        out.push(Identifier { name: tok.text.clone(), span: tok.span });
                    }
                    self.bump();
                }
                _ => { self.bump(); }
            }
        }
        self.eat(TokenKind::Semicolon);
    }

    /// Parse a NON-ANSI task/function body port declaration
    /// (`input integer x, y;` / `input [6:0] a;`) into full `FunctionPort`s so
    /// call-argument binding works. Previously only the names were captured
    /// (into strict_body_ports) and `ports` stayed empty, so a non-ANSI
    /// function's arguments never bound (returned X). Also records names for
    /// the strict-check pass. Handles one or more comma-separated declarators
    /// sharing the leading direction+type.
    pub(super) fn parse_tf_body_ports(
        &mut self,
        ports: &mut Vec<FunctionPort>,
        _strict: &mut Vec<Identifier>,
    ) {
        let start = self.current().span.start;
        let direction = self.parse_optional_direction().unwrap_or(PortDirection::Input);
        let var_kw = self.eat(TokenKind::KwVar).is_some();
        // Optional shared data type (implicit 1-bit when omitted, e.g. `input x;`).
        let data_type = if self.is_data_type_keyword() || self.at(TokenKind::KwVoid) {
            self.parse_data_type()
        } else if self.at(TokenKind::Identifier)
            && matches!(self.peek_kind(), TokenKind::Identifier | TokenKind::Hash | TokenKind::DoubleColon)
        {
            self.parse_data_type()
        } else if self.at(TokenKind::LBracket) {
            let dims = self.parse_packed_dimensions();
            DataType::Implicit { signing: None, dimensions: dims, span: self.span_from(start) }
        } else {
            DataType::Implicit { signing: None, dimensions: Vec::new(), span: self.span_from(start) }
        };
        // One or more declarators sharing that direction+type.
        loop {
            if !self.at(TokenKind::Identifier) && !self.at(TokenKind::EscapedIdentifier) {
                break;
            }
            let name = self.parse_identifier();
            let dimensions = self.parse_unpacked_dimensions();
            let default = if self.eat(TokenKind::Assign).is_some() {
                Some(self.parse_expression())
            } else {
                None
            };
            ports.push(FunctionPort {
                direction,
                var_kw,
                data_type: data_type.clone(),
                name,
                dimensions,
                default,
                span: self.span_from(start),
            });
            if self.eat(TokenKind::Comma).is_none() {
                break;
            }
        }
        self.eat(TokenKind::Semicolon);
    }

    pub(super) fn parse_task_declaration(&mut self) -> TaskDeclaration {
        let start = self.current().span.start;
        let _virt = self.eat(TokenKind::KwVirtual).is_some();
        self.expect(TokenKind::KwTask);
        let specifier = self.parse_optional_method_specifier();
        let lifetime = self.parse_optional_lifetime();
        // Name can be 'new', a regular identifier, or class::method
        let name = self.parse_method_name();
        let mut ports = self.parse_function_ports();
        self.expect(TokenKind::Semicolon);
        let mut items = Vec::new();
        let mut strict_body_ports = Vec::new();
        while !self.at(TokenKind::KwEndtask) && !self.at(TokenKind::Eof) {
            if matches!(self.current_kind(),
                TokenKind::KwInput | TokenKind::KwOutput | TokenKind::KwInout | TokenKind::KwRef) {
                self.parse_tf_body_ports(&mut ports, &mut strict_body_ports);
            } else {
                items.push(self.parse_statement());
            }
        }
        self.expect(TokenKind::KwEndtask);
        let endlabel = self.parse_end_label();
        Self::merge_nonansi_port_types(&mut ports, &mut items);
        TaskDeclaration { lifetime, specifier, name, ports, items, endlabel, strict_body_ports, span: self.span_from(start) }
    }

    /// §13.3: the non-ANSI style may declare a port's DIRECTION and its DATA
    /// TYPE as two separate body items (`input x;  int x;`). The second line
    /// parses as an ordinary variable declaration; left there it became a
    /// LOCAL that shadowed the 1-bit implicit port. Merge such a declaration's
    /// type into the matching implicit-typed port and drop the statement.
    /// Only single-declarator, no-initializer declarations whose name matches
    /// an IMPLICIT-typed port are merged — anything else really is a local.
    pub(super) fn merge_nonansi_port_types(
        ports: &mut [FunctionPort],
        items: &mut Vec<super::super::ast::stmt::Statement>,
    ) {
        use super::super::ast::stmt::StatementKind;
        items.retain(|it| {
            let StatementKind::VarDecl { data_type, lifetime: None, declarators } = &it.kind
            else {
                return true;
            };
            if declarators.len() != 1 {
                return true;
            }
            let d = &declarators[0];
            if d.init.is_some() || !d.dimensions.is_empty() {
                return true;
            }
            let Some(port) = ports.iter_mut().find(|p| {
                p.name.name == d.name.name
                    && matches!(&p.data_type, DataType::Implicit { dimensions, .. }
                        if dimensions.is_empty())
            }) else {
                return true;
            };
            port.data_type = data_type.clone();
            false
        });
    }

    /// Parse a method name: handles 'new', regular identifiers, and class_scope::name.
    /// At `function`'s type-or-name position, sitting on `ident :: ident`: is
    /// that scoped name the METHOD NAME rather than a scoped return type?
    ///
    /// §13.4 lets an out-of-class definition omit the return type
    /// (`function my_class::set_default();` returns a 1-bit logic). The caller
    /// otherwise sees the `::`, assumes `pkg::type_t name(...)`, and consumes
    /// the whole thing as a return type — then finds `(` where the name should
    /// be and reports "expected identifier, found LParen".
    ///
    /// A port list or `;` right after the second identifier means nothing is
    /// left to be the name, so the scoped name IS the name. When a real return
    /// type is present the next token is that name instead
    /// (`function pkg::t_e cls::m();`), and this stays false.
    fn scoped_name_is_the_method_name(&self) -> bool {
        matches!(
            self.peek_kind_n(3),
            TokenKind::LParen | TokenKind::Semicolon
        )
    }

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
        let specifier = self.parse_optional_method_specifier();

        let lifetime = self.parse_optional_lifetime();
        let return_type = if self.is_data_type_keyword() || self.at(TokenKind::KwVoid) ||
                            (self.at(TokenKind::Identifier) && (
                                self.peek_kind() == TokenKind::Identifier ||
                                (self.peek_kind() == TokenKind::DoubleColon
                                    && self.peek_kind_n(2) != TokenKind::KwNew
                                    && !self.scoped_name_is_the_method_name()) ||
                                self.peek_kind() == TokenKind::Hash
                            )) {
            self.parse_data_type()
        } else {
            DataType::Implicit { signing: None, dimensions: Vec::new(), span: self.span_from(start) }
        };
        let name = self.parse_method_name();
        let ports = self.parse_function_ports();
        self.expect(TokenKind::Semicolon);
        FunctionDeclaration { lifetime, specifier, return_type, name, ports, items: Vec::new(), endlabel: None, strict_body_ports: Vec::new(), span: self.span_from(start) }
    }

    pub(super) fn parse_task_prototype(&mut self) -> TaskDeclaration {
        let start = self.current().span.start;
        self.expect(TokenKind::KwTask);
        let specifier = self.parse_optional_method_specifier();
        let lifetime = self.parse_optional_lifetime();
        let name = self.parse_method_name();
        let ports = self.parse_function_ports();
        self.expect(TokenKind::Semicolon);
        TaskDeclaration { lifetime, specifier, name, ports, items: Vec::new(), endlabel: None, strict_body_ports: Vec::new(), span: self.span_from(start) }
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
        } else if self.at(TokenKind::KwVirtual)
            && (self.peek_kind() == TokenKind::KwInterface
                || self.peek_kind() == TokenKind::Identifier)
        {
            // §25.9 / §8.25.1: `virtual <iface_type>` or
            // `virtual interface <iface_type>` as a type-parameter argument
            // (e.g. `C#(virtual my_if)`). Parse as a Type so it binds to a
            // `type` parameter. May carry `#(...)` parameter args.
            ParamValue::Type(self.parse_data_type())
        } else {
            ParamValue::Expr(self.parse_expression())
        }
    }

    pub(super) fn parse_param_args(&mut self) -> Vec<ParamValue> {
        let mut args = Vec::new();
        let _has_hash = self.eat(TokenKind::Hash).is_some();
        // §28.3 gate/primitive delay without parens — `buf #2 b(o,i)`,
        // `ubuf #1.5 u(o,i)`. The old code ate the `#`, found no `(`, and
        // returned EMPTY, leaving the literal in the stream to trip the
        // instance-name parse ("expected identifier, found IntegerLiteral").
        // Accept a single NUMERIC literal as the one positional value; the
        // elaborator already reads a scalar delay out of `inst.params`, so
        // `#2` and `#(2)` converge downstream. Literals only — an identifier
        // delay would be ambiguous against too many neighbors.
        if _has_hash
            && matches!(
                self.current_kind(),
                TokenKind::IntegerLiteral | TokenKind::RealLiteral | TokenKind::TimeLiteral
            )
        {
            args.push(self.parse_param_value());
            return args;
        }
        if self.eat(TokenKind::LParen).is_none() { return args; }
        if self.at(TokenKind::RParen) { self.bump(); return args; }
        loop {
            if self.at(TokenKind::RParen) || self.at(TokenKind::Eof) { break; }
            // IEEE 1800-2023 §8.25.1 — `extends <base>#(.NAME(value), ...)` is
            // the named form of parameter binding. We accept it here and drop
            // the name (Elaboration matches positionally for now; recording
            // the name would require widening `ClassExtends.args`).
            if self.eat(TokenKind::Dot).is_some() {
                let _name = self.parse_identifier();
                self.expect(TokenKind::LParen);
                if self.at(TokenKind::RParen) {
                    // `.NAME()` — empty binding; skip without pushing.
                    self.bump();
                } else {
                    args.push(self.parse_param_value());
                    self.expect(TokenKind::RParen);
                }
            } else {
                args.push(self.parse_param_value());
            }
            if self.eat(TokenKind::Comma).is_none() { break; }
        }
        self.expect(TokenKind::RParen);
        args
    }
    pub(super) fn parse_function_ports(&mut self) -> Vec<FunctionPort> {
        let mut ports = Vec::new();
        if self.eat(TokenKind::LParen).is_none() { return ports; }
        if self.at(TokenKind::RParen) { self.bump(); return ports; }
        // §13.5.2: a formal whose direction is omitted takes the direction of
        // the PREVIOUS formal; only the first defaults to input. Defaulting
        // every one to input made `output logic [7:0] r0, r1, r2, r3` declare
        // r1..r3 as INPUTS — their copy-out silently vanished, so a caller saw
        // only the first result of a multi-output helper (an AES MixColumns
        // updated one byte per column and nothing else).
        let mut prev_direction = PortDirection::Input;
        loop {
            if self.at(TokenKind::RParen) || self.at(TokenKind::Eof) { break; }
            let start = self.current().span.start;
            let mut var_kw = self.eat(TokenKind::KwVar).is_some();
            let _const_kw = self.eat(TokenKind::KwConst).is_some();
            if !var_kw && self.at(TokenKind::KwVar) { var_kw = self.eat(TokenKind::KwVar).is_some(); } // Handle var after const
            let direction = self.parse_optional_direction().unwrap_or(prev_direction);
            prev_direction = direction;
            // §13.3: `input var int x` — `var` may follow the direction too.
            if !var_kw && self.at(TokenKind::KwVar) { var_kw = self.eat(TokenKind::KwVar).is_some(); }

            // Handle `virtual interface <name>` port type (legacy form)
            // and the LRM 1800-2017 §25.9 form `virtual <iface_type>` /
            // `virtual <iface_type>.<modport> <name>` (no `interface`
            // keyword). Both produce a TypeReference for the iface.
            if self.at(TokenKind::KwVirtual)
                && (self.peek_kind() == TokenKind::KwInterface
                    || self.peek_kind() == TokenKind::Identifier)
            {
                self.bump(); // virtual
                if self.at(TokenKind::KwInterface) {
                    self.bump();
                }
                let iface_name = self.parse_identifier();
                // §25.9: the interface may be PARAMETERIZED —
                // `virtual bus_if #(D, A) vif`. Without consuming the
                // `#(...)` here the formal failed to parse entirely (the
                // class-property form already accepted it via
                // `parse_data_type`). The args are consumed and discarded like
                // the modport below: the data type records only the interface,
                // and the binding is resolved by name at elaboration.
                if self.at(TokenKind::Hash) {
                    let _ = self.parse_param_args();
                }
                // Optional `.<modport>` suffix — for now consumed and
                // discarded (the data_type just records the iface).
                if self.at(TokenKind::Dot) {
                    self.bump();
                    let _modport = self.parse_identifier();
                }
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
            } else if self.at(TokenKind::Identifier) && self.peek_kind() == TokenKind::LBracket
                && self.peek_kind_n(2) == TokenKind::Dollar
                && self.peek_kind_n(3) == TokenKind::RBracket
            {
                // §6.3/§13.3: inherited-type port — `name [$]` where the type
                // is inherited from the previous port (e.g. the second arg in
                // `function f(string src, dest[$])`). The identifier is the
                // PORT NAME, `[$]` is the unpacked queue dimension, and the
                // data type is Implicit (elaboration copies the previous
                // port's resolved type). Handle the whole port inline to
                // avoid the later `parse_identifier` consuming the `[`.
                let name = self.parse_identifier();
                let dimensions = self.parse_unpacked_dimensions();
                let data_type = DataType::Implicit {
                    signing: None,
                    dimensions: Vec::new(),
                    span: self.span_from(start),
                };
                let default = if self.eat(TokenKind::Assign).is_some() {
                    Some(self.parse_expression())
                } else { None };
                ports.push(FunctionPort { direction, var_kw, data_type, name, dimensions, default, span: self.span_from(start) });
                if self.eat(TokenKind::Comma).is_none() { break; }
                continue;
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
                    // Implicit-typed port name with UNPACKED dims —
                    // `function parity(input bit_array[3:0])` (ivtest
                    // br1015b): the identifier is the PORT NAME, the
                    // brackets its unpacked dimension. Handle the whole
                    // port inline, mirroring the `name [$]` arm above.
                    let name = self.parse_identifier();
                    let dimensions = self.parse_unpacked_dimensions();
                    let data_type = DataType::Implicit {
                        signing: None,
                        dimensions: Vec::new(),
                        span: self.span_from(start),
                    };
                    let default = if self.eat(TokenKind::Assign).is_some() {
                        Some(self.parse_expression())
                    } else { None };
                    ports.push(FunctionPort { direction, var_kw, data_type, name, dimensions, default, span: self.span_from(start) });
                    if self.eat(TokenKind::Comma).is_none() { break; }
                    continue;
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
                    // §26.6 `export P::*;` / `export P::sym;` / `export *::*;`
                    // — modeled so a wildcard import only re-exposes nested
                    // imports the package actually EXPORTS (and, for
                    // wildcards, references). `*::*` records package "*".
                    let start_sp = self.current().span.start;
                    self.bump(); // export
                    let mut items = Vec::new();
                    loop {
                        let item_start = self.current().span.start;
                        let package = if self.at(TokenKind::Star) {
                            self.bump();
                            Identifier { name: "*".to_string(), span: crate::ast::Span { start: item_start, end: item_start } }
                        } else {
                            self.parse_identifier()
                        };
                        self.expect(TokenKind::DoubleColon);
                        let item = if self.eat(TokenKind::Star).is_some() {
                            None
                        } else {
                            Some(self.parse_identifier())
                        };
                        items.push(ImportItem { package, item, span: self.span_from(item_start) });
                        if self.eat(TokenKind::Comma).is_none() {
                            break;
                        }
                    }
                    self.expect(TokenKind::Semicolon);
                    Some(PackageItem::Export(ImportDeclaration { items, span: self.span_from(start_sp) }))
                }
            }
            // §8.26: `interface class …` inside a package is a class.
            TokenKind::KwInterface if self.peek_kind() == TokenKind::KwClass =>
                Some(PackageItem::Class(self.parse_class_declaration())),
            TokenKind::KwClass => Some(PackageItem::Class(self.parse_class_declaration())),
            // IEEE 1800-2023 §19: covergroup at package scope. Parsed for
            // syntactic acceptance, but not hosted as a PackageItem (no
            // PackageItem::Covergroup variant; covergroup runtime lives in
            // classes/modules). Returning Null prevents the loop from
            // bumping past `endpackage`.
            TokenKind::KwCovergroup => {
                let _ = self.parse_covergroup_declaration();
                Some(PackageItem::Null)
            }
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
            // §26.2: named property / sequence declarations at package
            // scope. Without these arms `property` was read as a type name
            // and every token after it derailed the whole package.
            TokenKind::KwProperty => {
                match self.parse_module_item() {
                    Some(ModuleItem::PropertyDeclaration(pd)) => Some(PackageItem::Property(pd)),
                    _ => Some(PackageItem::Null),
                }
            }
            TokenKind::KwSequence => {
                match self.parse_module_item() {
                    Some(ModuleItem::SequenceDeclaration(sd)) => Some(PackageItem::Sequence(sd)),
                    _ => Some(PackageItem::Null),
                }
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
                    let func = self.parse_function_declaration();
                    // Mark as virtual if we had the keyword (though PackageItem doesn't track it)
                    Some(PackageItem::Function(func))
                } else if self.peek_kind() == TokenKind::KwTask {
                    let task = self.parse_task_declaration();
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
