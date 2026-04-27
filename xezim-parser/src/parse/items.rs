//! Module-level item parsing (IEEE 1800-2017 §A.1)

use super::Parser;
use crate::ast::Identifier;
use crate::ast::decl::*;
use crate::ast::expr::*;
use crate::ast::module::*;
use crate::ast::types::*;
use crate::lexer::token::TokenKind;

impl Parser {
    pub(super) fn parse_module_declaration(&mut self) -> ModuleDeclaration {
        let start = self.current().span.start;
        let kind = if self.eat(TokenKind::KwMacromodule).is_some() { ModuleKind::Macromodule } else { self.expect(TokenKind::KwModule); ModuleKind::Module };
        let lifetime = self.parse_optional_lifetime();
        let name = self.parse_identifier();
        let header_imports = self.parse_module_header_imports();
        let params = self.parse_parameter_port_list();
        let ports = self.parse_port_list();
        self.expect(TokenKind::Semicolon);

        let mut items = self.parse_module_items();
        if !header_imports.is_empty() {
            let mut prefixed = Vec::with_capacity(header_imports.len() + items.len());
            prefixed.extend(header_imports);
            prefixed.extend(items);
            items = prefixed;
        }

        self.expect(TokenKind::KwEndmodule);
        let endlabel = self.parse_end_label();

        ModuleDeclaration {
            attrs: Vec::new(),
            kind, lifetime, name, params, ports, items, endlabel,
            span: self.span_from(start),
        }
    }

    pub(super) fn parse_interface_declaration(&mut self) -> InterfaceDeclaration {
        let start = self.current().span.start;
        self.expect(TokenKind::KwInterface);
        let lifetime = self.parse_optional_lifetime();
        let name = self.parse_identifier();
        let header_imports = self.parse_module_header_imports();
        let params = self.parse_parameter_port_list();
        let ports = self.parse_port_list();
        self.expect(TokenKind::Semicolon);

        let mut items = self.parse_module_items();
        if !header_imports.is_empty() {
            let mut prefixed = Vec::with_capacity(header_imports.len() + items.len());
            prefixed.extend(header_imports);
            prefixed.extend(items);
            items = prefixed;
        }

        self.expect(TokenKind::KwEndinterface);
        let endlabel = self.parse_end_label();

        InterfaceDeclaration {
            attrs: Vec::new(),
            lifetime, name, params, ports, items, endlabel,
            span: self.span_from(start),
        }
    }

    pub(super) fn parse_program_declaration(&mut self) -> ProgramDeclaration {
        let start = self.current().span.start;
        self.expect(TokenKind::KwProgram);
        let lifetime = self.parse_optional_lifetime();
        let name = self.parse_identifier();
        let header_imports = self.parse_module_header_imports();
        let params = self.parse_parameter_port_list();
        let ports = self.parse_port_list();
        self.expect(TokenKind::Semicolon);

        let mut items = self.parse_module_items();
        if !header_imports.is_empty() {
            let mut prefixed = Vec::with_capacity(header_imports.len() + items.len());
            prefixed.extend(header_imports);
            prefixed.extend(items);
            items = prefixed;
        }

        self.expect(TokenKind::KwEndprogram);
        let endlabel = self.parse_end_label();

        ProgramDeclaration {
            attrs: Vec::new(),
            lifetime, name, params, ports, items, endlabel,
            span: self.span_from(start),
        }
    }

    fn parse_module_header_imports(&mut self) -> Vec<ModuleItem> {
        let mut imports = Vec::new();
        while self.at(TokenKind::KwImport) && self.peek_kind() != TokenKind::StringLiteral {
            imports.push(ModuleItem::ImportDeclaration(self.parse_import_declaration()));
        }
        imports
    }

    pub(super) fn parse_package_declaration(&mut self) -> PackageDeclaration {
        let start = self.current().span.start;
        self.expect(TokenKind::KwPackage);
        let lifetime = self.parse_optional_lifetime();
        let name = self.parse_identifier();
        self.expect(TokenKind::Semicolon);

        let mut items = Vec::new();
        while !self.at(TokenKind::KwEndpackage) && !self.at(TokenKind::Eof) {
            if let Some(item) = self.parse_package_item() { items.push(item); }
            else { self.bump(); }
        }

        self.expect(TokenKind::KwEndpackage);
        let endlabel = self.parse_end_label();

        PackageDeclaration {
            attrs: Vec::new(),
            lifetime, name, items, endlabel,
            span: self.span_from(start),
        }
    }

    pub(super) fn parse_port_list(&mut self) -> PortList {
        if self.eat(TokenKind::LParen).is_none() { return PortList::Empty; }
        if self.at(TokenKind::RParen) { self.bump(); return PortList::Empty; }
        if self.is_port_direction() || self.is_data_type_keyword() || self.at(TokenKind::KwVar)
            || (self.at(TokenKind::Identifier) && self.peek_kind() == TokenKind::Dot)
            || (self.at(TokenKind::Identifier) && matches!(self.peek_kind(), TokenKind::Identifier | TokenKind::DoubleColon | TokenKind::Hash))
        {
            let mut ports = Vec::new();
            let mut last_direction: Option<PortDirection> = None;
            let mut last_data_type: Option<DataType> = None;
            let mut last_net_type: Option<NetType> = None;
            loop {
                if self.at(TokenKind::RParen) || self.at(TokenKind::Eof) { break; }
                let mut port = self.parse_ansi_port();
                let direction_was_explicit = port.direction.is_some();
                if port.direction.is_none() && last_direction.is_some() {
                    port.direction = last_direction;
                }
                if port.data_type.is_none() && last_data_type.is_some() && !direction_was_explicit {
                    port.data_type = last_data_type.clone();
                }
                if port.net_type.is_none() && last_net_type.is_some() && !direction_was_explicit {
                    port.net_type = last_net_type;
                }
                if port.direction.is_some() { last_direction = port.direction; }
                if port.data_type.is_some() { last_data_type = port.data_type.clone(); }
                if port.net_type.is_some() { last_net_type = port.net_type; }
                ports.push(port);
                if self.eat(TokenKind::Comma).is_none() { break; }
            }
            self.expect(TokenKind::RParen);
            PortList::Ansi(ports)
        } else {
            let mut names = Vec::new();
            loop {
                if self.at(TokenKind::RParen) || self.at(TokenKind::Eof) { break; }
                names.push(self.parse_identifier());
                if self.eat(TokenKind::Comma).is_none() { break; }
            }
            self.expect(TokenKind::RParen);
            PortList::NonAnsi(names)
        }
    }

    fn parse_ansi_port(&mut self) -> AnsiPort {
        let start = self.current().span.start;
        let direction = self.parse_optional_direction();
        let net_type = self.parse_optional_net_type();
        let var_kw = self.eat(TokenKind::KwVar).is_some();
        let data_type = if self.is_data_type_keyword() {
            Some(self.parse_data_type())
        } else if self.at(TokenKind::LBracket) {
            let dimensions = self.parse_packed_dimensions();
            Some(DataType::Implicit { signing: None, dimensions, span: self.span_from(start) })
        } else if self.at(TokenKind::Identifier) && self.peek_kind() == TokenKind::Dot {
            let if_name = self.parse_identifier();
            self.expect(TokenKind::Dot);
            let mp_name = self.parse_identifier();
            Some(DataType::Interface { name: if_name, modport: Some(mp_name), span: self.span_from(start) })
        } else if self.at(TokenKind::Identifier) && matches!(self.peek_kind(), TokenKind::Identifier | TokenKind::DoubleColon | TokenKind::Hash | TokenKind::LBracket) {
            Some(self.parse_data_type())
        } else { None };
        let mut dimensions = if data_type.is_some() {
            self.parse_unpacked_dimensions()
        } else {
            Vec::new()
        };
        let name = self.parse_identifier();
        dimensions.extend(self.parse_unpacked_dimensions());
        let default = if self.eat(TokenKind::Assign).is_some() { Some(self.parse_expression()) } else { None };
        AnsiPort { attrs: Vec::new(), direction, net_type, var_kw, data_type, name, dimensions, default, span: self.span_from(start) }
    }

    pub(super) fn parse_module_items(&mut self) -> Vec<ModuleItem> {
        let end_tokens = [TokenKind::KwEndmodule, TokenKind::KwEndinterface, TokenKind::KwEndprogram, TokenKind::Eof];
        let mut items = Vec::new();
        while !self.at_any(&end_tokens) {
            if let Some(item) = self.parse_module_item() { items.push(item); }
            else { self.error(format!("unexpected: {:?}", self.current().text)); self.bump(); }
        }
        items
    }

    pub(super) fn parse_module_item(&mut self) -> Option<ModuleItem> {
        let start = self.current().span.start;
        let mut is_extern = false;
        let mut is_virtual = false;
        let mut _is_static = false;
        loop {
            match self.current_kind() {
                TokenKind::KwExtern => { self.bump(); is_extern = true; }
                TokenKind::KwVirtual if self.peek_kind() == TokenKind::KwFunction 
                    || self.peek_kind() == TokenKind::KwTask
                    || self.peek_kind() == TokenKind::KwClass => {
                    self.bump(); is_virtual = true;
                }
                TokenKind::KwStatic if self.peek_kind() == TokenKind::KwFunction
                    || self.peek_kind() == TokenKind::KwTask => {
                    self.bump(); _is_static = true;
                }
                _ => break,
            }
        }

        match self.current_kind() {
            // Elaboration-time system tasks at module-item level: $error, $warning,
            // $info, $fatal — typically inside a `STATIC_ASSERT` macro expansion
            // (`generate if (!(cond)) $error msg; endgenerate`). Parse and discard.
            TokenKind::SystemIdentifier => {
                self.bump();
                if self.at(TokenKind::LParen) {
                    let _ = self.parse_call_args();
                } else {
                    // No-paren form: $error msg;  where msg is an expression.
                    while !self.at(TokenKind::Semicolon) && !self.at(TokenKind::Eof) {
                        self.bump();
                    }
                }
                self.expect(TokenKind::Semicolon);
                Some(ModuleItem::Null)
            }
            TokenKind::KwInput | TokenKind::KwOutput | TokenKind::KwInout | TokenKind::KwRef => {
                let dir = self.parse_optional_direction().unwrap_or(PortDirection::Input);
                let nt = self.parse_optional_net_type();
                let dt = if self.is_data_type_keyword() { self.parse_data_type() }
                    else if self.at(TokenKind::Identifier) && matches!(self.peek_kind(), TokenKind::Identifier | TokenKind::DoubleColon | TokenKind::Hash | TokenKind::LBracket) {
                        self.parse_data_type()
                    }
                    else if self.at(TokenKind::LBracket) {
                        let dimensions = self.parse_packed_dimensions();
                        DataType::Implicit { signing: None, dimensions, span: self.span_from(start) }
                    }
                    else { DataType::Implicit { signing: None, dimensions: Vec::new(), span: self.span_from(start) } };
                let decls = self.parse_var_declarator_list();
                self.expect(TokenKind::Semicolon);
                Some(ModuleItem::PortDeclaration(PortDeclaration { direction: dir, net_type: nt, data_type: dt, declarators: decls, span: self.span_from(start) }))
            }
            TokenKind::KwWire | TokenKind::KwTri | TokenKind::KwWand | TokenKind::KwWor |
            TokenKind::KwSupply0 | TokenKind::KwSupply1 | TokenKind::KwTriand | TokenKind::KwTrior |
            TokenKind::KwTri0 | TokenKind::KwTri1 | TokenKind::KwTrireg | TokenKind::KwUwire =>
                Some(ModuleItem::NetDeclaration(self.parse_net_declaration())),
            TokenKind::KwInterface if self.peek_kind() == TokenKind::KwClass => {
                // `interface class Name; ... endclass` — treat as a class decl.
                self.bump();
                let mut class = self.parse_class_declaration();
                class.virtual_kw = is_virtual;
                class.is_interface = true;
                Some(ModuleItem::ClassDeclaration(class))
            }
            _ if self.is_data_type_keyword() =>
                Some(ModuleItem::DataDeclaration(self.parse_data_declaration())),
            TokenKind::KwVar | TokenKind::KwConst | TokenKind::KwStatic | TokenKind::KwAutomatic =>
                Some(ModuleItem::DataDeclaration(self.parse_data_declaration())),
            TokenKind::KwParameter =>
                Some(ModuleItem::ParameterDeclaration(self.parse_parameter_decl_stmt())),
            TokenKind::KwLocalparam =>
                Some(ModuleItem::LocalparamDeclaration(self.parse_parameter_decl_stmt())),
            TokenKind::KwTypedef =>
                Some(ModuleItem::TypedefDeclaration(self.parse_typedef_declaration())),
            TokenKind::KwAlways | TokenKind::KwAlways_comb | TokenKind::KwAlways_ff | TokenKind::KwAlways_latch => {
                let kind = match self.bump().kind {
                    TokenKind::KwAlways_comb => AlwaysKind::AlwaysComb,
                    TokenKind::KwAlways_ff => AlwaysKind::AlwaysFf,
                    TokenKind::KwAlways_latch => AlwaysKind::AlwaysLatch,
                    _ => AlwaysKind::Always,
                };
                let stmt = self.parse_statement();
                Some(ModuleItem::AlwaysConstruct(AlwaysConstruct { kind, stmt, span: self.span_from(start) }))
            }
            TokenKind::KwInitial => { self.bump(); let st = self.parse_statement();
                Some(ModuleItem::InitialConstruct(InitialConstruct { stmt: st, span: self.span_from(start) })) }
            TokenKind::KwFinal => { self.bump(); let st = self.parse_statement();
                Some(ModuleItem::FinalConstruct(FinalConstruct { stmt: st, span: self.span_from(start) })) }
            TokenKind::KwAssign => {
                self.bump();
                if self.eat(TokenKind::Hash).is_some() {
                    if self.eat(TokenKind::LParen).is_some() {
                        let _ = self.parse_expression();
                        self.expect(TokenKind::RParen);
                    } else {
                        let _ = self.parse_expression();
                    }
                }
                let mut asgns = Vec::new();
                loop { let l = self.parse_expression(); self.expect(TokenKind::Assign); let r = self.parse_expression();
                    asgns.push((l, r)); if self.eat(TokenKind::Comma).is_none() { break; } }
                self.expect(TokenKind::Semicolon);
                Some(ModuleItem::ContinuousAssign(ContinuousAssign { strength: None, delay: None, assignments: asgns, span: self.span_from(start) }))
            }
            TokenKind::KwGenerate => {
                self.bump();
                let items = self.parse_module_items_until(TokenKind::KwEndgenerate);
                self.expect(TokenKind::KwEndgenerate);
                Some(ModuleItem::GenerateRegion(GenerateRegion { items, span: self.span_from(start) }))
            }
            TokenKind::KwGenvar => {
                self.bump();
                let mut names = Vec::new();
                loop { names.push(self.parse_identifier()); if self.eat(TokenKind::Comma).is_none() { break; } }
                self.expect(TokenKind::Semicolon);
                Some(ModuleItem::GenvarDeclaration(GenvarDeclaration { names, span: self.span_from(start) }))
            }
            TokenKind::KwFunction => {
                if is_extern { Some(ModuleItem::FunctionDeclaration(self.parse_function_prototype())) }
                else { Some(ModuleItem::FunctionDeclaration(self.parse_function_declaration())) }
            }
            TokenKind::KwTask => {
                if is_extern { Some(ModuleItem::TaskDeclaration(self.parse_task_prototype())) }
                else { Some(ModuleItem::TaskDeclaration(self.parse_task_declaration())) }
            }
            TokenKind::KwImport => {
                if self.peek_kind() == TokenKind::StringLiteral { Some(ModuleItem::DPIImport(self.parse_dpi_import())) }
                else { Some(ModuleItem::ImportDeclaration(self.parse_import_declaration())) }
            }
            TokenKind::KwExport => {
                if self.peek_kind() == TokenKind::StringLiteral { Some(ModuleItem::DPIExport(self.parse_dpi_export())) }
                else {
                    self.bump();
                    while !self.at(TokenKind::Semicolon) && !self.at(TokenKind::Eof) { self.bump(); }
                    self.expect(TokenKind::Semicolon);
                    Some(ModuleItem::Null)
                }
            }
            TokenKind::KwClass => {
                let mut class = self.parse_class_declaration();
                class.virtual_kw = is_virtual;
                Some(ModuleItem::ClassDeclaration(class))
            }
            TokenKind::KwConstraint => {
                // Out-of-class constraint definition: `constraint ClassName::name { ... }`.
                // Record the qualified name; discard the body.
                self.bump();
                let hid = self.parse_hierarchical_identifier();
                let (class_name, constraint_name) = if hid.path.len() >= 2 {
                    (hid.path[hid.path.len() - 2].name.name.clone(),
                     hid.path[hid.path.len() - 1].name.name.clone())
                } else {
                    (String::new(), hid.path.last().map(|s| s.name.name.clone()).unwrap_or_default())
                };
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
                } else if self.at(TokenKind::Semicolon) {
                    self.bump();
                }
                Some(ModuleItem::OutOfClassConstraint { class_name, constraint_name })
            }
            TokenKind::KwVirtual => {
                if self.peek_kind() == TokenKind::KwInterface { Some(self.parse_identifier_starting_item()) }
                else { self.bump(); self.parse_module_item() }
            }
            TokenKind::KwModport => {
                let start = self.current().span.start; self.bump();
                let mut items = Vec::new();
                loop {
                    let istart = self.current().span.start;
                    let name = self.parse_identifier();
                    self.expect(TokenKind::LParen);
                    let mut ports = Vec::new();
                    loop {
                        if self.at(TokenKind::RParen) || self.at(TokenKind::Eof) { break; }
                        let pstart = self.current().span.start;
                        let direction = self.parse_optional_direction().unwrap_or(PortDirection::Input);
                        let port_name = self.parse_identifier();
                        ports.push(ModportPort { direction, name: port_name, span: self.span_from(pstart) });
                        if self.eat(TokenKind::Comma).is_none() { break; }
                    }
                    self.expect(TokenKind::RParen);
                    items.push(ModportItem { name, ports, span: self.span_from(istart) });
                    if self.eat(TokenKind::Comma).is_none() { break; }
                }
                self.expect(TokenKind::Semicolon);
                Some(ModuleItem::ModportDeclaration(ModportDeclaration { items, span: self.span_from(start) }))
            }
            TokenKind::KwAssert | TokenKind::KwAssume | TokenKind::KwCover =>
                Some(ModuleItem::AssertionItem(self.parse_assertion_statement())),
            TokenKind::KwProperty => {
                let start = self.current().span.start; self.bump();
                let name = self.parse_identifier();
                if self.at(TokenKind::LParen) { self.bump(); while !self.at(TokenKind::RParen) && !self.at(TokenKind::Eof) { self.bump(); } self.expect(TokenKind::RParen); }
                self.expect(TokenKind::Semicolon);
                // Property grammar is rich (disable iff, temporal operators, sequence refs).
                // Skip body tokens so unsupported constructs do not become parse errors.
                let items = Vec::new();
                while !self.at(TokenKind::KwEndproperty) && !self.at(TokenKind::Eof) { self.bump(); }
                self.expect(TokenKind::KwEndproperty);
                let endlabel = self.parse_end_label();
                Some(ModuleItem::PropertyDeclaration(PropertyDeclaration { name, items, endlabel, span: self.span_from(start) }))
            }
            TokenKind::KwSequence => {
                let start = self.current().span.start; self.bump();
                let name = self.parse_identifier();
                if self.at(TokenKind::LParen) { self.bump(); while !self.at(TokenKind::RParen) && !self.at(TokenKind::Eof) { self.bump(); } self.expect(TokenKind::RParen); }
                self.expect(TokenKind::Semicolon);
                // Sequence expressions (e.g. ##n) are not represented in Statement AST yet.
                // Skip body tokens to keep parsing resilient.
                let items = Vec::new();
                while !self.at(TokenKind::KwEndsequence) && !self.at(TokenKind::Eof) { self.bump(); }
                self.expect(TokenKind::KwEndsequence);
                let endlabel = self.parse_end_label();
                Some(ModuleItem::SequenceDeclaration(SequenceDeclaration { name, items, endlabel, span: self.span_from(start) }))
            }
            TokenKind::KwCovergroup => {
                Some(ModuleItem::CovergroupDeclaration(self.parse_covergroup_declaration()))
            }
            TokenKind::KwClocking => {
                let start = self.current().span.start; self.bump();
                let name = if self.at(TokenKind::Identifier) { Some(self.parse_identifier()) } else { None };
                if self.at(TokenKind::At) { let _ = self.parse_event_control(); }
                self.expect(TokenKind::Semicolon);
                let mut items = Vec::new();
                let mut signals = Vec::new();
                while !self.at(TokenKind::KwEndclocking) && !self.at(TokenKind::Eof) {
                    match self.current_kind() {
                        TokenKind::KwInput | TokenKind::KwOutput | TokenKind::KwInout | TokenKind::KwRef => {
                            let sstart = self.current().span.start;
                            let direction = self.parse_optional_direction().unwrap_or(PortDirection::Input);
                            // Optional data type inside clocking declaration.
                            if self.is_data_type_keyword() || (self.at(TokenKind::Identifier) && self.peek_kind() == TokenKind::Identifier) {
                                let _ = self.parse_data_type();
                            }
                            loop {
                                if self.at(TokenKind::Identifier) {
                                    let id = self.parse_identifier();
                                    signals.push(ClockingSignal { direction, name: id, span: self.span_from(sstart) });
                                }
                                if self.eat(TokenKind::Comma).is_none() { break; }
                            }
                            self.expect(TokenKind::Semicolon);
                        }
                        _ => items.push(self.parse_statement()),
                    }
                }
                self.expect(TokenKind::KwEndclocking);
                let endlabel = self.parse_end_label();
                // ClockingDeclaration struct needs an Option<Identifier> for name if we want to store it accurately,
                // but for now let's just use a dummy identifier if it's missing.
                let id = name.unwrap_or_else(|| Identifier { name: "default".to_string(), span: self.span_from(start) });
                Some(ModuleItem::ClockingDeclaration(ClockingDeclaration { name: id, signals, items, endlabel, span: self.span_from(start) }))
            }
            TokenKind::KwDefault => {
                self.bump();
                if self.at(TokenKind::KwClocking) {
                    self.parse_module_item() // recurse to handle clocking
                } else {
                    None
                }
            }
            TokenKind::KwIf => { let s = self.current().span.start; Some(self.parse_generate_if(s)) }
            TokenKind::KwCase => { let s = self.current().span.start; Some(self.parse_generate_case(s)) }
            TokenKind::KwChecker => {
                let start = self.current().span.start; self.bump();
                let name = self.parse_identifier();
                let ports = self.parse_port_list();
                self.expect(TokenKind::Semicolon);
                let items = self.parse_module_items_until(TokenKind::KwEndchecker);
                self.expect(TokenKind::KwEndchecker);
                let endlabel = self.parse_end_label();
                Some(ModuleItem::CheckerDeclaration(CheckerDeclaration { name, ports, items, endlabel, span: self.span_from(start) }))
            }
            TokenKind::KwLet => {
                let start = self.current().span.start; self.bump();
                let name = self.parse_identifier();
                let ports = self.parse_port_list();
                self.expect(TokenKind::Assign);
                let expr = self.parse_expression();
                self.expect(TokenKind::Semicolon);
                Some(ModuleItem::LetDeclaration(LetDeclaration { name, ports, expr, span: self.span_from(start) }))
            }
            TokenKind::KwNettype => {
                let start = self.current().span.start; self.bump();
                let data_type = self.parse_data_type();
                let name = self.parse_identifier();
                let resolver = if self.eat(TokenKind::KwWith).is_some() { Some(self.parse_identifier()) } else { None };
                self.expect(TokenKind::Semicolon);
                Some(ModuleItem::NettypeDeclaration(NettypeDeclaration { data_type, name, resolver, span: self.span_from(start) }))
            }
            TokenKind::KwFor => {
                let s = self.current().span.start; self.bump(); self.expect(TokenKind::LParen);
                // Parse init: genvar i = 0 or i = 0
                let _has_genvar = self.eat(TokenKind::KwGenvar).is_some();
                let var_name = if self.at(TokenKind::Identifier) {
                    let n = self.current().text.clone(); self.bump(); n
                } else { String::new() };
                self.expect(TokenKind::Assign);
                let init_expr = self.parse_expression();
                let init_val = match &init_expr.kind {
                    ExprKind::Number(NumberLiteral::Integer { value, base, .. }) => {
                        let r = match base { NumberBase::Binary => 2, NumberBase::Octal => 8, NumberBase::Hex => 16, NumberBase::Decimal => 10 };
                        i64::from_str_radix(&value.replace('_', ""), r).unwrap_or(0)
                    }
                    _ => 0,
                };
                self.expect(TokenKind::Semicolon);
                // Parse condition
                let cond = self.parse_expression();
                self.expect(TokenKind::Semicolon);
                // Parse increment: allow both expression steps (`i++`) and
                // assignment-style steps (`i = i + 1`), which are common in
                // generate-for loops in real RTL.
                let incr = {
                    let expr = self.parse_lvalue_or_expr();
                    if self.at(TokenKind::Assign) || self.at_any(&[
                        TokenKind::PlusAssign, TokenKind::MinusAssign,
                        TokenKind::StarAssign, TokenKind::SlashAssign,
                        TokenKind::PercentAssign, TokenKind::AndAssign,
                        TokenKind::OrAssign, TokenKind::XorAssign,
                        TokenKind::ShiftLeftAssign, TokenKind::ShiftRightAssign,
                        TokenKind::ArithShiftLeftAssign, TokenKind::ArithShiftRightAssign,
                    ]) {
                        let op_kind = self.current().kind.clone();
                        self.bump();
                        let rhs = self.parse_expression();
                        let span = self.span_from(s);
                        let rvalue = match op_kind {
                            TokenKind::PlusAssign => Expression::new(ExprKind::Binary { op: BinaryOp::Add, left: Box::new(expr.clone()), right: Box::new(rhs) }, span),
                            TokenKind::MinusAssign => Expression::new(ExprKind::Binary { op: BinaryOp::Sub, left: Box::new(expr.clone()), right: Box::new(rhs) }, span),
                            TokenKind::StarAssign => Expression::new(ExprKind::Binary { op: BinaryOp::Mul, left: Box::new(expr.clone()), right: Box::new(rhs) }, span),
                            TokenKind::SlashAssign => Expression::new(ExprKind::Binary { op: BinaryOp::Div, left: Box::new(expr.clone()), right: Box::new(rhs) }, span),
                            TokenKind::PercentAssign => Expression::new(ExprKind::Binary { op: BinaryOp::Mod, left: Box::new(expr.clone()), right: Box::new(rhs) }, span),
                            TokenKind::AndAssign => Expression::new(ExprKind::Binary { op: BinaryOp::BitAnd, left: Box::new(expr.clone()), right: Box::new(rhs) }, span),
                            TokenKind::OrAssign => Expression::new(ExprKind::Binary { op: BinaryOp::BitOr, left: Box::new(expr.clone()), right: Box::new(rhs) }, span),
                            TokenKind::XorAssign => Expression::new(ExprKind::Binary { op: BinaryOp::BitXor, left: Box::new(expr.clone()), right: Box::new(rhs) }, span),
                            TokenKind::ShiftLeftAssign => Expression::new(ExprKind::Binary { op: BinaryOp::ShiftLeft, left: Box::new(expr.clone()), right: Box::new(rhs) }, span),
                            TokenKind::ShiftRightAssign => Expression::new(ExprKind::Binary { op: BinaryOp::ShiftRight, left: Box::new(expr.clone()), right: Box::new(rhs) }, span),
                            TokenKind::ArithShiftLeftAssign => Expression::new(ExprKind::Binary { op: BinaryOp::ArithShiftLeft, left: Box::new(expr.clone()), right: Box::new(rhs) }, span),
                            TokenKind::ArithShiftRightAssign => Expression::new(ExprKind::Binary { op: BinaryOp::ArithShiftRight, left: Box::new(expr.clone()), right: Box::new(rhs) }, span),
                            _ => Expression::new(ExprKind::AssignExpr { lvalue: Box::new(expr.clone()), rvalue: Box::new(rhs) }, span),
                        };
                        match op_kind {
                            TokenKind::Assign => rvalue,
                            _ => Expression::new(ExprKind::AssignExpr { lvalue: Box::new(expr), rvalue: Box::new(rvalue) }, span),
                        }
                    } else {
                        expr
                    }
                };
                self.expect(TokenKind::RParen);
                let items = self.parse_generate_branch_items();
                Some(ModuleItem::GenerateFor(GenerateFor { var: var_name, init_val, cond, incr, items, span: self.span_from(s) }))
            }
            TokenKind::KwAnd | TokenKind::KwNand | TokenKind::KwOr | TokenKind::KwNor |
            TokenKind::KwXor | TokenKind::KwXnor | TokenKind::KwBuf | TokenKind::KwNot |
            TokenKind::KwBufif0 | TokenKind::KwBufif1 | TokenKind::KwNotif0 | TokenKind::KwNotif1 =>
                Some(ModuleItem::GateInstantiation(self.parse_gate_instantiation())),
            TokenKind::KwSpecify => {
                self.bump();
                let mut paths = Vec::new();
                while !self.at(TokenKind::KwEndspecify) && !self.at(TokenKind::Eof) {
                    let pstart = self.current().span.start;
                    if self.eat(TokenKind::LParen).is_some() {
                        let src = self.parse_identifier();
                        self.expect(TokenKind::FatArrow);
                        let dst = self.parse_identifier();
                        self.expect(TokenKind::RParen);
                        self.expect(TokenKind::Assign);
                        let delay = if self.eat(TokenKind::LParen).is_some() {
                            let d = self.parse_expression();
                            if self.eat(TokenKind::Comma).is_some() {
                                let _ = self.parse_expression();
                                if self.eat(TokenKind::Comma).is_some() {
                                    let _ = self.parse_expression();
                                }
                            }
                            self.expect(TokenKind::RParen);
                            d
                        } else {
                            self.parse_expression()
                        };
                        self.expect(TokenKind::Semicolon);
                        paths.push(SpecifyPath { src, dst, delay, span: self.span_from(pstart) });
                    } else {
                        self.bump();
                    }
                }
                self.expect(TokenKind::KwEndspecify);
                Some(ModuleItem::SpecifyBlock(SpecifyBlock { paths, span: self.span_from(start) }))
            }
            TokenKind::Identifier | TokenKind::EscapedIdentifier => Some(self.parse_identifier_starting_item()),
            TokenKind::Semicolon => { self.bump(); Some(ModuleItem::Null) }
            TokenKind::Directive => { self.bump(); self.parse_module_item() }
            TokenKind::KwBegin => {
                let s = self.current().span.start; let items = self.parse_generate_branch_items();
                Some(ModuleItem::GenerateRegion(GenerateRegion { items, span: self.span_from(s) }))
            }
            _ => None,
        }
    }

    fn parse_net_declaration(&mut self) -> NetDeclaration {
        let start = self.current().span.start;
        let net_type = self.parse_optional_net_type().unwrap_or(NetType::Wire);
        let data_type = if self.is_data_type_keyword() { self.parse_data_type() }
            else if self.at(TokenKind::LBracket) {
                let dimensions = self.parse_packed_dimensions();
                DataType::Implicit { signing: None, dimensions, span: self.span_from(start) }
            }
            else { DataType::Implicit { signing: None, dimensions: Vec::new(), span: self.span_from(start) } };
        let declarators = self.parse_net_declarator_list();
        self.expect(TokenKind::Semicolon);
        NetDeclaration { net_type, strength: None, data_type, delay: None, declarators, span: self.span_from(start) }
    }

    fn parse_net_declarator_list(&mut self) -> Vec<NetDeclarator> {
        let mut decls = Vec::new();
        loop {
            let start = self.current().span.start;
            let name = self.parse_identifier();
            let dimensions = self.parse_unpacked_dimensions();
            let init = if self.eat(TokenKind::Assign).is_some() { Some(self.parse_expression()) } else { None };
            decls.push(NetDeclarator { name, dimensions, init, span: self.span_from(start) });
            if self.eat(TokenKind::Comma).is_none() { break; }
        }
        decls
    }

    fn parse_gate_instantiation(&mut self) -> GateInstantiation {
        let start = self.current().span.start;
        let gate_type = match self.current_kind() {
            TokenKind::KwAnd => GateType::And, TokenKind::KwNand => GateType::Nand,
            TokenKind::KwOr => GateType::Or, TokenKind::KwNor => GateType::Nor,
            TokenKind::KwXor => GateType::Xor, TokenKind::KwXnor => GateType::Xnor,
            TokenKind::KwBuf => GateType::Buf, TokenKind::KwNot => GateType::Not,
            TokenKind::KwBufif0 => GateType::Bufif0, TokenKind::KwBufif1 => GateType::Bufif1,
            TokenKind::KwNotif0 => GateType::Notif0, TokenKind::KwNotif1 => GateType::Notif1,
            _ => GateType::And,
        };
        self.bump();
        let mut instances = Vec::new();
        loop {
            let istart = self.current().span.start;
            let name = if self.at(TokenKind::Identifier) { Some(self.parse_identifier()) } else { None };
            let _dims = self.parse_unpacked_dimensions(); // Gates can have arrays too
            let mut terminals = Vec::new();
            self.expect(TokenKind::LParen);
            loop {
                terminals.push(self.parse_expression());
                if self.eat(TokenKind::Comma).is_none() { break; }
            }
            self.expect(TokenKind::RParen);
            instances.push(GateInstance { name, terminals, span: self.span_from(istart) });
            if self.eat(TokenKind::Comma).is_none() { break; }
        }
        self.expect(TokenKind::Semicolon);
        GateInstantiation { gate_type, instances, span: self.span_from(start) }
    }

    fn parse_generate_if(&mut self, start: usize) -> ModuleItem {
        let mut branches = Vec::new();
        self.bump(); self.expect(TokenKind::LParen);
        let cond = self.parse_expression(); self.expect(TokenKind::RParen);
        let items = self.parse_generate_branch_items();
        branches.push((Some(cond), items));
        while self.eat(TokenKind::KwElse).is_some() {
            if self.at(TokenKind::KwIf) {
                self.bump(); self.expect(TokenKind::LParen);
                let c = self.parse_expression(); self.expect(TokenKind::RParen);
                let items = self.parse_generate_branch_items();
                branches.push((Some(c), items));
            } else {
                let items = self.parse_generate_branch_items();
                branches.push((None, items)); break;
            }
        }
        ModuleItem::GenerateIf(GenerateIf { branches, span: self.span_from(start) })
    }

    fn parse_generate_case(&mut self, start: usize) -> ModuleItem {
        // case (selector)
        self.bump(); // consume `case`
        self.expect(TokenKind::LParen);
        let selector = self.parse_expression();
        self.expect(TokenKind::RParen);
        let mut arms: Vec<GenerateCaseArm> = Vec::new();
        while !self.at(TokenKind::KwEndcase) && !self.at(TokenKind::Eof) {
            // Either `default[:] generate-block` or `expr {, expr}: generate-block`.
            let mut values: Vec<crate::ast::expr::Expression> = Vec::new();
            if self.eat(TokenKind::KwDefault).is_some() {
                let _ = self.eat(TokenKind::Colon);
            } else {
                loop {
                    values.push(self.parse_expression());
                    if self.eat(TokenKind::Comma).is_none() { break; }
                }
                self.expect(TokenKind::Colon);
            }
            let items = self.parse_generate_branch_items();
            arms.push(GenerateCaseArm { values, items });
        }
        self.expect(TokenKind::KwEndcase);
        ModuleItem::GenerateCase(GenerateCase { selector, arms, span: self.span_from(start) })
    }

    fn parse_generate_branch_items(&mut self) -> Vec<ModuleItem> {
        if self.eat(TokenKind::KwBegin).is_some() {
            let _ = self.parse_end_label();
            let items = self.parse_module_items_until(TokenKind::KwEnd);
            self.expect(TokenKind::KwEnd); let _ = self.parse_end_label();
            items
        } else { self.parse_module_item().into_iter().collect() }
    }

    fn parse_identifier_starting_item(&mut self) -> ModuleItem {
        let start = self.current().span.start;
        let first_name = self.parse_identifier();
        if self.at(TokenKind::DoubleColon) {
            self.bump();
            let second_name = self.parse_identifier();
            let dimensions = self.parse_packed_dimensions();
            let dt = DataType::TypeReference {
                name: TypeName { scope: Some(first_name), name: second_name, span: self.span_from(start) },
                dimensions,
                type_args: Vec::new(),
                span: self.span_from(start),
            };
            let decls = self.parse_var_declarator_list();
            self.expect(TokenKind::Semicolon);
            return ModuleItem::DataDeclaration(DataDeclaration {
                const_kw: false,
                var_kw: false,
                lifetime: None,
                data_type: dt,
                declarators: decls,
                span: self.span_from(start),
            });
        }
        if self.eat(TokenKind::Colon).is_some() { return self.parse_module_item().unwrap_or(ModuleItem::Null); }
        let params = if self.at(TokenKind::Hash) {
            self.bump();
            if self.eat(TokenKind::LParen).is_some() {
                let mut p = Vec::new();
                while !self.at(TokenKind::RParen) && !self.at(TokenKind::Eof) {
                    if self.at(TokenKind::Dot) {
                        self.bump(); let pn = self.parse_identifier(); self.expect(TokenKind::LParen);
                        let pv = if !self.at(TokenKind::RParen) { Some(self.parse_param_value()) } else { None };
                        self.expect(TokenKind::RParen); p.push(ParamConnection::Named { name: pn, value: pv });
                        } else { p.push(ParamConnection::Ordered(Some(self.parse_param_value()))); }

                    if self.eat(TokenKind::Comma).is_none() { break; }
                }
                self.expect(TokenKind::RParen); Some(p)
            } else { None }
        } else { None };

        // Packed dimensions on a user-typedef base: `MyType [hi:lo] var_name;`
        // After the optional #(params), if we see `[`, treat the construct as a
        // data declaration of `MyType` with packed dimensions, not a module
        // instantiation.
        if self.at(TokenKind::LBracket) {
            let dimensions = self.parse_packed_dimensions();
            let type_args: Vec<crate::ast::expr::Expression> = match &params {
                Some(ps) => ps.iter().filter_map(|pc| match pc {
                    ParamConnection::Ordered(Some(ParamValue::Expr(e))) => Some(e.clone()),
                    ParamConnection::Named { value: Some(ParamValue::Expr(e)), .. } => Some(e.clone()),
                    _ => None,
                }).collect(),
                None => Vec::new(),
            };
            let dt = DataType::TypeReference {
                name: TypeName { scope: None, name: first_name, span: self.span_from(start) },
                dimensions, type_args, span: self.span_from(start),
            };
            let decls = self.parse_var_declarator_list();
            self.expect(TokenKind::Semicolon);
            return ModuleItem::DataDeclaration(DataDeclaration {
                const_kw: false, var_kw: false, lifetime: None,
                data_type: dt, declarators: decls, span: self.span_from(start),
            });
        }
        if self.at(TokenKind::Identifier) || self.at(TokenKind::EscapedIdentifier) {
            let initial_pos = self.pos;
            let mut is_data_decl = false;
            let mut instances = Vec::new();
            loop {
                let inst_save_pos = self.pos;
                let inst_start = self.current().span.start;
                let _iname = self.parse_identifier();
                let _dims = self.parse_unpacked_dimensions();
                if self.at(TokenKind::Assign) || self.at(TokenKind::Semicolon) || self.at(TokenKind::Comma) {
                    is_data_decl = true;
                    break;
                }
                self.pos = inst_save_pos; // rewind just this instance
                let iname = self.parse_identifier();
                let dims = self.parse_unpacked_dimensions();
                let conns = self.parse_port_connections();
                instances.push(HierarchicalInstance { name: iname, dimensions: dims, connections: conns, span: self.span_from(inst_start) });
                if self.eat(TokenKind::Comma).is_none() { break; }
            }
            if is_data_decl {
                self.pos = initial_pos;
                let type_args: Vec<crate::ast::expr::Expression> = match &params {
                    Some(ps) => ps.iter().filter_map(|pc| match pc {
                        ParamConnection::Ordered(Some(ParamValue::Expr(e))) => Some(e.clone()),
                        ParamConnection::Named { value: Some(ParamValue::Expr(e)), .. } => Some(e.clone()),
                        _ => None,
                    }).collect(),
                    None => Vec::new(),
                };
                let dt = DataType::TypeReference { name: TypeName { scope: None, name: first_name, span: self.span_from(start) }, dimensions: Vec::new(), type_args, span: self.span_from(start) };
                let decls = self.parse_var_declarator_list(); self.expect(TokenKind::Semicolon);
                ModuleItem::DataDeclaration(DataDeclaration { const_kw: false, var_kw: false, lifetime: None, data_type: dt, declarators: decls, span: self.span_from(start) })
            } else {
                self.expect(TokenKind::Semicolon);
                ModuleItem::ModuleInstantiation(ModuleInstantiation { module_name: first_name, params, instances, span: self.span_from(start) })
            }
        } else {
            let dt = DataType::TypeReference { name: TypeName { scope: None, name: first_name, span: self.span_from(start) }, dimensions: Vec::new(), type_args: Vec::new(), span: self.span_from(start) };
            let decls = self.parse_var_declarator_list(); self.expect(TokenKind::Semicolon);
            ModuleItem::DataDeclaration(DataDeclaration { const_kw: false, var_kw: false, lifetime: None, data_type: dt, declarators: decls, span: self.span_from(start) })
        }
    }

    fn parse_port_connections(&mut self) -> Vec<PortConnection> {
        let mut conns = Vec::new();
        if self.eat(TokenKind::LParen).is_none() { return conns; }
        if self.at(TokenKind::RParen) { self.bump(); return conns; }
        loop {
            if self.at(TokenKind::RParen) || self.at(TokenKind::Eof) { break; }
            if self.at(TokenKind::Dot) {
                self.bump();
                if self.at(TokenKind::Star) { self.bump(); conns.push(PortConnection::Wildcard); }
                else {
                    let nm = self.parse_identifier();
                    let ex = if self.eat(TokenKind::LParen).is_some() {
                        let e = if !self.at(TokenKind::RParen) { Some(self.parse_expression()) } else { None };
                        self.expect(TokenKind::RParen); e
                    } else { None };
                    conns.push(PortConnection::Named { name: nm, expr: ex });
                }
            } else { conns.push(PortConnection::Ordered(Some(self.parse_expression()))); }
            if self.eat(TokenKind::Comma).is_none() { break; }
        }
        self.expect(TokenKind::RParen); conns
    }

    pub(super) fn parse_module_items_until(&mut self, end: TokenKind) -> Vec<ModuleItem> {
        let mut items = Vec::new();
        while !self.at(end) && !self.at(TokenKind::Eof) {
            if let Some(item) = self.parse_module_item() { items.push(item); }
            else { self.error(format!("unexpected: {:?}", self.current().text)); self.bump(); }
        }
        items
    }

    pub(super) fn parse_class_declaration(&mut self) -> ClassDeclaration {
        let start = self.current().span.start;
        let virt = self.eat(TokenKind::KwVirtual).is_some();
        self.expect(TokenKind::KwClass);
        let _lifetime = self.parse_optional_lifetime();
        let name = self.parse_identifier();
        let params = self.parse_parameter_port_list();
        let extends = if self.eat(TokenKind::KwExtends).is_some() {
            let ext_start = self.current().span.start;
            let base_name = self.parse_identifier();
            let args = if self.at(TokenKind::Hash) { self.parse_param_args() }
                       else if self.at(TokenKind::LParen) { self.parse_param_args() } // Support extends C(args) or C#(args)
                       else { Vec::new() };
            Some(ClassExtends { name: base_name, args, span: self.span_from(ext_start) })
        } else { None };
        let mut implements = Vec::new();
        if self.eat(TokenKind::KwImplements).is_some() {
            loop { implements.push(self.parse_identifier()); if self.eat(TokenKind::Comma).is_none() { break; } }
        }
        self.expect(TokenKind::Semicolon);
        let mut items = Vec::new();
        while !self.at(TokenKind::KwEndclass) && !self.at(TokenKind::Eof) { items.push(self.parse_class_item()); }
        self.expect(TokenKind::KwEndclass);
        let endlabel = self.parse_end_label();
        ClassDeclaration { virtual_kw: virt, is_interface: false, name, params, extends, implements, items, endlabel, span: self.span_from(start) }
    }

    fn parse_class_item(&mut self) -> ClassItem {
        let start = self.current().span.start;
        if self.eat(TokenKind::Semicolon).is_some() { return ClassItem::Empty; }
        let mut qualifiers = Vec::new();
        loop {
            match self.current_kind() {
                TokenKind::KwStatic => { self.bump(); qualifiers.push(ClassQualifier::Static); }
                TokenKind::KwProtected => { self.bump(); qualifiers.push(ClassQualifier::Protected); }
                TokenKind::KwLocal => { self.bump(); qualifiers.push(ClassQualifier::Local); }
                TokenKind::KwRand => { self.bump(); qualifiers.push(ClassQualifier::Rand); }
                TokenKind::KwRandc => { self.bump(); qualifiers.push(ClassQualifier::Randc); }
                TokenKind::KwConst => { self.bump(); qualifiers.push(ClassQualifier::Const); }
                TokenKind::KwPure => {
                    self.bump();
                    qualifiers.push(ClassQualifier::Pure);
                    if self.at(TokenKind::KwVirtual) { self.bump(); qualifiers.push(ClassQualifier::Virtual); }
                }
                TokenKind::KwVirtual => {
                    self.bump();
                    qualifiers.push(ClassQualifier::Virtual);
                    if self.at(TokenKind::KwPure) { self.bump(); qualifiers.push(ClassQualifier::Pure); }
                }
                TokenKind::KwExtern => { self.bump(); qualifiers.push(ClassQualifier::Extern); }
                _ => break,
            }
        }

        match self.current_kind() {
            TokenKind::Directive => { self.bump(); self.parse_class_item() }
            TokenKind::KwFunction => {
                let is_pure = qualifiers.contains(&ClassQualifier::Pure);
                let is_extern = qualifiers.contains(&ClassQualifier::Extern);
                if is_pure || is_extern {
                    let func = self.parse_function_prototype();
                    if is_pure { ClassItem::Method(ClassMethod { qualifiers, kind: ClassMethodKind::PureVirtual(func), span: self.span_from(start) }) }
                    else { ClassItem::Method(ClassMethod { qualifiers, kind: ClassMethodKind::Extern(func), span: self.span_from(start) }) }
                } else {
                    let func = self.parse_function_declaration();
                    ClassItem::Method(ClassMethod { qualifiers, kind: ClassMethodKind::Function(func), span: self.span_from(start) })
                }
            }
            TokenKind::KwTask => {
                let is_pure = qualifiers.contains(&ClassQualifier::Pure);
                let is_extern = qualifiers.contains(&ClassQualifier::Extern);
                if is_pure || is_extern {
                    let task = self.parse_task_prototype();
                    ClassItem::Method(ClassMethod { qualifiers, kind: ClassMethodKind::Task(task), span: self.span_from(start) })
                } else {
                    let task = self.parse_task_declaration();
                    ClassItem::Method(ClassMethod { qualifiers, kind: ClassMethodKind::Task(task), span: self.span_from(start) })
                }
            }
            TokenKind::KwConstraint => {
                self.bump();
                let cname = self.parse_identifier();
                let (items, has_body) = if self.at(TokenKind::LBrace) {
                    self.bump();
                    let mut items = Vec::new();
                    while !self.at(TokenKind::RBrace) && !self.at(TokenKind::Eof) {
                        items.push(self.parse_constraint_item());
                    }
                    self.expect(TokenKind::RBrace);
                    (items, true)
                } else {
                    self.expect(TokenKind::Semicolon);
                    (Vec::new(), false)
                };
                ClassItem::Constraint(ClassConstraint {
                    is_static: qualifiers.contains(&ClassQualifier::Static),
                    is_extern: qualifiers.contains(&ClassQualifier::Extern),
                    has_body,
                    name: cname,
                    items,
                    span: self.span_from(start),
                })
            }
            TokenKind::KwTypedef => ClassItem::Typedef(self.parse_typedef_declaration()),
            TokenKind::KwParameter | TokenKind::KwLocalparam => {
                let pd = self.parse_parameter_declaration(); self.expect(TokenKind::Semicolon);
                ClassItem::Parameter(pd)
            }
            TokenKind::KwClass => ClassItem::Class(self.parse_class_declaration()),
            TokenKind::KwCovergroup => ClassItem::Covergroup(self.parse_covergroup_declaration()),
            TokenKind::KwImport => ClassItem::Import(self.parse_import_declaration()),
            _ if self.is_data_type_keyword() || self.at(TokenKind::Identifier) || self.at(TokenKind::KwVar) => {
                let dt = if self.at(TokenKind::KwVar) {
                    self.bump();
                    if self.is_data_type_keyword() || self.at(TokenKind::Identifier) { self.parse_data_type() }
                    else { DataType::Implicit { signing: None, dimensions: Vec::new(), span: self.span_from(start) } }
                } else { self.parse_data_type() };
                let decls = self.parse_var_declarator_list(); self.expect(TokenKind::Semicolon);
                ClassItem::Property(ClassProperty { qualifiers, data_type: dt, declarators: decls, span: self.span_from(start) })
            }
            _ => { self.error(format!("unexpected token in class: {:?}", self.current().text)); self.bump(); ClassItem::Empty }
        }
    }

    fn parse_covergroup_declaration(&mut self) -> CovergroupDeclaration {
        let start = self.current().span.start;
        self.bump();
        let name = self.parse_identifier();
        let event = if self.at(TokenKind::At) {
            Some(self.parse_event_control())
        } else { None };
        self.expect(TokenKind::Semicolon);
        let mut items = Vec::new();
        while !self.at(TokenKind::KwEndgroup) && !self.at(TokenKind::Eof) {
            items.push(self.parse_covergroup_item());
        }
        self.expect(TokenKind::KwEndgroup);
        let endlabel = self.parse_end_label();
        CovergroupDeclaration { name, event, items, endlabel, span: self.span_from(start) }
    }

    fn parse_covergroup_item(&mut self) -> CovergroupItem {
        let start = self.current().span.start;
        let mut name = None;
        if self.at(TokenKind::Identifier) && self.peek_kind() == TokenKind::Colon {
            name = Some(self.parse_identifier());
            self.expect(TokenKind::Colon);
        }

        match self.current_kind() {
            TokenKind::KwCoverpoint => {
                self.bump();
                let expr = self.parse_expression();
                // Handle optional bins etc (simplified: skip for now)
                if self.at(TokenKind::LBrace) {
                    self.bump();
                    let mut depth = 1;
                    while depth > 0 && !self.at(TokenKind::Eof) {
                        if self.at(TokenKind::LBrace) { depth += 1; }
                        else if self.at(TokenKind::RBrace) { depth -= 1; }
                        self.bump();
                    }
                } else {
                    self.expect(TokenKind::Semicolon);
                }
                CovergroupItem::Coverpoint(Coverpoint { name, expr, span: self.span_from(start) })
            }
            TokenKind::KwCross => {
                self.bump();
                let mut ids = Vec::new();
                loop {
                    ids.push(self.parse_identifier());
                    if !self.at(TokenKind::Comma) { break; }
                    self.bump();
                }
                if self.at(TokenKind::LBrace) {
                    self.bump();
                    let mut depth = 1;
                    while depth > 0 && !self.at(TokenKind::Eof) {
                        if self.at(TokenKind::LBrace) { depth += 1; }
                        else if self.at(TokenKind::RBrace) { depth -= 1; }
                        self.bump();
                    }
                } else {
                    self.expect(TokenKind::Semicolon);
                }
                CovergroupItem::Cross(Cross { name, items: ids, span: self.span_from(start) })
            }
            TokenKind::Identifier if self.current().text == "option" || self.current().text == "type_option" => {
                let id = self.parse_identifier();
                let is_type = id.name == "type_option";
                self.expect(TokenKind::Dot);
                let opt_name = self.parse_identifier().name;
                self.expect(TokenKind::Assign);
                let val = self.parse_expression();
                self.expect(TokenKind::Semicolon);
                if is_type { CovergroupItem::TypeOption { name: opt_name, val } }
                else { CovergroupItem::Option { name: opt_name, val } }
            }
            _ => {
                self.error(format!("unexpected token in covergroup: {:?}", self.current().text));
                self.bump();
                CovergroupItem::Option { name: "error".to_string(), val: Expression::new(ExprKind::Empty, self.span_from(start)) }
            }
        }
    }

    fn parse_constraint_item(&mut self) -> ConstraintItem {
        let start = self.current().span.start;
        match self.current_kind() {
            TokenKind::KwSolve => {
                self.bump();
                let mut before = Vec::new();
                loop {
                    before.push(self.parse_identifier());
                    if !self.at(TokenKind::Comma) { break; }
                    self.bump();
                }
                self.expect(TokenKind::KwBefore);
                let mut after = Vec::new();
                loop {
                    after.push(self.parse_identifier());
                    if !self.at(TokenKind::Comma) { break; }
                    self.bump();
                }
                self.expect(TokenKind::Semicolon);
                ConstraintItem::Solve { before, after, span: self.span_from(start) }
            }
            TokenKind::KwIf => {
                self.bump(); self.expect(TokenKind::LParen);
                let cond = self.parse_expression();
                self.expect(TokenKind::RParen);
                let then_item = self.parse_constraint_item();
                let else_item = if self.at(TokenKind::KwElse) {
                    self.bump(); Some(Box::new(self.parse_constraint_item()))
                } else { None };
                ConstraintItem::IfElse { condition: cond, then_item: Box::new(then_item), else_item, span: self.span_from(start) }
            }
            TokenKind::KwForeach => {
                self.bump(); self.expect(TokenKind::LParen);
                let array = self.parse_hierarchical_identifier();
                let array_expr = crate::ast::expr::Expression::new(
                    crate::ast::expr::ExprKind::Ident(array),
                    self.span_from(start),
                );
                self.expect(TokenKind::LBracket);
                let mut vars = Vec::new();
                loop {
                    if self.at(TokenKind::Identifier) { vars.push(Some(self.parse_identifier())); }
                    else if self.at(TokenKind::Comma) { vars.push(None); }
                    else if self.at(TokenKind::RBracket) { break; }
                    else {
                        self.error("expected identifier or comma in foreach");
                        self.bump();
                    }
                    if !self.at(TokenKind::Comma) { break; }
                    self.bump();
                }
                self.expect(TokenKind::RBracket); self.expect(TokenKind::RParen);
                let item = self.parse_constraint_item();
                ConstraintItem::Foreach { array: array_expr, vars, item: Box::new(item), span: self.span_from(start) }
            }
            TokenKind::KwSoft => {
                self.bump();
                ConstraintItem::Soft(Box::new(self.parse_constraint_item()))
            }
            TokenKind::KwDisable => {
                // `disable soft <expr>;` — accept and treat as a no-op block.
                self.bump();
                if self.at(TokenKind::KwSoft) { self.bump(); }
                let _expr = self.parse_expression();
                self.expect(TokenKind::Semicolon);
                ConstraintItem::Block(Vec::new())
            }
            TokenKind::KwUnique => {
                // `unique { var_list };` — accept; approximate as a no-op block.
                self.bump();
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
                ConstraintItem::Block(Vec::new())
            }
            TokenKind::LBrace => {
                self.bump();
                let mut items = Vec::new();
                while !self.at(TokenKind::RBrace) && !self.at(TokenKind::Eof) {
                    items.push(self.parse_constraint_item());
                }
                self.expect(TokenKind::RBrace);
                ConstraintItem::Block(items)
            }
            _ => {
                let expr = self.parse_expression();
                if self.at(TokenKind::KwDist) {
                    // `expr dist { value (:= | :/ ) weight, ... };` — approximate
                    // as `expr inside { value_list }` by keeping values/ranges and
                    // discarding weights.
                    self.bump();
                    self.expect(TokenKind::LBrace);
                    let mut range = Vec::new();
                    loop {
                        range.push(self.parse_constraint_range());
                        // Optional `:= weight` or `:/ weight`
                        if self.at(TokenKind::ColonAssign) || self.at(TokenKind::ColonSlash) {
                            self.bump();
                            let _w = self.parse_expression();
                        }
                        if !self.at(TokenKind::Comma) { break; }
                        self.bump();
                    }
                    self.expect(TokenKind::RBrace);
                    let span = self.span_from(start);
                    self.expect(TokenKind::Semicolon);
                    return ConstraintItem::Inside { expr, range, is_dist: true, span };
                }
                if self.at(TokenKind::KwInside) {
                    self.bump(); self.expect(TokenKind::LBrace);
                    let mut range = Vec::new();
                    loop {
                        range.push(self.parse_constraint_range());
                        if !self.at(TokenKind::Comma) { break; }
                        self.bump();
                    }
                    self.expect(TokenKind::RBrace);
                    let span = self.span_from(start);
                    self.expect(TokenKind::Semicolon);
                    ConstraintItem::Inside { expr, range, is_dist: false, span }
                } else if self.at(TokenKind::Arrow) {
                    self.bump();
                    let constraint = self.parse_constraint_item();
                    ConstraintItem::Implication { condition: expr, constraint: Box::new(constraint), span: self.span_from(start) }
                } else {
                    self.expect(TokenKind::Semicolon);
                    ConstraintItem::Expr(expr)
                }
            }
        }
    }

    fn parse_constraint_range(&mut self) -> ConstraintRange {
        if self.at(TokenKind::LBracket) {
            self.bump();
            let lo = self.parse_expression();
            self.expect(TokenKind::Colon);
            let hi = self.parse_expression();
            self.expect(TokenKind::RBracket);
            ConstraintRange::Range { lo, hi }
        } else {
            ConstraintRange::Value(self.parse_expression())
        }
    }
}
