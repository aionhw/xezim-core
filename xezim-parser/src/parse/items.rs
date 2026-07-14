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
        let endlabel = self.parse_end_label_checked(&name.name);

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
            // LRM §25.9 — `virtual <iface_t> <name>` port form.
            || (self.at(TokenKind::KwVirtual)
                && matches!(self.peek_kind(),
                    TokenKind::KwInterface | TokenKind::Identifier))
            // LRM §25.3.2 — generic interface port `interface [.mp] <name>`.
            || self.at(TokenKind::KwInterface)
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
        // LRM §25.9: `virtual <iface_t> [.<modport>] <name>` — module
        // port form. Mirror `parse_function_ports` so a child module
        // can take a virtual interface as a port for vif pass-through.
        let data_type = if self.at(TokenKind::KwVirtual)
            && (self.peek_kind() == TokenKind::KwInterface
                || self.peek_kind() == TokenKind::Identifier)
        {
            self.bump(); // virtual
            if self.at(TokenKind::KwInterface) {
                self.bump();
            }
            let if_name = self.parse_identifier();
            let modport = if self.at(TokenKind::Dot) {
                self.bump();
                Some(self.parse_identifier())
            } else { None };
            Some(DataType::Interface { name: if_name, modport, span: self.span_from(start) })
        } else if self.at(TokenKind::KwInterface) {
            // §25.3.2 generic interface port: `interface [.<modport>] <name>`.
            self.bump(); // interface
            let modport = if self.at(TokenKind::Dot) {
                self.bump();
                Some(self.parse_identifier())
            } else { None };
            Some(DataType::Interface {
                name: crate::ast::Identifier { name: "interface".to_string(), span: self.span_from(start) },
                modport, span: self.span_from(start),
            })
        } else if self.is_data_type_keyword() {
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
            let before = self.pos;
            if let Some(item) = self.parse_module_item() { items.push(item); }
            else if self.pos == before {
                // parse_module_item returned None WITHOUT consuming anything —
                // genuinely stuck; report and force progress. A None that DID
                // advance is a deliberate parse-accept/skip (specparam,
                // interconnect, …) and must not be flagged as an error.
                self.error(format!("unexpected: {:?}", self.current().text));
                self.bump();
            }
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
            // `timeunit 1ns / 10ps;` / `timeprecision …;` inside a module —
            // already parsed at top-level via Description::TimeunitsDecl;
            // accept and discard inside modules too (LRM allows both).
            TokenKind::KwTimeunit | TokenKind::KwTimeprecision => {
                Some(ModuleItem::TimeunitsDecl(self.parse_timeunits_declaration()))
            }
            // Deprecated hierarchical parameter override `defparam path.p = e;`
            // (LRM §23.10.1). Parse and discard — consume to the terminating
            // semicolon so it doesn't break the module-item stream (veer-el2 tb).
            TokenKind::KwDefparam => {
                self.bump();
                while !self.at(TokenKind::Semicolon) && !self.at(TokenKind::Eof) { self.bump(); }
                let _ = self.eat(TokenKind::Semicolon);
                None
            }
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
                // §23.2.2.1: `input var x;` — optional `var` keyword.
                let has_var = self.eat(TokenKind::KwVar).is_some();
                // §23.2.2.3: an `inout` port shall be of a net type — `inout var`
                // is illegal (a variable cannot have multiple drivers / be
                // bidirectionally connected).
                if has_var && dir == PortDirection::Inout {
                    self.error("an 'inout' port cannot be declared 'var' (must be a net type)");
                }
                let dt = if self.is_data_type_keyword()
                    || self.at(TokenKind::KwSigned) || self.at(TokenKind::KwUnsigned) { self.parse_data_type() }
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
            // §14.3: `global clocking …` — consume the `global` qualifier and
            // reuse the clocking-block parse via the KwClocking arm below.
            TokenKind::KwGlobal if self.peek_kind() == TokenKind::KwClocking => {
                self.bump();
                self.parse_module_item()
            }
            // §6.20.5 specparam — parse-accept (xezim doesn't model specify
            // timing); consume through the terminating ';'.
            TokenKind::KwSpecparam => {
                while !self.at(TokenKind::Semicolon) && !self.at(TokenKind::Eof) { self.bump(); }
                self.expect(TokenKind::Semicolon);
                None
            }
            // §6.6.8 interconnect net — parse-accept; consume to ';'.
            TokenKind::KwInterconnect => {
                while !self.at(TokenKind::Semicolon) && !self.at(TokenKind::Eof) { self.bump(); }
                self.expect(TokenKind::Semicolon);
                None
            }
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
                // Skip optional inline attribute spec `(* ... *)` between
                // `always_*` and the body. The preprocessor only strips
                // standalone-line attributes; inline ones reach the parser.
                self.skip_optional_attribute();
                let stmt = self.parse_statement();
                Some(ModuleItem::AlwaysConstruct(AlwaysConstruct { kind, stmt, span: self.span_from(start) }))
            }
            TokenKind::KwInitial => { self.bump(); let st = self.parse_statement();
                Some(ModuleItem::InitialConstruct(InitialConstruct { stmt: st, span: self.span_from(start) })) }
            TokenKind::KwFinal => { self.bump(); let st = self.parse_statement();
                Some(ModuleItem::FinalConstruct(FinalConstruct { stmt: st, span: self.span_from(start) })) }
            TokenKind::KwAssign => {
                self.bump();
                // Optional drive_strength `(strong1, weak0)` (§10.3.1).
                // Retained as a comma-joined keyword list so `%v` (§21.2.1.5)
                // can report the driven strength; otherwise unmodelled.
                let mut strength: Option<String> = None;
                if self.at(TokenKind::LParen) && self.peek_kind().is_strength_keyword() {
                    self.bump();
                    let mut parts: Vec<String> = Vec::new();
                    while !self.at(TokenKind::RParen) && !self.at(TokenKind::Eof) {
                        let t = self.bump();
                        if t.kind != TokenKind::Comma {
                            parts.push(t.text.clone());
                        }
                    }
                    self.expect(TokenKind::RParen);
                    strength = Some(parts.join(","));
                }
                let delay = if self.eat(TokenKind::Hash).is_some() {
                    if self.eat(TokenKind::LParen).is_some() {
                        let expr = self.parse_expression();
                        self.expect(TokenKind::RParen);
                        Some(expr)
                    } else {
                        Some(self.parse_expression())
                    }
                } else {
                    None
                };
                let mut asgns = Vec::new();
                loop { let l = self.parse_expression(); self.expect(TokenKind::Assign); let r = self.parse_expression();
                    asgns.push((l, r)); if self.eat(TokenKind::Comma).is_none() { break; } }
                self.expect(TokenKind::Semicolon);
                Some(ModuleItem::ContinuousAssign(ContinuousAssign { strength, delay, assignments: asgns, span: self.span_from(start) }))
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
                let mut items = Vec::new();
                if self.at(TokenKind::LBrace) {
                    self.bump();
                    while !self.at(TokenKind::RBrace) && !self.at(TokenKind::Eof) {
                        items.push(self.parse_constraint_item());
                    }
                    self.expect(TokenKind::RBrace);
                } else if self.at(TokenKind::Semicolon) {
                    self.bump();
                }
                Some(ModuleItem::OutOfClassConstraint { class_name, constraint_name, items })
            }
            TokenKind::KwVirtual => {
                if self.peek_kind() == TokenKind::KwInterface { Some(self.parse_identifier_starting_item()) }
                else { self.bump(); self.parse_module_item() }
            }
            // IEEE 1800-2023 §23.11: `bind` inside a module body. Parsed into a
            // `ModuleItem::Bind`, which elaboration applies the same way as a
            // compilation-unit bind (appending the bound instantiation to every
            // instance of <target>). Unhandled selectors skip-parse to `Null`.
            TokenKind::KwBind => {
                self.bump(); // bind
                match self.try_bind_directive() {
                    Some(b) => Some(ModuleItem::Bind(b)),
                    None => Some(ModuleItem::Null),
                }
            }
            TokenKind::KwModport => {
                let start = self.current().span.start; self.bump();
                let mut items = Vec::new();
                loop {
                    let istart = self.current().span.start;
                    let name = self.parse_identifier();
                    self.expect(TokenKind::LParen);
                    let mut ports = Vec::new();
                    // LRM §25.5: a direction keyword applies to ALL following
                    // comma-separated members until the next direction keyword
                    // (`output a, b, c, input d` → a/b/c output, d input). Carry
                    // the last-seen direction; a bare member inherits it instead
                    // of defaulting to input (which mis-marked outputs as inputs,
                    // wrongly rejecting writes — veer-el2 / rsd).
                    let mut last_dir = PortDirection::Input;
                    loop {
                        if self.at(TokenKind::RParen) || self.at(TokenKind::Eof) { break; }
                        let pstart = self.current().span.start;
                        // IEEE 1800-2023 §25.5: `modport <name> ( clocking <cb> )`
                        // — a modport_clocking_declaration. We record it as a
                        // synthetic Input port whose name is the clocking
                        // block; downstream consumers that don't understand
                        // clocking still see *something* there.
                        if self.eat(TokenKind::KwClocking).is_some() {
                            let cb_name = self.parse_identifier();
                            ports.push(ModportPort {
                                direction: PortDirection::Input,
                                name: cb_name,
                                span: self.span_from(pstart),
                            });
                        } else {
                            if let Some(d) = self.parse_optional_direction() { last_dir = d; }
                            let port_name = self.parse_identifier();
                            ports.push(ModportPort { direction: last_dir, name: port_name, span: self.span_from(pstart) });
                        }
                        if self.eat(TokenKind::Comma).is_none() { break; }
                    }
                    self.expect(TokenKind::RParen);
                    items.push(ModportItem { name, ports, span: self.span_from(istart) });
                    if self.eat(TokenKind::Comma).is_none() { break; }
                }
                self.expect(TokenKind::Semicolon);
                Some(ModuleItem::ModportDeclaration(ModportDeclaration { items, span: self.span_from(start) }))
            }
            // IEEE 1800-2023 §14.3 — clocking block. We now capture the
            // direction-tagged signals into a real ClockingDeclaration so
            // the elaborator can register `clocking_blocks[<name>]` and the
            // identifier validator accepts `<cb>.<sig>` references. Body
            // statements beyond `<dir> [type] <name> (, <name>)*` are
            // skipped (default skew, etc. — rich grammar not modelled).
            TokenKind::KwClocking => {
                let start = self.current().span.start; self.bump();
                let cb_name = if self.at(TokenKind::Identifier) || self.at(TokenKind::EscapedIdentifier) {
                    Some(self.parse_identifier())
                } else { None };
                // LRM §14.3 clock event: `@(posedge <sig>)` — capture
                // the signal identifier so the simulator can snapshot
                // its inputs before each clock edge. Falls back to the
                // legacy skip path for forms we don't recognise.
                let mut clock_signal_id: Option<crate::ast::Identifier> = None;
                if self.at(TokenKind::At) {
                    self.bump();
                    if self.at(TokenKind::LParen) {
                        self.bump();
                        let _ = self.eat(TokenKind::KwPosedge);
                        let _ = self.eat(TokenKind::KwNegedge);
                        let _ = self.eat(TokenKind::KwEdge);
                        if self.at(TokenKind::Identifier) {
                            clock_signal_id = Some(self.parse_identifier());
                        }
                        // Skip to matching close-paren (handles
                        // `(posedge clk iff cond)` etc.).
                        let mut d = 1i32;
                        while !self.at(TokenKind::Eof) && d > 0 {
                            match self.current_kind() {
                                TokenKind::LParen => d += 1,
                                TokenKind::RParen => {
                                    d -= 1;
                                    if d == 0 {
                                        self.bump();
                                        break;
                                    }
                                }
                                _ => {}
                            }
                            self.bump();
                        }
                    }
                }
                self.expect(TokenKind::Semicolon);
                let items: Vec<crate::ast::stmt::Statement> = Vec::new();
                let mut signals: Vec<ClockingSignal> = Vec::new();
                while !self.at(TokenKind::KwEndclocking) && !self.at(TokenKind::Eof) {
                    // `default input #1step output ...;` and other body
                    // statements (LRM §14.3) are not captured — skip to the
                    // matching `;` so the signal-list pass below stays in
                    // sync.
                    if self.at(TokenKind::KwDefault) {
                        while !self.at(TokenKind::Semicolon) && !self.at(TokenKind::Eof) { self.bump(); }
                        if self.at(TokenKind::Semicolon) { self.bump(); }
                        continue;
                    }
                    match self.current_kind() {
                        TokenKind::KwInput | TokenKind::KwOutput | TokenKind::KwInout | TokenKind::KwRef => {
                            let sstart = self.current().span.start;
                            let direction = self.parse_optional_direction().unwrap_or(PortDirection::Input);
                            // Optional `#delay` skew specifier — skip past
                            // (parse_optional_direction already left us
                            // looking at the next token after the dir kw).
                            if self.at(TokenKind::Hash) {
                                self.bump();
                                if self.at(TokenKind::LParen) {
                                    let mut d = 1i32; self.bump();
                                    while !self.at(TokenKind::Eof) && d > 0 {
                                        match self.current_kind() {
                                            TokenKind::LParen => d += 1,
                                            TokenKind::RParen => d -= 1,
                                            _ => {}
                                        }
                                        self.bump();
                                    }
                                } else {
                                    self.bump(); // single token (`1step`, identifier, etc.)
                                }
                            }
                            // Optional `negedge`/`posedge`/`edge` skew kw.
                            if matches!(self.current_kind(),
                                TokenKind::KwNegedge | TokenKind::KwPosedge | TokenKind::KwEdge)
                            {
                                self.bump();
                            }
                            if self.is_data_type_keyword()
                                || (self.at(TokenKind::Identifier) && self.peek_kind() == TokenKind::Identifier)
                            {
                                let _ = self.parse_data_type();
                            }
                            loop {
                                if self.at(TokenKind::Identifier) {
                                    let id = self.parse_identifier();
                                    signals.push(ClockingSignal { direction, name: id, span: self.span_from(sstart) });
                                }
                                if self.eat(TokenKind::Comma).is_none() { break; }
                            }
                            // Skip anything we don't understand up to `;`.
                            while !self.at(TokenKind::Semicolon) && !self.at(TokenKind::Eof) {
                                self.bump();
                            }
                            if self.at(TokenKind::Semicolon) { self.bump(); }
                        }
                        _ => { self.bump(); }
                    }
                }
                self.expect(TokenKind::KwEndclocking);
                let endlabel = if self.eat(TokenKind::Colon).is_some() {
                    Some(self.parse_identifier())
                } else { None };
                let id = cb_name.unwrap_or_else(|| Identifier { name: "default".to_string(), span: self.span_from(start) });
                Some(ModuleItem::ClockingDeclaration(ClockingDeclaration { name: id, clock_signal: clock_signal_id, signals, items, endlabel, span: self.span_from(start) }))
            }
            TokenKind::KwAssert | TokenKind::KwAssume | TokenKind::KwCover =>
                Some(ModuleItem::AssertionItem(self.parse_assertion_statement())),
            TokenKind::KwProperty => {
                let start = self.current().span.start; self.bump();
                let name = self.parse_identifier();
                if self.at(TokenKind::LParen) { self.bump(); while !self.at(TokenKind::RParen) && !self.at(TokenKind::Eof) { self.bump(); } self.expect(TokenKind::RParen); }
                self.expect(TokenKind::Semicolon);
                // LRM §16.6 — capture the property body when it matches
                // the common `@(<event>) <expr>;` shape. Re-uses the
                // assertion parser's clock-event capture (an
                // `SvaClocked { clock, body }` wrapper). Properties
                // not matching this shape fall back to the legacy
                // token-skip path so the parser stays resilient.
                let body_expr = if self.at(TokenKind::At) {
                    let bstart = self.current().span.start;
                    self.bump(); // @
                    let clk = if self.at(TokenKind::LParen) {
                        self.bump();
                        let _ = self.eat(TokenKind::KwPosedge);
                        let _ = self.eat(TokenKind::KwNegedge);
                        let _ = self.eat(TokenKind::KwEdge);
                        let e = self.parse_expression();
                        let _ = self.eat(TokenKind::RParen);
                        e
                    } else {
                        let _ = self.eat(TokenKind::KwPosedge);
                        let _ = self.eat(TokenKind::KwNegedge);
                        self.parse_expression()
                    };
                    // §16.12: optional `disable iff (<expr>)` after the
                    // clocking event, before the property expression. Consume
                    // it (parse-accept; the abort condition isn't modelled).
                    if self.at(TokenKind::KwDisable) && self.peek_kind() == TokenKind::KwIff {
                        self.bump(); // disable
                        self.bump(); // iff
                        if self.at(TokenKind::LParen) {
                            self.bump();
                            let mut depth = 1;
                            while depth > 0 && !self.at(TokenKind::Eof) {
                                match self.current_kind() {
                                    TokenKind::LParen => depth += 1,
                                    TokenKind::RParen => depth -= 1,
                                    _ => {}
                                }
                                self.bump();
                            }
                        }
                    }
                    self.in_sva_seq = true;
                    let body = self.parse_expression();
                    self.in_sva_seq = false;
                    let _ = self.eat(TokenKind::Semicolon);
                    Some(crate::ast::expr::Expression::new(
                        crate::ast::expr::ExprKind::SvaClocked {
                            clock: Box::new(clk),
                            body: Box::new(body),
                        },
                        self.span_from(bstart),
                    ))
                } else {
                    None
                };
                while !self.at(TokenKind::KwEndproperty) && !self.at(TokenKind::Eof) { self.bump(); }
                self.expect(TokenKind::KwEndproperty);
                let endlabel = self.parse_end_label();
                let items = Vec::new();
                Some(ModuleItem::PropertyDeclaration(PropertyDeclaration { name, items, body: body_expr, endlabel, span: self.span_from(start) }))
            }
            TokenKind::KwSequence => {
                let start = self.current().span.start; self.bump();
                let name = self.parse_identifier();
                if self.at(TokenKind::LParen) { self.bump(); while !self.at(TokenKind::RParen) && !self.at(TokenKind::Eof) { self.bump(); } self.expect(TokenKind::RParen); }
                self.expect(TokenKind::Semicolon);
                // LRM §16.5 — capture the sequence body when it matches
                // the common `@(<event>) <expr>;` shape, mirroring the
                // property-decl path. Other shapes (raw `##N` chains)
                // fall back to the token-skip path.
                let body_expr = if self.at(TokenKind::At) {
                    let bstart = self.current().span.start;
                    self.bump();
                    let clk = if self.at(TokenKind::LParen) {
                        self.bump();
                        let _ = self.eat(TokenKind::KwPosedge);
                        let _ = self.eat(TokenKind::KwNegedge);
                        let _ = self.eat(TokenKind::KwEdge);
                        let e = self.parse_expression();
                        let _ = self.eat(TokenKind::RParen);
                        e
                    } else {
                        let _ = self.eat(TokenKind::KwPosedge);
                        let _ = self.eat(TokenKind::KwNegedge);
                        self.parse_expression()
                    };
                    self.in_sva_seq = true;
                    let body = self.parse_expression();
                    self.in_sva_seq = false;
                    let _ = self.eat(TokenKind::Semicolon);
                    Some(crate::ast::expr::Expression::new(
                        crate::ast::expr::ExprKind::SvaClocked {
                            clock: Box::new(clk),
                            body: Box::new(body),
                        },
                        self.span_from(bstart),
                    ))
                } else { None };
                while !self.at(TokenKind::KwEndsequence) && !self.at(TokenKind::Eof) { self.bump(); }
                self.expect(TokenKind::KwEndsequence);
                let endlabel = self.parse_end_label();
                let items = Vec::new();
                Some(ModuleItem::SequenceDeclaration(SequenceDeclaration { name, items, body: body_expr, endlabel, span: self.span_from(start) }))
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
                Some(ModuleItem::ClockingDeclaration(ClockingDeclaration { name: id, clock_signal: None, signals, items, endlabel, span: self.span_from(start) }))
            }
            TokenKind::KwDefault => {
                self.bump();
                if self.at(TokenKind::KwClocking) {
                    self.parse_module_item() // recurse to handle clocking
                } else if self.at(TokenKind::KwDisable) {
                    // IEEE 1800-2023 §16.4.2: `default disable iff <expr>;`
                    // is a default for all concurrent assertions in scope.
                    // Skip-parse (we don't model SVA semantics yet).
                    self.bump(); // disable
                    let _ = self.eat(TokenKind::KwIff);
                    // Consume balanced expression up to the next ';' at depth 0.
                    let mut d = 0i32;
                    while !self.at(TokenKind::Eof) {
                        match self.current_kind() {
                            TokenKind::LParen => { d += 1; self.bump(); }
                            TokenKind::RParen => { d -= 1; self.bump(); }
                            TokenKind::Semicolon if d == 0 => { self.bump(); break; }
                            _ => { self.bump(); }
                        }
                    }
                    Some(ModuleItem::Null)
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
                let (items, name) = self.parse_generate_branch_items_named();
                Some(ModuleItem::GenerateFor(GenerateFor { var: var_name, init_val, cond, incr, items, name, span: self.span_from(s) }))
            }
            TokenKind::KwAnd | TokenKind::KwNand | TokenKind::KwOr | TokenKind::KwNor |
            TokenKind::KwXor | TokenKind::KwXnor | TokenKind::KwBuf | TokenKind::KwNot |
            TokenKind::KwBufif0 | TokenKind::KwBufif1 | TokenKind::KwNotif0 | TokenKind::KwNotif1 |
            TokenKind::KwNmos | TokenKind::KwPmos | TokenKind::KwCmos |
            TokenKind::KwRnmos | TokenKind::KwRpmos | TokenKind::KwRcmos |
            TokenKind::KwTran | TokenKind::KwRtran |
            TokenKind::KwTranif0 | TokenKind::KwTranif1 | TokenKind::KwRtranif0 | TokenKind::KwRtranif1 |
            TokenKind::KwPullup | TokenKind::KwPulldown =>
                Some(ModuleItem::GateInstantiation(self.parse_gate_instantiation())),
            TokenKind::KwSpecify => {
                // §28.2 specify block. The path grammar is rich (`=>`/`*>`
                // parallel/full, edge-sensitive, state-dependent, `if (...)`
                // conditional, $setup/$hold timing checks). We parse only the
                // common SIMPLE module path — `( src => dst ) = ( d {, d} ) ;`
                // (or a bare delay) with plain-identifier endpoints — into a
                // SpecifyPath so the elaborator can model its delay. Every
                // other form is skipped to the next `;`, preserving the prior
                // robust whole-block skip behavior.
                self.bump();
                let mut paths = Vec::new();
                while !self.at(TokenKind::KwEndspecify) && !self.at(TokenKind::Eof) {
                    if self.at(TokenKind::LParen) {
                        if let Some(p) = self.try_parse_simple_specify_path() {
                            paths.push(p);
                            continue;
                        }
                    }
                    // Unrecognized specify item: skip to (and past) the next ';'.
                    self.skip_to_semi();
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
        // §10.3.1: optional drive_strength `(strong1, weak0)` on a net
        // declaration with a continuous assignment, e.g.
        // `wire (strong1, weak0) w = a & b;`. xezim doesn't model strengths;
        // consume the group when it opens with a strength keyword.
        if self.at(TokenKind::LParen) && self.peek_kind().is_strength_keyword() {
            self.bump();
            while !self.at(TokenKind::RParen) && !self.at(TokenKind::Eof) { self.bump(); }
            self.expect(TokenKind::RParen);
        }
        // §6.9.2: optional `vectored` / `scalared` charge/drive qualifier
        // between the net type and the (optional) range — `tri1 vectored [15:0] a;`.
        if self.at(TokenKind::KwVectored) || self.at(TokenKind::KwScalared) { self.bump(); }
        // §10.3.3: optional net delay `wire #10 w;` / `wire #(d1,d2) w;`.
        // Parse-accept; xezim doesn't model net delays.
        if self.at(TokenKind::Hash) {
            self.bump();
            if self.eat(TokenKind::LParen).is_some() {
                let mut depth = 1i32;
                while depth > 0 && !self.at(TokenKind::Eof) {
                    match self.current_kind() {
                        TokenKind::LParen => depth += 1,
                        TokenKind::RParen => depth -= 1,
                        _ => {}
                    }
                    self.bump();
                }
            } else {
                self.bump(); // #10 / #delay_id
            }
        }
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
            TokenKind::KwNmos => GateType::Nmos, TokenKind::KwPmos => GateType::Pmos,
            TokenKind::KwCmos => GateType::Cmos,
            TokenKind::KwRnmos => GateType::Rnmos, TokenKind::KwRpmos => GateType::Rpmos,
            TokenKind::KwRcmos => GateType::Rcmos,
            TokenKind::KwTran => GateType::Tran, TokenKind::KwRtran => GateType::Rtran,
            TokenKind::KwTranif0 => GateType::Tranif0, TokenKind::KwTranif1 => GateType::Tranif1,
            TokenKind::KwRtranif0 => GateType::Rtranif0, TokenKind::KwRtranif1 => GateType::Rtranif1,
            TokenKind::KwPullup => GateType::Pullup, TokenKind::KwPulldown => GateType::Pulldown,
            _ => GateType::And,
        };
        self.bump();
        // Optional drive_strength `(strong0, strong1)` / charge_strength
        // `(small)` / pull strength `(pull1)` (§28.4). xezim doesn't model
        // strengths; consume the group when it opens with a strength keyword.
        if self.at(TokenKind::LParen) && self.peek_kind().is_strength_keyword() {
            self.bump(); // (
            while !self.at(TokenKind::RParen) && !self.at(TokenKind::Eof) { self.bump(); }
            self.expect(TokenKind::RParen);
        }
        // Optional `#(delay)` or `#delay` spec between the gate keyword and
        // the first instance: `buf #(D) name (...)`.
        if self.eat(TokenKind::Hash).is_some() {
            if self.eat(TokenKind::LParen).is_some() {
                let mut depth = 1;
                while depth > 0 && !self.at(TokenKind::Eof) {
                    match self.current_kind() {
                        TokenKind::LParen => { depth += 1; self.bump(); }
                        TokenKind::RParen => { depth -= 1; self.bump(); }
                        _ => { self.bump(); }
                    }
                }
            } else {
                let _ = self.parse_expression();
            }
        }
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
        self.parse_generate_branch_items_named().0
    }

    /// Parse the simple specify module path `( src => dst ) = ( d {, d} ) ;`
    /// (or `... = d ;`) with plain-identifier endpoints. Returns the path's
    /// first delay as its `delay`. Returns None and rewinds for any other
    /// form (edge-sensitive `( posedge a => ...)`, `*>`, conditional, bit-
    /// selected endpoints, timing checks) so the caller skips it.
    fn try_parse_simple_specify_path(&mut self) -> Option<SpecifyPath> {
        let start_pos = self.pos;
        let sp_start = self.current().span.start;
        let is_ident = |p: &Self| {
            matches!(
                p.current().kind,
                TokenKind::Identifier | TokenKind::EscapedIdentifier
            )
        };
        if !self.at(TokenKind::LParen) {
            return None;
        }
        self.bump();
        if !is_ident(self) {
            self.pos = start_pos;
            return None;
        }
        let src = self.parse_identifier();
        // Only the parallel-connection `=>` with a bare-identifier source.
        if !self.at(TokenKind::FatArrow) {
            self.pos = start_pos;
            return None;
        }
        self.bump();
        if !is_ident(self) {
            self.pos = start_pos;
            return None;
        }
        let dst = self.parse_identifier();
        if !self.at(TokenKind::RParen) {
            self.pos = start_pos;
            return None;
        }
        self.bump();
        if !self.at(TokenKind::Assign) {
            self.pos = start_pos;
            return None;
        }
        self.bump();
        // Delay: `( d {, d} )` (use the first) or a bare expression.
        let delay = if self.at(TokenKind::LParen) {
            self.bump();
            let d = self.parse_expression();
            while self.at(TokenKind::Comma) {
                self.bump();
                let _ = self.parse_expression();
            }
            if !self.at(TokenKind::RParen) {
                self.pos = start_pos;
                return None;
            }
            self.bump();
            d
        } else {
            self.parse_expression()
        };
        if self.at(TokenKind::Semicolon) {
            self.bump();
        }
        Some(SpecifyPath {
            src,
            dst,
            delay,
            span: self.span_from(sp_start),
        })
    }

    /// Like `parse_generate_branch_items` but also returns the optional
    /// `begin : <label>` block name (needed to namespace generate-for renames).
    fn parse_generate_branch_items_named(&mut self) -> (Vec<ModuleItem>, Option<String>) {
        if self.eat(TokenKind::KwBegin).is_some() {
            let label = self.parse_end_label().map(|id| id.name);
            let items = self.parse_module_items_until(TokenKind::KwEnd);
            self.expect(TokenKind::KwEnd); let _ = self.parse_end_label();
            (items, label)
        } else { (self.parse_module_item().into_iter().collect(), None) }
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

    pub(super) fn parse_port_connections(&mut self) -> Vec<PortConnection> {
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
        // IEEE 1800-2017 §8.26: `interface class <name>; … endclass`. The
        // leading `interface` keyword (mutually exclusive with `virtual`)
        // marks an interface class; the rest parses like a normal class.
        let is_iface = self.eat(TokenKind::KwInterface).is_some();
        self.expect(TokenKind::KwClass);
        // IEEE 1800-2023 §8.20.5: `class :final <name>` — only `:final` is
        // legal on a class declaration. Gated on --sv2023.
        let is_final = if crate::is_sv2023()
            && self.at(TokenKind::Colon)
            && self.peek_kind() == TokenKind::KwFinal
        {
            self.bump(); // ':'
            self.bump(); // 'final'
            true
        } else {
            false
        };
        let _lifetime = self.parse_optional_lifetime();
        let name = self.parse_identifier();
        let params = self.parse_parameter_port_list();
        let extends = if self.eat(TokenKind::KwExtends).is_some() {
            let ext_start = self.current().span.start;
            // §8.13: the base class may be package/class-scoped —
            // `extends pkg::Base` or `extends A::B::C`. Keep the final
            // segment as the base-class name; the scope prefix is consumed.
            let mut base_name = self.parse_identifier();
            while self.at(TokenKind::DoubleColon) {
                self.bump();
                base_name = self.parse_identifier();
            }
            let args = if self.at(TokenKind::Hash) { self.parse_param_args() }
                       else if self.at(TokenKind::LParen) { self.parse_param_args() } // Support extends C(args) or C#(args)
                       else { Vec::new() };
            // §8.26: an interface class may extend MULTIPLE interface classes
            // (`extends ic1#(T), ic2#(T)`). Keep the first in the AST and
            // parse-accept the rest (consume `, base[::seg]…[#(args)]`).
            while self.at(TokenKind::Comma) {
                self.bump();
                let _ = self.parse_identifier();
                while self.at(TokenKind::DoubleColon) { self.bump(); let _ = self.parse_identifier(); }
                if self.at(TokenKind::Hash) || self.at(TokenKind::LParen) { let _ = self.parse_param_args(); }
            }
            Some(ClassExtends { name: base_name, args, span: self.span_from(ext_start) })
        } else { None };
        let mut implements = Vec::new();
        if self.eat(TokenKind::KwImplements).is_some() {
            loop {
                let mut iface = self.parse_identifier();
                // §8.26: scoped interface-class name `implements pkg::Iface`.
                while self.at(TokenKind::DoubleColon) {
                    self.bump();
                    iface = self.parse_identifier();
                }
                implements.push(iface);
                // §8.26.1: `implements Iface#(params)` — consume and discard
                // the parameterization (only the base name is recorded).
                if self.at(TokenKind::Hash) { let _ = self.parse_param_args(); }
                if self.eat(TokenKind::Comma).is_none() { break; }
            }
        }
        self.expect(TokenKind::Semicolon);
        // Push the class name onto the parser's class-context stack so
        // `type(this)` references resolve to this class (§6.20.2.1).
        crate::push_class_context(name.name.clone());
        let mut items = Vec::new();
        while !self.at(TokenKind::KwEndclass) && !self.at(TokenKind::Eof) { items.push(self.parse_class_item()); }
        crate::pop_class_context();
        self.expect(TokenKind::KwEndclass);
        let endlabel = self.parse_end_label();
        ClassDeclaration { virtual_kw: virt, is_interface: is_iface, is_final, name, params, extends, implements, items, endlabel, span: self.span_from(start) }
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
            _ if self.is_data_type_keyword()
                || self.at(TokenKind::Identifier)
                || self.at(TokenKind::KwVar)
                || (crate::is_sv2023()
                    && self.at(TokenKind::KwType)
                    && self.peek_kind() == TokenKind::LParen) =>
            {
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

    /// Consume a balanced `( ... )` group, including nested parens. Assumes the
    /// current token is `(`. Used to skip clauses whose contents we don't model
    /// (covergroup formals, `with function sample` port lists, `iff` guards).
    fn skip_balanced_parens(&mut self) {
        if !self.at(TokenKind::LParen) { return; }
        self.bump();
        let mut depth = 1;
        while depth > 0 && !self.at(TokenKind::Eof) {
            if self.at(TokenKind::LParen) { depth += 1; }
            else if self.at(TokenKind::RParen) { depth -= 1; }
            self.bump();
        }
    }

    /// Skip an unmodeled coverpoint bin body up to (but not consuming) the
    /// terminating `;` at nesting depth 0, or a `}` / `)` / `]` that CLOSES
    /// the enclosing scope. Depth-aware so bodies like
    /// `cp with (item inside {list})` don't desync the coverpoint's brace
    /// matching on the inner `}`.
    fn skip_bin_body_to_semicolon(&mut self) {
        let mut depth = 0usize;
        loop {
            match self.current_kind() {
                TokenKind::Eof => break,
                TokenKind::LBrace | TokenKind::LParen | TokenKind::LBracket => depth += 1,
                TokenKind::RBrace | TokenKind::RParen | TokenKind::RBracket => {
                    if depth == 0 { break; }
                    depth -= 1;
                }
                TokenKind::Semicolon if depth == 0 => break,
                _ => {}
            }
            self.bump();
        }
    }

    pub(super) fn parse_covergroup_declaration(&mut self) -> CovergroupDeclaration {
        let start = self.current().span.start;
        self.bump();
        let name = self.parse_identifier();
        // Optional formal argument list: `covergroup cg (ref int x, ...) ...`
        if self.at(TokenKind::LParen) {
            self.skip_balanced_parens();
        }
        // Optional coverage event: either `@(event)` / `@@(block_event)` or a
        // `with function sample(tf_port_list)` clause (SV 19.4). The sample
        // function turns the covergroup into one sampled explicitly by call.
        let event = if self.at(TokenKind::At) {
            Some(self.parse_event_control())
        } else { None };
        if self.at(TokenKind::KwWith) {
            self.bump();
            self.expect(TokenKind::KwFunction);
            let _ = self.parse_identifier(); // `sample`
            if self.at(TokenKind::LParen) {
                self.skip_balanced_parens();
            }
        }
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
                // `parse_expression` includes `iff` as a low-precedence
                // binary op (`BinaryOp::Iff`), so `v iff (guard)` parses
                // as `Binary(Iff, v, guard)` — split that back into
                // `expr = v, iff_guard = guard` here. Standalone `iff` in
                // its own token still works as a fallback.
                let mut iff_guard: Option<crate::ast::expr::Expression> = None;
                let parsed_expr = self.parse_expression();
                let expr = match parsed_expr.kind {
                    crate::ast::expr::ExprKind::Binary {
                        op: crate::ast::expr::BinaryOp::Iff,
                        left, right,
                    } => {
                        iff_guard = Some(*right);
                        *left
                    }
                    _ => parsed_expr,
                };
                if self.at(TokenKind::KwIff) {
                    self.bump();
                    if self.eat(TokenKind::LParen).is_some() {
                        iff_guard = Some(self.parse_expression());
                        let _ = self.eat(TokenKind::RParen);
                    }
                }
                let mut bins: Vec<crate::ast::decl::CoverBin> = Vec::new();
                if self.at(TokenKind::LBrace) {
                    self.bump();
                    // Parse a sequence of bin declarations until matching `}`.
                    while !self.at(TokenKind::RBrace) && !self.at(TokenKind::Eof) {
                        let bin_start = self.current().span.start;
                        // Optional `wildcard` modifier (LRM §19.5) — applies
                        // to the next `bins`/`ignore_bins`/`illegal_bins`.
                        let is_wildcard = self.eat(TokenKind::KwWildcard).is_some();
                        let kind_tok = self.current_kind();
                        let kind = match kind_tok {
                            TokenKind::KwBins => Some(crate::ast::decl::CoverBinKind::Bins),
                            TokenKind::KwIgnore_bins => Some(crate::ast::decl::CoverBinKind::Ignore),
                            TokenKind::KwIllegal_bins => Some(crate::ast::decl::CoverBinKind::Illegal),
                            // Identifier text fallback for tokenizer variants.
                            TokenKind::Identifier => match self.current().text.as_str() {
                                "bins" => Some(crate::ast::decl::CoverBinKind::Bins),
                                "ignore_bins" => Some(crate::ast::decl::CoverBinKind::Ignore),
                                "illegal_bins" => Some(crate::ast::decl::CoverBinKind::Illegal),
                                _ => None,
                            },
                            _ => None,
                        };
                        if let Some(k) = kind {
                            self.bump(); // bins / ignore_bins / illegal_bins / KwBins
                            let bin_name = if self.at(TokenKind::Identifier) {
                                self.parse_identifier()
                            } else {
                                // unnamed — skip to next `;` (depth-aware)
                                // and continue.
                                self.skip_bin_body_to_semicolon();
                                if self.at(TokenKind::Semicolon) { self.bump(); }
                                continue;
                            };
                            // Optional `[]` or `[N]` array form (LRM §19.5).
                            // Captured into `array_form` so the sampler
                            // splits hits into per-value sub-bins.
                            let mut is_array = false;
                            if self.at(TokenKind::LBracket) {
                                is_array = true;
                                self.bump();
                                while !self.at(TokenKind::RBracket) && !self.at(TokenKind::Eof) { self.bump(); }
                                if self.at(TokenKind::RBracket) { self.bump(); }
                            }
                            // `=` then bin body.
                            if self.eat(TokenKind::Assign).is_some() {
                                let mut values: Vec<crate::ast::decl::ConstraintRange> = Vec::new();
                                let mut transitions: Vec<Vec<crate::ast::decl::ConstraintRange>> = Vec::new();
                                let mut bin_kind = k;
                                if self.at(TokenKind::LBrace) {
                                    self.bump();
                                    while !self.at(TokenKind::RBrace) && !self.at(TokenKind::Eof) {
                                        values.push(self.parse_constraint_range());
                                        if self.at(TokenKind::Comma) { self.bump(); }
                                    }
                                    if self.at(TokenKind::RBrace) { self.bump(); }
                                } else if self.at(TokenKind::KwDefault) {
                                    // `bins other = default;` — LRM §19.5
                                    // catches every value not matched by any
                                    // explicit bin in the same coverpoint.
                                    self.bump();
                                    bin_kind = crate::ast::decl::CoverBinKind::Default;
                                } else if self.at(TokenKind::LParen) {
                                    // LRM §19.5 transition bins:
                                    // `bins name = (prev => cur);` or
                                    // `bins name = (a => b, c => d);`.
                                    // `=>` is also parsed as a binary op
                                    // (BinaryOp::OrFatArrow), so
                                    // `parse_expression` slurps `a => b` as
                                    // one Binary node — split it back here.
                                    // Multi-step `a => b => c` only retains
                                    // the leftmost pair for now.
                                    self.bump(); // (
                                    loop {
                                        // Collect the whole chain
                                        // `a => b => c => …` where each
                                        // step is either a single value or
                                        // a `[lo:hi]` range. We re-use
                                        // `parse_constraint_range` to
                                        // capture both forms.
                                        let mut chain: Vec<crate::ast::decl::ConstraintRange> = Vec::new();
                                        chain.push(self.parse_constraint_range());
                                        while self.eat(TokenKind::FatArrow).is_some() {
                                            chain.push(self.parse_constraint_range());
                                        }
                                        transitions.push(chain);
                                        if !self.at(TokenKind::Comma) { break; }
                                        self.bump();
                                    }
                                    if self.at(TokenKind::RParen) { self.bump(); }
                                } else {
                                    // Forms we don't handle yet — gobble to
                                    // the terminating `;` (depth-aware).
                                    self.skip_bin_body_to_semicolon();
                                }
                                bins.push(crate::ast::decl::CoverBin {
                                    name: bin_name,
                                    kind: bin_kind,
                                    values,
                                    array_form: is_array,
                                    is_wildcard,
                                    transitions,
                                    span: self.span_from(bin_start),
                                });
                            } else {
                                self.skip_bin_body_to_semicolon();
                            }
                            if self.at(TokenKind::Semicolon) { self.bump(); }
                        } else {
                            // Not a bin keyword — skip token to make progress.
                            self.bump();
                        }
                    }
                    if self.at(TokenKind::RBrace) { self.bump(); }
                } else {
                    self.expect(TokenKind::Semicolon);
                }
                CovergroupItem::Coverpoint(Coverpoint { name, expr, iff_guard, bins, span: self.span_from(start) })
            }
            TokenKind::KwCross => {
                self.bump();
                let mut ids = Vec::new();
                loop {
                    ids.push(self.parse_identifier());
                    if !self.at(TokenKind::Comma) { break; }
                    self.bump();
                }
                // LRM §19.6 `iff (guard)` — sample is skipped when guard
                // is false. (Note: unlike for coverpoint, `parse_expression`
                // doesn't slurp `iff` here because we already consumed
                // identifiers.)
                let mut iff_guard: Option<crate::ast::expr::Expression> = None;
                if self.at(TokenKind::KwIff) {
                    self.bump();
                    if self.eat(TokenKind::LParen).is_some() {
                        iff_guard = Some(self.parse_expression());
                        let _ = self.eat(TokenKind::RParen);
                    }
                }
                let mut bins: Vec<crate::ast::decl::CrossBin> = Vec::new();
                if self.at(TokenKind::LBrace) {
                    self.bump();
                    // Lightweight body parser: recognise
                    //   `bins NAME = binsof(IDENT) intersect { ranges };`
                    // Everything else is skipped depth-tracked so the
                    // outer brace match remains balanced (legacy behavior).
                    loop {
                        if self.at(TokenKind::Eof) { break; }
                        if self.at(TokenKind::RBrace) { self.bump(); break; }
                        if self.current().text == "bins" {
                            let save = self.pos;
                            self.bump();
                            let bin_name = self.parse_identifier();
                            if self.eat(TokenKind::Assign).is_some()
                                && self.current().text == "binsof"
                            {
                                self.bump();
                                let _ = self.eat(TokenKind::LParen);
                                let cp_ref = self.parse_identifier();
                                let _ = self.eat(TokenKind::RParen);
                                if self.current().text == "intersect" {
                                    self.bump();
                                    let mut ranges: Vec<crate::ast::decl::ConstraintRange> = Vec::new();
                                    if self.eat(TokenKind::LBrace).is_some() {
                                        loop {
                                            if self.at(TokenKind::RBrace) { self.bump(); break; }
                                            if self.at(TokenKind::Eof) { break; }
                                            // parse_constraint_range handles
                                            // both bare values and `[lo:hi]`
                                            // range form (mirrors bins
                                            // value-list parsing).
                                            ranges.push(self.parse_constraint_range());
                                            if self.at(TokenKind::Comma) { self.bump(); }
                                        }
                                    }
                                    let _ = self.eat(TokenKind::Semicolon);
                                    bins.push(crate::ast::decl::CrossBin {
                                        name: bin_name,
                                        cp_ref,
                                        ranges,
                                    });
                                    continue;
                                }
                            }
                            // Not the form we recognise — restore and skip.
                            self.pos = save;
                        }
                        // Skip one token (depth-aware for nested braces).
                        if self.at(TokenKind::LBrace) {
                            let mut depth = 1usize;
                            self.bump();
                            while depth > 0 && !self.at(TokenKind::Eof) {
                                if self.at(TokenKind::LBrace) { depth += 1; }
                                else if self.at(TokenKind::RBrace) { depth -= 1; }
                                self.bump();
                            }
                        } else {
                            self.bump();
                        }
                    }
                } else {
                    self.expect(TokenKind::Semicolon);
                }
                CovergroupItem::Cross(Cross { name, items: ids, iff_guard, bins, span: self.span_from(start) })
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

    /// Parse a single term of a `solve ... before ...` list. SV allows the
    /// solve/before operands to be member-select and index-select lvalues
    /// (e.g. `mseccfg.mml`, `pmp_cfg[i].w`), not just bare identifiers. We
    /// consume the whole postfix chain but only retain the root identifier,
    /// which is all the elaborator's solve-ordering checks consult.
    fn parse_solve_term(&mut self) -> Identifier {
        let root = self.parse_identifier();
        loop {
            if self.at(TokenKind::Dot) {
                self.bump();
                let _ = self.parse_identifier();
            } else if self.at(TokenKind::LBracket) {
                self.bump();
                let _ = self.parse_expression();
                self.expect(TokenKind::RBracket);
            } else {
                break;
            }
        }
        root
    }

    pub(crate) fn parse_constraint_item(&mut self) -> ConstraintItem {
        let start = self.current().span.start;
        match self.current_kind() {
            TokenKind::KwSolve => {
                self.bump();
                let mut before = Vec::new();
                loop {
                    before.push(self.parse_solve_term());
                    if !self.at(TokenKind::Comma) { break; }
                    self.bump();
                }
                self.expect(TokenKind::KwBefore);
                let mut after = Vec::new();
                loop {
                    after.push(self.parse_solve_term());
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
                // `unique { expr_list };` — LRM §18.5.5. Desugared at parse
                // time into the pairwise inequalities it denotes
                // (`e[i] != e[j]` for all i<j) so the constraint solver only
                // ever sees plain relational items.
                self.bump();
                let mut exprs: Vec<crate::ast::expr::Expression> = Vec::new();
                if self.at(TokenKind::LBrace) {
                    self.bump();
                    while !self.at(TokenKind::RBrace) && !self.at(TokenKind::Eof) {
                        exprs.push(self.parse_expression());
                        if self.at(TokenKind::Comma) { self.bump(); } else { break; }
                    }
                    self.expect(TokenKind::RBrace);
                }
                if self.at(TokenKind::Semicolon) { self.bump(); }
                let span = self.span_from(start);
                if exprs.len() == 1 {
                    // A single-expression list names a whole array (`unique
                    // {gpr}`) — its element count is only known at solve
                    // time, so keep it as a dedicated item for the solver.
                    ConstraintItem::Unique { exprs, span }
                } else {
                    let mut items = Vec::new();
                    for i in 0..exprs.len() {
                        for j in (i + 1)..exprs.len() {
                            items.push(ConstraintItem::Expr(crate::ast::expr::Expression::new(
                                crate::ast::expr::ExprKind::Binary {
                                    op: crate::ast::expr::BinaryOp::Neq,
                                    left: Box::new(exprs[i].clone()),
                                    right: Box::new(exprs[j].clone()),
                                },
                                span,
                            )));
                        }
                    }
                    ConstraintItem::Block(items)
                }
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
                    // `expr dist { value (:= | :/ ) weight, ... };` — LRM
                    // §18.5.4. Weights are captured into a parallel vector
                    // so the runtime distribution picker can honor them.
                    self.bump();
                    self.expect(TokenKind::LBrace);
                    let mut range = Vec::new();
                    let mut dist_weights: Vec<Option<crate::ast::decl::DistWeight>> = Vec::new();
                    loop {
                        range.push(self.parse_constraint_range());
                        if self.at(TokenKind::ColonAssign) {
                            self.bump();
                            let w = self.parse_expression();
                            dist_weights.push(Some(crate::ast::decl::DistWeight::Each(w)));
                        } else if self.at(TokenKind::ColonSlash) {
                            self.bump();
                            let w = self.parse_expression();
                            dist_weights.push(Some(crate::ast::decl::DistWeight::Total(w)));
                        } else {
                            dist_weights.push(None);
                        }
                        if !self.at(TokenKind::Comma) { break; }
                        self.bump();
                    }
                    self.expect(TokenKind::RBrace);
                    let span = self.span_from(start);
                    self.expect(TokenKind::Semicolon);
                    return ConstraintItem::Inside { expr, range, is_dist: true, dist_weights, span };
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
                    ConstraintItem::Inside { expr, range, is_dist: false, dist_weights: Vec::new(), span }
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
