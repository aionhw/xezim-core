use super::*;

impl<'a> Parser<'a> {
    pub(in crate::parse) fn parse_module_items(&mut self) -> Vec<ModuleItem> {
        let end_tokens = [
            TokenKind::KwEndmodule,
            TokenKind::KwEndinterface,
            TokenKind::KwEndprogram,
            TokenKind::Eof,
        ];
        let mut items = Vec::new();
        while !self.at_any(&end_tokens) {
            let before = self.pos;
            let item = self.parse_module_item();
            if self.pos == before {
                // parse_module_item returned WITHOUT consuming anything —
                // genuinely stuck; report and force progress. This fires
                // whether it was a None (as before) or a Some(..) from a
                // branch that matched a token but failed to advance (e.g. a
                // keyword misrouted to parse_identifier, which returns `<e>`
                // without bump). A None that DID advance is a deliberate
                // parse-accept/skip (specparam, interconnect, …) and is not
                // flagged, since pos moved on.
                self.error(format!("unexpected: {:?}", self.current_text()));
                self.bump();
                self.release_consumed_tokens();
                continue;
            }
            if let Some(item) = item {
                self.hide_let_names_of_item(&item);
                items.push(item);
                items.append(&mut self.pending_module_items);
            }
            self.release_consumed_tokens();
        }
        items
    }

    pub(in crate::parse) fn parse_module_item(&mut self) -> Option<ModuleItem> {
        let start = self.current_span().start;
        let mut is_extern = false;
        let mut is_virtual = false;
        let mut _is_static = false;
        loop {
            match self.current_kind() {
                TokenKind::KwExtern => {
                    self.bump();
                    is_extern = true;
                }
                TokenKind::KwVirtual
                    if self.peek_kind() == TokenKind::KwFunction
                        || self.peek_kind() == TokenKind::KwTask
                        || self.peek_kind() == TokenKind::KwClass =>
                {
                    self.bump();
                    is_virtual = true;
                }
                TokenKind::KwStatic
                    if self.peek_kind() == TokenKind::KwFunction
                        || self.peek_kind() == TokenKind::KwTask =>
                {
                    self.bump();
                    _is_static = true;
                }
                _ => break,
            }
        }

        match self.current_kind() {
            // §23.4 nested module declaration — parsed whole and hoisted to
            // the definitions map by the top-level pipeline.
            TokenKind::KwModule | TokenKind::KwMacromodule => {
                if self.generate_depth > 0 && crate::strict_checks() {
                    self.error(
                        "a module declaration is not allowed inside a generate block \
                         (IEEE 1800-2017 §23.4, §27)",
                    );
                }
                return Some(ModuleItem::NestedModule(Box::new(
                    self.parse_module_declaration(),
                )));
            }
            // `timeunit 1ns / 10ps;` / `timeprecision …;` inside a module —
            // already parsed at top-level via Description::TimeunitsDecl;
            // accept and discard inside modules too (LRM allows both).
            TokenKind::KwTimeunit | TokenKind::KwTimeprecision => {
                if self.generate_depth > 0 && crate::strict_checks() {
                    self.error(
                        "a timeunit or timeprecision declaration is not allowed inside a \
                         generate block (IEEE 1800-2017 §3.14.2.2, §27)",
                    );
                }
                Some(ModuleItem::TimeunitsDecl(
                    self.parse_timeunits_declaration(),
                ))
            }
            // A `program … endprogram` block nested inside a module (LRM §24.3).
            // A program shares the enclosing scope for cross-references (its
            // `initial`/`final` blocks drive the module's nets), so inline its
            // items as an (unnamed) generate region — they elaborate directly in
            // the module scope, which is exactly the sharing the LRM prescribes
            // for the common testbench-in-module form.
            TokenKind::KwProgram => {
                let prog = self.parse_program_declaration();
                Some(ModuleItem::GenerateRegion(GenerateRegion {
                    items: prog.items,
                    span: prog.span,
                }))
            }
            // Deprecated hierarchical parameter override `defparam path.p = e, …;`
            // (LRM §23.10.1). Parse each `<hier_path> = <expr>` pair so
            // elaboration can apply the override; on any malformed pair, fall
            // back to consuming to the semicolon so the item stream survives.
            TokenKind::KwDefparam => {
                self.bump();
                let mut assigns: Vec<(Expression, Expression)> = Vec::new();
                loop {
                    let lhs = self.parse_expression();
                    if self.eat(TokenKind::Assign).is_none() {
                        break;
                    }
                    let rhs = self.parse_expression();
                    assigns.push((lhs, rhs));
                    if self.eat(TokenKind::Comma).is_some() {
                        continue;
                    }
                    break;
                }
                // Recover to the terminating semicolon regardless.
                while !self.at(TokenKind::Semicolon) && !self.at(TokenKind::Eof) {
                    self.bump();
                }
                let _ = self.eat(TokenKind::Semicolon);
                if assigns.is_empty() {
                    None
                } else {
                    Some(ModuleItem::Defparam(assigns))
                }
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
                let dir = self
                    .parse_optional_direction()
                    .unwrap_or(PortDirection::Input);
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
                    || self.at(TokenKind::KwSigned)
                    || self.at(TokenKind::KwUnsigned)
                {
                    self.parse_data_type()
                } else if self.at(TokenKind::Identifier)
                    && (matches!(
                        self.peek_kind(),
                        TokenKind::Identifier
                            | TokenKind::EscapedIdentifier
                            | TokenKind::DoubleColon
                            | TokenKind::Hash
                    ) || (self.peek_kind() == TokenKind::LBracket
                        && self.dims_then_identifier(1)))
                {
                    self.parse_data_type()
                } else if self.at(TokenKind::LBracket) {
                    let dimensions = self.parse_packed_dimensions();
                    DataType::Implicit {
                        signing: None,
                        dimensions,
                        span: self.span_from(start),
                    }
                } else {
                    DataType::Implicit {
                        signing: None,
                        dimensions: Vec::new(),
                        span: self.span_from(start),
                    }
                };
                let wreal_span = self.span_from(start);
                let dt = match nt {
                    Some(n) => self.wreal_data_type(n, dt, wreal_span),
                    None => dt,
                };
                let decls = self.parse_var_declarator_list();
                self.expect(TokenKind::Semicolon);
                Some(ModuleItem::PortDeclaration(PortDeclaration {
                    direction: dir,
                    net_type: nt,
                    data_type: dt,
                    declarators: decls,
                    span: self.span_from(start),
                }))
            }
            TokenKind::KwWire
            | TokenKind::KwTri
            | TokenKind::KwWand
            | TokenKind::KwWor
            | TokenKind::KwSupply0
            | TokenKind::KwSupply1
            | TokenKind::KwTriand
            | TokenKind::KwTrior
            | TokenKind::KwTri0
            | TokenKind::KwTri1
            | TokenKind::KwTrireg
            | TokenKind::KwUwire
            | TokenKind::KwWreal => Some(ModuleItem::NetDeclaration(self.parse_net_declaration())),
            // §14.3: `global clocking …` — consume the `global` qualifier and
            // reuse the clocking-block parse via the KwClocking arm below.
            TokenKind::KwGlobal if self.peek_kind() == TokenKind::KwClocking => {
                self.bump();
                self.parse_module_item()
            }
            // §6.20.5 specparam — parse-accept (xezim doesn't model specify
            // timing); consume through the terminating ';'.
            TokenKind::KwSpecparam => {
                if self.generate_depth > 0 && crate::strict_checks() {
                    self.error(
                        "a specparam declaration is not allowed inside a generate block \
                         (IEEE 1800-2017 §6.20.5, §27)",
                    );
                }
                // §6.20.5: a specparam is a module-scoped elaboration-time
                // constant, and §23.3.3 makes it reachable by hierarchical
                // name. The whole declaration used to be skipped to the `;`
                // and DROPPED, so `u_child.SPEC_DELAY` resolved to nothing and
                // read x while the sibling localparam read fine. Parse it as a
                // localparam instead: it then lands in the same constant table
                // that hierarchical resolution already searches.
                //
                // Backtracks to the old whole-declaration skip for any shape
                // this parser does not model — notably `specparam PATHPULSE$ =
                // ...`, whose name is not a plain identifier — so an exotic
                // form is still tolerated rather than becoming a hard error.
                let start_pos = self.pos;
                let diag_len = self.diagnostics.len();
                self.bump(); // specparam
                let mut decl = self.parse_parameter_declaration();
                if self.at(TokenKind::Semicolon) && self.diagnostics.len() == diag_len {
                    self.bump(); // ;
                    decl.local = true;
                    decl.specparam = true;
                    Some(ModuleItem::LocalparamDeclaration(decl))
                } else {
                    self.diagnostics.truncate(diag_len);
                    self.pos = start_pos;
                    while !self.at(TokenKind::Semicolon) && !self.at(TokenKind::Eof) {
                        self.bump();
                    }
                    self.expect(TokenKind::Semicolon);
                    None
                }
            }
            // §6.6.8 interconnect net — a REAL declaration (it used to be
            // consumed to ';' and dropped, so the name looked undeclared,
            // §6.10 gave it a 1-bit implicit wire, and a nettype port
            // truncated onto it while the diagnostic blamed a missing
            // declaration). Parsed like any net; the elaborator registers it
            // and adopts the connected formal's type.
            TokenKind::KwInterconnect => {
                Some(ModuleItem::NetDeclaration(self.parse_net_declaration()))
            }
            TokenKind::KwInterface if self.peek_kind() == TokenKind::KwClass => {
                // `interface class Name; ... endclass` — treat as a class decl.
                self.bump();
                let mut class = self.parse_class_declaration();
                class.virtual_kw = is_virtual;
                class.is_interface = true;
                Some(ModuleItem::ClassDeclaration(class))
            }
            _ if self.is_data_type_keyword() => {
                Some(ModuleItem::DataDeclaration(self.parse_data_declaration()))
            }
            TokenKind::KwVar
            | TokenKind::KwConst
            | TokenKind::KwStatic
            | TokenKind::KwAutomatic => {
                Some(ModuleItem::DataDeclaration(self.parse_data_declaration()))
            }
            TokenKind::KwParameter => {
                let pd = self.parse_parameter_decl_stmt();
                Some(ModuleItem::ParameterDeclaration(pd))
            }
            TokenKind::KwLocalparam => {
                let pd = self.parse_parameter_decl_stmt();
                Some(ModuleItem::LocalparamDeclaration(pd))
            }
            TokenKind::KwTypedef => Some(ModuleItem::TypedefDeclaration(
                self.parse_typedef_declaration(),
            )),
            TokenKind::KwAlways
            | TokenKind::KwAlways_comb
            | TokenKind::KwAlways_ff
            | TokenKind::KwAlways_latch => {
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
                let mut stmt = self.parse_statement();
                if matches!(kind, AlwaysKind::Always | AlwaysKind::AlwaysFf) {
                    Self::infer_procedural_assertion_clocks(&mut stmt);
                }
                Some(ModuleItem::AlwaysConstruct(AlwaysConstruct {
                    kind,
                    stmt,
                    span: self.span_from(start),
                    gen_scope: String::new(),
                }))
            }
            TokenKind::KwInitial => {
                self.bump();
                let st = self.parse_statement();
                Some(ModuleItem::InitialConstruct(InitialConstruct {
                    stmt: st,
                    span: self.span_from(start),
                    gen_scope: String::new(),
                }))
            }
            TokenKind::KwFinal => {
                self.bump();
                let st = self.parse_statement();
                Some(ModuleItem::FinalConstruct(FinalConstruct {
                    stmt: st,
                    span: self.span_from(start),
                }))
            }
            // §10.11 `alias a = b [= c ...];` — carried whole; elaboration
            // unifies the named nets onto one signal.
            TokenKind::KwAlias => {
                self.bump();
                let mut terms: Vec<Expression> = vec![self.parse_expression()];
                while self.at(TokenKind::Assign) {
                    self.bump();
                    terms.push(self.parse_expression());
                }
                self.expect(TokenKind::Semicolon);
                Some(ModuleItem::AliasDecl(terms))
            }
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
                            parts.push(self.token_text(t).into_owned());
                        }
                    }
                    self.expect(TokenKind::RParen);
                    strength = Some(parts.join(","));
                }
                let mut delay_fall = None;
                let mut delay_off = None;
                let delay = if self.eat(TokenKind::Hash).is_some() {
                    if self.eat(TokenKind::LParen).is_some() {
                        // §10.3.3 `#(rise, fall[, turnoff])`: up to three
                        // comma-separated delays.
                        let expr = self.parse_expression();
                        if self.eat(TokenKind::Comma).is_some() {
                            delay_fall = Some(self.parse_expression());
                            if self.eat(TokenKind::Comma).is_some() {
                                delay_off = Some(self.parse_expression());
                            }
                        }
                        self.expect(TokenKind::RParen);
                        Some(expr)
                    } else {
                        Some(self.parse_expression())
                    }
                } else {
                    None
                };
                let mut asgns = Vec::new();
                loop {
                    let l = self.parse_expression();
                    self.expect(TokenKind::Assign);
                    let r = self.parse_expression();
                    asgns.push((l, r));
                    if self.eat(TokenKind::Comma).is_none() {
                        break;
                    }
                }
                self.expect(TokenKind::Semicolon);
                Some(ModuleItem::ContinuousAssign(ContinuousAssign {
                    strength,
                    delay: delay.map(Box::new),
                    delay_fall: delay_fall.map(Box::new),
                    delay_off: delay_off.map(Box::new),
                    assignments: asgns,
                    span: self.span_from(start),
                }))
            }
            TokenKind::KwGenerate => {
                if self.generate_depth > 0 && crate::strict_checks() {
                    self.error(
                        "generate regions do not nest: `generate` is not allowed inside a \
                         generate region or block (IEEE 1800-2017 §27.3)",
                    );
                }
                self.bump();
                self.generate_depth += 1;
                let items = self.parse_module_items_until(TokenKind::KwEndgenerate);
                self.generate_depth -= 1;
                self.expect(TokenKind::KwEndgenerate);
                Some(ModuleItem::GenerateRegion(GenerateRegion {
                    items,
                    span: self.span_from(start),
                }))
            }
            TokenKind::KwGenvar => {
                self.bump();
                let mut names = Vec::new();
                loop {
                    names.push(self.parse_identifier());
                    if self.eat(TokenKind::Comma).is_none() {
                        break;
                    }
                }
                self.expect(TokenKind::Semicolon);
                Some(ModuleItem::GenvarDeclaration(GenvarDeclaration {
                    names,
                    span: self.span_from(start),
                }))
            }
            TokenKind::KwFunction => {
                if is_extern {
                    Some(ModuleItem::FunctionDeclaration(
                        self.parse_function_prototype(),
                    ))
                } else {
                    Some(ModuleItem::FunctionDeclaration(
                        self.parse_function_declaration(),
                    ))
                }
            }
            TokenKind::KwTask => {
                if is_extern {
                    Some(ModuleItem::TaskDeclaration(self.parse_task_prototype()))
                } else {
                    Some(ModuleItem::TaskDeclaration(self.parse_task_declaration()))
                }
            }
            TokenKind::KwImport => {
                if self.peek_kind() == TokenKind::StringLiteral {
                    Some(ModuleItem::DPIImport(Box::new(self.parse_dpi_import())))
                } else {
                    Some(ModuleItem::ImportDeclaration(
                        self.parse_import_declaration(),
                    ))
                }
            }
            TokenKind::KwExport => {
                if self.peek_kind() == TokenKind::StringLiteral {
                    Some(ModuleItem::DPIExport(Box::new(self.parse_dpi_export())))
                } else {
                    self.bump();
                    while !self.at(TokenKind::Semicolon) && !self.at(TokenKind::Eof) {
                        self.bump();
                    }
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
                    (
                        hid.path[hid.path.len() - 2].name.name.clone(),
                        hid.path[hid.path.len() - 1].name.name.clone(),
                    )
                } else {
                    (
                        String::new(),
                        hid.path
                            .last()
                            .map(|s| s.name.name.clone())
                            .unwrap_or_default(),
                    )
                };
                let mut items = Vec::new();
                if self.at(TokenKind::LBrace) {
                    self.bump();
                    while !self.at(TokenKind::RBrace) && !self.at(TokenKind::Eof) {
                        items.push(self.parse_constraint_item(ConstraintPos::BlockItem));
                    }
                    self.expect(TokenKind::RBrace);
                } else if self.at(TokenKind::Semicolon) {
                    self.bump();
                }
                Some(ModuleItem::OutOfClassConstraint {
                    class_name,
                    constraint_name,
                    items,
                })
            }
            TokenKind::KwVirtual => {
                if self.peek_kind() == TokenKind::KwInterface
                    || self.peek_kind() == TokenKind::Identifier
                {
                    // §25.9: a MODULE-scope virtual-interface variable —
                    // `virtual req_if #(4).driver rd;` or the `interface`
                    // spelling `virtual interface vif;`. Bumping past `virtual`
                    // and re-parsing (the old behavior) made `req_if #(4)`
                    // look like a parameterized INSTANTIATION, which then
                    // choked on `.driver` (and `virtual interface` looped
                    // forever: every token stays a keyword, nothing advances).
                    // parse_data_declaration starts at the `virtual` keyword
                    // and handles `#(...)` and `.modport` (and the optional
                    // `interface` keyword) through parse_data_type.
                    Some(ModuleItem::DataDeclaration(self.parse_data_declaration()))
                } else {
                    self.bump();
                    self.parse_module_item()
                }
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
                let start = self.current_span().start;
                self.bump();
                let mut items = Vec::new();
                loop {
                    let istart = self.current_span().start;
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
                    let mut tf_ports = false;
                    loop {
                        if self.at(TokenKind::RParen) || self.at(TokenKind::Eof) {
                            break;
                        }
                        let pstart = self.current_span().start;
                        // IEEE 1800-2023 §25.5: `modport <name> ( clocking <cb> )`
                        // — a modport_clocking_declaration. We record it as a
                        // synthetic Input port whose name is the clocking
                        // block; downstream consumers that don't understand
                        // clocking still see *something* there.
                        if self.eat(TokenKind::KwClocking).is_some() {
                            tf_ports = false;
                            let cb_name = self.parse_identifier();
                            ports.push(ModportPort {
                                direction: PortDirection::Input,
                                name: cb_name,
                                span: self.span_from(pstart),
                                expr: None,
                            });
                        } else if self.at(TokenKind::KwImport)
                            || self.at(TokenKind::KwExport)
                            || (tf_ports
                                && matches!(
                                    self.current_kind(),
                                    TokenKind::KwTask | TokenKind::KwFunction
                                ))
                        {
                            // IEEE 1800-2023 §25.3 Syntax 25-1, §25.7: each
                            // import/export member is a name or method prototype.
                            // Keep the callable name in the existing synthetic
                            // Input port; the interface owns its declaration.
                            if self.at(TokenKind::KwImport) || self.at(TokenKind::KwExport) {
                                self.bump();
                            }
                            tf_ports = true;
                            let prototype = matches!(
                                self.current_kind(),
                                TokenKind::KwTask | TokenKind::KwFunction
                            );
                            if prototype {
                                let function = self.bump().kind == TokenKind::KwFunction;
                                // Annex A footnote 25 excludes method specifiers here.
                                if self.parse_optional_method_specifier().is_some() {
                                    self.error(
                                        "method specifier is not allowed in a modport prototype",
                                    );
                                }
                                self.parse_optional_lifetime();
                                if function {
                                    self.parse_data_type();
                                }
                            }
                            let callable = if prototype
                                || matches!(
                                    self.current_kind(),
                                    TokenKind::Identifier | TokenKind::EscapedIdentifier
                                ) {
                                Some(self.parse_identifier())
                            } else {
                                None
                            };
                            if prototype {
                                // §25.7: parse exactly one optional tf_port_list.
                                // Reuse the port reader, including unnamed formals;
                                // it stops at a missing ')' rather than scanning to EOF.
                                let saved = std::mem::replace(&mut self.prototype_ports, true);
                                let args = self.parse_function_ports();
                                self.prototype_ports = saved;
                                for arg in args {
                                    if arg.default.is_some() {
                                        // §25.7 / §13.5.3: prototype defaults require
                                        // call metadata we do not retain. Keep an error.
                                        self.diagnostics.push(crate::diagnostics::Diagnostic::error(
                                            format!(
                                                "default argument '{}' in modport '{}' subroutine '{}' prototype is not supported",
                                                arg.name.name, name.name, callable.as_ref().unwrap().name
                                            ),
                                            arg.span,
                                        ));
                                    }
                                }
                                if !matches!(
                                    self.current_kind(),
                                    TokenKind::Comma | TokenKind::RParen
                                ) {
                                    self.error("expected ',' or ')' after modport prototype");
                                }
                            } else {
                                // Preserve the existing name-only import/export path.
                                while !matches!(
                                    self.current_kind(),
                                    TokenKind::Comma
                                        | TokenKind::RParen
                                        | TokenKind::Semicolon
                                        | TokenKind::KwEndinterface
                                        | TokenKind::Eof
                                ) {
                                    self.bump();
                                }
                            }
                            if let Some(callable) = callable {
                                ports.push(ModportPort {
                                    direction: PortDirection::Input,
                                    name: callable,
                                    span: self.span_from(pstart),
                                    expr: None,
                                });
                            }
                        } else {
                            if let Some(d) = self.parse_optional_direction() {
                                last_dir = d;
                                tf_ports = false;
                            }
                            // §25.5.4 modport expression: `.b(word[7:0])` —
                            // the member `b` stands for an expression over
                            // the interface's signals.
                            if self.eat(TokenKind::Dot).is_some() {
                                let port_name = self.parse_identifier();
                                self.expect(TokenKind::LParen);
                                let e = self.parse_expression();
                                self.expect(TokenKind::RParen);
                                ports.push(ModportPort {
                                    direction: last_dir,
                                    name: port_name,
                                    span: self.span_from(pstart),
                                    expr: Some(e),
                                });
                            } else {
                                let port_name = self.parse_identifier();
                                ports.push(ModportPort {
                                    direction: last_dir,
                                    name: port_name,
                                    span: self.span_from(pstart),
                                    expr: None,
                                });
                            }
                        }
                        if self.eat(TokenKind::Comma).is_none() {
                            break;
                        }
                    }
                    self.expect(TokenKind::RParen);
                    items.push(ModportItem {
                        name,
                        ports,
                        span: self.span_from(istart),
                    });
                    if self.eat(TokenKind::Comma).is_none() {
                        break;
                    }
                }
                self.expect(TokenKind::Semicolon);
                Some(ModuleItem::ModportDeclaration(ModportDeclaration {
                    items,
                    span: self.span_from(start),
                }))
            }
            // IEEE 1800-2023 §14.3 — clocking block. We now capture the
            // direction-tagged signals into a real ClockingDeclaration so
            // the elaborator can register `clocking_blocks[<name>]` and the
            // identifier validator accepts `<cb>.<sig>` references. Body
            // statements beyond `<dir> [type] <name> (, <name>)*` are
            // skipped (default skew, etc. — rich grammar not modelled).
            TokenKind::KwClocking => {
                let start = self.current_span().start;
                self.bump();
                let cb_name =
                    if self.at(TokenKind::Identifier) || self.at(TokenKind::EscapedIdentifier) {
                        Some(self.parse_identifier())
                    } else {
                        None
                    };
                // LRM §14.3 clock event: `@(posedge <sig>)` — capture
                // the signal identifier so the simulator can snapshot
                // its inputs before each clock edge. Falls back to the
                // legacy skip path for forms we don't recognise.
                let mut clock_signal_id: Option<crate::ast::Identifier> = None;
                let mut clock_edge: Option<crate::ast::stmt::Edge> = None;
                if self.at(TokenKind::At) {
                    self.bump();
                    if self.at(TokenKind::LParen) {
                        self.bump();
                        if self.eat(TokenKind::KwPosedge).is_some() {
                            clock_edge = Some(crate::ast::stmt::Edge::Posedge);
                        } else if self.eat(TokenKind::KwNegedge).is_some() {
                            clock_edge = Some(crate::ast::stmt::Edge::Negedge);
                        } else if self.eat(TokenKind::KwEdge).is_some() {
                            clock_edge = Some(crate::ast::stmt::Edge::Edge);
                        }
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
                let mut default_input_skew: Option<crate::ast::expr::Expression> = None;
                let mut default_output_skew: Option<crate::ast::expr::Expression> = None;
                let mut default_output_edge: Option<crate::ast::stmt::Edge> = None;
                while !self.at(TokenKind::KwEndclocking) && !self.at(TokenKind::Eof) {
                    // `default input #d output #d;` (§14.4) — capture the skew
                    // expressions; anything unrecognized is skipped to the `;`
                    // so the signal-list pass below stays in sync.
                    if self.at(TokenKind::KwDefault) {
                        self.bump();
                        loop {
                            let dir_in = self.at(TokenKind::KwInput);
                            let dir_out = self.at(TokenKind::KwOutput);
                            if !dir_in && !dir_out {
                                break;
                            }
                            self.bump();
                            // `clocking_skew ::= edge_identifier [delay_control]`
                            let edge = self.parse_clocking_skew_edge();
                            if dir_out {
                                default_output_edge = edge;
                            }
                            if self.at(TokenKind::Hash) {
                                self.bump();
                                let skew = self.parse_clocking_skew_value();
                                if dir_in {
                                    default_input_skew = skew;
                                } else {
                                    default_output_skew = skew;
                                }
                            }
                        }
                        while !self.at(TokenKind::Semicolon) && !self.at(TokenKind::Eof) {
                            self.bump();
                        }
                        if self.at(TokenKind::Semicolon) {
                            self.bump();
                        }
                        continue;
                    }
                    match self.current_kind() {
                        TokenKind::KwInput
                        | TokenKind::KwOutput
                        | TokenKind::KwInout
                        | TokenKind::KwRef => {
                            let sstart = self.current_span().start;
                            let direction = self
                                .parse_optional_direction()
                                .unwrap_or(PortDirection::Input);
                            // Optional `#delay` skew specifier (§14.4) —
                            // captured per-signal; `#1step`/opaque forms → None.
                            let mut sig_skew: Option<crate::ast::expr::Expression> = None;
                            // `clocking_skew ::= edge_identifier [delay_control]`
                            let sig_edge = self.parse_clocking_skew_edge();
                            if self.at(TokenKind::Hash) {
                                self.bump();
                                sig_skew = self.parse_clocking_skew_value();
                            }
                            if self.is_data_type_keyword()
                                || (self.at(TokenKind::Identifier)
                                    && self.peek_kind() == TokenKind::Identifier)
                            {
                                let _ = self.parse_data_type();
                            }
                            loop {
                                if self.at(TokenKind::Identifier) {
                                    let id = self.parse_identifier();
                                    // §14.3 signal renaming: `input alias = expr;`
                                    let bound_to = if self.eat(TokenKind::Assign).is_some() {
                                        Some(self.parse_expression())
                                    } else {
                                        None
                                    };
                                    signals.push(ClockingSignal {
                                        direction,
                                        name: id,
                                        skew: sig_skew.clone(),
                                        skew_edge: sig_edge,
                                        bound_to,
                                        bound: Default::default(),
                                        span: self.span_from(sstart),
                                    });
                                }
                                if self.eat(TokenKind::Comma).is_none() {
                                    break;
                                }
                            }
                            // Skip anything we don't understand up to `;`.
                            while !self.at(TokenKind::Semicolon) && !self.at(TokenKind::Eof) {
                                self.bump();
                            }
                            if self.at(TokenKind::Semicolon) {
                                self.bump();
                            }
                        }
                        _ => {
                            self.bump();
                        }
                    }
                }
                self.expect(TokenKind::KwEndclocking);
                let endlabel = if self.eat(TokenKind::Colon).is_some() {
                    Some(self.parse_identifier())
                } else {
                    None
                };
                let id = cb_name.unwrap_or_else(|| Identifier {
                    name: "default".to_string(),
                    span: self.span_from(start),
                });
                Some(ModuleItem::ClockingDeclaration(ClockingDeclaration {
                    name: id,
                    clock_signal: clock_signal_id,
                    clock_bound: Default::default(),
                    decl: Default::default(),
                    clock_edge,
                    default_input_skew: default_input_skew.map(Box::new),
                    default_output_skew: default_output_skew.map(Box::new),
                    default_output_edge,
                    is_default: false,
                    signals,
                    items,
                    endlabel,
                    span: self.span_from(start),
                }))
            }
            // §16.14.4: read and set aside, as a simulator checks no
            // restriction; it was a parse error that lost the rest of the
            // module (#614).
            TokenKind::KwRestrict if self.peek_kind() == TokenKind::KwProperty => {
                self.skip_restrict_property();
                Some(ModuleItem::Null)
            }
            TokenKind::KwAssert | TokenKind::KwAssume | TokenKind::KwCover => {
                Some(ModuleItem::AssertionItem(self.parse_assertion_statement()))
            }
            TokenKind::KwProperty => {
                let start = self.current_span().start;
                self.bump();
                let name = self.parse_identifier();
                let (ports, local_ports, port_defaults) = if self.at(TokenKind::LParen) {
                    self.parse_sva_port_names()
                } else {
                    (Vec::new(), Vec::new(), Vec::new())
                };
                self.expect(TokenKind::Semicolon);
                // §16.10: assertion-local variable declarations.
                let mut decls = self.parse_sva_local_declarations();
                // LRM §16.6 — capture the property body when it matches
                // the common `[@(<event>)] [disable iff (<expr>)] <expr>;`
                // shape. Re-uses the assertion parser's clock-event capture
                // (an `SvaClocked { events, body }` wrapper). Properties not
                // matching this shape fall back to the legacy token-skip
                // path so the parser stays resilient.
                let bstart = self.current_span().start;
                let save_pos = self.pos;
                let save_diag = self.diagnostics.len();
                let clocked = self.at(TokenKind::At);
                let clock = if clocked {
                    self.bump(); // @
                    Some(self.parse_sva_clock_event())
                } else {
                    None
                };
                // §16.12: optional `disable iff (<expr>)` after the clocking
                // event, before the property expression; kept as
                // `Binary{SvaDisableIff, guard, body}`.
                let disable_guard =
                    if self.at(TokenKind::KwDisable) && self.peek_kind() == TokenKind::KwIff {
                        self.bump(); // disable
                        self.bump(); // iff
                        let _ = self.eat(TokenKind::LParen);
                        let g = self.parse_expression();
                        let _ = self.eat(TokenKind::RParen);
                        Some(g)
                    } else {
                        None
                    };
                let body_expr = if clocked || !self.at(TokenKind::KwEndproperty) {
                    self.in_sva_seq = true;
                    let mut body = self.parse_expression();
                    self.in_sva_seq = false;
                    // An unclocked body is taken only when it parses cleanly
                    // (a default clocking or an inferred clock supplies the
                    // clock); otherwise the token-skip path below runs.
                    if !clocked
                        && !(self.diagnostics.len() == save_diag && self.at(TokenKind::Semicolon))
                    {
                        self.diagnostics.truncate(save_diag);
                        self.pos = save_pos;
                        None
                    } else {
                        let _ = self.eat(TokenKind::Semicolon);
                        Self::sva_bind_local_formals(&local_ports, &mut decls, &mut body);
                        let assignable = Self::sva_assignable_names(&decls, &ports);
                        self.check_sva_match_assignments(&body, &assignable);
                        let body = Self::sva_wrap_locals(std::mem::take(&mut decls), body);
                        let body = if let Some(g) = disable_guard {
                            let span = body.span;
                            Expression::new(
                                ExprKind::Binary {
                                    op: BinaryOp::SvaDisableIff,
                                    left: Box::new(g),
                                    right: Box::new(body),
                                },
                                span,
                            )
                        } else {
                            body
                        };
                        Some(match clock {
                            Some(events) => Expression::new(
                                ExprKind::SvaClocked {
                                    events,
                                    body: Box::new(body),
                                },
                                self.span_from(bstart),
                            ),
                            None => body,
                        })
                    }
                } else {
                    None
                };
                while !self.at(TokenKind::KwEndproperty) && !self.at(TokenKind::Eof) {
                    self.bump();
                }
                self.expect(TokenKind::KwEndproperty);
                let endlabel = self.parse_end_label();
                let items = Vec::new();
                Some(ModuleItem::PropertyDeclaration(PropertyDeclaration {
                    name,
                    ports,
                    port_defaults,
                    items,
                    body: body_expr,
                    endlabel,
                    span: self.span_from(start),
                    decl: Default::default(),
                }))
            }
            TokenKind::KwSequence => {
                let start = self.current_span().start;
                self.bump();
                let name = self.parse_identifier();
                let (ports, local_ports, port_defaults) = if self.at(TokenKind::LParen) {
                    self.parse_sva_port_names()
                } else {
                    (Vec::new(), Vec::new(), Vec::new())
                };
                self.expect(TokenKind::Semicolon);
                // §16.10: assertion-local variable declarations.
                let mut decls = self.parse_sva_local_declarations();
                // LRM §16.5 — capture the sequence body when it matches
                // the common `@(<event>) <expr>;` shape, mirroring the
                // property-decl path. Other shapes (raw `##N` chains)
                // fall back to the token-skip path.
                let body_expr = if self.at(TokenKind::At) {
                    let bstart = self.current_span().start;
                    self.bump();
                    let events = self.parse_sva_clock_event();
                    self.in_sva_seq = true;
                    let mut body = self.parse_expression();
                    self.in_sva_seq = false;
                    let _ = self.eat(TokenKind::Semicolon);
                    Self::sva_bind_local_formals(&local_ports, &mut decls, &mut body);
                    let assignable = Self::sva_assignable_names(&decls, &ports);
                    self.check_sva_match_assignments(&body, &assignable);
                    let body = Self::sva_wrap_locals(std::mem::take(&mut decls), body);
                    Some(Expression::new(
                        ExprKind::SvaClocked {
                            events,
                            body: Box::new(body),
                        },
                        self.span_from(bstart),
                    ))
                } else if !self.at(TokenKind::KwEndsequence) {
                    // Unclocked body (`sequence s; a ##1 b; endsequence`):
                    // parse it speculatively so a named sequence used INSIDE
                    // a property (`a |=> s`) has a body to expand. Any shape
                    // the expression parser does not cover backtracks to the
                    // token-skip path below, exactly as before.
                    let save_pos = self.pos;
                    let save_diag = self.diagnostics.len();
                    self.in_sva_seq = true;
                    let mut body = self.parse_expression();
                    self.in_sva_seq = false;
                    if self.diagnostics.len() == save_diag && self.at(TokenKind::Semicolon) {
                        self.bump();
                        Self::sva_bind_local_formals(&local_ports, &mut decls, &mut body);
                        let assignable = Self::sva_assignable_names(&decls, &ports);
                        self.check_sva_match_assignments(&body, &assignable);
                        Some(Self::sva_wrap_locals(std::mem::take(&mut decls), body))
                    } else {
                        self.diagnostics.truncate(save_diag);
                        self.pos = save_pos;
                        None
                    }
                } else {
                    None
                };
                while !self.at(TokenKind::KwEndsequence) && !self.at(TokenKind::Eof) {
                    self.bump();
                }
                self.expect(TokenKind::KwEndsequence);
                let endlabel = self.parse_end_label();
                let items = Vec::new();
                Some(ModuleItem::SequenceDeclaration(SequenceDeclaration {
                    name,
                    ports,
                    port_defaults,
                    items,
                    body: body_expr,
                    endlabel,
                    span: self.span_from(start),
                    decl: Default::default(),
                }))
            }
            TokenKind::KwCovergroup => Some(ModuleItem::CovergroupDeclaration(
                self.parse_covergroup_declaration(),
            )),
            TokenKind::KwDefault => {
                self.bump();
                if self.at(TokenKind::KwClocking) {
                    // §14.12 STANDALONE designation `default clocking <name>;`
                    // — names an ALREADY-declared block rather than declaring
                    // one. Detect by the `;` right after the identifier (a
                    // declaration always has `@(...)` or at least a body) and
                    // emit a marker: an empty, clock-less ClockingDeclaration
                    // with is_default set, which the elaborator folds into the
                    // existing same-named block. Without this the parser
                    // recursed into the block form and ran to EOF looking for
                    // `endclocking`.
                    if matches!(self.peek_kind(), TokenKind::Identifier)
                        && self.peek_kind_n(2) == TokenKind::Semicolon
                    {
                        self.bump(); // clocking
                        let name = self.parse_identifier();
                        self.expect(TokenKind::Semicolon);
                        return Some(ModuleItem::ClockingDeclaration(ClockingDeclaration {
                            name,
                            clock_signal: None,
                            clock_bound: Default::default(),
                            decl: Default::default(),
                            clock_edge: None,
                            default_input_skew: None,
                            default_output_skew: None,
                            default_output_edge: None,
                            is_default: true,
                            signals: Vec::new(),
                            items: Vec::new(),
                            endlabel: None,
                            span: self.span_from(start),
                        }));
                    }
                    // §14.11: mark the block so procedural `##N` knows which
                    // clocking block to synchronize to.
                    let mut item = self.parse_module_item(); // recurse to handle clocking
                    if let Some(ModuleItem::ClockingDeclaration(cd)) = item.as_mut() {
                        cd.is_default = true;
                    }
                    item
                } else if self.at(TokenKind::KwDisable) {
                    // §16.15 `default disable iff <expr>;`: the default
                    // disable condition of every concurrent assertion in this
                    // module, interface or generate scope that has no
                    // `disable iff` of its own. Kept as a marker assertion
                    // item, `$sva_default_disable(<expr>)`, which reaches the
                    // simulator in the same scope as the scope's assertions.
                    self.bump(); // disable
                    let _ = self.eat(TokenKind::KwIff);
                    let guard = self.parse_expression();
                    self.expect(TokenKind::Semicolon);
                    let span = self.span_from(start);
                    Some(ModuleItem::AssertionItem(
                        crate::ast::stmt::AssertionStatement {
                            kind: crate::ast::stmt::AssertionKind::Assert,
                            expr: Expression::new(
                                ExprKind::SystemCall {
                                    name: "$sva_default_disable".to_string(),
                                    args: vec![guard],
                                },
                                span,
                            ),
                            action: None,
                            else_action: None,
                            is_property: true,
                            is_sequence: false,
                            deferred: None,
                            label: None,
                            procedural: false,
                            inferred_clock: None,
                            span,
                        },
                    ))
                } else {
                    None
                }
            }
            TokenKind::KwIf => {
                let s = self.current_span().start;
                Some(self.parse_generate_if(s))
            }
            TokenKind::KwCase => {
                let s = self.current_span().start;
                Some(self.parse_generate_case(s))
            }
            TokenKind::KwChecker => {
                let start = self.current_span().start;
                self.bump();
                let name = self.parse_identifier();
                let ports = self.parse_port_list();
                self.expect(TokenKind::Semicolon);
                self.push_let_scope();
                let items = self.parse_module_items_until(TokenKind::KwEndchecker);
                self.pop_let_scope();
                self.expect(TokenKind::KwEndchecker);
                let endlabel = self.parse_end_label();
                Some(ModuleItem::CheckerDeclaration(CheckerDeclaration {
                    name,
                    ports,
                    items,
                    endlabel,
                    span: self.span_from(start),
                }))
            }
            TokenKind::KwLet => Some(ModuleItem::LetDeclaration(self.parse_let_declaration())),
            TokenKind::KwNettype => {
                let start = self.current_span().start;
                self.bump();
                let data_type = self.parse_data_type();
                let name = self.parse_identifier();
                let resolver = if self.eat(TokenKind::KwWith).is_some() {
                    Some(self.parse_identifier())
                } else {
                    None
                };
                self.expect(TokenKind::Semicolon);
                Some(ModuleItem::NettypeDeclaration(NettypeDeclaration {
                    data_type,
                    name,
                    resolver,
                    span: self.span_from(start),
                }))
            }
            TokenKind::KwFor => {
                let s = self.current_span().start;
                self.bump();
                self.expect(TokenKind::LParen);
                // Parse init: genvar i = 0 or i = 0
                let has_genvar = self.eat(TokenKind::KwGenvar).is_some();
                let var_name = if self.at(TokenKind::Identifier) {
                    let n = self.current_text().into_owned();
                    if !has_genvar {
                        let span = self.current_span();
                        self.plain_loop_vars.push(Identifier {
                            name: n.clone(),
                            span,
                        });
                    }
                    self.bump();
                    n
                } else {
                    String::new()
                };
                self.expect(TokenKind::Assign);
                let init_expr = self.parse_expression();
                let init_val = match &init_expr.kind {
                    ExprKind::Number(NumberLiteral::Integer { value, base, .. }) => {
                        let r = match base {
                            NumberBase::Binary => 2,
                            NumberBase::Octal => 8,
                            NumberBase::Hex => 16,
                            NumberBase::Decimal => 10,
                        };
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
                    if self.at(TokenKind::Assign)
                        || self.at_any(&[
                            TokenKind::PlusAssign,
                            TokenKind::MinusAssign,
                            TokenKind::StarAssign,
                            TokenKind::SlashAssign,
                            TokenKind::PercentAssign,
                            TokenKind::AndAssign,
                            TokenKind::OrAssign,
                            TokenKind::XorAssign,
                            TokenKind::ShiftLeftAssign,
                            TokenKind::ShiftRightAssign,
                            TokenKind::ArithShiftLeftAssign,
                            TokenKind::ArithShiftRightAssign,
                        ])
                    {
                        let op_kind = self.current_kind().clone();
                        self.bump();
                        let rhs = self.parse_expression();
                        let span = self.span_from(s);
                        let rvalue = match op_kind {
                            TokenKind::PlusAssign => Expression::new(
                                ExprKind::Binary {
                                    op: BinaryOp::Add,
                                    left: Box::new(expr.clone()),
                                    right: Box::new(rhs),
                                },
                                span,
                            ),
                            TokenKind::MinusAssign => Expression::new(
                                ExprKind::Binary {
                                    op: BinaryOp::Sub,
                                    left: Box::new(expr.clone()),
                                    right: Box::new(rhs),
                                },
                                span,
                            ),
                            TokenKind::StarAssign => Expression::new(
                                ExprKind::Binary {
                                    op: BinaryOp::Mul,
                                    left: Box::new(expr.clone()),
                                    right: Box::new(rhs),
                                },
                                span,
                            ),
                            TokenKind::SlashAssign => Expression::new(
                                ExprKind::Binary {
                                    op: BinaryOp::Div,
                                    left: Box::new(expr.clone()),
                                    right: Box::new(rhs),
                                },
                                span,
                            ),
                            TokenKind::PercentAssign => Expression::new(
                                ExprKind::Binary {
                                    op: BinaryOp::Mod,
                                    left: Box::new(expr.clone()),
                                    right: Box::new(rhs),
                                },
                                span,
                            ),
                            TokenKind::AndAssign => Expression::new(
                                ExprKind::Binary {
                                    op: BinaryOp::BitAnd,
                                    left: Box::new(expr.clone()),
                                    right: Box::new(rhs),
                                },
                                span,
                            ),
                            TokenKind::OrAssign => Expression::new(
                                ExprKind::Binary {
                                    op: BinaryOp::BitOr,
                                    left: Box::new(expr.clone()),
                                    right: Box::new(rhs),
                                },
                                span,
                            ),
                            TokenKind::XorAssign => Expression::new(
                                ExprKind::Binary {
                                    op: BinaryOp::BitXor,
                                    left: Box::new(expr.clone()),
                                    right: Box::new(rhs),
                                },
                                span,
                            ),
                            TokenKind::ShiftLeftAssign => Expression::new(
                                ExprKind::Binary {
                                    op: BinaryOp::ShiftLeft,
                                    left: Box::new(expr.clone()),
                                    right: Box::new(rhs),
                                },
                                span,
                            ),
                            TokenKind::ShiftRightAssign => Expression::new(
                                ExprKind::Binary {
                                    op: BinaryOp::ShiftRight,
                                    left: Box::new(expr.clone()),
                                    right: Box::new(rhs),
                                },
                                span,
                            ),
                            TokenKind::ArithShiftLeftAssign => Expression::new(
                                ExprKind::Binary {
                                    op: BinaryOp::ArithShiftLeft,
                                    left: Box::new(expr.clone()),
                                    right: Box::new(rhs),
                                },
                                span,
                            ),
                            TokenKind::ArithShiftRightAssign => Expression::new(
                                ExprKind::Binary {
                                    op: BinaryOp::ArithShiftRight,
                                    left: Box::new(expr.clone()),
                                    right: Box::new(rhs),
                                },
                                span,
                            ),
                            _ => Expression::new(
                                ExprKind::AssignExpr {
                                    lvalue: Box::new(expr.clone()),
                                    rvalue: Box::new(rhs),
                                },
                                span,
                            ),
                        };
                        match op_kind {
                            TokenKind::Assign => rvalue,
                            _ => Expression::new(
                                ExprKind::AssignExpr {
                                    lvalue: Box::new(expr),
                                    rvalue: Box::new(rvalue),
                                },
                                span,
                            ),
                        }
                    } else {
                        expr
                    }
                };
                self.expect(TokenKind::RParen);
                let (items, name, _) = self.parse_generate_branch_items_named();
                Some(ModuleItem::GenerateFor(Box::new(GenerateFor {
                    var: var_name,
                    init_val,
                    init: Some(init_expr),
                    cond,
                    incr,
                    items,
                    name,
                    name_decl: Default::default(),
                    implicit_name: String::new(),
                    span: self.span_from(s),
                })))
            }
            TokenKind::KwAnd
            | TokenKind::KwNand
            | TokenKind::KwOr
            | TokenKind::KwNor
            | TokenKind::KwXor
            | TokenKind::KwXnor
            | TokenKind::KwBuf
            | TokenKind::KwNot
            | TokenKind::KwBufif0
            | TokenKind::KwBufif1
            | TokenKind::KwNotif0
            | TokenKind::KwNotif1
            | TokenKind::KwNmos
            | TokenKind::KwPmos
            | TokenKind::KwCmos
            | TokenKind::KwRnmos
            | TokenKind::KwRpmos
            | TokenKind::KwRcmos
            | TokenKind::KwTran
            | TokenKind::KwRtran
            | TokenKind::KwTranif0
            | TokenKind::KwTranif1
            | TokenKind::KwRtranif0
            | TokenKind::KwRtranif1
            | TokenKind::KwPullup
            | TokenKind::KwPulldown => Some(ModuleItem::GateInstantiation(
                self.parse_gate_instantiation(),
            )),
            TokenKind::KwSpecify => {
                if self.generate_depth > 0 && crate::strict_checks() {
                    self.error(
                        "a specify block is not allowed inside a generate block \
                         (IEEE 1800-2017 §30, §27)",
                    );
                }
                // §30 specify block: module paths (every §30.4 form) into
                // SpecifyPaths so the elaborator can model their delays, plus
                // the §31 timing checks and `specparam`s. Anything else
                // (`pulsestyle_*`, `showcancelled`, ...) is skipped to the
                // next `;`.
                self.bump();
                let mut paths = Vec::new();
                let mut delayed_nets: Vec<(String, String)> = Vec::new();
                let mut timing_checks = Vec::new();
                while !self.at(TokenKind::KwEndspecify) && !self.at(TokenKind::Eof) {
                    if matches!(
                        self.current_kind(),
                        TokenKind::LParen | TokenKind::KwIf | TokenKind::KwIfnone
                    ) {
                        if let Some(p) = self.try_parse_specify_path() {
                            paths.push(p);
                            continue;
                        }
                    }
                    if self.at(TokenKind::SystemIdentifier)
                        && Self::is_timing_check_task(&self.current_text())
                    {
                        let check_pos = self.pos;
                        let check = self.parse_timing_check();
                        // §15.6 negative-timing-check tasks carry `delayed_reference`
                        // / `delayed_data` OUTPUT nets that the cell's functional
                        // path uses — extract those so the elaborator can drive them.
                        if Self::is_timing_check_name(&self.tokens.text_at(check_pos)) {
                            let end_pos = self.pos;
                            self.pos = check_pos;
                            self.parse_timing_check_delayed_nets(&mut delayed_nets);
                            self.pos = end_pos;
                        }
                        timing_checks.extend(check);
                        continue;
                    }
                    // §31.2 a specparam declared in the specify block is a
                    // module-scoped constant, like one at module level: emit
                    // it through the module-level specparam handling.
                    if self.at(TokenKind::KwSpecparam) {
                        let item = self.parse_module_item();
                        self.pending_module_items.extend(item);
                        continue;
                    }
                    // Unrecognized specify item: skip to (and past) the next ';'.
                    self.skip_to_semi();
                }
                self.expect(TokenKind::KwEndspecify);
                // A delayed net is typically named as the delayed_data/ref of
                // MANY checks on the same source — dedup so it gets exactly one
                // zero-delay driver (redundant identical drivers churn settle).
                delayed_nets.sort();
                delayed_nets.dedup();
                Some(ModuleItem::SpecifyBlock(SpecifyBlock {
                    paths,
                    delayed_nets,
                    timing_checks,
                    span: self.span_from(start),
                }))
            }
            TokenKind::Identifier | TokenKind::EscapedIdentifier => {
                Some(self.parse_identifier_starting_item())
            }
            TokenKind::Semicolon => {
                self.bump();
                Some(ModuleItem::Null)
            }
            TokenKind::Directive => {
                if self.recover_undefined_macro() {
                    return Some(ModuleItem::Null);
                }
                self.bump();
                self.parse_module_item()
            }
            TokenKind::KwBegin => {
                let s = self.current_span().start;
                let items = self.parse_generate_branch_items();
                Some(ModuleItem::GenerateRegion(GenerateRegion {
                    items,
                    span: self.span_from(s),
                }))
            }
            _ => None,
        }
    }
}
