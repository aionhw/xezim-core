use super::*;

impl<'a> Parser<'a> {
    /// Convert a `#(...)` parameter VALUE into a TYPE-ARG expression when it
    /// is used as the specialization of a parameterized CLASS in a data-
    /// declaration type (`param_obj #(int) x;`). `parse_param_value` returns
    /// `ParamValue::Type(dt)` for a type keyword (`int`, `bit`) or a
    /// typedef/class name; data declarations need those as identifier
    /// expressions so the specialize's `type_args` list is non-empty and
    /// downstream per-spec binding (type_bindings / current_spec / the
    /// class registry's `type_name`) can reconstruct `param_obj#(int)`. A
    /// position that drops them leaves the type_args empty and the variable
    /// default-specializes (`param_obj#(bit)`), which is what broke UVM's
    /// `type_id::type_name()` for parameterized-class fields/collections.
    /// One `#(...)` connection of a class-typed data declaration as a type
    /// arg. A named connection (`#(.W(5))`, §8.25) keeps its name as a
    /// `NamedArg`: dropping it bound the value to the class's FIRST
    /// parameter, whatever the name said.
    fn param_connection_to_type_arg(
        &self,
        pc: &ParamConnection,
    ) -> Option<crate::ast::expr::Expression> {
        match pc {
            ParamConnection::Ordered(Some(pv)) => self.param_value_to_type_arg(pv),
            ParamConnection::Named {
                name,
                value: Some(pv),
            } => {
                let v = self.param_value_to_type_arg(pv)?;
                let span = v.span;
                Some(crate::ast::expr::Expression::new(
                    crate::ast::expr::ExprKind::NamedArg {
                        name: name.clone(),
                        expr: Some(Box::new(v)),
                    },
                    span,
                ))
            }
            _ => None,
        }
    }

    fn param_value_to_type_arg(&self, pv: &ParamValue) -> Option<crate::ast::expr::Expression> {
        use crate::ast::Identifier as PIdent;
        use crate::ast::expr::{ExprKind, Expression, HierPathSegment, HierarchicalIdentifier};
        use crate::ast::types::DataType;
        let (leaf, span) = match pv {
            ParamValue::Expr(e) => return Some(e.clone()),
            ParamValue::Type(dt) => match dt {
                // A DIMENSIONED vector (`bit [7:0]`) or a signed atom is not a
                // bare name: rendering just the keyword would alias
                // `P#(bit[7:0])` with `P#(bit)`. Carry the whole type instead;
                // the spec-fragment renderer knows how to print a
                // `TypeLiteral`.
                DataType::IntegerVector {
                    dimensions, span, ..
                } if !dimensions.is_empty() => {
                    return Some(Expression::new(
                        ExprKind::TypeLiteral(Box::new(dt.clone())),
                        *span,
                    ));
                }
                DataType::IntegerAtom {
                    signing: Some(_),
                    span,
                    ..
                }
                | DataType::IntegerVector {
                    signing: Some(_),
                    span,
                    ..
                } => {
                    return Some(Expression::new(
                        ExprKind::TypeLiteral(Box::new(dt.clone())),
                        *span,
                    ));
                }
                DataType::TypeReference { name, .. } => (name.name.name.clone(), name.name.span),
                DataType::IntegerAtom { kind, span, .. } => (
                    match kind {
                        crate::ast::types::IntegerAtomType::Byte => "byte",
                        crate::ast::types::IntegerAtomType::ShortInt => "shortint",
                        crate::ast::types::IntegerAtomType::Int => "int",
                        crate::ast::types::IntegerAtomType::LongInt => "longint",
                        crate::ast::types::IntegerAtomType::Integer => "integer",
                        crate::ast::types::IntegerAtomType::Time => "time",
                    }
                    .to_string(),
                    *span,
                ),
                DataType::IntegerVector { kind, span, .. } => (
                    match kind {
                        crate::ast::types::IntegerVectorType::Bit => "bit",
                        crate::ast::types::IntegerVectorType::Logic => "logic",
                        crate::ast::types::IntegerVectorType::Reg => "reg",
                    }
                    .to_string(),
                    *span,
                ),
                DataType::Simple {
                    kind: crate::ast::types::SimpleType::String,
                    span,
                } => ("string".to_string(), *span),
                // §25.9: `C #(virtual bus_if) x;` — the same identifier
                // `parse_type_args_hash` builds for a procedural declaration.
                // Dropped, the module-scope variable was built as the
                // default specialization, so its type-parameter property was
                // no virtual interface.
                DataType::Interface { span, .. } => {
                    let slice = self.tokens.source().get(span.start..span.end).unwrap_or("");
                    let sub = crate::lexer::Lexer::new(slice).tokenize();
                    let toks: Vec<String> = sub
                        .iter()
                        .take_while(|t| t.kind != TokenKind::Eof)
                        .skip_while(|t| t.kind == TokenKind::KwVirtual)
                        .map(|t| sub.text(t).into_owned())
                        .collect();
                    (Self::virtual_type_arg_text(&toks), *span)
                }
                // §6.12: `C #(real) x;` — dropping the argument built the
                // object as the default specialization.
                DataType::Real { kind, span } => (
                    match kind {
                        crate::ast::types::RealType::Real => "real",
                        crate::ast::types::RealType::ShortReal => "shortreal",
                        crate::ast::types::RealType::RealTime => "realtime",
                    }
                    .to_string(),
                    *span,
                ),
                _ => return None,
            },
        };
        let hier = HierarchicalIdentifier {
            root: None,
            path: vec![HierPathSegment {
                name: PIdent { name: leaf, span },
                selects: Vec::new(),
            }],
            span,
            cached_signal_id: crate::ast::cache::SignalCache::new(None),
            cached_resolved_name: crate::ast::cache::NameCache::new(),
            bound: crate::ast::binding::Bound::UNSET,
        };
        Some(Expression::new(ExprKind::Ident(hier), span))
    }

    /// The optional `#(...)` parameter value assignment of an instantiation
    /// (`mod #(.P(v), .Q(3)) u (...)`), shared by module items and `bind`
    /// directives. `None` when no `#` follows.
    pub(in crate::parse) fn parse_instantiation_params(&mut self) -> Option<Vec<ParamConnection>> {
        if !self.at(TokenKind::Hash) {
            return None;
        }
        self.bump();
        if self.eat(TokenKind::LParen).is_some() {
            self.check_param_list_form();
            let mut p = Vec::new();
            while !self.at(TokenKind::RParen) && !self.at(TokenKind::Eof) {
                if self.at(TokenKind::Dot) {
                    self.bump();
                    let pn = self.parse_identifier();
                    self.expect(TokenKind::LParen);
                    let pv = if !self.at(TokenKind::RParen) {
                        Some(self.parse_param_value())
                    } else {
                        None
                    };
                    self.expect(TokenKind::RParen);
                    p.push(ParamConnection::Named {
                        name: pn,
                        value: pv,
                    });
                } else {
                    let v = self.parse_param_value();
                    // §29.3/§28.16 `delay2 ::= #(mintypmax [, mintypmax])`:
                    // a UDP's delay may be `min:typ:max`.
                    let v = match v {
                        ParamValue::Expr(e) if self.at(TokenKind::Colon) => {
                            ParamValue::Expr(self.parse_mintypmax_rest(e))
                        }
                        v => v,
                    };
                    p.push(ParamConnection::Ordered(Some(v)));
                }

                if self.eat(TokenKind::Comma).is_none() {
                    break;
                }
            }
            self.expect(TokenKind::RParen);
            Some(p)
        } else if matches!(
            self.current_kind(),
            TokenKind::IntegerLiteral | TokenKind::RealLiteral | TokenKind::TimeLiteral
        ) || (self.at(TokenKind::Identifier)
            && !matches!(self.peek_kind(), TokenKind::DoubleColon | TokenKind::Dot))
        {
            // §28.3 primitive delay without parens — `ubuf #2 u (o, i)`.
            // Eating the `#` and returning None left the literal in the
            // stream to trip the instance-name parse. A single NUMERIC
            // literal becomes the one positional value, converging with
            // `#(2)` downstream (the UDP elaborator reads a scalar delay
            // out of `params`). Literals only: an identifier here would
            // be ambiguous against too many neighbors.
            // A.2.2.3 `delay_value` is also a parameter name (`#D`): with
            // the `#` eaten and nothing returned, `my_mux #D (z, a)` became
            // an instance NAMED `D` with no delay.
            // One delay value (A.2.2.3), as for a gate: a general expression
            // went on into an unnamed instance's terminal list as a call on
            // the literal (`my_mux #0 (z, a, b, s)` read `0 (z, a, b, s)`).
            Some(vec![ParamConnection::Ordered(Some(ParamValue::Expr(
                self.parse_delay_value(),
            )))])
        } else {
            None
        }
    }

    pub(super) fn parse_identifier_starting_item(&mut self) -> ModuleItem {
        let start = self.current_span().start;
        let first_name = self.parse_identifier();
        if self.at(TokenKind::DoubleColon) {
            // `::`-chained scoped type: `pkg::T`, `pkg::cls::T`,
            // `pkg::cls::sub::T` (IEEE 1800-2017 §8.23) and `pkg::cls#(N)::T`
            // (§8.25.1). Walk the WHOLE chain — the old two-name form
            // collapsed `pkg::cls::T` to scope `pkg` + name `cls` and then
            // died on the trailing `::T` when the declarator list parsed.
            let mut scopes: Vec<crate::ast::types::TypeScope> = Vec::new();
            let mut tn_name = first_name;
            while self.at(TokenKind::DoubleColon) {
                self.bump(); // ::
                scopes.push(crate::ast::types::TypeScope {
                    name: tn_name,
                    type_args: Vec::new(),
                });
                tn_name = self.parse_identifier();
                // `cls#(N)::t` — a per-link specialization, consumed only
                // when a `::` follows (the leaf's own `#(...)` is parsed
                // below, as before).
                if self.at(TokenKind::Hash)
                    && self.peek_kind() == TokenKind::LParen
                    && self.peek_hash_paren_is_scope_link()
                {
                    let link_args = self.parse_type_args_hash(start);
                    self.expect(TokenKind::DoubleColon);
                    scopes.push(crate::ast::types::TypeScope {
                        name: tn_name,
                        type_args: link_args,
                    });
                    tn_name = self.parse_identifier();
                }
            }
            let second_name = tn_name;
            // `pkg::cls #(.P(v)) var = new;` — scoped PARAMETERIZED class
            // as the declaration type (§8.25). The specialization was never
            // consumed here, so the declarator parser saw `#`.
            let type_args = self.parse_type_args_hash(start);
            let dimensions = self.parse_packed_dimensions();
            let dt = DataType::TypeReference {
                name: TypeName {
                    scopes,
                    name: second_name,
                    span: self.span_from(start),
                    bound: Default::default(),
                },
                dimensions,
                type_args,
                span: self.span_from(start),
            };
            let decls = self.parse_var_declarator_list();
            self.expect(TokenKind::Semicolon);
            return ModuleItem::DataDeclaration(DataDeclaration {
                net_type: None,
                const_kw: false,
                var_kw: false,
                lifetime: None,
                data_type: dt,
                declarators: decls,
                span: self.span_from(start),
            });
        }
        if self.eat(TokenKind::Colon).is_some() {
            let mut item = self.parse_module_item().unwrap_or(ModuleItem::Null);
            if let ModuleItem::AssertionItem(a) = &mut item {
                a.label = Some(first_name);
            }
            return item;
        }
        // §25.5: non-ANSI body port declaration with a MODPORT-qualified
        // interface type — `counter_if.counter_mp c_data;`. The lookahead is
        // `. ident ident` with a `;`/`,` after: nothing else at item level
        // has that shape (an instantiation would be `type name (…)`). ANSI
        // headers already route through parse_data_type's Interface arm;
        // this body form died on the dot ("expected identifier, found Dot").
        if self.at(TokenKind::Dot)
            && self.peek_kind() == TokenKind::Identifier
            && self.peek_kind_n(2) == TokenKind::Identifier
            && matches!(self.peek_kind_n(3), TokenKind::Semicolon | TokenKind::Comma)
        {
            self.bump(); // .
            let modport = self.parse_identifier();
            let dt = DataType::Interface {
                name: first_name.clone(),
                modport: Some(modport),
                type_args: Vec::new(),
                span: self.span_from(start),
            };
            let decls = self.parse_var_declarator_list();
            self.expect(TokenKind::Semicolon);
            return ModuleItem::DataDeclaration(DataDeclaration {
                net_type: None,
                const_kw: false,
                var_kw: false,
                lifetime: None,
                data_type: dt,
                declarators: decls,
                span: self.span_from(start),
            });
        }
        // §29.3: `udp_identifier [drive_strength] [delay2] udp_instance`.
        // A `(` opening with a strength keyword is the drive strength; xezim
        // does not model strengths (as for gates, §28.4), so it is consumed.
        // Taken for the terminal list, it read `(strong0, weak1)` as ports.
        if self.at(TokenKind::LParen) && self.peek_kind().is_strength_keyword() {
            self.bump(); // (
            while !self.at(TokenKind::RParen) && !self.at(TokenKind::Eof) {
                self.bump();
            }
            self.expect(TokenKind::RParen);
        }
        let params = self.parse_instantiation_params();

        // §8.25.1: `Cls#(args)::td var;` — a parameterized class used as a
        // scope prefix, spelled WITHOUT a package qualifier. The `#(...)`
        // was just consumed as instantiation params; a following `::`
        // means it was the class's SPECIALIZATION, so convert the
        // connections to type args and walk the rest of the scope chain
        // (further `::` links and per-link `#(...)::` specializations,
        // §8.23).
        if self.at(TokenKind::DoubleColon) {
            let type_args: Vec<crate::ast::expr::Expression> = match &params {
                Some(ps) => ps
                    .iter()
                    .filter_map(|pc| self.param_connection_to_type_arg(pc))
                    .collect(),
                None => Vec::new(),
            };
            let mut scopes: Vec<crate::ast::types::TypeScope> =
                vec![crate::ast::types::TypeScope {
                    name: first_name,
                    type_args,
                }];
            self.bump(); // ::
            let mut tn_name = self.parse_identifier();
            while self.at(TokenKind::DoubleColon) {
                self.bump(); // ::
                scopes.push(crate::ast::types::TypeScope {
                    name: tn_name,
                    type_args: Vec::new(),
                });
                tn_name = self.parse_identifier();
                if self.at(TokenKind::Hash)
                    && self.peek_kind() == TokenKind::LParen
                    && self.peek_hash_paren_is_scope_link()
                {
                    let link_args = self.parse_type_args_hash(start);
                    self.expect(TokenKind::DoubleColon);
                    scopes.push(crate::ast::types::TypeScope {
                        name: tn_name,
                        type_args: link_args,
                    });
                    tn_name = self.parse_identifier();
                }
            }
            let dimensions = self.parse_packed_dimensions();
            let dt = DataType::TypeReference {
                name: TypeName {
                    scopes,
                    name: tn_name,
                    span: self.span_from(start),
                    bound: Default::default(),
                },
                dimensions,
                type_args: Vec::new(),
                span: self.span_from(start),
            };
            let decls = self.parse_var_declarator_list();
            self.expect(TokenKind::Semicolon);
            return ModuleItem::DataDeclaration(DataDeclaration {
                net_type: None,
                const_kw: false,
                var_kw: false,
                lifetime: None,
                data_type: dt,
                declarators: decls,
                span: self.span_from(start),
            });
        }

        // Packed dimensions on a user-typedef base: `MyType [hi:lo] var_name;`
        // After the optional #(params), if we see `[`, treat the construct as a
        // data declaration of `MyType` with packed dimensions, not a module
        // instantiation.
        if self.at(TokenKind::LBracket) {
            let dimensions = self.parse_packed_dimensions();
            let type_args: Vec<crate::ast::expr::Expression> = match &params {
                Some(ps) => ps
                    .iter()
                    .filter_map(|pc| self.param_connection_to_type_arg(pc))
                    .collect(),
                None => Vec::new(),
            };
            let dt = DataType::TypeReference {
                name: TypeName {
                    scopes: Vec::new(),
                    name: first_name,
                    span: self.span_from(start),
                    bound: Default::default(),
                },
                dimensions,
                type_args,
                span: self.span_from(start),
            };
            let decls = self.parse_var_declarator_list();
            self.expect(TokenKind::Semicolon);
            return ModuleItem::DataDeclaration(DataDeclaration {
                net_type: None,
                const_kw: false,
                var_kw: false,
                lifetime: None,
                data_type: dt,
                declarators: decls,
                span: self.span_from(start),
            });
        }
        // §29.3 `udp_instance ::= [name_of_instance] ( terminals )`: a UDP
        // instance may omit its name (`p (q, d);`). It is kept with an empty
        // name; the elaborator rejects a nameless module instance (§23.3.2).
        if self.at(TokenKind::LParen) {
            let mut instances = Vec::new();
            loop {
                let inst_start = self.current_span().start;
                let name = if self.at(TokenKind::Identifier) {
                    self.parse_identifier()
                } else {
                    Identifier {
                        name: String::new(),
                        span: self.span_from(inst_start),
                    }
                };
                let dims = self.parse_unpacked_dimensions();
                let conns = self.parse_port_connections();
                instances.push(HierarchicalInstance {
                    decl: crate::ast::binding::Bound::UNSET,
                    name,
                    dimensions: dims,
                    connections: conns,
                    gen_indices: Vec::new(),
                    span: self.span_from(inst_start),
                });
                if self.eat(TokenKind::Comma).is_none() {
                    break;
                }
            }
            self.expect(TokenKind::Semicolon);
            return ModuleItem::ModuleInstantiation(ModuleInstantiation {
                module_name: first_name,
                params,
                instances,
                scope: None,
                span: self.span_from(start),
            });
        }
        if self.at(TokenKind::Identifier) || self.at(TokenKind::EscapedIdentifier) {
            let initial_pos = self.pos;
            let mut is_data_decl = false;
            let mut instances = Vec::new();
            loop {
                let inst_save_pos = self.pos;
                let inst_start = self.current_span().start;
                let _iname = self.parse_identifier();
                let _dims = self.parse_unpacked_dimensions();
                if self.at(TokenKind::Assign)
                    || self.at(TokenKind::Semicolon)
                    || self.at(TokenKind::Comma)
                {
                    is_data_decl = true;
                    break;
                }
                self.pos = inst_save_pos; // rewind just this instance
                let iname = self.parse_identifier();
                let dims = self.parse_unpacked_dimensions();
                let conns = self.parse_port_connections();
                instances.push(HierarchicalInstance {
                    decl: crate::ast::binding::Bound::UNSET,
                    name: iname,
                    dimensions: dims,
                    connections: conns,
                    gen_indices: Vec::new(),
                    span: self.span_from(inst_start),
                });
                if self.eat(TokenKind::Comma).is_none() {
                    break;
                }
            }
            if is_data_decl {
                self.pos = initial_pos;
                let type_args: Vec<crate::ast::expr::Expression> = match &params {
                    Some(ps) => ps
                        .iter()
                        .filter_map(|pc| self.param_connection_to_type_arg(pc))
                        .collect(),
                    None => Vec::new(),
                };
                let dt = DataType::TypeReference {
                    name: TypeName {
                        scopes: Vec::new(),
                        name: first_name,
                        span: self.span_from(start),
                        bound: Default::default(),
                    },
                    dimensions: Vec::new(),
                    type_args,
                    span: self.span_from(start),
                };
                let decls = self.parse_var_declarator_list();
                self.expect(TokenKind::Semicolon);
                ModuleItem::DataDeclaration(DataDeclaration {
                    net_type: None,
                    const_kw: false,
                    var_kw: false,
                    lifetime: None,
                    data_type: dt,
                    declarators: decls,
                    span: self.span_from(start),
                })
            } else {
                self.expect(TokenKind::Semicolon);
                ModuleItem::ModuleInstantiation(ModuleInstantiation {
                    module_name: first_name,
                    params,
                    instances,
                    scope: None,
                    span: self.span_from(start),
                })
            }
        } else {
            let dt = DataType::TypeReference {
                name: TypeName {
                    scopes: Vec::new(),
                    name: first_name,
                    span: self.span_from(start),
                    bound: Default::default(),
                },
                dimensions: Vec::new(),
                type_args: Vec::new(),
                span: self.span_from(start),
            };
            let decls = self.parse_var_declarator_list();
            self.expect(TokenKind::Semicolon);
            ModuleItem::DataDeclaration(DataDeclaration {
                net_type: None,
                const_kw: false,
                var_kw: false,
                lifetime: None,
                data_type: dt,
                declarators: decls,
                span: self.span_from(start),
            })
        }
    }

    /// One actual of an instance connection. §17.2: a checker's event
    /// formal takes an event expression (`chk u(v, posedge clk)`), which
    /// is not an ordinary expression; it is carried as the internal
    /// `$__posedge(e)` / `$__negedge(e)` / `$__edge(e)` call and folded
    /// into the clocking event when the checker body is instantiated.
    fn parse_port_actual(&mut self) -> Expression {
        let name = match self.current_kind() {
            TokenKind::KwPosedge => "$__posedge",
            TokenKind::KwNegedge => "$__negedge",
            TokenKind::KwEdge => "$__edge",
            _ => return self.parse_expression(),
        };
        let start = self.current_span().start;
        self.bump();
        let e = self.parse_expression();
        Expression::new(
            ExprKind::SystemCall {
                name: name.to_string(),
                args: vec![e],
            },
            self.span_from(start),
        )
    }

    pub(in crate::parse) fn parse_port_connections(&mut self) -> Vec<PortConnection> {
        let mut conns = Vec::new();
        if self.eat(TokenKind::LParen).is_none() {
            return conns;
        }
        if self.at(TokenKind::RParen) {
            self.bump();
            return conns;
        }
        loop {
            if self.at(TokenKind::RParen) || self.at(TokenKind::Eof) {
                break;
            }
            if self.at(TokenKind::Comma) {
                // Empty positional connection: `dut(, result)`. An omitted
                // ordered port takes its declared default (§23.2.2.4) or is
                // left unconnected.
                conns.push(PortConnection::Ordered(None));
            } else if self.at(TokenKind::Dot) {
                self.bump();
                if self.at(TokenKind::Star) {
                    self.bump();
                    conns.push(PortConnection::Wildcard);
                } else {
                    let nm = self.parse_identifier();
                    let (ex, had_parens) = if self.eat(TokenKind::LParen).is_some() {
                        let e = if !self.at(TokenKind::RParen) {
                            Some(self.parse_port_actual())
                        } else {
                            None
                        };
                        self.expect(TokenKind::RParen);
                        (e, true)
                    } else {
                        (None, false)
                    };
                    conns.push(PortConnection::Named {
                        name: nm,
                        expr: ex,
                        implicit: !had_parens,
                    });
                }
            } else {
                conns.push(PortConnection::Ordered(Some(self.parse_port_actual())));
            }
            if self.eat(TokenKind::Comma).is_none() {
                break;
            }
            // Trailing empty positional connection: `dut(result, )`.
            if self.at(TokenKind::RParen) {
                conns.push(PortConnection::Ordered(None));
                break;
            }
        }
        // §23.3.2: connections are all by position or all by name.
        if crate::strict_checks()
            && conns
                .iter()
                .any(|c| matches!(c, PortConnection::Ordered(Some(_))))
            && conns
                .iter()
                .any(|c| !matches!(c, PortConnection::Ordered(_)))
        {
            self.error(
                "port connections by position and by name cannot be mixed in one \
                 instance (IEEE 1800-2017 §23.3.2)",
            );
        }
        self.expect(TokenKind::RParen);
        conns
    }

    pub(in crate::parse) fn parse_module_items_until(&mut self, end: TokenKind) -> Vec<ModuleItem> {
        let mut items = Vec::new();
        while !self.at(end) && !self.at(TokenKind::Eof) {
            let before = self.pos;
            let item = self.parse_module_item();
            if self.pos == before {
                // Same guard as parse_module_items: a Some(..) that consumed
                // nothing would loop forever, so force progress here too (this
                // is the loop behind generate-block bodies, so it shares the
                // virtual-interface hazard).
                self.error(format!("unexpected: {:?}", self.current_text()));
                self.bump();
                continue;
            }
            if let Some(item) = item {
                self.hide_let_names_of_item(&item);
                items.push(item);
                items.append(&mut self.pending_module_items);
            }
        }
        items
    }

    /// The tokens of a parameter value list parsed from `start` on, as text,
    /// to tell specializations apart (empty without a list).
    pub(super) fn param_args_text(&self, start: usize) -> String {
        let toks: Vec<Token> = (start..self.pos).map(|i| self.tokens[i]).collect();
        let inner = match toks.as_slice() {
            [h, l, rest @ .., _] if h.kind == TokenKind::Hash && l.kind == TokenKind::LParen => {
                rest
            }
            [l, rest @ .., _] if l.kind == TokenKind::LParen => rest,
            _ => toks.as_slice(),
        };
        inner
            .iter()
            .map(|&t| self.token_text(t))
            .collect::<Vec<_>>()
            .join(" ")
    }
}
