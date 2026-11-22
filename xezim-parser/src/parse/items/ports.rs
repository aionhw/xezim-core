use super::*;

impl<'a> Parser<'a> {
    pub(in crate::parse) fn parse_port_list(&mut self) -> PortList {
        self.port_exprs.clear();
        if self.eat(TokenKind::LParen).is_none() {
            return PortList::Empty;
        }
        if self.at(TokenKind::RParen) {
            self.bump();
            return PortList::Empty;
        }
        if self.is_port_direction() || self.is_data_type_keyword() || self.at(TokenKind::KwVar)
            // §6.6.8 — `interconnect p` opens an ANSI port list too.
            || self.at(TokenKind::KwInterconnect)
            // §23.2.2.3 — a port kind or an implicit data type, `(wire x)`,
            // `([5:0] x, wire y)`: the first port gives one, so the list is
            // ANSI. No non-ANSI port starts with either.
            || self.is_net_type_keyword()
            || self.at(TokenKind::LBracket)
            || (self.at(TokenKind::Identifier) && self.peek_kind() == TokenKind::Dot)
            || (self.at(TokenKind::Identifier) && matches!(self.peek_kind(), TokenKind::Identifier | TokenKind::DoubleColon | TokenKind::Hash))
            // LRM §25.9 — `virtual <iface_t> <name>` port form.
            || (self.at(TokenKind::KwVirtual)
                && matches!(self.peek_kind(),
                    TokenKind::KwInterface | TokenKind::Identifier))
            // LRM §25.3.2 — generic interface port `interface [.mp] <name>`.
            || self.at(TokenKind::KwInterface)
        {
            let mut ports: Vec<AnsiPort> = Vec::new();
            loop {
                if self.at(TokenKind::RParen) || self.at(TokenKind::Eof) {
                    break;
                }
                let mut port = self.parse_ansi_port();
                // §23.2.2.3: a later port that omits its direction, port kind
                // and data type all three takes all three from the previous
                // port, as that port ended up (`output var a, b`: b is a
                // variable too). One that gives any of them takes only an
                // omitted direction; an omitted kind follows the first-port
                // rules and an omitted data type is `logic`. So in
                // `input logic [7:0] d, input clk, rst_n` the port `rst_n` is
                // a scalar like `clk`, and `wire y` after `inout [5:0] x` is
                // one bit.
                if let Some(prev) = ports.last() {
                    if port.direction.is_none()
                        && port.net_type.is_none()
                        && !port.var_kw
                        && port.data_type.is_none()
                    {
                        port.direction = prev.direction;
                        port.net_type = prev.net_type;
                        port.var_kw = prev.var_kw;
                        port.data_type = prev.data_type.clone();
                    } else if port.direction.is_none() {
                        port.direction = prev.direction;
                    }
                }
                // §23.2.2.3: a default pull applies to inferred net ports
                // after inheritance. Explicit net kinds and variables retain
                // their declaration.
                if port.net_type.is_none() && !port.var_kw
                    && !matches!(port.direction, Some(PortDirection::Ref))
                    && !matches!(&port.data_type, Some(DataType::Interface { .. }))
                    && (!matches!(port.direction, Some(PortDirection::Output))
                        || matches!(&port.data_type, None | Some(DataType::Implicit { .. })))
                {
                    let n = self.default_net_pulls.partition_point(|(pos, _)| *pos <= port.span.start);
                    port.net_type = n.checked_sub(1).and_then(|i| self.default_net_pulls[i].1);
                }
                // §23.2.2.4: only an input port takes a default value; an
                // inout is a net.
                if crate::strict_checks()
                    && port.direction == Some(PortDirection::Inout)
                    && let Some(d) = &port.default
                {
                    self.diagnostics.push(crate::diagnostics::Diagnostic::error(
                        format!(
                            "inout port '{}' cannot have a default value (IEEE 1800-2017 §23.2.2.4)",
                            port.name.name
                        ),
                        d.span,
                    ));
                }
                ports.push(port);
                if self.eat(TokenKind::Comma).is_none() {
                    break;
                }
            }
            self.expect(TokenKind::RParen);
            PortList::Ansi(ports)
        } else {
            let mut names = Vec::new();
            let null_port = |names: &Vec<Identifier>, span| crate::ast::Identifier {
                name: format!("__xz_null_port_{}", names.len()),
                span,
            };
            loop {
                if self.at(TokenKind::RParen) || self.at(TokenKind::Eof) {
                    break;
                }
                // §23.2.2.1 null port — `(a, , b)` / `(a,, b)` is legal: the
                // position exists but is unnamed. Synthesize a placeholder
                // name so ordered instantiation keeps positional alignment;
                // nothing in the body can bind it, so a connection landing on
                // this slot is dropped, matching the LRM's "connection to a
                // null port is ignored".
                if self.at(TokenKind::Comma) {
                    let sp = self.current_span();
                    names.push(null_port(&names, sp));
                    self.bump(); // consume the comma standing in for the port
                    if self.at(TokenKind::RParen) {
                        names.push(null_port(&names, sp));
                    }
                    continue;
                }
                // §23.2.2.1 port expressions: `.name(expr)`, an unnamed
                // concatenation `{a, b}` or a select `a[7:0]`. Lowered by the
                // module declaration once the body declares the signals.
                if self.at(TokenKind::Dot) {
                    self.bump();
                    let name = self.parse_identifier();
                    self.expect(TokenKind::LParen);
                    if self.at(TokenKind::RParen) {
                        names.push(null_port(&names, name.span));
                    } else {
                        let e = self.parse_expression();
                        self.port_exprs.push((names.len(), e));
                        names.push(name);
                    }
                    self.expect(TokenKind::RParen);
                } else if self.at(TokenKind::LBrace)
                    || (self.at(TokenKind::Identifier) && self.peek_kind() == TokenKind::LBracket)
                {
                    let e = self.parse_expression();
                    let span = e.span;
                    self.port_exprs.push((names.len(), e));
                    names.push(crate::ast::Identifier {
                        name: format!("__xz_port_expr_{}", names.len()),
                        span,
                    });
                } else {
                    names.push(self.parse_identifier());
                }
                if self.eat(TokenKind::Comma).is_none() {
                    break;
                }
                // A trailing `, )` leaves one more null port.
                if self.at(TokenKind::RParen) {
                    let sp = self.current_span();
                    names.push(null_port(&names, sp));
                }
            }
            self.expect(TokenKind::RParen);
            PortList::NonAnsi(names)
        }
    }

    /// §23.2.2.1: lower the port expressions of a non-ANSI header
    /// (`.b(a[2:1])`, `{a, b}`, `a[7:0]`) to plain ports. Each becomes a port
    /// as wide as its expression, joined to the signals it names by a
    /// continuous assignment (driving them for an input, reading them for an
    /// output). Those signals stop being ports and keep their declared type
    /// as nets or variables.
    pub(super) fn lower_port_expressions(
        &mut self,
        ports: &PortList,
        items: &mut Vec<ModuleItem>,
        exprs: Vec<(usize, Expression)>,
    ) {
        if exprs.is_empty() {
            return;
        }
        let PortList::NonAnsi(names) = ports else {
            return;
        };
        let plain: Vec<String> = names
            .iter()
            .enumerate()
            .filter(|(i, _)| !exprs.iter().any(|(j, _)| j == i))
            .map(|(_, n)| n.name.clone())
            .collect();
        let mut demoted = Vec::new();
        for (idx, e) in exprs {
            let port = names[idx].clone();
            if let Err(msg) = Self::lower_port_expression(&port, &e, &plain, items, &mut demoted) {
                self.diagnostics.push(crate::diagnostics::Diagnostic::error(
                    format!(
                        "unsupported port expression for port '{}': {msg} \
                         (IEEE 1800-2017 §23.2.2.1)",
                        port.name
                    ),
                    e.span,
                ));
            }
        }
        // Port declarations whose every name moved to a net or variable.
        items
            .retain(|it| !matches!(it, ModuleItem::PortDeclaration(d) if d.declarators.is_empty()));
    }

    fn lower_port_expression(
        port: &Identifier,
        e: &Expression,
        plain: &[String],
        items: &mut Vec<ModuleItem>,
        demoted: &mut Vec<(String, PortDirection, DataType)>,
    ) -> Result<(), String> {
        let span = e.span;
        let num = |v: i64| {
            Expression::new(
                ExprKind::Number(NumberLiteral::Integer {
                    size: None,
                    signed: true,
                    base: NumberBase::Decimal,
                    value: v.to_string(),
                    cached_val: crate::ast::cache::LiteralCache::new(None),
                }),
                span,
            )
        };
        let bin = |op, l: Expression, r: Expression| {
            Expression::new(
                ExprKind::Binary {
                    op,
                    left: Box::new(l),
                    right: Box::new(r),
                },
                span,
            )
        };
        // |l - r| + 1
        let range_width = |l: &Expression, r: &Expression| {
            Expression::new(
                ExprKind::Conditional {
                    condition: Box::new(bin(BinaryOp::Geq, l.clone(), r.clone())),
                    then_expr: Box::new(bin(BinaryOp::Sub, l.clone(), r.clone())),
                    else_expr: Box::new(bin(BinaryOp::Sub, r.clone(), l.clone())),
                },
                span,
            )
        };
        // The signals named by the expression, each with the width of its
        // part when that is a select.
        fn leaves<'e>(
            e: &'e Expression,
            out: &mut Vec<(
                &'e Identifier,
                Option<(&'e Expression, &'e Expression, RangeKind)>,
                bool,
            )>,
        ) -> Result<(), String> {
            let base = |x: &'e Expression| -> Result<&'e Identifier, String> {
                match &x.kind {
                    ExprKind::Ident(h) if h.path.len() == 1 && h.path[0].selects.is_empty() => {
                        Ok(&h.path[0].name)
                    }
                    _ => {
                        Err("only names, selects of names and concatenations are supported".into())
                    }
                }
            };
            match &e.kind {
                ExprKind::Concatenation(parts) => {
                    for p in parts {
                        leaves(p, out)?;
                    }
                }
                ExprKind::Index { expr, .. } => out.push((base(expr)?, None, true)),
                ExprKind::RangeSelect {
                    expr,
                    kind,
                    left,
                    right,
                } => out.push((base(expr)?, Some((left, right, *kind)), false)),
                _ => out.push((base(e)?, None, false)),
            }
            Ok(())
        }
        let mut parts = Vec::new();
        leaves(e, &mut parts)?;
        let decl_of = |items: &[ModuleItem], n: &str| {
            items.iter().find_map(|it| match it {
                ModuleItem::PortDeclaration(d)
                    if d.declarators.iter().any(|v| v.name.name == n) =>
                {
                    Some(d.clone())
                }
                _ => None,
            })
        };
        // A separate net or variable declaration completing the port.
        let completion = |items: &[ModuleItem], n: &str| {
            items.iter().find_map(|it| match it {
                ModuleItem::NetDeclaration(d) if d.declarators.iter().any(|v| v.name.name == n) => {
                    Some(d.data_type.clone())
                }
                ModuleItem::DataDeclaration(d)
                    if d.declarators.iter().any(|v| v.name.name == n) =>
                {
                    Some(d.data_type.clone())
                }
                _ => None,
            })
        };
        let packed = |dt: &DataType| match dt {
            DataType::Implicit { dimensions, .. } | DataType::IntegerVector { dimensions, .. } => {
                Some(dimensions.clone())
            }
            _ => None,
        };
        let mut direction = None;
        let mut width: Option<Expression> = None;
        for (id, sel, bit) in &parts {
            if plain.contains(&id.name) || id.name == port.name {
                return Err(format!("'{}' is also a port of its own", id.name));
            }
            // A signal already demoted by an earlier port expression keeps
            // the direction and type it was declared with.
            let (dir, dt) = match demoted.iter().find(|(n, ..)| *n == id.name) {
                Some((_, dir, dt)) => (*dir, dt.clone()),
                None => {
                    let d = decl_of(items, &id.name).ok_or_else(|| {
                        format!("'{}' has no input or output declaration", id.name)
                    })?;
                    (d.direction, d.data_type)
                }
            };
            if dir == PortDirection::Inout || direction.is_some_and(|d| d != dir) {
                return Err("an inout or mixed-direction port expression".into());
            }
            direction = Some(dir);
            let w = if *bit {
                num(1)
            } else if let Some((l, r, kind)) = sel {
                match kind {
                    RangeKind::Constant => bin(BinaryOp::Add, range_width(l, r), num(1)),
                    _ => (*r).clone(),
                }
            } else {
                // The range may sit on the completing declaration instead.
                let own = packed(&dt);
                let dims = match own {
                    Some(d) if !d.is_empty() => d,
                    _ => completion(items, &id.name)
                        .as_ref()
                        .and_then(packed)
                        .or(own)
                        .ok_or_else(|| format!("'{}' has no vector type", id.name))?,
                };
                match dims.as_slice() {
                    [] => num(1),
                    [PackedDimension::Range { left, right, .. }] => {
                        bin(BinaryOp::Add, range_width(left, right), num(1))
                    }
                    _ => return Err(format!("'{}' has more than one packed dimension", id.name)),
                }
            };
            width = Some(match width {
                None => w,
                Some(acc) => bin(BinaryOp::Add, acc, w),
            });
        }
        let (Some(direction), Some(width)) = (direction, width) else {
            return Err("an empty port expression".into());
        };
        // The named signals leave the port list: each keeps its declared type
        // as a net or variable unless another declaration already completes it.
        for (id, _, _) in &parts {
            if demoted.iter().any(|(n, ..)| *n == id.name) {
                continue;
            }
            let completed = completion(items, &id.name).is_some();
            let Some(at) = items.iter().position(|it| {
                matches!(it, ModuleItem::PortDeclaration(d)
                    if d.declarators.iter().any(|v| v.name.name == id.name))
            }) else {
                continue;
            };
            let ModuleItem::PortDeclaration(d) = &mut items[at] else {
                continue;
            };
            let pos = d.declarators.iter().position(|v| v.name.name == id.name);
            let v = d.declarators.remove(pos.unwrap_or_default());
            let (net_type, data_type, dspan) = (d.net_type, d.data_type.clone(), d.span);
            demoted.push((id.name.clone(), direction, data_type.clone()));
            if completed {
                continue;
            }
            let is_var = net_type.is_none() && !matches!(data_type, DataType::Implicit { .. });
            // In the port declaration's place, so later items see it.
            items.insert(
                at + 1,
                if is_var {
                    ModuleItem::DataDeclaration(DataDeclaration {
                        net_type: None,
                        const_kw: false,
                        var_kw: false,
                        lifetime: None,
                        data_type,
                        declarators: vec![v],
                        span: dspan,
                    })
                } else {
                    ModuleItem::NetDeclaration(NetDeclaration {
                        net_type: net_type.unwrap_or(NetType::Wire),
                        strength: None,
                        data_type,
                        delay: None,
                        delay_fall: None,
                        delay_off: None,
                        declarators: vec![NetDeclarator {
                            decl: crate::ast::binding::Bound::UNSET,
                            name: v.name,
                            dimensions: v.dimensions,
                            init: None,
                            span: v.span,
                        }],
                        span: dspan,
                    })
                },
            );
        }
        // The new port follows the declarations of the signals it joins
        // (their ranges may use parameters declared before them).
        let joined = |it: &ModuleItem| {
            let named = |n: &str| parts.iter().any(|(id, ..)| id.name == n);
            match it {
                ModuleItem::PortDeclaration(d) => d.declarators.iter().any(|v| named(&v.name.name)),
                ModuleItem::NetDeclaration(d) => d.declarators.iter().any(|v| named(&v.name.name)),
                ModuleItem::DataDeclaration(d) => d.declarators.iter().any(|v| named(&v.name.name)),
                _ => false,
            }
        };
        let at = items.iter().rposition(joined).map_or(0, |i| i + 1);
        let port_ref = Expression::new(
            ExprKind::Ident(HierarchicalIdentifier {
                root: None,
                path: vec![HierPathSegment {
                    name: port.clone(),
                    selects: Vec::new(),
                }],
                span,
                cached_signal_id: crate::ast::cache::SignalCache::new(None),
                cached_resolved_name: crate::ast::cache::NameCache::new(),
                bound: crate::ast::binding::Bound::UNSET,
            }),
            span,
        );
        items.insert(
            at,
            ModuleItem::PortDeclaration(PortDeclaration {
                direction,
                net_type: None,
                data_type: DataType::Implicit {
                    signing: None,
                    dimensions: vec![PackedDimension::Range {
                        left: Box::new(bin(BinaryOp::Sub, width, num(1))),
                        right: Box::new(num(0)),
                        span,
                    }],
                    span,
                },
                declarators: vec![crate::ast::stmt::VarDeclarator {
                    decl: crate::ast::binding::Bound::UNSET,
                    name: port.clone(),
                    dimensions: Vec::new(),
                    init: None,
                    span,
                }],
                span,
            }),
        );
        let (lhs, rhs) = match direction {
            PortDirection::Input => (e.clone(), port_ref),
            _ => (port_ref, e.clone()),
        };
        items.push(ModuleItem::ContinuousAssign(ContinuousAssign {
            strength: None,
            delay: None,
            delay_fall: None,
            delay_off: None,
            assignments: vec![(lhs, rhs)],
            span,
        }));
        Ok(())
    }

    fn parse_ansi_port(&mut self) -> AnsiPort {
        let start = self.current_span().start;
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
            } else {
                None
            };
            Some(DataType::Interface {
                name: if_name,
                modport,
                type_args: Vec::new(),
                span: self.span_from(start),
            })
        } else if self.at(TokenKind::KwInterface) {
            // §25.3.2 generic interface port: `interface [.<modport>] <name>`.
            self.bump(); // interface
            let modport = if self.at(TokenKind::Dot) {
                self.bump();
                Some(self.parse_identifier())
            } else {
                None
            };
            Some(DataType::Interface {
                name: crate::ast::Identifier {
                    name: "interface".to_string(),
                    span: self.span_from(start),
                },
                modport,
                type_args: Vec::new(),
                span: self.span_from(start),
            })
        } else if self.is_data_type_keyword() {
            Some(self.parse_data_type())
        } else if self.at(TokenKind::LBracket) {
            let dimensions = self.parse_packed_dimensions();
            Some(DataType::Implicit {
                signing: None,
                dimensions,
                span: self.span_from(start),
            })
        } else if self.at(TokenKind::Identifier) && self.peek_kind() == TokenKind::Dot {
            let if_name = self.parse_identifier();
            self.expect(TokenKind::Dot);
            let mp_name = self.parse_identifier();
            Some(DataType::Interface {
                name: if_name,
                modport: Some(mp_name),
                type_args: Vec::new(),
                span: self.span_from(start),
            })
        } else if self.at(TokenKind::Identifier)
            && matches!(
                self.peek_kind(),
                TokenKind::Identifier | TokenKind::DoubleColon | TokenKind::Hash
            )
        {
            Some(self.parse_data_type())
        } else if self.at(TokenKind::Identifier) && self.peek_kind() == TokenKind::LBracket {
            // AMBIGUOUS: `typedef_t [7:0] name` (a type with packed dims)
            // vs `name[t-1:0]` (an implicit-typed port whose NAME carries an
            // unpacked dimension — `output v0vJ[t-1:0],`). Look past the
            // balanced bracket groups: an IDENTIFIER there means the first
            // token was a type; a comma/`)`/`=` means it was the port name.
            let mut p = self.pos + 1;
            while self
                .tokens
                .get(p)
                .is_some_and(|t| t.kind == TokenKind::LBracket)
            {
                let mut depth = 1;
                p += 1;
                while depth > 0 {
                    match self.tokens.get(p).map(|t| t.kind) {
                        Some(TokenKind::LBracket) => depth += 1,
                        Some(TokenKind::RBracket) => depth -= 1,
                        Some(_) => {}
                        None => break,
                    }
                    p += 1;
                }
            }
            if self.tokens.get(p).is_some_and(|t| {
                matches!(t.kind, TokenKind::Identifier | TokenKind::EscapedIdentifier)
            }) {
                Some(self.parse_data_type())
            } else {
                None
            }
        } else {
            None
        };
        // An ANSI `wreal` port carries a real and declares no data type of
        // its own. Same reason as the net path: fill one in so the width
        // and real-ness queries downstream have something to read. A ranged
        // one (`input wreal [3:0] p`) reaches here as an `Implicit` with
        // packed dimensions and is rejected by the shared helper.
        let wreal_span = self.span_from(start);
        let data_type = match (net_type, data_type) {
            (Some(NetType::Wreal), None) => Some(DataType::Real {
                kind: RealType::Real,
                span: wreal_span,
            }),
            (Some(nt), Some(dt)) => Some(self.wreal_data_type(nt, dt, wreal_span)),
            (_, dt) => dt,
        };
        let mut dimensions = if data_type.is_some() {
            self.parse_unpacked_dimensions()
        } else {
            Vec::new()
        };
        let name = self.parse_identifier();
        dimensions.extend(self.parse_unpacked_dimensions());
        let default = if self.eat(TokenKind::Assign).is_some() {
            Some(self.parse_expression())
        } else {
            None
        };
        AnsiPort {
            attrs: Vec::new(),
            direction,
            net_type,
            var_kw,
            data_type,
            name,
            dimensions,
            default,
            span: self.span_from(start),
        }
    }
}
