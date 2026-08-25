//! Data type parsing (IEEE 1800-2017 §A.2.2)

use super::Parser;
use crate::ast::types::*;
use crate::lexer::token::TokenKind;

impl Parser {
    pub(super) fn is_data_type_keyword(&self) -> bool {
        matches!(self.current_kind(),
            TokenKind::KwBit | TokenKind::KwLogic | TokenKind::KwReg |
            TokenKind::KwByte | TokenKind::KwShortint | TokenKind::KwInt |
            TokenKind::KwLongint | TokenKind::KwInteger | TokenKind::KwTime |
            TokenKind::KwReal | TokenKind::KwShortreal | TokenKind::KwRealtime |
            TokenKind::KwString | TokenKind::KwChandle | TokenKind::KwEvent |
            TokenKind::KwVoid | TokenKind::KwStruct | TokenKind::KwUnion |
            TokenKind::KwEnum | TokenKind::KwSigned | TokenKind::KwUnsigned |
            TokenKind::KwInterface
        )
    }

    #[allow(dead_code)]
    pub(super) fn is_type_start(&self) -> bool {
        self.is_data_type_keyword() || self.at(TokenKind::Identifier)
    }

    pub(super) fn parse_data_type(&mut self) -> DataType {
        let start = self.current().span.start;
        match self.current_kind() {
            // §6.20.2.1 / §25.3: `virtual [interface] <iface>[#(params)][.modport]`
            // used as a type — e.g. a parameter-type default
            // `#(type IFType = virtual x_if)`.
            TokenKind::KwVirtual => {
                self.bump();
                self.eat(TokenKind::KwInterface);
                let name = self.parse_identifier();
                if self.at(TokenKind::Hash) { let _ = self.parse_param_args(); }
                let modport = if self.eat(TokenKind::Dot).is_some() {
                    Some(self.parse_identifier())
                } else { None };
                DataType::Interface { name, modport, span: self.span_from(start) }
            }
            // §6.23 type operator `type(expr_or_data_type)` — parse-accept and
            // treat as implicit (the resolved type is not modelled).
            TokenKind::KwType if self.peek_kind() == TokenKind::LParen => {
                self.bump(); // type
                self.bump(); // (
                let mut depth = 1i32;
                while depth > 0 && !self.at(TokenKind::Eof) {
                    match self.current_kind() {
                        TokenKind::LParen => depth += 1,
                        TokenKind::RParen => depth -= 1,
                        _ => {}
                    }
                    self.bump();
                }
                DataType::Implicit { signing: None, dimensions: Vec::new(), span: self.span_from(start) }
            }
            TokenKind::KwBit | TokenKind::KwLogic | TokenKind::KwReg => {
                let kind = match self.bump().kind {
                    TokenKind::KwBit => IntegerVectorType::Bit,
                    TokenKind::KwLogic => IntegerVectorType::Logic,
                    _ => IntegerVectorType::Reg,
                };
                let signing = self.parse_optional_signing();
                let dimensions = self.parse_packed_dimensions();
                DataType::IntegerVector { kind, signing, dimensions, span: self.span_from(start) }
            }
            TokenKind::KwByte | TokenKind::KwShortint | TokenKind::KwInt |
            TokenKind::KwLongint | TokenKind::KwInteger | TokenKind::KwTime => {
                let kind = match self.bump().kind {
                    TokenKind::KwByte => IntegerAtomType::Byte,
                    TokenKind::KwShortint => IntegerAtomType::ShortInt,
                    TokenKind::KwInt => IntegerAtomType::Int,
                    TokenKind::KwLongint => IntegerAtomType::LongInt,
                    TokenKind::KwInteger => IntegerAtomType::Integer,
                    _ => IntegerAtomType::Time,
                };
                let signing = self.parse_optional_signing();
                DataType::IntegerAtom { kind, signing, span: self.span_from(start) }
            }
            TokenKind::KwReal => { self.bump(); DataType::Real { kind: RealType::Real, span: self.span_from(start) } }
            TokenKind::KwShortreal => { self.bump(); DataType::Real { kind: RealType::ShortReal, span: self.span_from(start) } }
            TokenKind::KwRealtime => { self.bump(); DataType::Real { kind: RealType::RealTime, span: self.span_from(start) } }
            TokenKind::KwString => { self.bump(); DataType::Simple { kind: SimpleType::String, span: self.span_from(start) } }
            TokenKind::KwChandle => { self.bump(); DataType::Simple { kind: SimpleType::Chandle, span: self.span_from(start) } }
            TokenKind::KwEvent => { self.bump(); DataType::Simple { kind: SimpleType::Event, span: self.span_from(start) } }
            TokenKind::KwInterface => {
                self.bump();
                let name = self.parse_identifier();
                let modport = if self.eat(TokenKind::Dot).is_some() {
                    Some(self.parse_identifier())
                } else { None };
                DataType::Interface { name, modport, span: self.span_from(start) }
            }
            TokenKind::KwVoid => { self.bump(); DataType::Void(self.span_from(start)) }
            // IEEE 1800-2023 §6.20.2.1: `type(expr)` typeof operator in
            // type position. We special-case `type(this)` to resolve to
            // the enclosing class name captured at parse time. Other
            // forms fall back to an Implicit type.
            TokenKind::KwType if crate::is_sv2023()
                && self.peek_kind() == TokenKind::LParen =>
            {
                self.bump(); // 'type'
                self.bump(); // '('
                let is_this = matches!(
                    self.current_kind(),
                    TokenKind::KwThis | TokenKind::Identifier
                ) && self.current().text == "this";
                if is_this {
                    self.bump();
                    self.expect(TokenKind::RParen);
                    if let Some(cls) = crate::current_class_name() {
                        let span = self.span_from(start);
                        let name = TypeName {
                            scope: None,
                            name: crate::ast::Identifier { name: cls, span },
                            span,
                        };
                        return DataType::TypeReference {
                            name,
                            dimensions: Vec::new(),
                            type_args: Vec::new(),
                            span,
                        };
                    }
                }
                // Fallback: consume the inner expression and produce an
                // Implicit type. Keeps subsequent declarators parseable.
                let _ = self.parse_expression();
                self.expect(TokenKind::RParen);
                DataType::Implicit { signing: None, dimensions: Vec::new(), span: self.span_from(start) }
            }
            TokenKind::KwEnum => self.parse_enum_type(),
            TokenKind::KwStruct | TokenKind::KwUnion => self.parse_struct_type(),
            TokenKind::KwSigned | TokenKind::KwUnsigned => {
                let signing = self.parse_optional_signing();
                let dimensions = self.parse_packed_dimensions();
                DataType::Implicit { signing, dimensions, span: self.span_from(start) }
            }
            TokenKind::Identifier => {
                let name = self.parse_type_name();
                // Parse optional parameterized type list #(...). Collect
                // the positional arguments as expressions; named (.NAME(expr))
                // args are captured by value only (name discarded for now).
                let type_args = self.parse_type_args_hash(start);
                if name.scope.is_none() && self.at(TokenKind::Dot) {
                    self.bump();
                    let modport = Some(self.parse_identifier());
                    let _dimensions = self.parse_packed_dimensions();
                    DataType::Interface { name: name.name, modport, span: self.span_from(start) }
                } else {
                    let dimensions = self.parse_packed_dimensions();
                    DataType::TypeReference { name, dimensions, type_args, span: self.span_from(start) }
                }
            }
            // Implicit data type that begins with a packed dimension, e.g.
            // `var [7:0] y;` or `wire [3:0] w;` reached via a `data_type`
            // context. Consume the dimensions so the declarator list parses.
            TokenKind::LBracket => {
                let dimensions = self.parse_packed_dimensions();
                DataType::Implicit { signing: None, dimensions, span: self.span_from(start) }
            }
            _ => DataType::Implicit { signing: None, dimensions: Vec::new(), span: self.span_from(start) }
        }
    }

    /// The optional `#(...)` specialization after a (possibly scoped) type
    /// name — shared between `parse_data_type`'s Identifier arm and the
    /// module-item path for `pkg::class #(...) var = new;` declarations,
    /// which previously never consumed the `#` and died with
    /// "expected identifier, found Hash".
    pub(super) fn parse_type_args_hash(&mut self, start: usize) -> Vec<crate::ast::expr::Expression> {
        let mut type_args: Vec<crate::ast::expr::Expression> = Vec::new();
        if self.eat(TokenKind::Hash).is_some() {
                    if self.eat(TokenKind::LParen).is_some() {
                        if !self.at(TokenKind::RParen) {
                            loop {
                                if self.eat(TokenKind::Dot).is_some() {
                                    let _ident = self.parse_identifier();
                                    self.expect(TokenKind::LParen);
                                    if !self.at(TokenKind::RParen) {
                                        type_args.push(self.parse_expression());
                                    }
                                    self.expect(TokenKind::RParen);
                                } else if self.is_data_type_keyword() {
                                    // A builtin/keyword TYPE as a `#(...)` type
                                    // parameter arg (e.g. `uvm_resource#(int)`).
                                    // `parse_expression` can't represent a type
                                    // keyword — it yields an Empty expr, losing
                                    // the specialization — so capture the type's
                                    // leaf name as an Ident expression. Downstream
                                    // per-spec keying (type_bindings / current_spec)
                                    // then recovers the signature, matching the
                                    // expression-context `Specialization`'s
                                    // `type_args_text`. Class-name args already
                                    // parse as an Ident via `parse_expression`.
                                    let tok_text = self.current().text.clone();
                                    let tsp = self.current().span;
                                    let _dt = self.parse_data_type();
                                    let sp = self.span_from(start);
                                    let id = crate::ast::Identifier {
                                        name: tok_text,
                                        span: crate::ast::Span { start: tsp.start, end: tsp.end },
                                    };
                                    let hier = crate::ast::expr::HierarchicalIdentifier {
                                        root: None,
                                        path: vec![crate::ast::expr::HierPathSegment {
                                            name: id,
                                            selects: Vec::new(),
                                        }],
                                        span: sp,
                                        cached_signal_id: std::cell::Cell::new(None),
                                        cached_resolved_name: std::cell::OnceCell::new(),
                                    };
                                    type_args.push(crate::ast::expr::Expression::new(
                                        crate::ast::expr::ExprKind::Ident(hier),
                                        sp,
                                    ));
                                } else if self.at(TokenKind::KwVirtual)
                                    && (self.peek_kind() == TokenKind::KwInterface
                                        || self.peek_kind() == TokenKind::Identifier)
                                {
                                    // §25.9: `virtual <iface_type>` (or
                                    // `virtual interface <iface>`) as a
                                    // type-parameter argument, e.g.
                                    // `uvc_env#(virtual uvc_intf)`. Capture
                                    // the leaf as an Ident expression so
                                    // per-spec keying recovers the signature,
                                    // matching the builtin-keyword path above.
                                    let tok_text = self.current().text.clone(); // 'virtual'
                                    let tsp = self.current().span;
                                    let _dt = self.parse_data_type();
                                    let sp = self.span_from(start);
                                    let iface_name = self
                                        .tokens
                                        .get(self.pos - 1)
                                        .map(|t| t.text.clone())
                                        .unwrap_or_else(|| tok_text);
                                    let full_name = format!(
                                        "virtual {}",
                                        iface_name
                                    );
                                    let id = crate::ast::Identifier {
                                        name: full_name,
                                        span: crate::ast::Span { start: tsp.start, end: tsp.end },
                                    };
                                    let hier = crate::ast::expr::HierarchicalIdentifier {
                                        root: None,
                                        path: vec![crate::ast::expr::HierPathSegment {
                                            name: id,
                                            selects: Vec::new(),
                                        }],
                                        span: sp,
                                        cached_signal_id: std::cell::Cell::new(None),
                                        cached_resolved_name: std::cell::OnceCell::new(),
                                    };
                                    type_args.push(crate::ast::expr::Expression::new(
                                        crate::ast::expr::ExprKind::Ident(hier),
                                        sp,
                                    ));
                                } else {
                                    type_args.push(self.parse_expression());
                                }
                                if self.eat(TokenKind::Comma).is_none() { break; }
                            }
                        }
                        self.expect(TokenKind::RParen);
                    }
                }
        type_args
    }

    pub(super) fn parse_type_name(&mut self) -> TypeName {
        let start = self.current().span.start;
        let first = self.parse_identifier();
        if self.at(TokenKind::DoubleColon) {
            self.bump();
            let second = self.parse_identifier();
            TypeName { scope: Some(first), name: second, span: self.span_from(start) }
        } else {
            TypeName { scope: None, name: first, span: self.span_from(start) }
        }
    }

    /// Skip an optional inline `(* attr_spec *)` attribute. Used at points
    /// where the LRM grammar permits attribute_instance prefixes that the
    /// preprocessor's standalone-line stripper missed. Tolerates nested
    /// parens inside the attribute body.
    pub(super) fn skip_optional_attribute(&mut self) {
        if self.at(TokenKind::LParen) && self.peek_kind() == TokenKind::Star {
            self.bump(); // (
            self.bump(); // *
            // consume up to and including the closing *)
            while !self.at(TokenKind::Eof) {
                if self.at(TokenKind::Star) && self.peek_kind() == TokenKind::RParen {
                    self.bump(); self.bump();
                    break;
                }
                self.bump();
            }
        }
    }

    pub(super) fn parse_optional_signing(&mut self) -> Option<Signing> {
        match self.current_kind() {
            TokenKind::KwSigned => { self.bump(); Some(Signing::Signed) }
            TokenKind::KwUnsigned => { self.bump(); Some(Signing::Unsigned) }
            _ => None,
        }
    }

    pub(super) fn parse_optional_lifetime(&mut self) -> Option<Lifetime> {
        match self.current_kind() {
            TokenKind::KwStatic => { self.bump(); Some(Lifetime::Static) }
            TokenKind::KwAutomatic => { self.bump(); Some(Lifetime::Automatic) }
            _ => None,
        }
    }

    pub(super) fn parse_packed_dimensions(&mut self) -> Vec<PackedDimension> {
        let mut dims = Vec::new();
        while self.at(TokenKind::LBracket) {
            let start = self.current().span.start;
            self.bump();
            if self.at(TokenKind::RBracket) {
                self.bump();
                dims.push(PackedDimension::Unsized(self.span_from(start)));
            } else {
                let left = self.parse_expression();
                self.expect(TokenKind::Colon);
                let right = self.parse_expression();
                self.expect(TokenKind::RBracket);
                dims.push(PackedDimension::Range {
                    left: Box::new(left), right: Box::new(right),
                    span: self.span_from(start),
                });
            }
        }
        dims
    }

    pub(super) fn parse_unpacked_dimensions(&mut self) -> Vec<UnpackedDimension> {
        let mut dims = Vec::new();
        while self.at(TokenKind::LBracket) {
            let start = self.current().span.start;
            self.bump();
            if self.at(TokenKind::RBracket) {
                self.bump();
                dims.push(UnpackedDimension::Unsized(self.span_from(start)));
            } else if self.at(TokenKind::Dollar) {
                self.bump();
                let max_size = if self.eat(TokenKind::Colon).is_some() {
                    Some(Box::new(self.parse_expression()))
                } else { None };
                self.expect(TokenKind::RBracket);
                dims.push(UnpackedDimension::Queue { max_size, span: self.span_from(start) });
            } else if self.at(TokenKind::Star) {
                self.bump();
                self.expect(TokenKind::RBracket);
                dims.push(UnpackedDimension::Associative { data_type: None, span: self.span_from(start) });
            } else if self.is_associative_index_type_start() {
                // Associative arrays use a data type between brackets, but
                // scoped constants like [pkg::WIDTH-1:0] look similar at the
                // beginning. Only keep the associative parse if it closes the
                // bracket immediately; otherwise rewind and treat it as a
                // regular expression/range dimension.
                let save_pos = self.pos;
                let dt = self.parse_data_type();
                if self.at(TokenKind::RBracket) {
                    self.expect(TokenKind::RBracket);
                    dims.push(UnpackedDimension::Associative { data_type: Some(Box::new(dt)), span: self.span_from(start) });
                } else {
                    self.pos = save_pos;
                    let expr = self.parse_expression();
                    if self.eat(TokenKind::Colon).is_some() {
                        let right = self.parse_expression();
                        self.expect(TokenKind::RBracket);
                        dims.push(UnpackedDimension::Range {
                            left: Box::new(expr), right: Box::new(right),
                            span: self.span_from(start),
                        });
                    } else {
                        self.expect(TokenKind::RBracket);
                        dims.push(UnpackedDimension::Expression {
                            expr: Box::new(expr), span: self.span_from(start),
                        });
                    }
                }
            } else {
                let expr = self.parse_expression();
                if self.eat(TokenKind::Colon).is_some() {
                    let right = self.parse_expression();
                    self.expect(TokenKind::RBracket);
                    dims.push(UnpackedDimension::Range {
                        left: Box::new(expr), right: Box::new(right),
                        span: self.span_from(start),
                    });
                } else {
                    self.expect(TokenKind::RBracket);
                    dims.push(UnpackedDimension::Expression {
                        expr: Box::new(expr), span: self.span_from(start),
                    });
                }
            }
        }
        dims
    }

    fn is_associative_index_type_start(&self) -> bool {
        if self.is_data_type_keyword() {
            return true;
        }
        if !self.at(TokenKind::Identifier) {
            return false;
        }
        matches!(
            self.peek_kind(),
            TokenKind::RBracket | TokenKind::DoubleColon | TokenKind::Hash
        )
    }
fn parse_enum_type(&mut self) -> DataType {
    let start = self.current().span.start;
    self.expect(TokenKind::KwEnum);
    // Forward enum typedef `typedef enum name;` (§6.18): the identifier after
    // `enum` is the typedef NAME (left for the caller to consume), not a base
    // type or enum name. Return an empty enum without touching it.
    if self.at(TokenKind::Identifier)
        && matches!(self.peek_kind(), TokenKind::Semicolon | TokenKind::Comma) {
        return DataType::Enum(crate::ast::types::EnumType {
            base_type: None, members: Vec::new(), dimensions: Vec::new(), span: self.span_from(start),
        });
    }
    let base_type = if self.is_data_type_keyword() || self.at(TokenKind::Identifier) {
        // §6.19.1 (grammar A.2.2.1): `enum_base_type` may be a
        // `type_identifier`, and there is NO enum name between `enum` and `{`.
        // An identifier here was being discarded as a supposed "enum name", so
        // `typedef enum nib_t {A0,A1} e_t;` silently fell back to the 32-bit
        // int default — `$bits` read 32 instead of 4, and a signed base
        // (`enum sb_t {B0=-2,…}`) lost its sign so `e < 0` was false.
        Some(Box::new(self.parse_data_type()))
    } else { None };

    let _name = if self.at(TokenKind::Identifier) {
        Some(self.parse_identifier())
    } else { None };

    // Forward / bodyless enum typedef `typedef enum name;` (§6.18) — no member
    // list. (The forward name may have been consumed above as `base_type`;
    // harmless for a forward declaration.) Without this the member loop below
    // started on a non-`{` token and could spin without progress.
    if !self.at(TokenKind::LBrace) {
        return DataType::Enum(crate::ast::types::EnumType {
            base_type, members: Vec::new(), dimensions: Vec::new(), span: self.span_from(start),
        });
    }
    self.expect(TokenKind::LBrace);

        let mut members = Vec::new();
        loop {
            if self.at(TokenKind::RBrace) || self.at(TokenKind::Eof) { break; }
            let loop_start = self.pos;
            let mstart = self.current().span.start;
            let name = self.parse_identifier();
            // IEEE 1800-2017 §6.19 enum_name_declaration:
            //   identifier [ '[' integral_number [ ':' integral_number ] ']' ] [ '=' constant_expression ]
            // E.g. `ReqPeriResetIdx[0:1]` declares `ReqPeriResetIdx0` and
            // `ReqPeriResetIdx1`. We capture the range; downstream
            // elaboration can split it.
            // §6.19.1 enum name range. Two forms:
            //   name[N]      => N names, indices 0 .. N-1
            //   name[lo:hi]  => names indexed lo .. hi (inclusive, either dir)
            // Normalize the count form `[N]` to the inclusive range `[0 : N-1]`
            // so downstream expansion is uniform.
            let range = if self.eat(TokenKind::LBracket).is_some() {
                let first = self.parse_expression();
                let (lo, hi) = if self.eat(TokenKind::Colon).is_some() {
                    (first, self.parse_expression())
                } else {
                    let sp = first.span;
                    let zero = crate::ast::expr::Expression::new(
                        crate::ast::expr::ExprKind::Number(crate::ast::expr::NumberLiteral::Integer {
                            size: None, signed: false, base: crate::ast::expr::NumberBase::Decimal,
                            value: "0".to_string(), cached_val: std::cell::Cell::new(None) }), sp);
                    let one = crate::ast::expr::Expression::new(
                        crate::ast::expr::ExprKind::Number(crate::ast::expr::NumberLiteral::Integer {
                            size: None, signed: false, base: crate::ast::expr::NumberBase::Decimal,
                            value: "1".to_string(), cached_val: std::cell::Cell::new(None) }), sp);
                    let nminus1 = crate::ast::expr::Expression::new(
                        crate::ast::expr::ExprKind::Binary {
                            op: crate::ast::expr::BinaryOp::Sub,
                            left: Box::new(first), right: Box::new(one) }, sp);
                    (zero, nminus1)
                };
                self.expect(TokenKind::RBracket);
                Some((lo, hi))
            } else {
                None
            };
            let init = if self.eat(TokenKind::Assign).is_some() {
                Some(self.parse_expression())
            } else { None };
            members.push(crate::ast::types::EnumMember {
                name, range, init, span: self.span_from(mstart),
            });
            if self.pos == loop_start { self.bump(); } // defensive progress guard
            if self.eat(TokenKind::Comma).is_none() { break; }
        }
        self.expect(TokenKind::RBrace);

        // IEEE 1800-2017 §6.19:
        // - An enum name with x/z init requires a 4-state base type.
        // - An unassigned name following an x/z-init name is a syntax error
        //   (the auto-increment from an unknown is undefined).
        let base_is_two_state = match &base_type {
            Some(bt) => is_two_state_base(bt),
            None => true, // default base `int` is 2-state
        };
        for (idx, m) in members.iter().enumerate() {
            let has_xz = m.init.as_ref().map_or(false, expr_has_xz_literal);
            if has_xz && base_is_two_state {
                self.diagnostics.push(crate::diagnostics::Diagnostic::error(
                    format!("enum member '{}' has x/z in initializer but base type is 2-state", m.name.name),
                    m.span,
                ));
            }
            if has_xz {
                if let Some(next) = members.get(idx + 1) {
                    if next.init.is_none() {
                        self.diagnostics.push(crate::diagnostics::Diagnostic::error(
                            format!("enum member '{}' follows x/z-valued '{}' without an explicit initializer", next.name.name, m.name.name),
                            next.span,
                        ));
                    }
                }
            }
        }

        // §7.4.2: packed dims AFTER the body — `enum {...} [1:0] x;` is a
        // packed array of the enum (same as the struct body-suffix form).
        let dimensions = self.parse_packed_dimensions();
        DataType::Enum(crate::ast::types::EnumType {
            base_type, members, dimensions, span: self.span_from(start),
        })
    }

    fn parse_struct_type(&mut self) -> DataType {
        let start = self.current().span.start;
        let kind = if self.eat(TokenKind::KwUnion).is_some() {
            StructUnionKind::Union
        } else {
            self.expect(TokenKind::KwStruct);
            StructUnionKind::Struct
        };
        let tagged1 = self.eat(TokenKind::KwTagged).is_some();
        // §7.3.2 `union soft [packed]`. Gated on --sv2023 and on the aggregate
        // actually being a union: `struct soft` has no meaning, so leaving
        // `soft` unconsumed there lets the usual "unexpected token" diagnostic
        // fire rather than silently accepting it.
        let soft = crate::is_sv2023()
            && matches!(kind, StructUnionKind::Union)
            && self.eat(TokenKind::KwSoft).is_some();
        let packed = self.eat(TokenKind::KwPacked).is_some();
        let tagged2 = self.eat(TokenKind::KwTagged).is_some();
        let tagged = tagged1 || tagged2;
        let signing = self.parse_optional_signing();
        // Forward / bodyless `struct`/`union` — e.g. the forward typedef
        // `typedef union myu;` (IEEE 1800-2017 §6.18). With no `{`, there is no
        // member list: return an empty aggregate. Without this guard the member
        // loop below started at a non-`{` token (`expect(LBrace)` reports the
        // error but doesn't consume) and could spin without making progress,
        // pushing members until the process OOMs.
        if !self.at(TokenKind::LBrace) {
            return DataType::Struct(StructUnionType {
                kind, packed, tagged, soft, signing, members: Vec::new(),
                dimensions: Vec::new(),
                span: self.span_from(start),
            });
        }
        self.expect(TokenKind::LBrace);
        let mut members = Vec::new();
        while !self.at(TokenKind::RBrace) && !self.at(TokenKind::Eof) {
            let mstart = self.current().span.start;
            let loop_start_pos = self.pos;
            let rand_qualifier = match self.current_kind() {
                TokenKind::KwRand => { self.bump(); Some(RandQualifier::Rand) }
                TokenKind::KwRandc => { self.bump(); Some(RandQualifier::Randc) }
                _ => None,
            };
            let data_type = self.parse_data_type();
            let mut declarators = Vec::new();
            loop {
                let dstart = self.current().span.start;
                let name = self.parse_identifier();
                let dimensions = self.parse_unpacked_dimensions();
                let init = if self.eat(TokenKind::Assign).is_some() {
                    Some(self.parse_expression())
                } else { None };
                declarators.push(StructDeclarator { name, dimensions, init, span: self.span_from(dstart) });
                if self.eat(TokenKind::Comma).is_none() { break; }
            }
            self.expect(TokenKind::Semicolon);
            members.push(StructMember { rand_qualifier, data_type, declarators, span: self.span_from(mstart) });
            // Defensive: guarantee forward progress so a malformed body can
            // never spin this loop into an OOM.
            if self.pos == loop_start_pos { self.bump(); }
        }
        self.expect(TokenKind::RBrace);
        // Packed array dimensions after the body: `struct packed {...} [N-1:0] x;`
        let dimensions = self.parse_packed_dimensions();
        DataType::Struct(StructUnionType { kind, packed, tagged, soft, signing, members, dimensions, span: self.span_from(start) })
    }

    pub(super) fn parse_optional_direction(&mut self) -> Option<PortDirection> {
        match self.current_kind() {
            TokenKind::KwInput => { self.bump(); Some(PortDirection::Input) }
            TokenKind::KwOutput => { self.bump(); Some(PortDirection::Output) }
            TokenKind::KwInout => { self.bump(); Some(PortDirection::Inout) }
            TokenKind::KwRef => {
                self.bump();
                // IEEE 1800-2023 §13.5.2: `ref static` is a lifetime-pinned ref.
                // We accept the syntax and treat it as a normal ref; the static
                // guarantee is trivially satisfied for module-scope referents.
                if crate::is_sv2023() && self.current_kind() == TokenKind::KwStatic {
                    self.bump();
                }
                Some(PortDirection::Ref)
            }
            _ => None,
        }
    }

    pub(super) fn parse_optional_net_type(&mut self) -> Option<NetType> {
        match self.current_kind() {
            TokenKind::KwWire => { self.bump(); Some(NetType::Wire) }
            TokenKind::KwTri => { self.bump(); Some(NetType::Tri) }
            TokenKind::KwWand => { self.bump(); Some(NetType::Wand) }
            TokenKind::KwWor => { self.bump(); Some(NetType::Wor) }
            TokenKind::KwTriand => { self.bump(); Some(NetType::TriAnd) }
            TokenKind::KwTrior => { self.bump(); Some(NetType::TriOr) }
            TokenKind::KwTri0 => { self.bump(); Some(NetType::Tri0) }
            TokenKind::KwTri1 => { self.bump(); Some(NetType::Tri1) }
            TokenKind::KwSupply0 => { self.bump(); Some(NetType::Supply0) }
            TokenKind::KwSupply1 => { self.bump(); Some(NetType::Supply1) }
            TokenKind::KwTrireg => { self.bump(); Some(NetType::TriReg) }
            TokenKind::KwUwire => { self.bump(); Some(NetType::Uwire) }
            // §6.6.8 interconnect: a typeless net — declaration and port
            // forms both route through the normal net machinery; the
            // elaborator adopts the connected formal's type.
            TokenKind::KwInterconnect => { self.bump(); Some(NetType::Interconnect) }
            _ => None,
        }
    }

    pub(super) fn is_port_direction(&self) -> bool {
        matches!(self.current_kind(),
            TokenKind::KwInput | TokenKind::KwOutput | TokenKind::KwInout | TokenKind::KwRef)
    }
}

fn is_two_state_base(dt: &DataType) -> bool {
    match dt {
        DataType::IntegerVector { kind, .. } => matches!(kind, IntegerVectorType::Bit),
        DataType::IntegerAtom { kind, .. } => matches!(
            kind,
            IntegerAtomType::Byte | IntegerAtomType::ShortInt |
            IntegerAtomType::Int  | IntegerAtomType::LongInt
        ),
        DataType::Enum(e) => e.base_type.as_deref().map_or(true, is_two_state_base),
        _ => false,
    }
}

fn expr_has_xz_literal(e: &crate::ast::expr::Expression) -> bool {
    use crate::ast::expr::{ExprKind, NumberLiteral};
    match &e.kind {
        ExprKind::Number(NumberLiteral::Integer { value, .. }) =>
            value.chars().any(|c| matches!(c, 'x' | 'X' | 'z' | 'Z' | '?')),
        ExprKind::Number(NumberLiteral::UnbasedUnsized(c)) =>
            matches!(*c, 'x' | 'X' | 'z' | 'Z'),
        ExprKind::Unary { operand, .. } => expr_has_xz_literal(operand),
        ExprKind::Binary { left, right, .. } =>
            expr_has_xz_literal(left) || expr_has_xz_literal(right),
        ExprKind::Paren(inner) => expr_has_xz_literal(inner),
        ExprKind::Concatenation(items) => items.iter().any(expr_has_xz_literal),
        ExprKind::Replication { count, exprs } =>
            expr_has_xz_literal(count) || exprs.iter().any(expr_has_xz_literal),
        _ => false,
    }
}
