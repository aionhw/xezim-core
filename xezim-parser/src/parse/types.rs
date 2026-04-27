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
                                } else {
                                    type_args.push(self.parse_expression());
                                }
                                if self.eat(TokenKind::Comma).is_none() { break; }
                            }
                        }
                        self.expect(TokenKind::RParen);
                    }
                }
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
            _ => DataType::Implicit { signing: None, dimensions: Vec::new(), span: self.span_from(start) }
        }
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
    let base_type = if self.is_data_type_keyword() || self.at(TokenKind::Identifier) {
        if self.at(TokenKind::Identifier) && self.peek_kind() == TokenKind::LBrace {
            // This is the enum name, not a base type
            None
        } else {
            Some(Box::new(self.parse_data_type()))
        }
    } else { None };

    let _name = if self.at(TokenKind::Identifier) {
        Some(self.parse_identifier())
    } else { None };

    self.expect(TokenKind::LBrace);

        let mut members = Vec::new();
        loop {
            if self.at(TokenKind::RBrace) || self.at(TokenKind::Eof) { break; }
            let mstart = self.current().span.start;
            let name = self.parse_identifier();
            let init = if self.eat(TokenKind::Assign).is_some() {
                Some(self.parse_expression())
            } else { None };
            members.push(crate::ast::types::EnumMember {
                name, range: None, init, span: self.span_from(mstart),
            });
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

        DataType::Enum(crate::ast::types::EnumType {
            base_type, members, span: self.span_from(start),
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
        let packed = self.eat(TokenKind::KwPacked).is_some();
        let tagged2 = self.eat(TokenKind::KwTagged).is_some();
        let tagged = tagged1 || tagged2;
        let signing = self.parse_optional_signing();
        self.expect(TokenKind::LBrace);
        let mut members = Vec::new();
        while !self.at(TokenKind::RBrace) && !self.at(TokenKind::Eof) {
            let mstart = self.current().span.start;
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
        }
        self.expect(TokenKind::RBrace);
        DataType::Struct(StructUnionType { kind, packed, tagged, signing, members, span: self.span_from(start) })
    }

    pub(super) fn parse_optional_direction(&mut self) -> Option<PortDirection> {
        match self.current_kind() {
            TokenKind::KwInput => { self.bump(); Some(PortDirection::Input) }
            TokenKind::KwOutput => { self.bump(); Some(PortDirection::Output) }
            TokenKind::KwInout => { self.bump(); Some(PortDirection::Inout) }
            TokenKind::KwRef => { self.bump(); Some(PortDirection::Ref) }
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
