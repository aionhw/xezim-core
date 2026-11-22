use super::*;

impl<'a> Parser<'a> {
    pub(in crate::parse) fn parse_net_declaration(&mut self) -> NetDeclaration {
        let start = self.current_span().start;
        let net_type = self.parse_optional_net_type().unwrap_or(NetType::Wire);
        // §10.3.1: declaration assignments retain the same strength pair as
        // explicit continuous assignments, for resolution and `%v` reporting.
        let mut strength = None;
        if self.at(TokenKind::LParen) && self.peek_kind().is_strength_keyword() {
            self.bump();
            let mut parts = Vec::new();
            while !self.at(TokenKind::RParen) && !self.at(TokenKind::Eof) {
                let token = self.bump();
                if token.kind != TokenKind::Comma {
                    parts.push(self.token_text(token).into_owned());
                }
            }
            self.expect(TokenKind::RParen);
            strength = Some(parts.join(","));
        }
        // §6.9.2: optional `vectored` / `scalared` charge/drive qualifier
        // between the net type and the (optional) range — `tri1 vectored [15:0] a;`.
        if self.at(TokenKind::KwVectored) || self.at(TokenKind::KwScalared) {
            self.bump();
        }
        // §10.3.3: optional net delay `wire #10 w;` / `wire #(d1,d2) w;`.
        // The LRM places it after the data type (below); this position is
        // accepted too.
        let mut delay = self.parse_net_delay();
        let data_type = if self.is_data_type_keyword() {
            self.parse_data_type()
        }
        // User-defined typedef net type — `wire dword foo;`,
        // `wire word_t a, b;`, `wire pkg::t x;`, `wire t#(8) x;`. A bare
        // identifier followed by another identifier / `::` / `#` is a type
        // name, not the net name (mirrors the port path). `[` is excluded
        // to preserve `wire foo [3:0];` (unpacked net array named foo).
        else if self.at(TokenKind::Identifier)
            && matches!(
                self.peek_kind(),
                TokenKind::Identifier | TokenKind::DoubleColon | TokenKind::Hash
            )
        {
            self.parse_data_type()
        }
        // `wire word_t [1:0][7:0] x;` — identifier followed by packed dims
        // and THEN another identifier is a typedef'd net with packed
        // dimensions (§6.7.1). Distinguish from `wire foo [3:0];` (a net
        // NAMED foo with an unpacked dim) by looking past the balanced
        // bracket groups: an identifier there means the first token was a
        // type. This form used to be a hard parse error ("expected
        // Semicolon"), because the type name was taken as the declarator.
        else if self.at(TokenKind::Identifier) && self.peek_kind() == TokenKind::LBracket && {
            let mut p = self.pos + 1;
            while p < self.tokens.len() && self.tokens[p].kind == TokenKind::LBracket {
                let mut depth = 0usize;
                while p < self.tokens.len() {
                    match self.tokens[p].kind {
                        TokenKind::LBracket => depth += 1,
                        TokenKind::RBracket => {
                            depth -= 1;
                            if depth == 0 {
                                p += 1;
                                break;
                            }
                        }
                        _ => {}
                    }
                    p += 1;
                }
            }
            p < self.tokens.len() && self.tokens[p].kind == TokenKind::Identifier
        } {
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
        let data_type = self.wreal_data_type(net_type, data_type, wreal_span);
        // §6.7: `net_type data_type_or_implicit [delay3] list_of_net_decl_assignments`
        // — `wire [5:0] #1 w = a + b;`.
        if delay.0.is_none() {
            delay = self.parse_net_delay();
        }
        let declarators = self.parse_net_declarator_list();
        self.expect(TokenKind::Semicolon);
        let (delay, delay_fall, delay_off) = delay;
        NetDeclaration {
            net_type,
            strength,
            data_type,
            delay: delay.map(Box::new),
            delay_fall: delay_fall.map(Box::new),
            delay_off: delay_off.map(Box::new),
            declarators,
            span: self.span_from(start),
        }
    }

    /// Optional `#d` / `#(rise[, fall[, turn-off]])` net delay (§6.7.1,
    /// §28.16), as (rise, fall, turn-off). A min:typ:max value keeps typ.
    fn parse_net_delay(&mut self) -> (Option<Expression>, Option<Expression>, Option<Expression>) {
        if self.eat(TokenKind::Hash).is_none() {
            return (None, None, None);
        }
        if self.eat(TokenKind::LParen).is_none() {
            return (Some(self.parse_delay_value()), None, None);
        }
        let mut vals: Vec<Expression> = Vec::new();
        loop {
            let first = self.parse_expression();
            vals.push(self.parse_mintypmax_rest(first));
            if vals.len() == 3 || self.eat(TokenKind::Comma).is_none() {
                break;
            }
        }
        let mut depth = 1i32;
        while depth > 0 && !self.at(TokenKind::Eof) {
            match self.current_kind() {
                TokenKind::LParen => depth += 1,
                TokenKind::RParen => depth -= 1,
                _ => {}
            }
            self.bump();
        }
        let mut it = vals.into_iter();
        (it.next(), it.next(), it.next())
    }

    fn parse_net_declarator_list(&mut self) -> Vec<NetDeclarator> {
        let mut decls = Vec::new();
        loop {
            let start = self.current_span().start;
            let name = self.parse_identifier();
            let dimensions = self.parse_unpacked_dimensions();
            let init = if self.eat(TokenKind::Assign).is_some() {
                Some(self.parse_expression())
            } else {
                None
            };
            decls.push(NetDeclarator {
                decl: crate::ast::binding::Bound::UNSET,
                name,
                dimensions,
                init: init.map(Box::new),
                span: self.span_from(start),
            });
            if self.eat(TokenKind::Comma).is_none() {
                break;
            }
        }
        compact_syntax_list(decls)
    }

    pub(super) fn parse_gate_instantiation(&mut self) -> GateInstantiation {
        let start = self.current_span().start;
        let gate_type = match self.current_kind() {
            TokenKind::KwAnd => GateType::And,
            TokenKind::KwNand => GateType::Nand,
            TokenKind::KwOr => GateType::Or,
            TokenKind::KwNor => GateType::Nor,
            TokenKind::KwXor => GateType::Xor,
            TokenKind::KwXnor => GateType::Xnor,
            TokenKind::KwBuf => GateType::Buf,
            TokenKind::KwNot => GateType::Not,
            TokenKind::KwBufif0 => GateType::Bufif0,
            TokenKind::KwBufif1 => GateType::Bufif1,
            TokenKind::KwNotif0 => GateType::Notif0,
            TokenKind::KwNotif1 => GateType::Notif1,
            TokenKind::KwNmos => GateType::Nmos,
            TokenKind::KwPmos => GateType::Pmos,
            TokenKind::KwCmos => GateType::Cmos,
            TokenKind::KwRnmos => GateType::Rnmos,
            TokenKind::KwRpmos => GateType::Rpmos,
            TokenKind::KwRcmos => GateType::Rcmos,
            TokenKind::KwTran => GateType::Tran,
            TokenKind::KwRtran => GateType::Rtran,
            TokenKind::KwTranif0 => GateType::Tranif0,
            TokenKind::KwTranif1 => GateType::Tranif1,
            TokenKind::KwRtranif0 => GateType::Rtranif0,
            TokenKind::KwRtranif1 => GateType::Rtranif1,
            TokenKind::KwPullup => GateType::Pullup,
            TokenKind::KwPulldown => GateType::Pulldown,
            _ => GateType::And,
        };
        self.bump();
        // Optional drive_strength `(strong0, strong1)` / charge_strength
        // `(small)` / pull strength `(pull1)` (§28.4). xezim doesn't model
        // strengths; consume the group when it opens with a strength keyword.
        if self.at(TokenKind::LParen) && self.peek_kind().is_strength_keyword() {
            self.bump(); // (
            while !self.at(TokenKind::RParen) && !self.at(TokenKind::Eof) {
                self.bump();
            }
            self.expect(TokenKind::RParen);
        }
        // Optional `#(delay)` or `#delay` spec between the gate keyword and
        // the first instance: `buf #(D) name (...)`. §28.11: the list is
        // `(rise, fall, turn-off)` for a delay3 primitive.
        let mut delay: Option<Expression> = None;
        let mut delay_fall: Option<Expression> = None;
        let mut delay_off = None;
        if self.eat(TokenKind::Hash).is_some() {
            if self.eat(TokenKind::LParen).is_some() {
                let rise = self.parse_expression();
                delay = Some(self.parse_mintypmax_rest(rise));
                if self.eat(TokenKind::Comma).is_some() {
                    let fall = self.parse_expression();
                    delay_fall = Some(self.parse_mintypmax_rest(fall));
                    if self.eat(TokenKind::Comma).is_some() {
                        let off = self.parse_expression();
                        delay_off = Some(self.parse_mintypmax_rest(off));
                    }
                }
                let mut depth = 1;
                while depth > 0 && !self.at(TokenKind::Eof) {
                    match self.current_kind() {
                        TokenKind::LParen => {
                            depth += 1;
                            self.bump();
                        }
                        TokenKind::RParen => {
                            depth -= 1;
                            self.bump();
                        }
                        _ => {
                            self.bump();
                        }
                    }
                }
            } else {
                delay = Some(self.parse_delay_value());
            }
        }
        let mut instances = Vec::new();
        loop {
            let istart = self.current_span().start;
            let name = if self.at(TokenKind::Identifier) {
                Some(self.parse_identifier())
            } else {
                None
            };
            let _dims = self.parse_unpacked_dimensions(); // Gates can have arrays too
            let mut terminals = Vec::new();
            self.expect(TokenKind::LParen);
            loop {
                terminals.push(self.parse_expression());
                if self.eat(TokenKind::Comma).is_none() {
                    break;
                }
            }
            self.expect(TokenKind::RParen);
            instances.push(GateInstance {
                name,
                terminals,
                span: self.span_from(istart),
            });
            if self.eat(TokenKind::Comma).is_none() {
                break;
            }
        }
        self.expect(TokenKind::Semicolon);
        GateInstantiation {
            gate_type,
            delay,
            delay_fall,
            delay_off,
            instances,
            span: self.span_from(start),
        }
    }
}
