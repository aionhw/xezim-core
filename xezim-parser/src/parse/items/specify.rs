use super::*;

impl<'a> Parser<'a> {
    /// Parse the simple specify module path `( src => dst ) = ( d {, d} ) ;`
    /// (or `... = d ;`) with plain-identifier endpoints. Returns the path's
    /// first delay as its `delay`. Returns None and rewinds for any other
    /// form (edge-sensitive `( posedge a => ...)`, `*>`, conditional, bit-
    /// selected endpoints, timing checks) so the caller skips it.
    /// System-task names whose argument list carries `delayed_reference` /
    /// `delayed_data` output nets (IEEE 1364 §15.6).
    pub(super) fn is_timing_check_name(name: &str) -> bool {
        matches!(
            name,
            "$setuphold" | "$recrem" | "$setup" | "$hold" | "$recovery" | "$removal"
        )
    }

    /// IEEE 1800-2017 §31 timing check system tasks.
    pub(super) fn is_timing_check_task(name: &str) -> bool {
        matches!(
            name,
            "$setup"
                | "$hold"
                | "$setuphold"
                | "$recovery"
                | "$removal"
                | "$recrem"
                | "$skew"
                | "$timeskew"
                | "$fullskew"
                | "$period"
                | "$width"
                | "$nochange"
        )
    }

    /// Parse a §31 timing check `$name ( arg {, arg} ) ;` into its argument
    /// list, consuming through the `;`. Each argument is split out at the
    /// top-level commas and parsed on its own (see `parse_timing_check_arg`);
    /// an argument that does not parse becomes `None`, like an omitted one.
    /// Returns None (after skipping the item) when the list is malformed.
    pub(super) fn parse_timing_check(&mut self) -> Option<TimingCheck> {
        let start = self.current_span().start;
        let name_tok = self.bump();
        let name = self.token_text(name_tok).into_owned();
        if !self.at(TokenKind::LParen) {
            self.skip_to_semi();
            return None;
        }
        self.bump();
        let mut ranges: Vec<(usize, usize)> = Vec::new();
        let mut arg_start = self.pos;
        let mut depth = 0i32;
        loop {
            match self.current_kind() {
                TokenKind::Eof | TokenKind::KwEndspecify => return None,
                TokenKind::Semicolon if depth == 0 => {
                    self.bump();
                    return None;
                }
                TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace => depth += 1,
                TokenKind::RParen if depth == 0 => {
                    ranges.push((arg_start, self.pos));
                    self.bump();
                    break;
                }
                TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace => depth -= 1,
                TokenKind::Comma if depth == 0 => {
                    ranges.push((arg_start, self.pos));
                    self.bump();
                    arg_start = self.pos;
                    continue;
                }
                _ => {}
            }
            self.bump();
        }
        self.eat(TokenKind::Semicolon);
        let span = self.span_from(start);
        let args = ranges
            .into_iter()
            .map(|(a, b)| {
                let arg_toks: Vec<Token> = (a..b).map(|i| self.tokens[i]).collect();
                Self::parse_timing_check_arg(&self.tokens, &arg_toks)
            })
            .collect();
        Some(TimingCheck { name, args, span })
    }

    /// One timing check argument (§31.2 `timing_check_event` or a plain
    /// expression): `[posedge | negedge | edge [descriptors]] terminal
    /// [&&& condition]`. `&&&` lexes as `&&` followed by `&`. A limit may be a
    /// `min:typ:max` triplet, resolved by `+mindelays/+typdelays/+maxdelays`.
    fn parse_timing_check_arg(
        stream: &TokenStream<'a>,
        toks: &[Token],
    ) -> Option<TimingCheckArg> {
        if toks.is_empty() {
            return None;
        }
        let text = Self::tokens_source_text(stream, toks);
        let mut i = 0usize;
        let mut edges = None;
        match toks[0].kind {
            TokenKind::KwPosedge => {
                edges = Some(TIMING_POSEDGE);
                i = 1;
            }
            TokenKind::KwNegedge => {
                edges = Some(TIMING_NEGEDGE);
                i = 1;
            }
            TokenKind::KwEdge => {
                i = 1;
                if toks.get(1).map(|t| t.kind) == Some(TokenKind::LBracket) {
                    let close = toks.iter().position(|t| t.kind == TokenKind::RBracket)?;
                    let mut mask = 0u16;
                    for desc in toks[2..close].split(|t| t.kind == TokenKind::Comma) {
                        let d: String = desc
                            .iter()
                            .map(|&t| stream.text(t).to_ascii_lowercase())
                            .collect();
                        let level = |c: char| match c {
                            '0' => Some(0u8),
                            '1' => Some(1u8),
                            'x' | 'z' => Some(2u8),
                            _ => None,
                        };
                        let mut cs = d.chars();
                        let (Some(from), Some(to), None) = (
                            cs.next().and_then(level),
                            cs.next().and_then(level),
                            cs.next(),
                        ) else {
                            return None;
                        };
                        if from == to {
                            return None;
                        }
                        mask |= timing_edge_bit(from, to);
                    }
                    edges = Some(mask);
                    i = close + 1;
                } else {
                    edges = Some(TIMING_POSEDGE | TIMING_NEGEDGE);
                }
            }
            _ => {}
        }
        let mut depth = 0i32;
        let mut split = None;
        for k in i..toks.len() {
            match toks[k].kind {
                TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace => depth += 1,
                TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace => depth -= 1,
                TokenKind::LogAnd
                    if depth == 0 && toks.get(k + 1).map(|t| t.kind) == Some(TokenKind::BitAnd) =>
                {
                    split = Some(k);
                    break;
                }
                _ => {}
            }
        }
        let (expr_toks, cond) = match split {
            Some(k) => (
                &toks[i..k],
                Some(Self::parse_token_expr(stream, &toks[k + 2..])?),
            ),
            None => (&toks[i..], None),
        };
        let expr = Self::parse_token_expr(stream, Self::select_mintypmax(expr_toks))?;
        Some(TimingCheckArg {
            edges,
            expr,
            cond,
            text,
        })
    }

    /// Pick the `+mindelays/+typdelays/+maxdelays` element of a `min:typ:max`
    /// token run (optionally parenthesized); any other run is returned whole.
    fn select_mintypmax(toks: &[Token]) -> &[Token] {
        let inner = if toks.len() >= 2
            && toks[0].kind == TokenKind::LParen
            && toks[toks.len() - 1].kind == TokenKind::RParen
        {
            &toks[1..toks.len() - 1]
        } else {
            toks
        };
        let mut depth = 0i32;
        let mut colons = Vec::new();
        for (k, t) in inner.iter().enumerate() {
            match t.kind {
                TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace => depth += 1,
                TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace => depth -= 1,
                TokenKind::Question if depth == 0 => return toks,
                TokenKind::Colon if depth == 0 => colons.push(k),
                _ => {}
            }
        }
        if colons.len() != 2 {
            return toks;
        }
        match crate::delay_select() {
            0 => &inner[..colons[0]],
            2 => &inner[colons[1] + 1..],
            _ => &inner[colons[0] + 1..colons[1]],
        }
    }

    /// Parse a complete expression from a token run with a private parser, so
    /// a run that is not one expression is rejected without diagnostics.
    fn parse_token_expr(stream: &TokenStream<'a>, toks: &[Token]) -> Option<Expression> {
        if toks.is_empty() {
            return None;
        }
        let end = stream.span(toks[toks.len() - 1]).end;
        let sub = stream.sub_stream_with_eof(toks, end);
        let mut p = super::Parser::new_sub(sub);
        let e = p.parse_expression();
        (p.at(TokenKind::Eof) && !p.has_errors()).then_some(e)
    }

    /// Token texts joined with a single space wherever the source had one.
    fn tokens_source_text(stream: &TokenStream<'a>, toks: &[Token]) -> String {
        let mut s = String::new();
        for (k, &t) in toks.iter().enumerate() {
            if k > 0 && stream.span(toks[k - 1]).end < stream.span(t).start {
                s.push(' ');
            }
            s.push_str(&stream.text(t));
        }
        s
    }

    /// Parse a `$setuphold(...)` / `$recrem(...)` timing check ONLY to recover
    /// its delayed nets. The full arg list is `(ref_event, data_event, limit1,
    /// limit2, [notifier], [tstamp], [tcheck], [delayed_ref], [delayed_data])`;
    /// only `$setuphold`/`$recrem` carry the two delayed-net outputs (args 8,9).
    /// We split on top-level commas, take the reference/data SIGNAL from the
    /// first two edge-event args, and pair each present delayed net with its
    /// source signal → `(delayed_ref, ref_sig)`, `(delayed_data, data_sig)`.
    /// Everything is then consumed to the terminating `;`.
    pub(super) fn parse_timing_check_delayed_nets(&mut self, out: &mut Vec<(String, String)>) {
        let is_recrem_or_setuphold =
            matches!(self.current_text().as_ref(), "$setuphold" | "$recrem");
        self.bump(); // the $name
        if !self.at(TokenKind::LParen) {
            self.skip_to_semi();
            return;
        }
        self.bump(); // '('
        // Collect each top-level (paren-depth-0) comma-separated arg as the
        // list of its tokens' texts, plus whether it began with posedge/negedge.
        let mut args: Vec<Vec<String>> = Vec::new();
        let mut cur: Vec<String> = Vec::new();
        let mut depth = 0i32;
        while !self.at(TokenKind::Eof) {
            match self.current_kind() {
                TokenKind::LParen => {
                    depth += 1;
                    let tok = self.bump();
                    cur.push(self.token_text(tok).into_owned());
                }
                TokenKind::RParen => {
                    if depth == 0 {
                        self.bump(); // closing ')'
                        break;
                    }
                    depth -= 1;
                    let tok = self.bump();
                    cur.push(self.token_text(tok).into_owned());
                }
                TokenKind::Comma if depth == 0 => {
                    self.bump();
                    args.push(std::mem::take(&mut cur));
                }
                _ => {
                    let tok = self.bump();
                    cur.push(self.token_text(tok).into_owned());
                }
            }
        }
        args.push(cur);
        self.eat(TokenKind::Semicolon);

        // The SIGNAL of an edge-event arg is the first identifier after a
        // posedge/negedge (or the first identifier); a `&&& cond` tail is
        // ignored. A plain delayed-net arg is a single identifier.
        fn signal_of(arg: &[String]) -> Option<String> {
            let mut it = arg.iter();
            while let Some(t) = it.next() {
                if t == "posedge" || t == "negedge" || t == "edge" {
                    if let Some(n) = it.next() {
                        return Some(n.clone());
                    }
                }
            }
            // no edge keyword: first identifier-looking token
            arg.iter()
                .find(|t| {
                    t.chars()
                        .next()
                        .map(|c| c.is_alphabetic() || c == '_')
                        .unwrap_or(false)
                })
                .cloned()
        }
        fn plain_net(arg: &[String]) -> Option<String> {
            let toks: Vec<&String> = arg.iter().filter(|t| !t.trim().is_empty()).collect();
            if toks.len() == 1
                && toks[0]
                    .chars()
                    .next()
                    .map(|c| c.is_alphabetic() || c == '_')
                    .unwrap_or(false)
            {
                Some(toks[0].clone())
            } else {
                None
            }
        }

        // Two-limit checks ($setuphold/$recrem) carry delayed_ref/delayed_data
        // at args[7]/[8] (§15.6 13-arg form); single-limit checks ($setup/
        // $hold/$recovery/$removal) at args[6]/[7] in the vendor-extension
        // 8-arg form `(ref, data, limit, notifier, tstamp_cond, tcheck_cond,
        // delayed_ref, delayed_data)` that gate libraries wire UDP terminals
        // from. Short (LRM-minimal) forms have no delayed nets.
        let (dref_idx, ddata_idx) = if is_recrem_or_setuphold {
            (7, 8)
        } else {
            (6, 7)
        };
        if args.len() <= dref_idx {
            return;
        }
        let ref_sig = signal_of(&args[0]);
        let data_sig = signal_of(&args[1]);
        if let (Some(dref), Some(src)) = (plain_net(&args[dref_idx]), ref_sig) {
            out.push((dref, src));
        }
        if let Some(a) = args.get(ddata_idx) {
            if let (Some(ddata), Some(src)) = (plain_net(a), data_sig) {
                out.push((ddata, src));
            }
        }
    }

    /// §30.4 module path declaration: parallel `=>` or full `*>`, with an
    /// optional polarity, edge identifier and data source (§30.4.3), under an
    /// optional `if (cond)` / `ifnone` (§30.4.4), and a delay list of 1, 2,
    /// 3, 6 or 12 values (§30.5.1) with or without parentheses. Each value
    /// may be a min:typ:max triplet — the element chosen by
    /// `+mindelays`/`+typdelays`/`+maxdelays` (default typ) is kept. Returns
    /// `None` (position restored) for anything else, which the caller skips.
    pub(super) fn try_parse_specify_path(&mut self) -> Option<SpecifyPath> {
        let start_pos = self.pos;
        let diag_len = self.diagnostics.len();
        let sp_start = self.current_span().start;
        let p = self.parse_specify_path_inner(sp_start);
        if p.is_none() || self.diagnostics.len() != diag_len {
            self.diagnostics.truncate(diag_len);
            self.pos = start_pos;
            return None;
        }
        p
    }

    fn parse_specify_path_inner(&mut self, sp_start: usize) -> Option<SpecifyPath> {
        let mut cond = None;
        let mut ifnone = false;
        if self.eat(TokenKind::KwIf).is_some() {
            self.eat(TokenKind::LParen)?;
            cond = Some(self.parse_expression());
            self.eat(TokenKind::RParen)?;
        } else if self.eat(TokenKind::KwIfnone).is_some() {
            ifnone = true;
        }
        self.eat(TokenKind::LParen)?;
        let edge = matches!(
            self.current_kind(),
            TokenKind::KwPosedge | TokenKind::KwNegedge | TokenKind::KwEdge
        );
        if edge {
            self.bump();
        }
        let srcs = self.parse_specify_terminals()?;
        // Parallel `=>` or full `*>` connection with optional polarity (a
        // per-net delay model needs neither). The lexer splits `+=>` into
        // `+=` `>` and `*>` into `*` `>`.
        if matches!(
            self.current_kind(),
            TokenKind::PlusAssign | TokenKind::MinusAssign
        ) {
            self.bump();
            self.eat(TokenKind::Gt)?;
        } else {
            if matches!(self.current_kind(), TokenKind::Plus | TokenKind::Minus) {
                self.bump();
            }
            if self.at(TokenKind::FatArrow) && self.current_text() == "=>" {
                self.bump();
            } else if self.at(TokenKind::Star) && self.peek_kind() == TokenKind::Gt {
                self.bump();
                self.bump();
            } else {
                return None;
            }
        }
        let dsts = if self.eat(TokenKind::LParen).is_some() {
            // Edge-sensitive `( dst [+|-] : data_source )`.
            let dsts = self.parse_specify_terminals()?;
            match self.current_kind() {
                TokenKind::PlusColon | TokenKind::MinusColon | TokenKind::Colon => {
                    self.bump();
                }
                TokenKind::Plus | TokenKind::Minus if self.peek_kind() == TokenKind::Colon => {
                    self.bump();
                    self.bump();
                }
                _ => return None,
            }
            let _ = self.parse_expression();
            self.eat(TokenKind::RParen)?;
            dsts
        } else {
            self.parse_specify_terminals()?
        };
        self.eat(TokenKind::RParen)?;
        self.eat(TokenKind::Assign)?;
        let delays = self.parse_path_delay_value()?;
        self.eat(TokenKind::Semicolon)?;
        Some(SpecifyPath {
            srcs,
            dsts,
            cond,
            ifnone,
            delays,
            span: self.span_from(sp_start),
        })
    }

    /// `name [ [range] ] {, name [ [range] ]}` — the base names; a bit or
    /// part select only narrows the path to part of the net.
    fn parse_specify_terminals(&mut self) -> Option<Vec<Identifier>> {
        let mut out = Vec::new();
        loop {
            if !matches!(
                self.current_kind(),
                TokenKind::Identifier | TokenKind::EscapedIdentifier
            ) {
                return None;
            }
            out.push(self.parse_identifier());
            if self.eat(TokenKind::LBracket).is_some() {
                let _ = self.parse_expression();
                if matches!(
                    self.current_kind(),
                    TokenKind::Colon | TokenKind::PlusColon | TokenKind::MinusColon
                ) {
                    self.bump();
                    let _ = self.parse_expression();
                }
                self.eat(TokenKind::RBracket)?;
            }
            if self.eat(TokenKind::Comma).is_none() {
                return Some(out);
            }
        }
    }

    /// §30.5.1 `path_delay_value`: a list of delay values, parenthesized or
    /// not. A parenthesized form followed by anything but `;` was a bare
    /// expression that merely starts with `(`.
    fn parse_path_delay_value(&mut self) -> Option<Vec<Expression>> {
        let entry = |p: &mut Self| -> Expression {
            let first = p.parse_expression();
            if !p.at(TokenKind::Colon) {
                return first;
            }
            p.bump();
            let typ = p.parse_expression();
            let max = if p.at(TokenKind::Colon) {
                p.bump();
                Some(p.parse_expression())
            } else {
                None
            };
            match crate::delay_select() {
                0 => first,
                2 => max.unwrap_or(typ),
                _ => typ,
            }
        };
        let list = |p: &mut Self| -> Vec<Expression> {
            let mut v = vec![entry(p)];
            while p.eat(TokenKind::Comma).is_some() {
                v.push(entry(p));
            }
            v
        };
        let start = self.pos;
        if self.eat(TokenKind::LParen).is_some() {
            let v = list(self);
            if self.eat(TokenKind::RParen).is_some() && self.at(TokenKind::Semicolon) {
                return Some(v);
            }
            self.pos = start;
        }
        Some(list(self))
    }
}
