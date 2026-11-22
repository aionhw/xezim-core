use super::*;

impl<'a> Parser<'a> {
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
                    if depth == 0 {
                        break;
                    }
                    depth -= 1;
                }
                TokenKind::Semicolon if depth == 0 => break,
                _ => {}
            }
            self.bump();
        }
    }

    /// §19.5.2 trans_set: `trans_range_list { => trans_range_list }`.
    fn parse_trans_set(&mut self) -> Vec<crate::ast::decl::TransStep> {
        use crate::ast::decl::{TransRepeat, TransRepeatKind, TransStep};
        let mut steps = Vec::new();
        loop {
            let mut values = vec![self.parse_constraint_range()];
            while self.eat(TokenKind::Comma).is_some() {
                values.push(self.parse_constraint_range());
            }
            let mut repeat = None;
            // The expression parser folds a trailing `v [-> n]` into its SVA
            // repetition marker; unwrap it into the step's repetition.
            if let Some(crate::ast::decl::ConstraintRange::Value(e)) = values.last_mut() {
                if let crate::ast::expr::ExprKind::SystemCall { name, args } = &mut e.kind {
                    let kind = match name.as_str() {
                        "$sva_rep_consec" => Some(TransRepeatKind::Consecutive),
                        "$sva_rep_goto" => Some(TransRepeatKind::Goto),
                        "$sva_rep_noncon" => Some(TransRepeatKind::NonConsecutive),
                        _ => None,
                    };
                    if let (Some(kind), 3) = (kind, args.len()) {
                        let hi = args.pop();
                        let lo = args.pop().unwrap();
                        let operand = args.pop().unwrap();
                        *e = operand;
                        repeat = Some(TransRepeat { kind, lo, hi });
                    }
                }
            }
            if repeat.is_none() && self.at(TokenKind::LBracket) {
                self.bump();
                let kind = match self.current_kind() {
                    TokenKind::Star => Some(TransRepeatKind::Consecutive),
                    TokenKind::Arrow => Some(TransRepeatKind::Goto),
                    TokenKind::Assign => Some(TransRepeatKind::NonConsecutive),
                    _ => None,
                };
                match kind {
                    Some(kind) => {
                        self.bump();
                        let lo = self.parse_expression();
                        let hi = if self.eat(TokenKind::Colon).is_some() {
                            Some(self.parse_expression())
                        } else {
                            None
                        };
                        repeat = Some(TransRepeat { kind, lo, hi });
                    }
                    None => self.error("expected [*, [-> or [= in a transition"),
                }
                self.expect(TokenKind::RBracket);
            }
            steps.push(TransStep { values, repeat });
            if self.eat(TokenKind::FatArrow).is_none() {
                break;
            }
        }
        steps
    }

    /// §19.6.1 select_expression, `||` level.
    /// §19.6.1.4: a cross bin given as a list of value tuples,
    /// `'{'{1,2}, '{3,4}}`, one value per crossed item in order: the product
    /// bins holding one of the tuples, i.e. the `||` over the tuples of the
    /// `&&` of `binsof(item) intersect {value}` (#651).
    fn cross_tuple_select(
        &mut self,
        set: &Expression,
        items: &[Identifier],
    ) -> crate::ast::decl::CrossSelect {
        use crate::ast::decl::{ConstraintRange, CrossSelect};
        let tuples: Option<Vec<Vec<Expression>>> = match &set.kind {
            ExprKind::AssignmentPattern(list) => list
                .iter()
                .map(|t| match t {
                    AssignmentPatternItem::Ordered(e) => match &e.kind {
                        ExprKind::AssignmentPattern(vals) => vals
                            .iter()
                            .map(|v| match v {
                                AssignmentPatternItem::Ordered(x) => Some(x.clone()),
                                _ => None,
                            })
                            .collect(),
                        _ => None,
                    },
                    _ => None,
                })
                .collect(),
            _ => None,
        };
        let Some(tuples) = tuples else {
            self.diagnostics.push(crate::diagnostics::Diagnostic::error(
                "a cross bin's tuple list is an ordered list of ordered tuples, \
                 '{'{v1, v2}, ...} (IEEE 1800-2023 §19.6.1.4)",
                set.span,
            ));
            return CrossSelect::All;
        };
        let mut any: Option<CrossSelect> = None;
        for t in tuples {
            if t.len() != items.len() {
                self.diagnostics.push(crate::diagnostics::Diagnostic::error(
                    format!(
                        "a tuple of {} values for a cross of {} items (IEEE 1800-2023 §19.6.1.4)",
                        t.len(),
                        items.len()
                    ),
                    set.span,
                ));
                continue;
            }
            let mut all: Option<CrossSelect> = None;
            for (cp, v) in items.iter().zip(t) {
                let term = CrossSelect::Binsof {
                    cp: cp.clone(),
                    bin: None,
                    intersect: Some(vec![ConstraintRange::Value(v)]),
                };
                all = Some(match all {
                    Some(a) => CrossSelect::And(Box::new(a), Box::new(term)),
                    None => term,
                });
            }
            if let Some(all) = all {
                any = Some(match any {
                    Some(a) => CrossSelect::Or(Box::new(a), Box::new(all)),
                    None => all,
                });
            }
        }
        // An empty list selects no product bin.
        any.unwrap_or_else(|| CrossSelect::Not(Box::new(CrossSelect::All)))
    }

    /// §19.6.1 `bins_expression`: `cp` or `cp.bin`. With the cross
    /// hierarchical item relaxation, a dotted name that the standard form
    /// can't read and that is one of the cross's items names that item, and
    /// one whose prefix is one of them names that item and a bin.
    fn parse_binsof_bins_expression(
        &mut self,
    ) -> (crate::ast::Identifier, Option<crate::ast::Identifier>) {
        let mut cp = self.parse_identifier();
        let mut segs = Vec::new();
        while self.eat(TokenKind::Dot).is_some() {
            segs.push(self.parse_identifier());
            if !crate::RELAX_CROSS_HIER_ITEM.get() {
                break;
            }
        }
        let path = |segs: &[crate::ast::Identifier]| {
            segs.iter()
                .fold(cp.name.clone(), |n, s| format!("{n}.{}", s.name))
        };
        let is_item = |n: String| self.cross_items.contains(&n);
        // `cp.bin` keeps its standard meaning whenever `cp` is a cross item.
        let bin = match segs.len() {
            0 => None,
            1 if !crate::RELAX_CROSS_HIER_ITEM.get()
                || is_item(cp.name.clone())
                || !is_item(path(&segs)) =>
            {
                segs.pop()
            }
            n if n > 1 && !is_item(path(&segs)) && is_item(path(&segs[..n - 1])) => segs.pop(),
            _ => None,
        };
        if let Some(last) = segs.last() {
            let name = path(&segs);
            cp.name = name;
            cp.span = crate::ast::Span::new(cp.span.start, last.span.end);
        }
        (cp, bin)
    }

    fn parse_cross_select_or(&mut self) -> crate::ast::decl::CrossSelect {
        let mut l = self.parse_cross_select_and();
        while self.eat(TokenKind::LogOr).is_some() {
            let r = self.parse_cross_select_and();
            l = crate::ast::decl::CrossSelect::Or(Box::new(l), Box::new(r));
        }
        l
    }

    fn parse_cross_select_and(&mut self) -> crate::ast::decl::CrossSelect {
        let mut l = self.parse_cross_select_with();
        while self.eat(TokenKind::LogAnd).is_some() {
            let r = self.parse_cross_select_with();
            l = crate::ast::decl::CrossSelect::And(Box::new(l), Box::new(r));
        }
        l
    }

    fn parse_cross_select_with(&mut self) -> crate::ast::decl::CrossSelect {
        let mut s = self.parse_cross_select_primary();
        while self.eat(TokenKind::KwWith).is_some() {
            self.expect(TokenKind::LParen);
            let e = self.parse_expression();
            self.expect(TokenKind::RParen);
            if self.eat(TokenKind::KwMatches).is_some() {
                let _ = self.parse_expression();
            }
            s = crate::ast::decl::CrossSelect::With(Box::new(s), e);
        }
        s
    }

    fn parse_cross_select_primary(&mut self) -> crate::ast::decl::CrossSelect {
        use crate::ast::decl::CrossSelect;
        if self.eat(TokenKind::LogNot).is_some() {
            return CrossSelect::Not(Box::new(self.parse_cross_select_primary()));
        }
        if self.eat(TokenKind::LParen).is_some() {
            let s = self.parse_cross_select_or();
            self.expect(TokenKind::RParen);
            return s;
        }
        if self.eat(TokenKind::KwBinsof).is_some() {
            self.expect(TokenKind::LParen);
            let (cp, bin) = self.parse_binsof_bins_expression();
            self.expect(TokenKind::RParen);
            let intersect = if self.eat(TokenKind::KwIntersect).is_some() {
                self.expect(TokenKind::LBrace);
                let mut ranges = Vec::new();
                while !self.at(TokenKind::RBrace) && !self.at(TokenKind::Eof) {
                    ranges.push(self.parse_constraint_range());
                    if self.eat(TokenKind::Comma).is_none() {
                        break;
                    }
                }
                self.expect(TokenKind::RBrace);
                Some(ranges)
            } else {
                None
            };
            return CrossSelect::Binsof { cp, bin, intersect };
        }
        if self.at(TokenKind::Identifier) {
            self.bump();
            return CrossSelect::All;
        }
        self.error(format!(
            "expected a cross bin select expression, found '{}'",
            self.current_text()
        ));
        CrossSelect::All
    }

    pub(in crate::parse) fn parse_covergroup_declaration(&mut self) -> CovergroupDeclaration {
        let start = self.current_span().start;
        self.bump();
        let name = self.parse_identifier();
        // §19.3 constructor formal list (`covergroup cg (int lo, int hi)`),
        // parsed like function ports and bound at `new(...)`.
        let ports = if self.at(TokenKind::LParen) {
            self.parse_function_ports()
        } else {
            Vec::new()
        };
        // Optional coverage event: either `@(event)` / `@@(block_event)` or a
        // `with function sample(tf_port_list)` clause (SV 19.4). The sample
        // function turns the covergroup into one sampled explicitly by call.
        let event = if self.at(TokenKind::At) {
            Some(self.parse_event_control())
        } else {
            None
        };
        let mut sample_ports: Vec<FunctionPort> = Vec::new();
        if self.at(TokenKind::KwWith) {
            self.bump();
            self.expect(TokenKind::KwFunction);
            let _ = self.parse_identifier(); // `sample`
            if self.at(TokenKind::LParen) {
                sample_ports = self.parse_function_ports();
            }
        }
        self.expect(TokenKind::Semicolon);
        let mut items = Vec::new();
        while !self.at(TokenKind::KwEndgroup) && !self.at(TokenKind::Eof) {
            items.push(self.parse_covergroup_item());
        }
        self.expect(TokenKind::KwEndgroup);
        let endlabel = self.parse_end_label();
        // §19.5: an unlabeled coverpoint on a variable is named after the
        // variable; one on any other expression gets a generated name
        // (`coverpoint#<n>`, n counting coverpoints from 1).
        let mut n_cp = 0usize;
        for it in &mut items {
            if let CovergroupItem::Coverpoint(cp) = it {
                n_cp += 1;
                if cp.name.is_none() {
                    let var = match &cp.expr.kind {
                        ExprKind::Ident(h) if h.path.iter().all(|s| s.selects.is_empty()) => Some(
                            h.path
                                .iter()
                                .map(|s| s.name.name.as_str())
                                .collect::<Vec<_>>()
                                .join("."),
                        ),
                        _ => None,
                    };
                    cp.name = Some(crate::ast::Identifier {
                        name: var.unwrap_or_else(|| format!("coverpoint#{}", n_cp)),
                        span: cp.expr.span,
                    });
                }
            }
        }
        CovergroupDeclaration {
            name,
            ports,
            sample_ports,
            event,
            items,
            endlabel,
            span: self.span_from(start),
        }
    }

    fn parse_covergroup_item(&mut self) -> CovergroupItem {
        let start = self.current_span().start;
        let mut name = None;
        if self.at(TokenKind::Identifier) && self.peek_kind() == TokenKind::Colon {
            name = Some(self.parse_identifier());
            self.expect(TokenKind::Colon);
        }

        match self.current_kind() {
            TokenKind::KwCoverpoint => {
                self.bump();
                // §19.5 (SV-2023) `coverpoint real <expr>`. Gated on --sv2023
                // so that under SV-2017 `real` stays whatever it was before
                // (an ordinary expression token) rather than being silently
                // swallowed as a modifier.
                // §6.24.1: in `real'(expr)` the keyword belongs to the cast.
                let is_real = crate::is_sv2023()
                    && !self.followed_by_cast_quote()
                    && self.eat(TokenKind::KwReal).is_some();
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
                        left,
                        right,
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
                let mut cp_options: Vec<(String, crate::ast::expr::Expression)> = Vec::new();
                if self.at(TokenKind::LBrace) {
                    self.bump();
                    // Parse a sequence of bin declarations until matching `}`.
                    while !self.at(TokenKind::RBrace) && !self.at(TokenKind::Eof) {
                        let bin_start = self.current_span().start;
                        // Optional `wildcard` modifier (LRM §19.5) — applies
                        // to the next `bins`/`ignore_bins`/`illegal_bins`.
                        let is_wildcard = self.eat(TokenKind::KwWildcard).is_some();
                        let kind_tok = self.current_kind();
                        let kind = match kind_tok {
                            TokenKind::KwBins => Some(crate::ast::decl::CoverBinKind::Bins),
                            TokenKind::KwIgnore_bins => {
                                Some(crate::ast::decl::CoverBinKind::Ignore)
                            }
                            TokenKind::KwIllegal_bins => {
                                Some(crate::ast::decl::CoverBinKind::Illegal)
                            }
                            // Identifier text fallback for tokenizer variants.
                            TokenKind::Identifier => match self.current_text().as_ref() {
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
                                // §19.5: a bin is named by an identifier; a
                                // reserved word (`small`, `large`) is not one.
                                self.error(format!(
                                    "expected a bin name, found '{}'",
                                    self.current_text()
                                ));
                                self.skip_bin_body_to_semicolon();
                                if self.at(TokenKind::Semicolon) {
                                    self.bump();
                                }
                                continue;
                            };
                            // §19.5.1 `[]` or `[N]` array form.
                            let mut is_array = false;
                            let mut array_size = None;
                            if self.at(TokenKind::LBracket) {
                                is_array = true;
                                self.bump();
                                if !self.at(TokenKind::RBracket) {
                                    array_size = Some(self.parse_expression());
                                }
                                self.expect(TokenKind::RBracket);
                            }
                            // `=` then bin body.
                            if self.eat(TokenKind::Assign).is_some() {
                                let mut values: Vec<crate::ast::decl::ConstraintRange> = Vec::new();
                                let mut transitions: Vec<Vec<crate::ast::decl::TransStep>> =
                                    Vec::new();
                                let mut bin_kind = k;
                                if self.at(TokenKind::LBrace) {
                                    self.bump();
                                    while !self.at(TokenKind::RBrace) && !self.at(TokenKind::Eof) {
                                        values.push(self.parse_constraint_range());
                                        if self.at(TokenKind::Comma) {
                                            self.bump();
                                        }
                                    }
                                    if self.at(TokenKind::RBrace) {
                                        self.bump();
                                    }
                                } else if self.at(TokenKind::KwDefault) {
                                    // `bins other = default;` — LRM §19.5
                                    // catches every value not matched by any
                                    // explicit bin in the same coverpoint.
                                    self.bump();
                                    bin_kind = crate::ast::decl::CoverBinKind::Default;
                                } else if self.at(TokenKind::LParen) {
                                    // §19.5.2 trans_list: `(set), (set), ...`.
                                    loop {
                                        self.expect(TokenKind::LParen);
                                        transitions.push(self.parse_trans_set());
                                        self.expect(TokenKind::RParen);
                                        if !(self.at(TokenKind::Comma)
                                            && self.peek_kind() == TokenKind::LParen)
                                        {
                                            break;
                                        }
                                        self.bump();
                                    }
                                } else {
                                    // Forms we don't handle yet — gobble to
                                    // the terminating `;` (depth-aware).
                                    self.skip_bin_body_to_semicolon();
                                }
                                // §19.5.1.1: `with (expr)` filters the bin's
                                // values; it comes before any `iff` (#611).
                                let with_filter = if self.eat(TokenKind::KwWith).is_some() {
                                    self.expect(TokenKind::LParen);
                                    let f = self.parse_expression();
                                    self.expect(TokenKind::RParen);
                                    Some(f)
                                } else {
                                    None
                                };
                                // §19.5: `iff (expr)` after the bin's values.
                                // Unparsed, its tokens were skipped one by one
                                // and the guard was lost, or tripped the
                                // covergroup parser on an `inside` (#605).
                                let iff_guard = if self.eat(TokenKind::KwIff).is_some() {
                                    self.expect(TokenKind::LParen);
                                    let g = self.parse_expression();
                                    self.expect(TokenKind::RParen);
                                    Some(g)
                                } else {
                                    None
                                };
                                bins.push(crate::ast::decl::CoverBin {
                                    iff_guard,
                                    with_filter,
                                    name: bin_name,
                                    kind: bin_kind,
                                    values,
                                    array_form: is_array,
                                    array_size,
                                    is_wildcard,
                                    transitions,
                                    span: self.span_from(bin_start),
                                });
                            } else {
                                self.skip_bin_body_to_semicolon();
                            }
                            if self.at(TokenKind::Semicolon) {
                                self.bump();
                            }
                        } else if self.at(TokenKind::Identifier)
                            && (self.current_text() == "option"
                                || self.current_text() == "type_option")
                        {
                            // §19.7 coverpoint-level `option.NAME = expr;`.
                            self.bump(); // option / type_option
                            if self.eat(TokenKind::Dot).is_some() {
                                let opt_name = self.parse_identifier().name;
                                if self.eat(TokenKind::Assign).is_some() {
                                    let val = self.parse_expression();
                                    cp_options.push((opt_name, val));
                                }
                            }
                            if self.at(TokenKind::Semicolon) {
                                self.bump();
                            }
                        } else {
                            // Not a bin keyword — skip token to make progress.
                            self.bump();
                        }
                    }
                    if self.at(TokenKind::RBrace) {
                        self.bump();
                    }
                } else {
                    self.expect(TokenKind::Semicolon);
                }
                CovergroupItem::Coverpoint(Coverpoint {
                    name,
                    expr,
                    is_real,
                    iff_guard,
                    bins,
                    options: cp_options,
                    span: self.span_from(start),
                })
            }
            TokenKind::KwCross => {
                self.bump();
                let mut ids = Vec::new();
                loop {
                    let mut id = self.parse_identifier();
                    // XEZIM_RELAX_CROSS_HIER_ITEM (#629): a cross item is a
                    // coverpoint label or a variable (A.2.11); read a
                    // hierarchical reference (`vif.mode`) as a variable too,
                    // kept as its dotted name for an implicit coverpoint.
                    if self.at(TokenKind::Dot)
                        && self.peek_kind() == TokenKind::Identifier
                        && crate::RELAX_CROSS_HIER_ITEM.get()
                    {
                        while self.at(TokenKind::Dot) && self.peek_kind() == TokenKind::Identifier {
                            self.bump();
                            let next = self.parse_identifier();
                            id.name = format!("{}.{}", id.name, next.name);
                            id.span = crate::ast::Span::new(id.span.start, next.span.end);
                        }
                        self.diagnostics
                            .push(crate::diagnostics::Diagnostic::warning(
                                format!(
                                    "a cross item is a coverpoint or a variable; '{}' gets an \
                                     implicit coverpoint (IEEE 1800-2017 §19.6, A.2.11, \
                                     XEZIM_RELAX_CROSS_HIER_ITEM)",
                                    id.name
                                ),
                                id.span,
                            ));
                    }
                    ids.push(id);
                    if !self.at(TokenKind::Comma) {
                        break;
                    }
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
                let mut options: Vec<(String, crate::ast::expr::Expression)> = Vec::new();
                if self.at(TokenKind::LBrace) {
                    self.bump();
                    // §19.6.1 cross body: bins selections and options. Other
                    // items are skipped depth-tracked.
                    loop {
                        if self.at(TokenKind::Eof) {
                            break;
                        }
                        if self.at(TokenKind::RBrace) {
                            self.bump();
                            break;
                        }
                        let kind = match self.current_kind() {
                            TokenKind::KwBins => Some(crate::ast::decl::CoverBinKind::Bins),
                            TokenKind::KwIgnore_bins => {
                                Some(crate::ast::decl::CoverBinKind::Ignore)
                            }
                            TokenKind::KwIllegal_bins => {
                                Some(crate::ast::decl::CoverBinKind::Illegal)
                            }
                            _ => None,
                        };
                        if let Some(kind) = kind {
                            self.bump();
                            if !self.at(TokenKind::Identifier) {
                                self.error(format!(
                                    "expected a bin name, found '{}'",
                                    self.current_text()
                                ));
                                self.skip_bin_body_to_semicolon();
                                let _ = self.eat(TokenKind::Semicolon);
                                continue;
                            }
                            let bin_name = self.parse_identifier();
                            self.expect(TokenKind::Assign);
                            let select = if self.at(TokenKind::ApostropheLBrace) {
                                let set = self.parse_expression();
                                self.cross_tuple_select(&set, &ids)
                            } else {
                                let names = ids.iter().map(|i| i.name.clone()).collect();
                                let saved = std::mem::replace(&mut self.cross_items, names);
                                let select = self.parse_cross_select_or();
                                self.cross_items = saved;
                                select
                            };
                            let mut iff_guard = None;
                            if self.eat(TokenKind::KwIff).is_some() {
                                self.expect(TokenKind::LParen);
                                iff_guard = Some(self.parse_expression());
                                self.expect(TokenKind::RParen);
                            }
                            self.expect(TokenKind::Semicolon);
                            bins.push(crate::ast::decl::CrossBin {
                                name: bin_name,
                                kind,
                                select,
                                iff_guard,
                            });
                            continue;
                        }
                        if self.at(TokenKind::Identifier)
                            && (self.current_text() == "option"
                                || self.current_text() == "type_option")
                            && self.peek_kind() == TokenKind::Dot
                        {
                            self.bump();
                            self.bump();
                            let opt_name = self.parse_identifier().name;
                            if self.eat(TokenKind::Assign).is_some() {
                                options.push((opt_name, self.parse_expression()));
                            }
                            let _ = self.eat(TokenKind::Semicolon);
                            continue;
                        }
                        // Skip one token (depth-aware for nested braces).
                        if self.at(TokenKind::LBrace) {
                            let mut depth = 1usize;
                            self.bump();
                            while depth > 0 && !self.at(TokenKind::Eof) {
                                if self.at(TokenKind::LBrace) {
                                    depth += 1;
                                } else if self.at(TokenKind::RBrace) {
                                    depth -= 1;
                                }
                                self.bump();
                            }
                        } else {
                            self.bump();
                        }
                    }
                } else {
                    self.expect(TokenKind::Semicolon);
                }
                CovergroupItem::Cross(Cross {
                    name,
                    items: ids,
                    iff_guard,
                    bins,
                    options,
                    span: self.span_from(start),
                })
            }
            TokenKind::Identifier
                if self.current_text() == "option" || self.current_text() == "type_option" =>
            {
                let id = self.parse_identifier();
                let is_type = id.name == "type_option";
                self.expect(TokenKind::Dot);
                let opt_name = self.parse_identifier().name;
                self.expect(TokenKind::Assign);
                let val = self.parse_expression();
                self.expect(TokenKind::Semicolon);
                if is_type {
                    CovergroupItem::TypeOption {
                        name: opt_name,
                        val,
                    }
                } else {
                    CovergroupItem::Option {
                        name: opt_name,
                        val,
                    }
                }
            }
            _ => {
                self.error(format!(
                    "unexpected token in covergroup: {:?}",
                    self.current_text()
                ));
                self.bump();
                CovergroupItem::Option {
                    name: "error".to_string(),
                    val: Expression::new(ExprKind::Empty, self.span_from(start)),
                }
            }
        }
    }
}
