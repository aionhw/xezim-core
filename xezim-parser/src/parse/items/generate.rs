use super::*;

impl<'a> Parser<'a> {
    pub(super) fn parse_generate_if(&mut self, start: usize) -> ModuleItem {
        let mut branches = Vec::new();
        let mut branch_labels = Vec::new();
        let mut branch_direct = Vec::new();
        self.bump();
        self.expect(TokenKind::LParen);
        let cond = self.parse_expression();
        self.expect(TokenKind::RParen);
        let (items, label, direct) = self.parse_generate_branch_items_named();
        branches.push((Some(cond), items));
        branch_labels.push(label);
        branch_direct.push(direct);
        while self.eat(TokenKind::KwElse).is_some() {
            if self.at(TokenKind::KwIf) {
                self.bump();
                self.expect(TokenKind::LParen);
                let c = self.parse_expression();
                self.expect(TokenKind::RParen);
                let (items, label, direct) = self.parse_generate_branch_items_named();
                branches.push((Some(c), items));
                branch_labels.push(label);
                branch_direct.push(direct);
            } else {
                let (items, label, direct) = self.parse_generate_branch_items_named();
                branches.push((None, items));
                branch_labels.push(label);
                branch_direct.push(direct);
                break;
            }
        }
        ModuleItem::GenerateIf(GenerateIf {
            branches,
            branch_labels,
            branch_label_decls: Vec::new(),
            branch_direct,
            implicit_name: String::new(),
            span: self.span_from(start),
        })
    }

    pub(super) fn parse_generate_case(&mut self, start: usize) -> ModuleItem {
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
                    if self.eat(TokenKind::Comma).is_none() {
                        break;
                    }
                }
                self.expect(TokenKind::Colon);
            }
            let (items, label, direct) = self.parse_generate_branch_items_named();
            arms.push(GenerateCaseArm {
                values,
                items,
                label,
                label_decl: Default::default(),
                direct,
            });
        }
        self.expect(TokenKind::KwEndcase);
        ModuleItem::GenerateCase(GenerateCase {
            selector,
            arms,
            implicit_name: String::new(),
            span: self.span_from(start),
        })
    }

    pub(super) fn parse_generate_branch_items(&mut self) -> Vec<ModuleItem> {
        self.parse_generate_branch_items_named().0
    }

    /// Like `parse_generate_branch_items` but also returns the optional
    /// `begin : <label>` block name (needed to namespace generate-for renames).
    pub(super) fn parse_generate_branch_items_named(
        &mut self,
    ) -> (Vec<ModuleItem>, Option<String>, bool) {
        self.generate_depth += 1;
        // §27.5: a generate block is a scope, for lets too (§11.13).
        self.push_let_scope();
        let prefixed = self.after_block_label();
        let r = if self.eat(TokenKind::KwBegin).is_some() {
            let label = self.parse_end_label().map(|id| id.name);
            let items = self.parse_module_items_until(TokenKind::KwEnd);
            self.expect(TokenKind::KwEnd);
            if let Some(l) = self.parse_end_label()
                && label.is_none()
                && !prefixed
            {
                self.unnamed_block_end_label(&l);
            }
            (items, label, false)
        } else {
            let items: Vec<ModuleItem> = self.parse_module_item().into_iter().collect();
            // §27.5: without `begin`, a lone conditional generate is directly nested.
            let direct = matches!(
                items.as_slice(),
                [ModuleItem::GenerateIf(_) | ModuleItem::GenerateCase(_)]
            );
            (items, None, direct)
        };
        self.pop_let_scope();
        self.generate_depth -= 1;
        r
    }
}
