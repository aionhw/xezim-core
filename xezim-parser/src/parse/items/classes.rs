use super::*;

impl<'a> Parser<'a> {
    pub(in crate::parse) fn parse_class_declaration(&mut self) -> ClassDeclaration {
        let start = self.current_span().start;
        // A module item arrives here with `virtual` / `interface` already
        // consumed; the caller sets the flags, but the class checks below
        // need them too.
        let after = |p: &Self, k: TokenKind| {
            p.at(TokenKind::KwClass) && p.pos > 0 && p.tokens[p.pos - 1].kind == k
        };
        let virt = self.eat(TokenKind::KwVirtual).is_some() || after(self, TokenKind::KwVirtual);
        // IEEE 1800-2017 §8.26: `interface class <name>; … endclass`. The
        // leading `interface` keyword (mutually exclusive with `virtual`)
        // marks an interface class; the rest parses like a normal class.
        let is_iface =
            self.eat(TokenKind::KwInterface).is_some() || after(self, TokenKind::KwInterface);
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
        let mut bases = Vec::new();
        let mut unscoped_bases: Vec<Identifier> = Vec::new();
        let extends = if self.eat(TokenKind::KwExtends).is_some() {
            let ext_start = self.current_span().start;
            // §8.13: the base class may be package/class-scoped —
            // `extends pkg::Base` or `extends A::B::C`. Keep the final
            // segment as the base-class name; the scope prefix is kept in
            // `ClassExtends::scopes`.
            let mut base_name = self.parse_identifier();
            let mut scoped = false;
            let mut base_scopes: Vec<Identifier> = Vec::new();
            while self.at(TokenKind::DoubleColon) {
                self.bump();
                scoped = true;
                base_scopes.push(base_name);
                base_name = self.parse_identifier();
            }
            if !scoped {
                unscoped_bases.push(base_name.clone());
            }
            let args_at = self.pos;
            let mut ext_default_args = false;
            let args = if self.at(TokenKind::Hash) {
                self.parse_param_args()
            } else if self.at(TokenKind::LParen) {
                // IEEE 1800-2023 §8.17: `extends Base(default)` forwards the
                // subclass constructor's arguments to the superclass's.
                if crate::is_sv2023()
                    && self.peek_kind() == TokenKind::KwDefault
                    && self.peek_kind_n(2) == TokenKind::RParen
                {
                    self.bump();
                    self.bump();
                    self.bump();
                    ext_default_args = true;
                    Vec::new()
                } else {
                    self.parse_param_args()
                }
            }
            // Support extends C(args) or C#(args)
            else {
                Vec::new()
            };
            bases.push((base_name.name.clone(), self.param_args_text(args_at)));
            // §8.26: an interface class may extend MULTIPLE interface classes
            // (`extends ic1#(T), ic2#(T)`). Keep the first in the AST and
            // parse-accept the rest (consume `, base[::seg]…[#(args)]`).
            while self.at(TokenKind::Comma) {
                self.bump();
                let mut other = self.parse_identifier();
                let mut scoped = false;
                while self.at(TokenKind::DoubleColon) {
                    self.bump();
                    scoped = true;
                    other = self.parse_identifier();
                }
                if !scoped {
                    unscoped_bases.push(other.clone());
                }
                let at = self.pos;
                if self.at(TokenKind::Hash) || self.at(TokenKind::LParen) {
                    let _ = self.parse_param_args();
                }
                bases.push((other.name, self.param_args_text(at)));
            }
            Some(ClassExtends {
                name: base_name,
                args,
                span: self.span_from(ext_start),
                scopes: base_scopes,
                default_args: ext_default_args,
                bound: Default::default(),
            })
        } else {
            None
        };
        // IEEE 1800-2017 §8.26.4: an interface class shall not extend a type
        // parameter, even one whose type is an interface class. Every base is
        // checked, not only the first one the AST keeps.
        if is_iface {
            for b in &unscoped_bases {
                let is_type_param = params.iter().any(|p| match &p.kind {
                    ParameterKind::Type { assignments } => {
                        assignments.iter().any(|a| a.name.name == b.name)
                    }
                    _ => false,
                });
                if is_type_param {
                    self.diagnostics.push(crate::diagnostics::Diagnostic::error(
                        format!(
                            "interface class '{}' extends type parameter '{}'; an interface \
                             class shall not extend a type parameter (IEEE 1800-2017 §8.26.4)",
                            name.name, b.name
                        ),
                        b.span,
                    ));
                }
            }
        }
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
                if self.at(TokenKind::Hash) {
                    let _ = self.parse_param_args();
                }
                if self.eat(TokenKind::Comma).is_none() {
                    break;
                }
            }
        }
        self.expect(TokenKind::Semicolon);
        // Push the class name onto the parser's class-context stack so
        // `type(this)` references resolve to this class (§6.20.2.1).
        crate::push_class_context(name.name.clone());
        let mut items = Vec::new();
        let outer_pure = std::mem::take(&mut self.pure_constraints);
        // A class is a scope: its members hide outer lets of the same name.
        self.push_let_scope();
        while !self.at(TokenKind::KwEndclass) && !self.at(TokenKind::Eof) {
            let it = self.parse_class_item();
            self.hide_let_names_of_class_item(&it);
            items.push(it);
            self.release_consumed_tokens();
        }
        self.pop_let_scope();
        let pure_constraints = std::mem::replace(&mut self.pure_constraints, outer_pure);
        crate::pop_class_context();
        {
            let mut type_names = Vec::new();
            let add_params = |pd: &ParameterDeclaration, out: &mut Vec<String>| match &pd.kind {
                ParameterKind::Data { assignments, .. } => {
                    out.extend(assignments.iter().map(|a| a.name.name.clone()))
                }
                ParameterKind::Type { assignments } => {
                    out.extend(assignments.iter().map(|a| a.name.name.clone()))
                }
            };
            for pd in &params {
                add_params(pd, &mut type_names);
            }
            let mut constraints = Vec::new();
            for it in &items {
                match it {
                    ClassItem::Parameter(pd) => add_params(pd, &mut type_names),
                    ClassItem::Typedef(t) => type_names.push(t.name.name.clone()),
                    ClassItem::Constraint(c) if !pure_constraints.contains(&c.name.name) => {
                        constraints.push(c.name.name.clone())
                    }
                    _ => {}
                }
            }
            self.class_infos.push(super::ClassInfo {
                name: name.clone(),
                is_virtual: virt,
                is_interface: is_iface,
                bases,
                type_names,
                pure_constraints,
                constraints,
            });
        }
        self.expect(TokenKind::KwEndclass);
        let endlabel = self.parse_end_label();
        if crate::strict_checks() {
            self.check_interface_class_names();
        }
        ClassDeclaration {
            virtual_kw: virt,
            is_interface: is_iface,
            is_final,
            name,
            params,
            extends,
            implements,
            items,
            endlabel,
            span: self.span_from(start),
        }
    }

    /// §8.26.6.2 / §8.26.6.3: an interface class that inherits one parameter
    /// or type name from two different base classes, or from two
    /// specializations of one, declares that name itself. Checked for the
    /// class just parsed, against the classes before it in this file; a chain
    /// through any other class is not followed.
    fn check_interface_class_names(&mut self) {
        let find = |n: &str| self.class_infos.iter().find(|c| c.name.name == n);
        let mut errs = Vec::new();
        for c in self
            .class_infos
            .last()
            .filter(|c| c.is_interface && c.bases.len() > 1)
            .into_iter()
        {
            // (name, the specialized class it is inherited from)
            let mut origin: Vec<(String, String)> = Vec::new();
            let mut stack: Vec<(String, String, u32)> = c
                .bases
                .iter()
                .map(|(b, a)| (b.clone(), a.clone(), 0))
                .collect();
            let mut complete = true;
            while let Some((b, args, depth)) = stack.pop() {
                let Some(bi) = find(&b) else {
                    complete = false;
                    break;
                };
                let from = format!("{b}#({args})");
                for n in &bi.type_names {
                    origin.push((n.clone(), from.clone()));
                }
                if depth < 32 {
                    stack.extend(
                        bi.bases
                            .iter()
                            .map(|(b, a)| (b.clone(), a.clone(), depth + 1)),
                    );
                }
            }
            if !complete {
                continue;
            }
            origin.sort();
            origin.dedup();
            let mut names: Vec<&str> = origin.iter().map(|(n, _)| n.as_str()).collect();
            names.dedup();
            for n in names {
                let from: Vec<&str> = origin
                    .iter()
                    .filter(|(o, _)| o == n)
                    .map(|(_, f)| f.as_str())
                    .collect();
                if from.len() > 1 && !c.type_names.iter().any(|t| t == n) {
                    errs.push(crate::diagnostics::Diagnostic::error(
                        format!(
                            "interface class '{}' inherits '{n}' from {} and must declare it \
                             itself (IEEE 1800-2017 §8.26.6.2)",
                            c.name.name,
                            from.join(" and ")
                        ),
                        c.name.span,
                    ));
                }
            }
        }
        self.diagnostics.extend(errs);
    }

    fn parse_class_item(&mut self) -> ClassItem {
        let start = self.current_span().start;
        if self.eat(TokenKind::Semicolon).is_some() {
            return ClassItem::Empty;
        }
        let mut qualifiers = Vec::new();
        loop {
            match self.current_kind() {
                TokenKind::KwStatic => {
                    self.bump();
                    qualifiers.push(ClassQualifier::Static);
                }
                TokenKind::KwProtected => {
                    self.bump();
                    qualifiers.push(ClassQualifier::Protected);
                }
                TokenKind::KwLocal => {
                    self.bump();
                    qualifiers.push(ClassQualifier::Local);
                }
                TokenKind::KwRand => {
                    self.bump();
                    qualifiers.push(ClassQualifier::Rand);
                }
                TokenKind::KwRandc => {
                    self.bump();
                    qualifiers.push(ClassQualifier::Randc);
                }
                TokenKind::KwConst => {
                    self.bump();
                    qualifiers.push(ClassQualifier::Const);
                }
                TokenKind::KwPure => {
                    self.bump();
                    qualifiers.push(ClassQualifier::Pure);
                    if self.at(TokenKind::KwVirtual) {
                        self.bump();
                        qualifiers.push(ClassQualifier::Virtual);
                    }
                }
                TokenKind::KwVirtual => {
                    self.bump();
                    qualifiers.push(ClassQualifier::Virtual);
                    if self.at(TokenKind::KwPure) {
                        self.bump();
                        qualifiers.push(ClassQualifier::Pure);
                    }
                }
                TokenKind::KwExtern => {
                    self.bump();
                    qualifiers.push(ClassQualifier::Extern);
                }
                _ => break,
            }
        }

        match self.current_kind() {
            TokenKind::Directive => {
                if self.recover_undefined_macro() {
                    return ClassItem::Empty;
                }
                self.bump();
                self.parse_class_item()
            }
            TokenKind::KwFunction => {
                let is_pure = qualifiers.contains(&ClassQualifier::Pure);
                let is_extern = qualifiers.contains(&ClassQualifier::Extern);
                if is_pure || is_extern {
                    let func = self.parse_function_prototype();
                    if is_pure {
                        ClassItem::Method(ClassMethod {
                            qualifiers,
                            kind: ClassMethodKind::PureVirtual(func),
                            span: self.span_from(start),
                        })
                    } else {
                        ClassItem::Method(ClassMethod {
                            qualifiers,
                            kind: ClassMethodKind::Extern(func),
                            span: self.span_from(start),
                        })
                    }
                } else {
                    let func = self.parse_function_declaration();
                    ClassItem::Method(ClassMethod {
                        qualifiers,
                        kind: ClassMethodKind::Function(func),
                        span: self.span_from(start),
                    })
                }
            }
            TokenKind::KwTask => {
                let is_pure = qualifiers.contains(&ClassQualifier::Pure);
                let is_extern = qualifiers.contains(&ClassQualifier::Extern);
                if is_pure || is_extern {
                    let task = self.parse_task_prototype();
                    ClassItem::Method(ClassMethod {
                        qualifiers,
                        kind: ClassMethodKind::Task(task),
                        span: self.span_from(start),
                    })
                } else {
                    let task = self.parse_task_declaration();
                    ClassItem::Method(ClassMethod {
                        qualifiers,
                        kind: ClassMethodKind::Task(task),
                        span: self.span_from(start),
                    })
                }
            }
            TokenKind::KwConstraint => {
                self.bump();
                let cname = self.parse_identifier();
                if qualifiers.contains(&ClassQualifier::Pure) {
                    self.pure_constraints.push(cname.name.clone());
                }
                let (items, has_body) = if self.at(TokenKind::LBrace) {
                    self.bump();
                    let mut items = Vec::new();
                    while !self.at(TokenKind::RBrace) && !self.at(TokenKind::Eof) {
                        items.push(self.parse_constraint_item(ConstraintPos::BlockItem));
                    }
                    self.expect(TokenKind::RBrace);
                    (items, true)
                } else {
                    self.expect(TokenKind::Semicolon);
                    (Vec::new(), false)
                };
                ClassItem::Constraint(std::sync::Arc::new(ClassConstraint {
                    is_static: qualifiers.contains(&ClassQualifier::Static),
                    is_extern: qualifiers.contains(&ClassQualifier::Extern),
                    has_body,
                    name: cname,
                    items,
                    span: self.span_from(start),
                }))
            }
            TokenKind::KwTypedef => ClassItem::Typedef(self.parse_typedef_declaration()),
            TokenKind::KwParameter | TokenKind::KwLocalparam => {
                let pd = self.parse_parameter_declaration();
                self.expect(TokenKind::Semicolon);
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
                    if self.is_data_type_keyword() || self.at(TokenKind::Identifier) {
                        self.parse_data_type()
                    } else {
                        DataType::Implicit {
                            signing: None,
                            dimensions: Vec::new(),
                            span: self.span_from(start),
                        }
                    }
                } else {
                    self.parse_data_type()
                };
                let decls = self.parse_var_declarator_list();
                self.expect(TokenKind::Semicolon);
                ClassItem::Property(ClassProperty {
                    qualifiers,
                    data_type: dt,
                    declarators: decls,
                    span: self.span_from(start),
                })
            }
            _ => {
                self.error(format!(
                    "unexpected token in class: {:?}",
                    self.current_text()
                ));
                self.bump();
                ClassItem::Empty
            }
        }
    }
}
