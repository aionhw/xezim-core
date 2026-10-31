//! Declarations: namespace-scope items, class bodies, the SystemC module
//! macros, templates, and the declaration specifiers and declarators they
//! share.

use super::*;

/// Where a simple declaration appears; decides how `name(` is read and
/// whether the declaration ends at `;`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum Ctx {
    Namespace,
    Class,
    /// A statement in a function body.
    Block,
    /// The condition of `if`/`while`/`switch`: one declarator, no `;`.
    Condition,
}

/// What a simple declaration turned out to declare.
pub(super) enum Decl {
    Var(VarDecl),
    Function(Box<FunctionDecl>),
    Typedef(TypedefDecl),
    Class(ClassDecl),
    Enum(EnumDecl),
    Forward {
        key: ClassKey,
        name: QualifiedName,
        span: ScSpan,
    },
    Empty(ScSpan),
}

pub(super) enum UsingResult {
    Using(UsingDecl),
    Alias(TypedefDecl),
}

const BUILTIN_TYPE_KEYWORDS: &[&str] = &[
    "void", "bool", "char", "char8_t", "char16_t", "char32_t", "wchar_t", "short", "int", "long",
    "signed", "unsigned", "float", "double",
];

pub(super) fn is_builtin_type_keyword(t: &ScToken) -> bool {
    t.kind == ScTokenKind::Keyword && BUILTIN_TYPE_KEYWORDS.contains(&t.text.as_str())
}

/// Whether `q` names `sc_core::sc_module` or one of its §5.2.23 aliases.
fn is_sc_module_base(q: &QualifiedName) -> bool {
    matches!(q.last_name(), "sc_module" | "sc_channel" | "sc_behavior")
        && q.qualifiers().all(|n| n == "sc_core")
}

/// Macros at namespace scope that expand to nothing a parser needs: vendor
/// top-module registrations (`SC_MODULE_EXPORT(top);`) and
/// `SC_HAS_PROCESS(m);` before out-of-class constructors (a typedef of the
/// module, §5.2.8).
const IGNORED_ITEM_MACROS: &[&str] = &["SC_MODULE_EXPORT", "NCSC_MODULE_EXPORT", "SC_HAS_PROCESS"];

fn function_skeleton(name: QualifiedName, span: ScSpan) -> FunctionDecl {
    FunctionDecl {
        specifiers: Specifiers::default(),
        return_type: None,
        return_ptr_ops: Vec::new(),
        name,
        params: Vec::new(),
        variadic: false,
        is_const: false,
        is_volatile: false,
        ref_qualifier: None,
        noexcept: false,
        is_override: false,
        is_final: false,
        trailing_return: None,
        special_body: None,
        initializers: Vec::new(),
        body: None,
        sc_ctor: false,
        span,
    }
}

impl Parser {
    // ---- namespace scope -------------------------------------------------

    /// Items up to the end of input, or up to (not past) the `}` closing the
    /// enclosing namespace when `in_braces`.
    pub(super) fn parse_items(&mut self, in_braces: bool) -> Vec<Item> {
        let mut items = Vec::new();
        loop {
            if self.at_eof() {
                break;
            }
            if self.at("}") {
                if in_braces {
                    break;
                }
                let span = self.cur_span();
                self.error("unexpected '}'", span);
                self.bump();
                continue;
            }
            match self.parse_item() {
                Ok(item) => items.push(item),
                Err(Fail) => self.recover(),
            }
        }
        items
    }

    fn parse_item(&mut self) -> PResult<Item> {
        self.skip_attributes();
        let start = self.cur_span();
        if self.eat(";") {
            return Ok(Item::Empty(start));
        }
        if self.at_kw("namespace") || (self.at_kw("inline") && self.nth(1).is_keyword("namespace"))
        {
            return self.parse_namespace();
        }
        if self.at_kw("using") {
            return Ok(match self.parse_using()? {
                UsingResult::Using(u) => Item::Using(u),
                UsingResult::Alias(t) => Item::Typedef(t),
            });
        }
        if self.at_kw("typedef") {
            return self.parse_typedef().map(Item::Typedef);
        }
        if self.at_kw("template") {
            return self.parse_template_item();
        }
        if self.at_kw("extern") && self.nth(1).kind == ScTokenKind::StringLit {
            return self.parse_extern_block();
        }
        if self.at_kw("extern") && self.nth(1).is_keyword("template") {
            self.bump();
            self.bump();
            let decl = self.parse_item()?;
            return Ok(Item::ExplicitInstantiation {
                decl: Box::new(decl),
                span: self.span_from(start),
            });
        }
        if self.at_kw("static_assert") {
            return self.parse_static_assert().map(Item::StaticAssert);
        }
        if self.peek().is_ident("SC_MODULE") && self.nth(1).is_punct("(") {
            return self.parse_sc_module().map(Item::Class);
        }
        if self.at_ident()
            && IGNORED_ITEM_MACROS.contains(&self.peek().text.as_str())
            && self.nth(1).is_punct("(")
        {
            self.bump();
            self.skip_balanced()?;
            self.eat(";");
            return Ok(Item::Empty(self.span_from(start)));
        }
        if let Some(f) = self.try_out_of_class_special()? {
            return Ok(Item::Function(f));
        }
        Ok(match self.parse_simple_decl(Ctx::Namespace)? {
            Decl::Var(v) => Item::Var(v),
            Decl::Function(f) => Item::Function(*f),
            Decl::Typedef(t) => Item::Typedef(t),
            Decl::Class(c) => Item::Class(c),
            Decl::Enum(e) => Item::Enum(e),
            Decl::Forward { key, name, span } => Item::ForwardDecl { key, name, span },
            Decl::Empty(s) => Item::Empty(s),
        })
    }

    fn parse_namespace(&mut self) -> PResult<Item> {
        let start = self.cur_span();
        let inline = self.eat_kw("inline");
        self.bump(); // namespace
        self.skip_attributes();
        let mut names = Vec::new();
        if self.at_ident() {
            names.push(self.expect_ident()?);
            if self.at("=") {
                self.bump();
                let target = self.parse_qualified_name(true)?;
                self.expect(";")?;
                return Ok(Item::Using(UsingDecl::NamespaceAlias {
                    alias: names.pop().expect("one name"),
                    target,
                    span: self.span_from(start),
                }));
            }
            while self.eat("::") {
                self.eat_kw("inline");
                names.push(self.expect_ident()?);
            }
        }
        self.expect("{")?;
        let items = self.parse_items(true);
        self.expect("}")?;
        let span = self.span_from(start);
        // `namespace a::b { … }` nests (C++17 §10.3.1).
        let mut item_list = items;
        let mut name_iter = names.into_iter().rev().peekable();
        if name_iter.peek().is_none() {
            return Ok(Item::Namespace {
                name: None,
                inline,
                items: item_list,
                span,
            });
        }
        let mut result = None;
        while let Some(n) = name_iter.next() {
            let is_outermost = name_iter.peek().is_none();
            let ns = Item::Namespace {
                name: Some(n),
                inline: inline && is_outermost,
                items: item_list,
                span,
            };
            if is_outermost {
                result = Some(ns);
                break;
            }
            item_list = vec![ns];
        }
        Ok(result.expect("at least one name"))
    }

    fn parse_extern_block(&mut self) -> PResult<Item> {
        let start = self.cur_span();
        self.bump(); // extern
        let lit = self.bump().text;
        let linkage = lit.trim_matches('"').to_string();
        let items = if self.eat("{") {
            let items = self.parse_items(true);
            self.expect("}")?;
            items
        } else {
            vec![self.parse_item()?]
        };
        Ok(Item::ExternBlock {
            linkage,
            items,
            span: self.span_from(start),
        })
    }

    pub(super) fn parse_using(&mut self) -> PResult<UsingResult> {
        let start = self.cur_span();
        let is_template = std::mem::take(&mut self.pending_template);
        self.bump(); // using
        if self.eat_kw("namespace") {
            let name = self.parse_qualified_name(true)?;
            self.expect(";")?;
            return Ok(UsingResult::Using(UsingDecl::Namespace {
                name,
                span: self.span_from(start),
            }));
        }
        if self.at_ident() && self.nth(1).is_punct("=") {
            let name = self.expect_ident()?;
            self.bump(); // =
            let ty = self.parse_type_id(true)?;
            self.expect(";")?;
            self.add_type_name(&name.name);
            if is_template {
                self.class_templates.insert(name.name.clone());
            }
            let span = self.span_from(start);
            return Ok(UsingResult::Alias(TypedefDecl {
                ty,
                declarators: vec![Declarator {
                    ptr_ops: Vec::new(),
                    span: name.span,
                    name,
                    array_dims: Vec::new(),
                    bitfield: None,
                    init: None,
                    sc_init: None,
                }],
                alias_syntax: true,
                span,
            }));
        }
        self.eat_kw("typename");
        let name = self.parse_qualified_name(true)?;
        self.expect(";")?;
        Ok(UsingResult::Using(UsingDecl::Declaration {
            name,
            span: self.span_from(start),
        }))
    }

    pub(super) fn parse_typedef(&mut self) -> PResult<TypedefDecl> {
        let start = self.cur_span();
        self.bump(); // typedef
        let (_, ty) = self.parse_decl_specifiers()?;
        let mut declarators = Vec::new();
        loop {
            let dstart = self.cur_span();
            let ptr_ops = self.parse_ptr_ops();
            if self.at("(") {
                let span = self.cur_span();
                return Err(self.error("function pointer typedefs are not supported", span));
            }
            let name = self.expect_ident()?;
            let array_dims = self.parse_array_dims()?;
            self.add_type_name(&name.name);
            declarators.push(Declarator {
                ptr_ops,
                name,
                array_dims,
                bitfield: None,
                init: None,
                sc_init: None,
                span: self.span_from(dstart),
            });
            if !self.eat(",") {
                break;
            }
        }
        self.expect(";")?;
        Ok(TypedefDecl {
            ty,
            declarators,
            alias_syntax: false,
            span: self.span_from(start),
        })
    }

    fn parse_template_item(&mut self) -> PResult<Item> {
        let start = self.cur_span();
        self.bump(); // template
        if !self.at("<") {
            let decl = self.parse_item()?;
            return Ok(Item::ExplicitInstantiation {
                decl: Box::new(decl),
                span: self.span_from(start),
            });
        }
        let params = self.parse_template_params()?;
        self.pending_template = true;
        let item = self.parse_item();
        self.pending_template = false;
        Ok(Item::Template {
            params,
            item: Box::new(item?),
            span: self.span_from(start),
        })
    }

    pub(super) fn parse_template_params(&mut self) -> PResult<Vec<TemplateParam>> {
        self.expect("<")?;
        let saved = self.no_gt;
        self.no_gt = 1;
        let r = self.template_param_list();
        self.no_gt = saved;
        let params = r?;
        self.expect_template_close()?;
        Ok(params)
    }

    fn template_param_list(&mut self) -> PResult<Vec<TemplateParam>> {
        let mut params = Vec::new();
        if self.peek().text.starts_with('>') {
            return Ok(params);
        }
        loop {
            let start = self.cur_span();
            if self.at_kw("template") {
                return Err(self.error("template template parameters are not supported", start));
            }
            let type_param = (self.at_kw("typename") || self.at_kw("class"))
                && !self.nth(2).is_punct("::")
                && !(self.nth(1).is_punct("::"));
            if type_param {
                self.bump();
                let variadic = self.eat("...");
                let name = if self.at_ident() {
                    Some(self.expect_ident()?)
                } else {
                    None
                };
                if let Some(n) = &name {
                    self.add_type_name(&n.name);
                }
                let default = if self.eat("=") {
                    Some(self.parse_type_id(true)?)
                } else {
                    None
                };
                params.push(TemplateParam::Type {
                    name,
                    default,
                    variadic,
                    span: self.span_from(start),
                });
            } else {
                let ty = self.parse_type_id(false)?;
                let variadic = self.eat("...");
                let name = if self.at_ident() {
                    Some(self.expect_ident()?)
                } else {
                    None
                };
                let default = if self.eat("=") {
                    Some(self.parse_conditional()?)
                } else {
                    None
                };
                params.push(TemplateParam::Value {
                    ty,
                    name,
                    default,
                    variadic,
                    span: self.span_from(start),
                });
            }
            if !self.eat(",") {
                break;
            }
        }
        Ok(params)
    }

    pub(super) fn parse_static_assert(&mut self) -> PResult<StaticAssert> {
        let start = self.cur_span();
        self.bump(); // static_assert
        self.expect("(")?;
        let (cond, message) = self.nested(|p| {
            let cond = p.parse_assign()?;
            let message = if p.eat(",") {
                Some(p.parse_assign()?)
            } else {
                None
            };
            Ok((cond, message))
        })?;
        self.expect(")")?;
        self.expect(";")?;
        Ok(StaticAssert {
            cond,
            message,
            span: self.span_from(start),
        })
    }

    /// `Top::Top(…)` / `Top::~Top()` defined outside the class.
    fn try_out_of_class_special(&mut self) -> PResult<Option<FunctionDecl>> {
        let cp = self.checkpoint();
        let start = self.cur_span();
        let mut specs = Specifiers::default();
        self.parse_function_specifiers(&mut specs);
        if !(self.at_ident() || self.at("::")) {
            self.restore(cp);
            return Ok(None);
        }
        let Ok(name) = self.parse_qualified_name(true) else {
            self.restore(cp);
            return Ok(None);
        };
        let n = name.segments.len();
        let is_special = n >= 2 && self.at("(") && {
            let last = &name.segments[n - 1].ident.name;
            let class = &name.segments[n - 2].ident.name;
            last == class || last.strip_prefix('~') == Some(class.as_str())
        };
        if !is_special {
            self.restore(cp);
            return Ok(None);
        }
        self.pending_template = false;
        let mut f = function_skeleton(name, start);
        f.specifiers = specs;
        self.parse_function_rest(&mut f, start)?;
        Ok(Some(f))
    }

    /// `[virtual] [access] name, …` after a class head's `:`.
    fn parse_base_list(&mut self) -> PResult<Vec<BaseSpec>> {
        let mut bases = Vec::new();
        loop {
            let bstart = self.cur_span();
            let mut access = None;
            let mut is_virtual = false;
            loop {
                if self.eat_kw("virtual") {
                    is_virtual = true;
                } else if self.eat_kw("public") {
                    access = Some(Access::Public);
                } else if self.eat_kw("protected") {
                    access = Some(Access::Protected);
                } else if self.eat_kw("private") {
                    access = Some(Access::Private);
                } else {
                    break;
                }
            }
            let bname = self.parse_qualified_name(true)?;
            self.eat("...");
            bases.push(BaseSpec {
                access,
                is_virtual,
                name: bname,
                span: self.span_from(bstart),
            });
            if !self.eat(",") {
                break;
            }
        }
        Ok(bases)
    }

    // ---- SystemC module macros -------------------------------------------

    /// `SC_MODULE(name) { … };` — a struct publicly derived from
    /// `sc_core::sc_module` (IEEE 1666-2023 §5.2.5).
    pub(super) fn parse_sc_module(&mut self) -> PResult<ClassDecl> {
        let is_template = std::mem::take(&mut self.pending_template);
        let start = self.cur_span();
        let macro_span = self.bump().span; // SC_MODULE
        self.expect("(")?;
        let name = self.expect_ident()?;
        self.expect(")")?;
        self.add_type_name(&name.name);
        if is_template {
            self.class_templates.insert(name.name.clone());
        }
        let base_name = QualifiedName {
            global: true,
            segments: ["sc_core", "sc_module"]
                .iter()
                .map(|s| NameSegment {
                    ident: Ident {
                        name: s.to_string(),
                        span: macro_span,
                    },
                    template_args: None,
                })
                .collect(),
            span: macro_span,
        };
        // The macro expands to the class head `struct name : sc_module`, so
        // more bases may follow (`SC_MODULE(m), public tlm_fw_transport_if<>`).
        let mut bases = vec![BaseSpec {
            access: Some(Access::Public),
            is_virtual: false,
            name: base_name,
            span: macro_span,
        }];
        if self.eat(",") {
            bases.extend(self.parse_base_list()?);
        }
        let members = self.parse_class_body(&name.name)?;
        self.expect(";")?;
        Ok(ClassDecl {
            key: ClassKey::Struct,
            name: Some(name),
            bases,
            members,
            is_final: false,
            sc_module: true,
            sc_module_macro: true,
            span: self.span_from(start),
        })
    }

    /// `SC_CTOR(name) [: inits] { … }`, with the IEEE 1666-2023 §5.2.7
    /// extra constructor parameters `SC_CTOR(name, int depth)`.
    fn parse_sc_ctor(&mut self) -> PResult<FunctionDecl> {
        let start = self.cur_span();
        self.bump(); // SC_CTOR
        self.expect("(")?;
        let name = self.expect_ident()?;
        let mut f = function_skeleton(QualifiedName::simple(name), start);
        f.sc_ctor = true;
        while self.eat(",") {
            let p = self.nested(|p| p.parse_param())?;
            f.params.push(p);
        }
        self.expect(")")?;
        if self.at(":") {
            f.initializers = self.parse_mem_initializers()?;
        }
        if self.at("{") {
            f.body = Some(self.parse_block()?);
        } else {
            self.expect(";")?;
        }
        f.span = self.span_from(start);
        Ok(f)
    }

    /// SystemC 3.0 in-class process declaration (`sc_initializer_function.h`):
    /// `SC_METHOD_IMP(f, init…)`, `SC_THREAD_IMP(f, init…)` or
    /// `SC_CTHREAD_IMP(f, edge, init…)`, then `;` or the body of `void f()`.
    fn parse_sc_process_imp(&mut self) -> PResult<Member> {
        let start = self.cur_span();
        let kind = match self.bump().text.as_str() {
            "SC_METHOD_IMP" => ProcessKind::Method,
            "SC_THREAD_IMP" => ProcessKind::Thread,
            _ => ProcessKind::CThread,
        };
        self.expect("(")?;
        let name = self.expect_ident()?;
        let clock = if kind == ProcessKind::CThread {
            self.expect(",")?;
            Some(self.nested(|p| p.parse_assign())?)
        } else {
            None
        };
        // The initialization code is the macro's variadic part: statements
        // (or one braced block) up to the closing `)`.
        let mut init = Vec::new();
        if self.eat(",") {
            self.nested(|p| {
                while !p.at(")") && !p.at_eof() {
                    init.push(p.parse_stmt()?);
                }
                Ok(())
            })?;
        }
        self.expect(")")?;
        let mut method = function_skeleton(QualifiedName::simple(name), start);
        method.return_type = Some(Type {
            is_const: false,
            is_volatile: false,
            base: TypeName::Builtin("void".to_string()),
            ptr_ops: Vec::new(),
            span: start,
        });
        if self.at("{") {
            method.body = Some(self.parse_block()?);
        } else {
            self.expect(";")?;
        }
        method.span = self.span_from(start);
        Ok(Member::ScProcessImp {
            kind,
            clock,
            init,
            method,
            span: self.span_from(start),
        })
    }

    // ---- classes ---------------------------------------------------------

    /// `{ members }` of a class named `name` (empty for an anonymous one).
    fn parse_class_body(&mut self, name: &str) -> PResult<Vec<Member>> {
        self.expect("{")?;
        self.class_stack.push(name.to_string());
        let saved = self.no_gt;
        self.no_gt = 0;
        let mut members = Vec::new();
        while !self.at("}") && !self.at_eof() {
            match self.parse_member() {
                Ok(m) => members.push(m),
                Err(Fail) => self.recover(),
            }
        }
        self.no_gt = saved;
        self.class_stack.pop();
        self.expect("}")?;
        Ok(members)
    }

    /// Whether the class/struct/union/enum keyword at the cursor starts a
    /// definition (a body or a base clause follows the name).
    fn at_type_definition(&mut self) -> bool {
        let cp = self.checkpoint();
        self.bump(); // key
        let is_enum = self.toks[cp.pos].text == "enum";
        if is_enum {
            let _ = self.eat_kw("class") || self.eat_kw("struct");
        }
        self.skip_attributes();
        let mut ok = true;
        if self.at_ident() || self.at("::") {
            ok = self.parse_qualified_name(true).is_ok();
        }
        let _ = self.eat_contextual("final");
        let result = ok && (self.at("{") || (self.at(":") && !self.at("::")));
        self.restore(cp);
        result
    }

    fn parse_class_specifier(&mut self) -> PResult<ClassDecl> {
        let is_template = std::mem::take(&mut self.pending_template);
        let start = self.cur_span();
        let key = match self.bump().text.as_str() {
            "class" => ClassKey::Class,
            "struct" => ClassKey::Struct,
            _ => ClassKey::Union,
        };
        self.skip_attributes();
        let mut name = None;
        if self.at_ident() || self.at("::") {
            let q = self.parse_qualified_name(true)?;
            let last = q.segments.last().expect("non-empty").ident.clone();
            self.add_type_name(&last.name);
            if is_template {
                self.class_templates.insert(last.name.clone());
            }
            name = Some(last);
        }
        let is_final = self.eat_contextual("final");
        let bases = if self.eat(":") {
            self.parse_base_list()?
        } else {
            Vec::new()
        };
        let class_name = name.as_ref().map_or(String::new(), |n| n.name.clone());
        let members = self.parse_class_body(&class_name)?;
        let sc_module = bases.iter().any(|b| is_sc_module_base(&b.name));
        Ok(ClassDecl {
            key,
            name,
            bases,
            members,
            is_final,
            sc_module,
            sc_module_macro: false,
            span: self.span_from(start),
        })
    }

    fn parse_enum_specifier(&mut self) -> PResult<EnumDecl> {
        let start = self.cur_span();
        self.bump(); // enum
        let scoped = self.eat_kw("class") || self.eat_kw("struct");
        self.skip_attributes();
        let name = if self.at_ident() {
            Some(self.expect_ident()?)
        } else {
            None
        };
        if let Some(n) = &name {
            self.add_type_name(&n.name);
        }
        let underlying = if self.eat(":") {
            Some(self.parse_type_id(false)?)
        } else {
            None
        };
        self.expect("{")?;
        let enumerators = self.nested(|p| {
            let mut list = Vec::new();
            while !p.at("}") && !p.at_eof() {
                let name = p.expect_ident()?;
                p.skip_attributes();
                let value = if p.eat("=") {
                    Some(p.parse_assign()?)
                } else {
                    None
                };
                list.push(Enumerator { name, value });
                if !p.eat(",") {
                    break;
                }
            }
            Ok(list)
        })?;
        self.expect("}")?;
        Ok(EnumDecl {
            scoped,
            name,
            underlying,
            enumerators,
            span: self.span_from(start),
        })
    }

    fn parse_member(&mut self) -> PResult<Member> {
        self.skip_attributes();
        let start = self.cur_span();
        if self.eat(";") {
            return Ok(Member::Empty(start));
        }
        for (kw, access) in [
            ("public", Access::Public),
            ("protected", Access::Protected),
            ("private", Access::Private),
        ] {
            if self.at_kw(kw) && self.nth(1).is_punct(":") {
                self.bump();
                self.bump();
                return Ok(Member::Access(access, self.span_from(start)));
            }
        }
        if self.at_ident() && self.nth(1).is_punct("(") {
            match self.peek().text.as_str() {
                "SC_CTOR" => return self.parse_sc_ctor().map(Member::Constructor),
                "SC_HAS_PROCESS" => {
                    self.bump();
                    self.expect("(")?;
                    let name = self.expect_ident()?;
                    self.expect(")")?;
                    self.expect(";")?;
                    return Ok(Member::ScHasProcess(name));
                }
                "SC_MODULE" => return self.parse_sc_module().map(Member::NestedClass),
                "SC_METHOD_IMP" | "SC_THREAD_IMP" | "SC_CTHREAD_IMP" => {
                    return self.parse_sc_process_imp();
                }
                "SC_INIT" => {
                    self.bump();
                    self.expect("(")?;
                    let name = self.expect_ident()?;
                    self.expect(")")?;
                    let body = self.parse_block()?;
                    return Ok(Member::ScInit {
                        name,
                        body,
                        span: self.span_from(start),
                    });
                }
                _ => {}
            }
        }
        if self.at_kw("using") {
            return Ok(match self.parse_using()? {
                UsingResult::Using(u) => Member::Using(u),
                UsingResult::Alias(t) => Member::Typedef(t),
            });
        }
        if self.at_kw("typedef") {
            return self.parse_typedef().map(Member::Typedef);
        }
        if self.at_kw("static_assert") {
            return self.parse_static_assert().map(Member::StaticAssert);
        }
        if self.at_kw("template") && self.nth(1).is_punct("<") {
            self.bump();
            let params = self.parse_template_params()?;
            self.pending_template = true;
            let member = self.parse_member();
            self.pending_template = false;
            return Ok(Member::Template {
                params,
                member: Box::new(member?),
                span: self.span_from(start),
            });
        }
        if self.at_kw("friend")
            && (self.nth(1).is_keyword("class") || self.nth(1).is_keyword("struct"))
            && self.nth(2).kind == ScTokenKind::Ident
            && self.nth(3).is_punct(";")
        {
            self.bump();
            self.bump();
            let name = self.parse_qualified_name(true)?;
            self.expect(";")?;
            return Ok(Member::Friend {
                name,
                span: self.span_from(start),
            });
        }
        if let Some(m) = self.try_special_member()? {
            return Ok(m);
        }
        Ok(match self.parse_simple_decl(Ctx::Class)? {
            Decl::Var(v) => Member::Field(v),
            Decl::Function(f) => Member::Method(*f),
            Decl::Typedef(t) => Member::Typedef(t),
            Decl::Class(c) => Member::NestedClass(c),
            Decl::Enum(e) => Member::Enum(e),
            Decl::Forward { key, name, span } => Member::ForwardDecl { key, name, span },
            Decl::Empty(s) => Member::Empty(s),
        })
    }

    /// A constructor, destructor or conversion operator declared in the
    /// class body: no declaration specifiers name a type before the name.
    fn try_special_member(&mut self) -> PResult<Option<Member>> {
        let cp = self.checkpoint();
        let start = self.cur_span();
        let mut specs = Specifiers::default();
        self.parse_function_specifiers(&mut specs);
        let class = self.class_stack.last().cloned().unwrap_or_default();
        let (name, kind) = if self.at("~")
            && self.nth(1).kind == ScTokenKind::Ident
            && self.nth(2).is_punct("(")
        {
            let tilde = self.bump().span;
            let id = self.bump();
            let ident = Ident {
                name: format!("~{}", id.text),
                span: tilde.to(id.span),
            };
            (QualifiedName::simple(ident), 2)
        } else if self.at_ident()
            && !class.is_empty()
            && self.peek().text == class
            && self.nth(1).is_punct("(")
        {
            let id = self.expect_ident()?;
            (QualifiedName::simple(id), 1)
        } else if self.at_kw("operator") {
            let id = self.parse_operator_name()?;
            (QualifiedName::simple(id), 3)
        } else {
            self.restore(cp);
            return Ok(None);
        };
        let mut f = function_skeleton(name, start);
        f.specifiers = specs;
        self.parse_function_rest(&mut f, start)?;
        Ok(Some(match kind {
            1 => Member::Constructor(f),
            2 => Member::Destructor(f),
            _ => Member::Method(f),
        }))
    }

    // ---- simple declarations ---------------------------------------------

    /// `[specifiers] type declarator-list ;` or a function declaration or
    /// definition.
    pub(super) fn parse_simple_decl(&mut self, ctx: Ctx) -> PResult<Decl> {
        let start = self.cur_span();
        let is_template = self.pending_template;
        if self.at_kw("typedef") {
            return self.parse_typedef().map(Decl::Typedef);
        }
        let (specs, ty) = self.parse_decl_specifiers()?;
        self.pending_template = false;
        if ctx != Ctx::Condition && self.at(";") {
            self.bump();
            let span = self.span_from(start);
            return Ok(match ty.base {
                TypeName::ClassDef(c) => Decl::Class(*c),
                TypeName::EnumDef(e) => Decl::Enum(*e),
                TypeName::Elaborated { key, name } => match key.as_str() {
                    "class" => Decl::Forward {
                        key: ClassKey::Class,
                        name,
                        span,
                    },
                    "struct" => Decl::Forward {
                        key: ClassKey::Struct,
                        name,
                        span,
                    },
                    "union" => Decl::Forward {
                        key: ClassKey::Union,
                        name,
                        span,
                    },
                    _ => Decl::Empty(span),
                },
                _ => {
                    self.diags.push(ScDiagnostic::warning(
                        "declaration does not declare anything",
                        span,
                    ));
                    Decl::Empty(span)
                }
            });
        }
        let mut declarators = Vec::new();
        loop {
            let dstart = self.cur_span();
            let ptr_ops = self.parse_ptr_ops();
            if self.at("(") && matches!(self.nth(1).text.as_str(), "*" | "&" | "^") {
                let span = self.cur_span();
                return Err(self.error("function pointer declarators are not supported", span));
            }
            // SC_NAMED(name[, args]) (IEEE 1666-2023 §5.17): the object's
            // name string is the variable's own name. SystemC 3.0's
            // SC_NAMED_WITH_INIT(name[, args]) { code } adds code run for
            // the object during construction, and ends the declaration.
            let named_with_init = self.peek().is_ident("SC_NAMED_WITH_INIT");
            if (self.peek().is_ident("SC_NAMED") || named_with_init) && self.nth(1).is_punct("(") {
                self.bump();
                self.bump();
                let name = self.expect_ident()?;
                let mut args = vec![Expr {
                    kind: ExprKind::StringLit {
                        text: format!("\"{}\"", name.name),
                        value: name.name.clone(),
                    },
                    span: name.span,
                }];
                while self.eat(",") {
                    args.push(self.nested(|p| p.parse_assign())?);
                }
                self.expect(")")?;
                declarators.push(Declarator {
                    ptr_ops,
                    name,
                    array_dims: Vec::new(),
                    bitfield: None,
                    init: Some(Initializer::Brace(args)),
                    sc_init: None,
                    span: self.span_from(dstart),
                });
                if named_with_init {
                    let body = self.parse_block()?;
                    let d = declarators.last_mut().expect("just pushed");
                    d.sc_init = Some(body);
                    d.span = self.span_from(dstart);
                    self.eat(";");
                    return Ok(Decl::Var(VarDecl {
                        specifiers: specs,
                        ty,
                        declarators,
                        span: self.span_from(start),
                    }));
                }
            } else {
                let name = if self.at_kw("operator") {
                    QualifiedName::simple(self.parse_operator_name()?)
                } else if ctx == Ctx::Namespace && (self.at_ident() || self.at("::")) {
                    // Out-of-class definitions: `void top::run()`,
                    // `int top::count = 0;`.
                    self.parse_qualified_name(false)?
                } else if ctx == Ctx::Class && self.at(":") {
                    // Unnamed bit-field `int : 3;`
                    QualifiedName::simple(Ident {
                        name: String::new(),
                        span: self.cur_span(),
                    })
                } else {
                    QualifiedName::simple(self.expect_ident()?)
                };
                if self.at("(") && self.paren_is_params(ctx, &name) {
                    if !declarators.is_empty() {
                        let span = self.cur_span();
                        return Err(self.error(
                            "a function declarator cannot follow variable declarators",
                            span,
                        ));
                    }
                    let mut f = function_skeleton(name, start);
                    f.specifiers = specs;
                    f.return_type = Some(ty);
                    f.return_ptr_ops = ptr_ops;
                    self.parse_function_rest(&mut f, start)?;
                    if is_template {
                        self.fn_templates.insert(f.base_name().to_string());
                    }
                    return Ok(Decl::Function(Box::new(f)));
                }
                let ident = if name.segments.len() == 1 && !name.global {
                    name.segments.into_iter().next().expect("one segment").ident
                } else {
                    Ident {
                        name: name.path(),
                        span: name.span,
                    }
                };
                let d = self.parse_var_declarator_rest(ptr_ops, ident, ctx, dstart)?;
                declarators.push(d);
            }
            if ctx == Ctx::Condition || !self.eat(",") {
                break;
            }
        }
        if ctx != Ctx::Condition {
            self.expect(";")?;
        }
        Ok(Decl::Var(VarDecl {
            specifiers: specs,
            ty,
            declarators,
            span: self.span_from(start),
        }))
    }

    /// At `(` after a declarator name: does a parameter list follow (a
    /// function declarator) rather than a parenthesized initializer?
    fn paren_is_params(&mut self, ctx: Ctx, name: &QualifiedName) -> bool {
        if ctx == Ctx::Class || name.segments.len() > 1 {
            return true;
        }
        if ctx == Ctx::Condition {
            return false;
        }
        let t1 = self.nth(1).clone();
        if t1.is_punct(")") {
            // `T f();` declares a function (§9.8); in a function body a
            // SystemC design means an object, so it stays a variable there.
            return ctx == Ctx::Namespace;
        }
        if t1.is_punct("...") {
            return true;
        }
        if t1.kind == ScTokenKind::Keyword {
            return is_builtin_type_keyword(&t1)
                || matches!(
                    t1.text.as_str(),
                    "const"
                        | "volatile"
                        | "struct"
                        | "class"
                        | "enum"
                        | "union"
                        | "typename"
                        | "auto"
                        | "decltype"
                );
        }
        if t1.kind == ScTokenKind::Ident || t1.is_punct("::") {
            let cp = self.checkpoint();
            self.bump(); // (
            let result = match self.parse_qualified_name(true) {
                Ok(q) => {
                    let known = self.names_type(&q);
                    let next = self.peek().clone();
                    let follows_type = matches!(
                        next.text.as_str(),
                        "," | ")" | "*" | "&" | "&&" | "=" | "[" | "..."
                    ) && next.kind == ScTokenKind::Punct
                        || next.is_keyword("const");
                    (known && (follows_type || next.kind == ScTokenKind::Ident))
                        || (next.kind == ScTokenKind::Ident
                            && matches!(self.nth(1).text.as_str(), "," | ")" | "=" | "["))
                }
                Err(Fail) => false,
            };
            self.restore(cp);
            return result;
        }
        false
    }

    fn parse_var_declarator_rest(
        &mut self,
        ptr_ops: Vec<PtrOp>,
        name: Ident,
        ctx: Ctx,
        dstart: ScSpan,
    ) -> PResult<Declarator> {
        let array_dims = self.parse_array_dims()?;
        let bitfield = if ctx == Ctx::Class && self.at(":") {
            self.bump();
            Some(self.parse_conditional()?)
        } else {
            None
        };
        let init = if self.eat("=") {
            Some(Initializer::Assign(if self.at("{") {
                self.parse_init_list_expr()?
            } else {
                self.parse_assign()?
            }))
        } else if self.at("(") {
            Some(Initializer::Paren(self.parse_call_args()?))
        } else if self.at("{") {
            Some(Initializer::Brace(self.parse_brace_list()?))
        } else {
            None
        };
        Ok(Declarator {
            ptr_ops,
            name,
            array_dims,
            bitfield,
            init,
            sc_init: None,
            span: self.span_from(dstart),
        })
    }

    fn parse_array_dims(&mut self) -> PResult<Vec<Option<Expr>>> {
        let mut dims = Vec::new();
        while self.at("[") && !self.nth(1).is_punct("[") {
            self.bump();
            if self.eat("]") {
                dims.push(None);
                continue;
            }
            let e = self.nested(|p| p.parse_expr())?;
            self.expect("]")?;
            dims.push(Some(e));
        }
        Ok(dims)
    }

    // ---- functions --------------------------------------------------------

    fn parse_function_specifiers(&mut self, specs: &mut Specifiers) {
        loop {
            self.skip_attributes();
            if self.eat_kw("virtual") {
                specs.is_virtual = true;
            } else if self.eat_kw("explicit") {
                specs.is_explicit = true;
                if self.at("(") {
                    // C++20 `explicit(bool)`
                    let _ = self.skip_balanced();
                }
            } else if self.eat_kw("inline") {
                specs.is_inline = true;
            } else if self.eat_kw("constexpr") || self.eat_kw("consteval") {
                specs.is_constexpr = true;
            } else if self.eat_kw("static") {
                specs.is_static = true;
            } else if self.eat_kw("friend") {
                specs.is_friend = true;
            } else {
                break;
            }
        }
    }

    /// Everything after the declarator name of a function: parameters,
    /// qualifiers, and the body, `= 0/default/delete` or `;`.
    fn parse_function_rest(&mut self, f: &mut FunctionDecl, start: ScSpan) -> PResult<()> {
        let (params, variadic) = self.parse_params()?;
        f.params = params;
        f.variadic = variadic;
        loop {
            self.skip_attributes();
            if self.eat_kw("const") {
                f.is_const = true;
            } else if self.eat_kw("volatile") {
                f.is_volatile = true;
            } else if self.eat("&") {
                f.ref_qualifier = Some(PtrOp::LRef);
            } else if self.eat("&&") {
                f.ref_qualifier = Some(PtrOp::RRef);
            } else if self.eat_kw("noexcept") {
                f.noexcept = true;
                if self.at("(") {
                    self.skip_balanced()?;
                }
            } else if self.eat_kw("throw") {
                self.skip_balanced()?; // dynamic exception specification
            } else if self.eat_contextual("override") {
                f.is_override = true;
            } else if self.eat_contextual("final") {
                f.is_final = true;
            } else if self.eat("->") {
                f.trailing_return = Some(self.parse_type_id(false)?);
            } else {
                break;
            }
        }
        if self.eat("=") {
            f.special_body = Some(if self.eat_kw("default") {
                FunctionBodyKind::Defaulted
            } else if self.eat_kw("delete") {
                FunctionBodyKind::Deleted
            } else if self.peek().kind == ScTokenKind::IntLit && self.peek().text == "0" {
                self.bump();
                FunctionBodyKind::Pure
            } else {
                return Err(self.err_expected("'0', 'default' or 'delete'"));
            });
            self.expect(";")?;
        } else if self.at(":") {
            f.initializers = self.parse_mem_initializers()?;
            f.body = Some(self.parse_block()?);
        } else if self.at("{") {
            f.body = Some(self.parse_block()?);
        } else if self.at_kw("try") {
            let span = self.cur_span();
            return Err(self.error("function-try-blocks are not supported", span));
        } else {
            self.expect(";")?;
        }
        f.span = self.span_from(start);
        Ok(())
    }

    pub(super) fn parse_params(&mut self) -> PResult<(Vec<Param>, bool)> {
        self.expect("(")?;
        let r = self.nested(|p| {
            let mut params = Vec::new();
            let mut variadic = false;
            if p.at(")") {
                return Ok((params, variadic));
            }
            if p.at_kw("void") && p.nth(1).is_punct(")") {
                p.bump();
                return Ok((params, variadic));
            }
            loop {
                if p.eat("...") {
                    variadic = true;
                    break;
                }
                params.push(p.parse_param()?);
                if p.eat("...") {
                    variadic = true;
                    break;
                }
                if !p.eat(",") {
                    break;
                }
            }
            Ok((params, variadic))
        })?;
        self.expect(")")?;
        Ok(r)
    }

    pub(super) fn parse_param(&mut self) -> PResult<Param> {
        self.skip_attributes();
        let start = self.cur_span();
        let (_, mut ty) = self.parse_decl_specifiers()?;
        ty.ptr_ops = self.parse_ptr_ops();
        if self.at("(") && matches!(self.nth(1).text.as_str(), "*" | "&") {
            let span = self.cur_span();
            return Err(self.error("function pointer parameters are not supported", span));
        }
        self.eat("..."); // parameter pack
        let name = if self.at_ident() {
            Some(self.expect_ident()?)
        } else {
            None
        };
        let array_dims = self.parse_array_dims()?;
        let default = if self.eat("=") {
            Some(if self.at("{") {
                self.parse_init_list_expr()?
            } else {
                self.parse_assign()?
            })
        } else {
            None
        };
        ty.span = ty.span.to(self.prev_span());
        Ok(Param {
            ty,
            name,
            array_dims,
            default,
            span: self.span_from(start),
        })
    }

    fn parse_mem_initializers(&mut self) -> PResult<Vec<MemInit>> {
        self.expect(":")?;
        let mut inits = Vec::new();
        loop {
            let start = self.cur_span();
            let name = self.parse_qualified_name(true)?;
            let (args, braced) = if self.at("(") {
                (self.parse_call_args()?, false)
            } else if self.at("{") {
                (self.parse_brace_list()?, true)
            } else {
                return Err(self.err_expected("'(' or '{' in member initializer"));
            };
            self.eat("...");
            inits.push(MemInit {
                name,
                args,
                braced,
                span: self.span_from(start),
            });
            if !self.eat(",") {
                break;
            }
        }
        Ok(inits)
    }

    /// `operator` followed by the operator or conversion type it names.
    pub(super) fn parse_operator_name(&mut self) -> PResult<Ident> {
        let start = self.cur_span();
        self.bump(); // operator
        let suffix = if self.at("(") && self.nth(1).is_punct(")") {
            self.bump();
            self.bump();
            "()".to_string()
        } else if self.at("[") && self.nth(1).is_punct("]") {
            self.bump();
            self.bump();
            "[]".to_string()
        } else if self.at_kw("new") || self.at_kw("delete") {
            let mut s = self.bump().text;
            if self.at("[") && self.nth(1).is_punct("]") {
                self.bump();
                self.bump();
                s.push_str("[]");
            }
            format!(" {}", s)
        } else if self.peek().kind == ScTokenKind::Punct {
            self.bump().text
        } else if self.peek().kind == ScTokenKind::StringLit && self.peek().text == "\"\"" {
            self.bump();
            let id = self.expect_ident()?;
            format!("\"\" {}", id.name)
        } else {
            // Conversion function `operator bool()`.
            let from = self.pos;
            let _ = self.parse_type_id(false)?;
            format!(" {}", self.spell_from(from))
        };
        Ok(Ident {
            name: format!("operator{}", suffix),
            span: self.span_from(start),
        })
    }

    // ---- types -------------------------------------------------------------

    /// Declaration specifiers: storage and function specifiers, cv
    /// qualifiers and exactly one type.
    pub(super) fn parse_decl_specifiers(&mut self) -> PResult<(Specifiers, Type)> {
        let start = self.cur_span();
        let mut specs = Specifiers::default();
        let mut is_const = false;
        let mut is_volatile = false;
        let mut builtin: Vec<String> = Vec::new();
        let mut base: Option<TypeName> = None;
        loop {
            self.skip_attributes();
            let t = self.peek().clone();
            let no_type = base.is_none() && builtin.is_empty();
            if t.kind == ScTokenKind::Keyword {
                match t.text.as_str() {
                    "static" => specs.is_static = true,
                    "extern" => specs.is_extern = true,
                    "mutable" => specs.is_mutable = true,
                    "inline" => specs.is_inline = true,
                    "virtual" => specs.is_virtual = true,
                    "explicit" => specs.is_explicit = true,
                    "constexpr" | "consteval" | "constinit" => specs.is_constexpr = true,
                    "friend" => specs.is_friend = true,
                    "thread_local" => specs.is_thread_local = true,
                    "register" => specs.is_register = true,
                    "const" => is_const = true,
                    "volatile" => is_volatile = true,
                    "typename" if no_type => {}
                    "auto" if no_type => base = Some(TypeName::Auto),
                    _ if base.is_none() && is_builtin_type_keyword(&t) => {
                        builtin.push(t.text.clone())
                    }
                    "decltype" if no_type => {
                        self.bump();
                        self.expect("(")?;
                        let e = self.nested(|p| p.parse_expr())?;
                        self.expect(")")?;
                        base = Some(TypeName::Decltype(Box::new(e)));
                        continue;
                    }
                    "class" | "struct" | "union" | "enum" if no_type => {
                        base = Some(self.parse_class_or_enum_type()?);
                        continue;
                    }
                    _ => break,
                }
                self.bump();
                continue;
            }
            if no_type && (t.kind == ScTokenKind::Ident || t.is_punct("::")) {
                let q = self.parse_qualified_name(true)?;
                base = Some(TypeName::Named(q));
                continue;
            }
            break;
        }
        let base = if !builtin.is_empty() {
            TypeName::Builtin(builtin.join(" "))
        } else if let Some(b) = base {
            b
        } else {
            return Err(self.err_expected("type"));
        };
        Ok((
            specs,
            Type {
                is_const,
                is_volatile,
                base,
                ptr_ops: Vec::new(),
                span: self.span_from(start),
            },
        ))
    }

    fn parse_class_or_enum_type(&mut self) -> PResult<TypeName> {
        if self.at_type_definition() {
            return Ok(if self.at_kw("enum") {
                TypeName::EnumDef(Box::new(self.parse_enum_specifier()?))
            } else {
                TypeName::ClassDef(Box::new(self.parse_class_specifier()?))
            });
        }
        let key = self.bump().text;
        if key == "enum" {
            let _ = self.eat_kw("class") || self.eat_kw("struct");
        }
        self.skip_attributes();
        let name = self.parse_qualified_name(true)?;
        if let Some(last) = name.segments.last() {
            let n = last.ident.name.clone();
            self.add_type_name(&n);
        }
        if key == "enum" && self.at(":") && !self.at("::") {
            // Opaque enum declaration `enum class e : int;`
            self.bump();
            let _ = self.parse_type_id(false)?;
        }
        Ok(TypeName::Elaborated { key, name })
    }

    pub(super) fn parse_ptr_ops(&mut self) -> Vec<PtrOp> {
        let mut ops = Vec::new();
        loop {
            self.skip_attributes();
            if self.eat("*") {
                let mut is_const = false;
                let mut is_volatile = false;
                loop {
                    if self.eat_kw("const") {
                        is_const = true;
                    } else if self.eat_kw("volatile") {
                        is_volatile = true;
                    } else {
                        break;
                    }
                }
                ops.push(PtrOp::Pointer {
                    is_const,
                    is_volatile,
                });
            } else if self.eat("&") {
                ops.push(PtrOp::LRef);
            } else if self.eat("&&") {
                ops.push(PtrOp::RRef);
            } else {
                break;
            }
        }
        ops
    }

    /// A type-id: specifiers, pointer/reference parts and, where
    /// `fn_types`, a function type's parameter list (`void(int)`).
    pub(super) fn parse_type_id(&mut self, fn_types: bool) -> PResult<Type> {
        let start = self.cur_span();
        let (_, mut ty) = self.parse_decl_specifiers()?;
        ty.ptr_ops = self.parse_ptr_ops();
        if fn_types && self.at("(") && !matches!(self.nth(1).text.as_str(), "*" | "&") {
            let (params, variadic) = self.parse_params()?;
            ty = Type {
                is_const: false,
                is_volatile: false,
                base: TypeName::Function {
                    ret: Box::new(ty),
                    params,
                    variadic,
                },
                ptr_ops: Vec::new(),
                span: start,
            };
        }
        if fn_types && self.at("[") && self.nth(1).is_punct("]") {
            // `unique_ptr<T[]>`: an array of unknown bound.
            self.bump();
            self.bump();
        }
        ty.span = self.span_from(start);
        Ok(ty)
    }

    /// Skip `[[…]]`, `alignas(…)`, `__attribute__((…))` and
    /// `__declspec(…)`: they do not change what a declaration declares.
    pub(super) fn skip_attributes(&mut self) {
        loop {
            if self.at("[") && self.nth(1).is_punct("[") {
                self.bump();
                if self.skip_balanced_from_open().is_err() {
                    return;
                }
                self.eat("]");
            } else if (self.at_kw("alignas")
                || self.peek().is_ident("__attribute__")
                || self.peek().is_ident("__declspec"))
                && self.nth(1).is_punct("(")
            {
                self.bump();
                if self.skip_balanced().is_err() {
                    return;
                }
            } else {
                return;
            }
        }
    }

    /// Skip a balanced `(…)`, `[…]` or `{…}` group starting at the cursor.
    pub(super) fn skip_balanced(&mut self) -> PResult<()> {
        if !(self.at("(") || self.at("[") || self.at("{")) {
            return Err(self.err_expected("'('"));
        }
        self.skip_balanced_from_open()
    }

    fn skip_balanced_from_open(&mut self) -> PResult<()> {
        let open = self.cur_span();
        let mut depth = 0usize;
        loop {
            let t = self.bump();
            match t.text.as_str() {
                _ if t.kind == ScTokenKind::Eof => {
                    return Err(self.error("unbalanced brackets", open));
                }
                "(" | "[" | "{" if t.kind == ScTokenKind::Punct => depth += 1,
                ")" | "]" | "}" if t.kind == ScTokenKind::Punct => {
                    depth = depth.saturating_sub(1);
                    if depth == 0 {
                        return Ok(());
                    }
                }
                _ => {}
            }
        }
    }

    /// Run `f` with bracket depth reset: a `>` inside parentheses, brackets
    /// or braces never closes an enclosing template argument list.
    pub(super) fn nested<T>(&mut self, f: impl FnOnce(&mut Self) -> PResult<T>) -> PResult<T> {
        let saved = self.no_gt;
        self.no_gt = 0;
        let r = f(self);
        self.no_gt = saved;
        r
    }
}
