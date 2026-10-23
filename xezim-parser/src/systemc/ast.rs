//! Typed AST for SystemC designs: the C++ subset the parser accepts, plus
//! the SystemC registration macros as nodes of their own (IEEE 1666-2023).
//!
//! The tree is syntactic. Nothing here resolves names or types; library
//! types such as `sc_in<bool>` are ordinary [`QualifiedName`]s, which
//! [`super::classify`] interprets.

use super::token::ScSpan;

/// An identifier with its location.
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Ident {
    pub name: String,
    pub span: ScSpan,
}

/// A whole preprocessed source file and everything it includes.
#[derive(Debug, Clone, Default, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TranslationUnit {
    pub items: Vec<Item>,
}

/// A namespace-scope declaration.
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Item {
    /// A class, struct or union definition, including `SC_MODULE(name)`.
    Class(ClassDecl),
    /// A function declaration or definition: free functions, `sc_main`, and
    /// out-of-class member definitions (`void top::run() {…}`,
    /// `top::top(sc_module_name n) : … {}`).
    Function(FunctionDecl),
    Var(VarDecl),
    Enum(EnumDecl),
    Typedef(TypedefDecl),
    Using(UsingDecl),
    Namespace {
        /// `None` for an anonymous namespace.
        name: Option<Ident>,
        inline: bool,
        items: Vec<Item>,
        span: ScSpan,
    },
    /// `extern "C" { … }` (or a single `extern "C"` declaration).
    ExternBlock {
        linkage: String,
        items: Vec<Item>,
        span: ScSpan,
    },
    /// `template<…>` applied to the wrapped declaration. `params` is empty for
    /// an explicit specialization (`template<>`).
    Template {
        params: Vec<TemplateParam>,
        item: Box<Item>,
        span: ScSpan,
    },
    /// Explicit instantiation: `template class fifo<int>;`.
    ExplicitInstantiation {
        decl: Box<Item>,
        span: ScSpan,
    },
    StaticAssert(StaticAssert),
    /// `class X;` / `struct X;`
    ForwardDecl {
        key: ClassKey,
        name: QualifiedName,
        span: ScSpan,
    },
    /// A stray `;`.
    Empty(ScSpan),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ClassKey {
    Class,
    Struct,
    Union,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Access {
    Public,
    Protected,
    Private,
}

#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct BaseSpec {
    pub access: Option<Access>,
    pub is_virtual: bool,
    pub name: QualifiedName,
    pub span: ScSpan,
}

/// A class, struct or union. SystemC modules are classes too: `sc_module`
/// is true for `SC_MODULE(name)`, for a class deriving from `sc_module`
/// (any qualification), and for one deriving from another module class of
/// the same translation unit.
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ClassDecl {
    pub key: ClassKey,
    /// `None` for an anonymous class (`struct { int a; } s;`).
    pub name: Option<Ident>,
    pub bases: Vec<BaseSpec>,
    pub members: Vec<Member>,
    pub is_final: bool,
    /// The class is a SystemC module (IEEE 1666-2023 §5.2).
    pub sc_module: bool,
    /// Declared with the `SC_MODULE(name)` macro (§5.2.5).
    pub sc_module_macro: bool,
    pub span: ScSpan,
}

impl ClassDecl {
    pub fn name_str(&self) -> Option<&str> {
        self.name.as_ref().map(|n| n.name.as_str())
    }
}

/// A member of a class body.
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Member {
    /// `public:` / `protected:` / `private:`
    Access(Access, ScSpan),
    Field(VarDecl),
    Method(FunctionDecl),
    /// A constructor; `SC_CTOR(name)` has `sc_ctor` set (§5.2.7).
    Constructor(FunctionDecl),
    Destructor(FunctionDecl),
    /// `SC_HAS_PROCESS(name);` (§5.2.8)
    ScHasProcess(Ident),
    /// SystemC 3.0 in-class process: `SC_METHOD_IMP(f, init…) { body }`,
    /// `SC_THREAD_IMP(f, init…)`, `SC_CTHREAD_IMP(f, edge, init…)`. Declares
    /// member function `void f()` (`method`, whose body may instead be
    /// defined out of class) and registers it as a process during
    /// construction, running `init` (typically its sensitivity) after the
    /// registration.
    ScProcessImp {
        kind: ProcessKind,
        /// The clock edge of an `SC_CTHREAD_IMP`.
        clock: Option<Expr>,
        init: Vec<Stmt>,
        method: FunctionDecl,
        span: ScSpan,
    },
    /// SystemC 3.0 `SC_INIT(name) { … }`: code run during construction.
    ScInit {
        name: Ident,
        body: Block,
        span: ScSpan,
    },
    Typedef(TypedefDecl),
    Enum(EnumDecl),
    NestedClass(ClassDecl),
    Using(UsingDecl),
    /// `class Impl;`
    ForwardDecl {
        key: ClassKey,
        name: QualifiedName,
        span: ScSpan,
    },
    /// `friend class X;` (a friend function is a `Method` with
    /// `specifiers.friend` set).
    Friend {
        name: QualifiedName,
        span: ScSpan,
    },
    StaticAssert(StaticAssert),
    /// `template<…>` member (function or nested class).
    Template {
        params: Vec<TemplateParam>,
        member: Box<Member>,
        span: ScSpan,
    },
    Empty(ScSpan),
}

/// `static_assert(cond, "msg");`
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct StaticAssert {
    pub cond: Expr,
    pub message: Option<Expr>,
    pub span: ScSpan,
}

#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum TemplateParam {
    /// `typename T = int` / `class T`
    Type {
        name: Option<Ident>,
        default: Option<Type>,
        variadic: bool,
        span: ScSpan,
    },
    /// `int N = 8`
    Value {
        ty: Type,
        name: Option<Ident>,
        default: Option<Expr>,
        variadic: bool,
        span: ScSpan,
    },
}

// ---- names and types ------------------------------------------------------

/// `[::] a<…> :: b :: c<…>`
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct QualifiedName {
    /// Leading `::`.
    pub global: bool,
    pub segments: Vec<NameSegment>,
    pub span: ScSpan,
}

impl QualifiedName {
    pub fn simple(ident: Ident) -> Self {
        let span = ident.span;
        QualifiedName {
            global: false,
            segments: vec![NameSegment {
                ident,
                template_args: None,
            }],
            span,
        }
    }

    /// The last segment's identifier (`sc_in` for `sc_core::sc_in<bool>`).
    pub fn last_name(&self) -> &str {
        self.segments.last().map_or("", |s| s.ident.name.as_str())
    }

    /// The last segment's template arguments, if any.
    pub fn last_args(&self) -> Option<&[TemplateArg]> {
        self.segments
            .last()
            .and_then(|s| s.template_args.as_deref())
    }

    /// The segments' identifiers joined by `::`, template arguments
    /// dropped (`sc_core::sc_in`).
    pub fn path(&self) -> String {
        let mut s = String::new();
        if self.global {
            s.push_str("::");
        }
        for (n, seg) in self.segments.iter().enumerate() {
            if n > 0 {
                s.push_str("::");
            }
            s.push_str(&seg.ident.name);
        }
        s
    }

    /// The namespace/class qualifiers before the last segment.
    pub fn qualifiers(&self) -> impl Iterator<Item = &str> {
        self.segments[..self.segments.len().saturating_sub(1)]
            .iter()
            .map(|s| s.ident.name.as_str())
    }
}

#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct NameSegment {
    /// Also `~name` for a destructor and `operator<<` (any operator
    /// spelling) for an operator function.
    pub ident: Ident,
    pub template_args: Option<Vec<TemplateArg>>,
}

/// A template argument. A bare name is a `Type` when it names a type the
/// parser knows of (a library type, a declared class/typedef or a type
/// template parameter) and an `Expr` otherwise.
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum TemplateArg {
    Type(Type),
    Expr(Expr),
}

#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Type {
    pub is_const: bool,
    pub is_volatile: bool,
    pub base: TypeName,
    /// Abstract declarator parts on a type that stands alone (a template
    /// argument, a cast, a parameter without a name): `int*`, `T&`.
    pub ptr_ops: Vec<PtrOp>,
    pub span: ScSpan,
}

#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum TypeName {
    /// A fundamental type, normalized to single spaces in source order:
    /// `"unsigned long long"`, `"bool"`, `"void"`.
    Builtin(String),
    Named(QualifiedName),
    Auto,
    /// `decltype(expr)`
    Decltype(Box<Expr>),
    /// A class defined in place: `struct { int a; } s;`
    ClassDef(Box<ClassDecl>),
    EnumDef(Box<EnumDecl>),
    /// `struct S` / `enum E` used as a type without a body.
    Elaborated {
        key: String,
        name: QualifiedName,
    },
    /// A function type, as in `std::function<void(int)>`.
    Function {
        ret: Box<Type>,
        params: Vec<Param>,
        variadic: bool,
    },
}

impl Type {
    /// The type's named path when it is a [`TypeName::Named`].
    pub fn name(&self) -> Option<&QualifiedName> {
        match &self.base {
            TypeName::Named(q) | TypeName::Elaborated { name: q, .. } => Some(q),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum PtrOp {
    /// `*`, with `const`/`volatile` applying to the pointer itself.
    Pointer { is_const: bool, is_volatile: bool },
    /// `&`
    LRef,
    /// `&&`
    RRef,
}

// ---- declarations ---------------------------------------------------------

#[derive(Debug, Clone, Default, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Specifiers {
    pub is_static: bool,
    pub is_extern: bool,
    pub is_mutable: bool,
    pub is_inline: bool,
    pub is_virtual: bool,
    pub is_explicit: bool,
    pub is_constexpr: bool,
    pub is_friend: bool,
    pub is_thread_local: bool,
    pub is_register: bool,
}

/// `[specifiers] type declarator [, declarator]… ;`
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct VarDecl {
    pub specifiers: Specifiers,
    pub ty: Type,
    pub declarators: Vec<Declarator>,
    pub span: ScSpan,
}

#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Declarator {
    /// `*`, `&`, … applied to this declarator only (`int *a, b;`).
    pub ptr_ops: Vec<PtrOp>,
    pub name: Ident,
    /// `[N]` dimensions; `None` for `[]`.
    pub array_dims: Vec<Option<Expr>>,
    /// `unsigned x : 3;`
    pub bitfield: Option<Expr>,
    pub init: Option<Initializer>,
    /// SystemC 3.0 `T SC_NAMED_WITH_INIT(name) { code }`: code run for this
    /// object during the enclosing module's construction.
    pub sc_init: Option<Block>,
    pub span: ScSpan,
}

#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Initializer {
    /// `= expr` (an `= {…}` list is an [`ExprKind::InitList`]).
    Assign(Expr),
    /// `(a, b)` — e.g. `top t("top");`
    Paren(Vec<Expr>),
    /// `{a, b}` — e.g. `sc_vector<sc_in<bool>> in{"in", 4};`
    Brace(Vec<Expr>),
}

#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct EnumDecl {
    /// `enum class` / `enum struct`
    pub scoped: bool,
    pub name: Option<Ident>,
    pub underlying: Option<Type>,
    pub enumerators: Vec<Enumerator>,
    pub span: ScSpan,
}

#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Enumerator {
    pub name: Ident,
    pub value: Option<Expr>,
}

/// `typedef T name;` or `using name = T;`
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TypedefDecl {
    pub ty: Type,
    /// The declared names with their own pointer/array parts
    /// (`typedef int *ip, arr[4];`).
    pub declarators: Vec<Declarator>,
    pub alias_syntax: bool,
    pub span: ScSpan,
}

#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum UsingDecl {
    /// `using namespace sc_core;`
    Namespace { name: QualifiedName, span: ScSpan },
    /// `using std::cout;` / `using base::f;`
    Declaration { name: QualifiedName, span: ScSpan },
    /// `namespace tu = tlm_utils;`
    NamespaceAlias {
        alias: Ident,
        target: QualifiedName,
        span: ScSpan,
    },
}

#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Param {
    pub ty: Type,
    pub name: Option<Ident>,
    pub array_dims: Vec<Option<Expr>>,
    pub default: Option<Expr>,
    pub span: ScSpan,
}

/// A member initializer `name(args)` / `name{args}`; `name` may be a base
/// class (`sc_module(nm)`).
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct MemInit {
    pub name: QualifiedName,
    pub args: Vec<Expr>,
    pub braced: bool,
    pub span: ScSpan,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum FunctionBodyKind {
    /// `= default;`
    Defaulted,
    /// `= delete;`
    Deleted,
    /// `= 0;`
    Pure,
}

#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct FunctionDecl {
    pub specifiers: Specifiers,
    /// `None` for constructors, destructors and conversion operators.
    pub return_type: Option<Type>,
    /// Pointer/reference parts of the return declarator (`T& get()`).
    pub return_ptr_ops: Vec<PtrOp>,
    pub name: QualifiedName,
    pub params: Vec<Param>,
    /// `f(int, ...)`
    pub variadic: bool,
    pub is_const: bool,
    pub is_volatile: bool,
    pub ref_qualifier: Option<PtrOp>,
    pub noexcept: bool,
    pub is_override: bool,
    pub is_final: bool,
    /// Trailing return type `auto f() -> T`.
    pub trailing_return: Option<Type>,
    pub special_body: Option<FunctionBodyKind>,
    pub initializers: Vec<MemInit>,
    /// `None` for a declaration without a definition.
    pub body: Option<Block>,
    /// Declared with `SC_CTOR(name)` (IEEE 1666-2023 §5.2.7).
    pub sc_ctor: bool,
    pub span: ScSpan,
}

impl FunctionDecl {
    /// The unqualified function name (`run` for `top::run`).
    pub fn base_name(&self) -> &str {
        self.name.last_name()
    }
}

// ---- statements -----------------------------------------------------------

#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Block {
    pub stmts: Vec<Stmt>,
    pub span: ScSpan,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ProcessKind {
    /// `SC_METHOD(f)` (§5.2.9)
    Method,
    /// `SC_THREAD(f)`
    Thread,
    /// `SC_CTHREAD(f, clk.pos())`
    CThread,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum SensitivityEdge {
    /// `sensitive` (§5.4)
    Any,
    /// The deprecated `sensitive_pos`.
    Pos,
    /// The deprecated `sensitive_neg`.
    Neg,
}

#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct SwitchArm {
    /// `case` values; `None` is `default`.
    pub labels: Vec<Option<Expr>>,
    pub body: Vec<Stmt>,
    pub span: ScSpan,
}

#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct CatchClause {
    /// `None` for `catch (...)`.
    pub param: Option<Param>,
    pub body: Block,
}

#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Stmt {
    Block(Block),
    Decl(VarDecl),
    /// A local `typedef` / `using X = T`.
    Typedef(TypedefDecl),
    /// A local `using namespace` / using-declaration.
    Using(UsingDecl),
    /// A local class or enum definition.
    Class(Box<ClassDecl>),
    Enum(EnumDecl),
    StaticAssert(Box<StaticAssert>),
    Expr(Expr),
    If {
        /// `if constexpr`
        constexpr: bool,
        /// C++17 init-statement `if (int x = f(); x > 0)`.
        init: Option<Box<Stmt>>,
        cond: Box<Condition>,
        then_branch: Box<Stmt>,
        else_branch: Option<Box<Stmt>>,
        span: ScSpan,
    },
    Switch {
        init: Option<Box<Stmt>>,
        cond: Box<Condition>,
        arms: Vec<SwitchArm>,
        span: ScSpan,
    },
    For {
        init: Option<Box<Stmt>>,
        cond: Option<Box<Condition>>,
        step: Option<Expr>,
        body: Box<Stmt>,
        span: ScSpan,
    },
    /// `for (auto& x : v)`
    RangeFor {
        decl: Box<Param>,
        range: Expr,
        body: Box<Stmt>,
        span: ScSpan,
    },
    While {
        cond: Box<Condition>,
        body: Box<Stmt>,
        span: ScSpan,
    },
    DoWhile {
        body: Box<Stmt>,
        cond: Expr,
        span: ScSpan,
    },
    Break(ScSpan),
    Continue(ScSpan),
    Return(Option<Expr>, ScSpan),
    Try {
        body: Block,
        handlers: Vec<CatchClause>,
        span: ScSpan,
    },
    /// `label:` before a statement.
    Labeled {
        label: Ident,
        stmt: Box<Stmt>,
        span: ScSpan,
    },
    Empty(ScSpan),
    /// `SC_FORK spawn, spawn, … SC_JOIN` (§5.6): spawn the listed
    /// processes and wait for all of them; `clocked` for `SC_CJOIN`.
    ScFork {
        spawns: Vec<Expr>,
        clocked: bool,
        span: ScSpan,
    },
    /// `SC_METHOD(f);`, `SC_THREAD(f);`, `SC_CTHREAD(f, clk.pos());`
    /// (IEEE 1666-2023 §5.2.9).
    ScProcess {
        kind: ProcessKind,
        func: Ident,
        /// The clock edge of an `SC_CTHREAD`.
        clock: Option<Expr>,
        span: ScSpan,
    },
    /// `sensitive << a << b.pos();`, `sensitive(a, b);`,
    /// `sensitive_pos << clk;` (§5.2.14, §5.4).
    Sensitive {
        edge: SensitivityEdge,
        items: Vec<Expr>,
        span: ScSpan,
    },
    /// `dont_initialize();` (§5.2.16)
    DontInitialize(ScSpan),
    /// `reset_signal_is(rst, true);` / `async_reset_signal_is(…)` (§5.2.13)
    ResetSignalIs {
        is_async: bool,
        signal: Expr,
        level: Expr,
        span: ScSpan,
    },
}

/// The controlling clause of `if`/`while`/`switch`/`for`: an expression or a
/// declaration (`if (auto* p = dynamic_cast<T*>(q))`).
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Condition {
    Expr(Expr),
    Decl(VarDecl),
}

// ---- expressions ----------------------------------------------------------

#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Expr {
    pub kind: ExprKind,
    pub span: ScSpan,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum UnaryOp {
    Plus,
    Neg,
    Not,
    BitNot,
    /// `&x`
    AddrOf,
    /// `*p`
    Deref,
    PreInc,
    PreDec,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum PostfixOp {
    Inc,
    Dec,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum BinaryOp {
    Mul,
    Div,
    Rem,
    Add,
    Sub,
    Shl,
    Shr,
    Lt,
    Gt,
    Le,
    Ge,
    Spaceship,
    Eq,
    Ne,
    BitAnd,
    BitXor,
    BitOr,
    LogAnd,
    LogOr,
    /// `a, b` — in SystemC also bit concatenation of `sc_uint`/`sc_bv`
    /// operands (IEEE 1666-2023 §7.2.7).
    Comma,
    /// `.*`
    PtrMem,
    /// `->*`
    ArrowPtrMem,
}

impl BinaryOp {
    pub fn spelling(self) -> &'static str {
        use BinaryOp::*;
        match self {
            Mul => "*",
            Div => "/",
            Rem => "%",
            Add => "+",
            Sub => "-",
            Shl => "<<",
            Shr => ">>",
            Lt => "<",
            Gt => ">",
            Le => "<=",
            Ge => ">=",
            Spaceship => "<=>",
            Eq => "==",
            Ne => "!=",
            BitAnd => "&",
            BitXor => "^",
            BitOr => "|",
            LogAnd => "&&",
            LogOr => "||",
            Comma => ",",
            PtrMem => ".*",
            ArrowPtrMem => "->*",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum AssignOp {
    Assign,
    Mul,
    Div,
    Rem,
    Add,
    Sub,
    Shl,
    Shr,
    And,
    Xor,
    Or,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum CastKind {
    Static,
    Dynamic,
    Reinterpret,
    Const,
    /// `(T)e`
    CStyle,
}

#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Capture {
    /// `=`
    DefaultCopy,
    /// `&`
    DefaultRef,
    This,
    /// `*this`
    StarThis,
    /// `x`, `&x`, `x = e`, `&x = e`
    Var {
        name: Ident,
        by_ref: bool,
        init: Option<Expr>,
    },
}

#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Lambda {
    pub captures: Vec<Capture>,
    pub params: Vec<Param>,
    pub is_mutable: bool,
    pub return_type: Option<Type>,
    pub body: Block,
}

#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ExprKind {
    /// Integer literal as spelled; `value` when it fits in 64 bits.
    IntLit {
        text: String,
        value: Option<u64>,
    },
    FloatLit {
        text: String,
    },
    /// Character literal as spelled (with quotes and prefix).
    CharLit {
        text: String,
    },
    /// Adjacent string literals concatenated. `value` has the escapes of
    /// ordinary literals decoded; `text` is the first literal's spelling.
    StringLit {
        text: String,
        value: String,
    },
    BoolLit(bool),
    Nullptr,
    This,
    Name(QualifiedName),
    Unary {
        op: UnaryOp,
        operand: Box<Expr>,
    },
    Postfix {
        op: PostfixOp,
        operand: Box<Expr>,
    },
    Binary {
        op: BinaryOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    Assign {
        op: AssignOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    Conditional {
        cond: Box<Expr>,
        then_expr: Box<Expr>,
        else_expr: Box<Expr>,
    },
    Call {
        callee: Box<Expr>,
        args: Vec<Expr>,
    },
    Index {
        base: Box<Expr>,
        index: Box<Expr>,
    },
    /// `a.b` / `p->b`; `name` may carry template args (`x.template f<T>()`).
    Member {
        base: Box<Expr>,
        arrow: bool,
        name: NameSegment,
    },
    Cast {
        kind: CastKind,
        ty: Box<Type>,
        expr: Box<Expr>,
    },
    /// A functional cast or temporary of a type that is not a plain name:
    /// `int(x)`, `unsigned(x)`, `T{a, b}` with `braced`.
    Construct {
        ty: Box<Type>,
        args: Vec<Expr>,
        braced: bool,
    },
    /// `new T(args)` / `new T[n]`
    New {
        ty: Box<Type>,
        placement: Vec<Expr>,
        array_size: Option<Box<Expr>>,
        args: Option<Vec<Expr>>,
    },
    Delete {
        array: bool,
        expr: Box<Expr>,
    },
    SizeofType(Box<Type>),
    SizeofExpr(Box<Expr>),
    /// `sizeof...(Args)`
    SizeofPack(Ident),
    AlignofType(Box<Type>),
    TypeidType(Box<Type>),
    TypeidExpr(Box<Expr>),
    /// `{a, b, c}`
    InitList(Vec<Expr>),
    Lambda(Box<Lambda>),
    Throw(Option<Box<Expr>>),
    /// A parenthesized expression, kept so `(a, b)` concatenation and
    /// explicit grouping stay visible.
    Paren(Box<Expr>),
    /// `pack...` in a call or initializer.
    PackExpansion(Box<Expr>),
    /// `noexcept(expr)`
    NoexceptExpr(Box<Expr>),
}

impl Expr {
    /// The [`QualifiedName`] of a plain name expression.
    pub fn as_name(&self) -> Option<&QualifiedName> {
        match &self.kind {
            ExprKind::Name(q) => Some(q),
            _ => None,
        }
    }
}
