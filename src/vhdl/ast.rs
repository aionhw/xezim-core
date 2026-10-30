//! xezim's own VHDL syntax tree, built from the parser's concrete syntax tree
//! by `cst`. Everything after parsing works on this tree, so the parser crate
//! stays an implementation detail of `cst`.
//!
//! Identifiers are folded to lower case (VHDL is case-insensitive, IEEE
//! 1076-2008 §15.4.2); extended identifiers (`\Foo\`) keep their text,
//! backslashes included. Names are unclassified here: `f(x)` is a call, an
//! index, a slice or a type conversion — semantic analysis decides.

use std::ops::Range;

/// A byte range of the source file the node came from.
pub type Span = Range<usize>;

#[derive(Clone, Debug, PartialEq)]
pub struct Ident {
    pub name: String,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct DesignFile {
    pub units: Vec<DesignUnit>,
}

#[derive(Clone, Debug)]
pub struct DesignUnit {
    pub context: Vec<ContextItem>,
    pub unit: LibraryUnit,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum ContextItem {
    Library(Vec<Ident>),
    Use(Vec<Name>),
    Context(Vec<Name>),
}

#[derive(Clone, Debug)]
pub enum LibraryUnit {
    Entity(EntityDecl),
    Architecture(ArchBody),
    Package(PackageDecl),
    PackageBody(PackageBody),
    PackageInst(PackageInst),
    Configuration(ConfigDecl),
    Context(ContextDecl),
}

impl LibraryUnit {
    pub fn name(&self) -> &Ident {
        match self {
            LibraryUnit::Entity(u) => &u.name,
            LibraryUnit::Architecture(u) => &u.name,
            LibraryUnit::Package(u) => &u.name,
            LibraryUnit::PackageBody(u) => &u.name,
            LibraryUnit::PackageInst(u) => &u.name,
            LibraryUnit::Configuration(u) => &u.name,
            LibraryUnit::Context(u) => &u.name,
        }
    }
}

#[derive(Clone, Debug)]
pub struct EntityDecl {
    pub name: Ident,
    pub generics: Vec<InterfaceDecl>,
    pub ports: Vec<InterfaceDecl>,
    pub decls: Vec<Decl>,
    pub stmts: Vec<ConcStmt>,
}

#[derive(Clone, Debug)]
pub struct ArchBody {
    pub name: Ident,
    pub entity: Ident,
    pub decls: Vec<Decl>,
    pub stmts: Vec<ConcStmt>,
}

#[derive(Clone, Debug)]
pub struct PackageDecl {
    pub name: Ident,
    pub generics: Vec<InterfaceDecl>,
    pub generic_map: Option<Vec<Assoc>>,
    pub decls: Vec<Decl>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct PackageBody {
    pub name: Ident,
    pub decls: Vec<Decl>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct PackageInst {
    pub name: Ident,
    pub package: Name,
    pub generic_map: Vec<Assoc>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct ConfigDecl {
    pub name: Ident,
    pub entity: Name,
    pub block: Option<BlockConfig>,
    pub span: Span,
}

/// `for <block spec> <items> end for;` (§3.4.2).
#[derive(Clone, Debug)]
pub struct BlockConfig {
    /// An architecture name, block label, or generate label with an
    /// optional index, range or alternative label.
    pub spec: Name,
    pub items: Vec<ConfigItem>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum ConfigItem {
    Block(BlockConfig),
    Component(Box<ComponentConfig>),
}

/// `for <component spec> [binding;] [block configuration] end for;`
/// (§3.4.3).
#[derive(Clone, Debug)]
pub struct ComponentConfig {
    pub spec: ComponentSpec,
    pub binding: Option<BindingInd>,
    pub block: Option<BlockConfig>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum InstList {
    Labels(Vec<Ident>),
    Others,
    All,
}

#[derive(Clone, Debug)]
pub struct ComponentSpec {
    pub insts: InstList,
    pub comp: Name,
}

#[derive(Clone, Debug)]
pub enum EntityAspect {
    /// `entity lib.e(arch)`
    Entity(Name, Option<Ident>),
    Configuration(Name),
    Open,
}

/// `use <entity aspect> generic map (…) port map (…)` (§7.3.2).
#[derive(Clone, Debug)]
pub struct BindingInd {
    pub aspect: Option<EntityAspect>,
    pub generic_map: Vec<Assoc>,
    pub port_map: Vec<Assoc>,
    pub span: Span,
}

/// The signals of a disconnection specification (§7.4).
#[derive(Clone, Debug)]
pub enum SignalList {
    Names(Vec<Ident>),
    Others,
    All,
}

/// `disconnect <signals> : <type mark> after <time>;` (§7.4).
#[derive(Clone, Debug)]
pub struct DisconnectSpec {
    pub signals: SignalList,
    pub mark: Name,
    pub after: Expr,
    pub span: Span,
}

/// `for <component spec> <binding>;` in a declarative part (§7.3.1).
#[derive(Clone, Debug)]
pub struct ConfigSpec {
    pub spec: ComponentSpec,
    pub binding: BindingInd,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct ContextDecl {
    pub name: Ident,
    pub items: Vec<ContextItem>,
}

// ---- interfaces -----------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ObjClass {
    Constant,
    Signal,
    Variable,
    File,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mode {
    In,
    Out,
    InOut,
    Buffer,
    Linkage,
}

#[derive(Clone, Debug)]
pub enum InterfaceDecl {
    Object(InterfaceObject),
    /// `type t`, or with its class (VHDL-2019 §6.5.3, `type t is range <>`).
    Type(Ident, Option<TypeClass>),
    Subprogram {
        spec: SubprogramSpec,
        default: Option<SubprogramDefault>,
    },
    Package {
        name: Ident,
        package: Name,
        generic_map: Option<Vec<Assoc>>,
        span: Span,
    },
}

/// The class of a generic type (VHDL-2019 §6.5.3, incomplete type
/// definitions).
#[derive(Clone, Debug)]
pub enum TypeClass {
    /// `private`: any type.
    Private,
    /// `<>`: a scalar type.
    Scalar,
    /// `(<>)`: a discrete type.
    Discrete,
    /// `range <>`: an integer type.
    Integer,
    /// `units <>`: a physical type.
    Physical,
    /// `range <> . <>`: a floating-point type.
    Floating,
    /// `array (index, ...) of element`.
    Array(Vec<ClassIndex>, Box<ClassSubtype>),
    /// `access subtype`.
    Access(Box<ClassSubtype>),
    /// `file of type_mark`.
    File(Box<ClassSubtype>),
}

/// A subtype in a type class: a subtype indication, or an anonymous generic
/// type (`type is (<>)`).
#[derive(Clone, Debug)]
pub enum ClassSubtype {
    Subtype(Box<SubtypeInd>),
    Anonymous(TypeClass),
}

/// An index of an array type class.
#[derive(Clone, Debug)]
pub enum ClassIndex {
    /// `t range <>`
    Unbounded(Name),
    /// A discrete range (`natural range 0 to 3`).
    Range(DiscreteRange),
    /// `type is (<>)`
    Anonymous(TypeClass),
}

#[derive(Clone, Debug)]
pub struct InterfaceObject {
    pub class: Option<ObjClass>,
    pub names: Vec<Ident>,
    pub mode: Option<Mode>,
    pub ty: SubtypeInd,
    pub bus: bool,
    pub default: Option<Expr>,
    /// A mode view (VHDL-2019 §6.5.2), `view v [of t]` or `view (v) of t`.
    /// Without `of`, `ty` is a mark naming the view (its type is the view's).
    pub view: Option<ViewInd>,
    pub span: Span,
}

/// The mode view indication of an interface object.
#[derive(Clone, Debug)]
pub struct ViewInd {
    /// The view, possibly `v'converse`.
    pub name: Name,
    /// `view (v)`: each element of an array has the view.
    pub array: bool,
    /// The subtype was given with `of`.
    pub of: bool,
}

/// A mode view declaration (VHDL-2019 §6.5.2): the modes of the elements of
/// a record type.
#[derive(Clone, Debug)]
pub struct ViewDecl {
    pub name: Ident,
    pub ty: SubtypeInd,
    pub elems: Vec<(Vec<Ident>, ElemMode)>,
    pub span: Span,
}

/// The mode of an element in a mode view.
#[derive(Clone, Debug)]
pub enum ElemMode {
    Mode(Mode),
    /// `view v` (a record element), possibly `v'converse`.
    View(Name),
    /// `view (v)` (an array element of records).
    ArrayView(Name),
}

#[derive(Clone, Debug)]
pub enum SubprogramDefault {
    Box,
    Name(Name),
}

// ---- types ----------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Dir {
    To,
    Downto,
}

/// `left to right`, `left downto right`, or a range attribute name
/// (`x'range`, `t'reverse_range`).
#[derive(Clone, Debug)]
pub enum RangeExpr {
    Explicit {
        left: Box<Expr>,
        dir: Dir,
        right: Box<Expr>,
        span: Span,
    },
    Attr(Name),
}

impl RangeExpr {
    pub fn span(&self) -> Span {
        match self {
            RangeExpr::Explicit { span, .. } => span.clone(),
            RangeExpr::Attr(n) => n.span.clone(),
        }
    }
}

/// A discrete range: an explicit range, a range attribute, or a subtype
/// indication (`natural`, `integer range 0 to 3`).
#[derive(Clone, Debug)]
pub enum DiscreteRange {
    Range(RangeExpr),
    Subtype(SubtypeInd),
}

impl DiscreteRange {
    pub fn span(&self) -> Span {
        match self {
            DiscreteRange::Range(r) => r.span(),
            DiscreteRange::Subtype(s) => s.span.clone(),
        }
    }
}

#[derive(Clone, Debug)]
pub enum Constraint {
    Range(RangeExpr),
    /// Parenthesized constraints in order: an index constraint, then element
    /// constraints (`(open)(7 downto 0)`), or a record constraint
    /// (`(a(3 downto 0))`). The parser cannot tell them apart; semantic
    /// analysis interprets each list against the type (§5.3.2.1, §5.3.3).
    Paren(Vec<Vec<Assoc>>),
}

#[derive(Clone, Debug)]
pub enum Resolution {
    Function(Name),
    /// `(f)` element resolution of an array.
    Element(Box<Resolution>),
    Record(Vec<(Ident, Resolution)>),
}

#[derive(Clone, Debug)]
pub struct SubtypeInd {
    pub resolution: Option<Resolution>,
    pub mark: Name,
    pub constraint: Option<Constraint>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum EnumLit {
    Ident(Ident),
    Char(u8, Span),
}

#[derive(Clone, Debug)]
pub enum ArrayIndex {
    /// `array (natural range <>) of …`: the index subtype marks.
    Unbounded(Vec<Name>),
    Constrained(Vec<DiscreteRange>),
}

#[derive(Clone, Debug)]
pub enum TypeDef {
    Enum(Vec<EnumLit>),
    /// Integer or floating type: decided by the bounds.
    Range(RangeExpr),
    Physical {
        range: RangeExpr,
        primary: Ident,
        secondary: Vec<(Ident, Expr)>,
    },
    Array {
        index: ArrayIndex,
        elem: SubtypeInd,
    },
    Record(Vec<(Vec<Ident>, SubtypeInd)>),
    Access(SubtypeInd),
    File(Name),
    /// A protected type declaration; VHDL-2019 adds a generic clause and map
    /// (§5.6.2), and private variables (the `Decl::Variable`s of `decls`).
    Protected {
        generics: Vec<InterfaceDecl>,
        generic_map: Option<Vec<Assoc>>,
        decls: Vec<Decl>,
    },
    ProtectedBody(Vec<Decl>),
    /// `type t is range implementation_defined` (std.standard only).
    ImplementationDefined,
}

#[derive(Clone, Debug)]
pub struct TypeDecl {
    pub name: Ident,
    /// `None` for an incomplete type declaration (`type t;`).
    pub def: Option<TypeDef>,
    pub span: Span,
}

// ---- declarations -----------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SignalKind {
    Register,
    Bus,
}

#[derive(Clone, Debug)]
pub enum Designator {
    Ident(Ident),
    /// An operator symbol, e.g. `"+"`, folded to lower case (`"and"`).
    Op(String, Span),
}

impl Designator {
    pub fn text(&self) -> &str {
        match self {
            Designator::Ident(i) => &i.name,
            Designator::Op(s, _) => s,
        }
    }
    pub fn span(&self) -> Span {
        match self {
            Designator::Ident(i) => i.span.clone(),
            Designator::Op(_, s) => s.clone(),
        }
    }
}

/// `[t1, t2 return r]`: selects one overload (§4.5.3).
#[derive(Clone, Debug)]
pub struct Signature {
    pub params: Vec<Name>,
    pub ret: Option<Name>,
}

#[derive(Clone, Debug)]
pub enum SubprogramKind {
    Function { pure: bool, ret: Name },
    Procedure,
}

#[derive(Clone, Debug)]
pub struct SubprogramSpec {
    pub kind: SubprogramKind,
    pub designator: Designator,
    pub generics: Vec<InterfaceDecl>,
    pub params: Vec<InterfaceDecl>,
    /// A function's return identifier (VHDL-2019 §4.2.1, `return r of t`):
    /// the subtype of the value the call's context expects.
    pub ret_id: Option<Ident>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct SubprogramBody {
    pub spec: SubprogramSpec,
    pub decls: Vec<Decl>,
    pub stmts: Vec<SeqStmt>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct ObjectDecl {
    pub names: Vec<Ident>,
    pub ty: SubtypeInd,
    pub value: Option<Expr>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct FileOpen {
    pub kind: Option<Expr>,
    pub name: Expr,
}

#[derive(Clone, Debug)]
pub struct ComponentDecl {
    pub name: Ident,
    pub generics: Vec<InterfaceDecl>,
    pub ports: Vec<InterfaceDecl>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct AttributeSpec {
    pub attr: Ident,
    /// The named entities (`others`/`all` as an empty list with the flag).
    pub entities: Vec<Ident>,
    pub all_or_others: bool,
    pub class: String,
    pub value: Expr,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum Decl {
    Type(TypeDecl),
    Subtype {
        name: Ident,
        ind: SubtypeInd,
        span: Span,
    },
    Constant(ObjectDecl),
    Signal {
        obj: ObjectDecl,
        kind: Option<SignalKind>,
    },
    Variable {
        obj: ObjectDecl,
        shared: bool,
    },
    File {
        names: Vec<Ident>,
        ty: SubtypeInd,
        open: Option<FileOpen>,
        span: Span,
    },
    Alias {
        name: Designator,
        ty: Option<SubtypeInd>,
        target: Name,
        signature: Option<Signature>,
        span: Span,
    },
    Component(ComponentDecl),
    ConfigSpec(ConfigSpec),
    Disconnect(DisconnectSpec),
    /// A mode view declaration (VHDL-2019).
    View(ViewDecl),
    Attribute {
        name: Ident,
        mark: Name,
        span: Span,
    },
    AttributeSpec(AttributeSpec),
    SubprogramDecl(SubprogramSpec),
    SubprogramBody(SubprogramBody),
    SubprogramInst {
        spec_kind: SubprogramKind,
        name: Ident,
        uninst: Name,
        generic_map: Vec<Assoc>,
        span: Span,
    },
    Use(Vec<Name>),
    Package(Box<PackageDecl>),
    PackageBody(Box<PackageBody>),
    PackageInst(Box<PackageInst>),
    /// A declaration xezim does not model yet, with its kind for the error.
    Unsupported(String, Span),
}

// ---- concurrent statements -------------------------------------------------

#[derive(Clone, Debug)]
pub enum Sensitivity {
    All,
    List(Vec<Name>),
}

#[derive(Clone, Debug)]
pub enum InstUnit {
    Component(Name),
    Entity(Name, Option<Ident>),
    Configuration(Name),
}

#[derive(Clone, Debug)]
pub struct GenerateBranch {
    pub alt_label: Option<Ident>,
    /// The condition (if-generate) or choices (case-generate); `None` for
    /// the `else` branch.
    pub cond: Option<Expr>,
    pub choices: Vec<Choice>,
    pub decls: Vec<Decl>,
    pub stmts: Vec<ConcStmt>,
}

#[derive(Clone, Debug)]
pub enum ConcKind {
    Process {
        postponed: bool,
        sens: Option<Sensitivity>,
        decls: Vec<Decl>,
        stmts: Vec<SeqStmt>,
    },
    SignalAssign {
        postponed: bool,
        guarded: bool,
        target: Target,
        delay: Option<DelayMech>,
        rhs: AssignRhs<Waveform>,
    },
    Assert {
        postponed: bool,
        cond: Expr,
        report: Option<Expr>,
        severity: Option<Expr>,
    },
    ProcCall {
        postponed: bool,
        call: Name,
    },
    Instance {
        unit: InstUnit,
        generic_map: Vec<Assoc>,
        port_map: Vec<Assoc>,
    },
    Block {
        guard: Option<Expr>,
        generics: Vec<InterfaceDecl>,
        generic_map: Vec<Assoc>,
        ports: Vec<InterfaceDecl>,
        port_map: Vec<Assoc>,
        decls: Vec<Decl>,
        stmts: Vec<ConcStmt>,
    },
    ForGenerate {
        param: Ident,
        range: DiscreteRange,
        decls: Vec<Decl>,
        stmts: Vec<ConcStmt>,
    },
    IfGenerate(Vec<GenerateBranch>),
    CaseGenerate {
        expr: Expr,
        branches: Vec<GenerateBranch>,
    },
    Unsupported(String),
}

#[derive(Clone, Debug)]
pub struct ConcStmt {
    pub label: Option<Ident>,
    pub kind: ConcKind,
    pub span: Span,
}

// ---- sequential statements ---------------------------------------------------

#[derive(Clone, Debug)]
pub enum Target {
    Name(Name),
    Aggregate(Vec<ElemAssoc>, Span),
}

impl Target {
    pub fn span(&self) -> Span {
        match self {
            Target::Name(n) => n.span.clone(),
            Target::Aggregate(_, s) => s.clone(),
        }
    }
}

#[derive(Clone, Debug)]
pub enum DelayMech {
    Transport,
    /// `inertial` or `reject t inertial`.
    Inertial(Option<Expr>),
}

#[derive(Clone, Debug)]
pub struct WaveElem {
    /// `None` for a null transaction (`null after t`).
    pub value: Option<Expr>,
    pub after: Option<Expr>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum Waveform {
    Elems(Vec<WaveElem>),
    Unaffected(Span),
}

#[derive(Clone, Debug)]
pub enum AssignRhs<T> {
    Simple(T),
    /// `a when c1 else b when c2 else d`: the final `else` has no condition.
    Cond(Vec<(T, Option<Expr>)>),
    Select {
        expr: Expr,
        matching: bool,
        items: Vec<(T, Vec<Choice>)>,
    },
}

#[derive(Clone, Debug)]
pub enum LoopScheme {
    Plain,
    While(Expr),
    For(Ident, DiscreteRange),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ForceMode {
    In,
    Out,
}

#[derive(Clone, Debug)]
pub enum SeqKind {
    Wait {
        on: Vec<Name>,
        until: Option<Expr>,
        timeout: Option<Expr>,
    },
    Assert {
        cond: Expr,
        report: Option<Expr>,
        severity: Option<Expr>,
    },
    Report {
        msg: Expr,
        severity: Option<Expr>,
    },
    SignalAssign {
        target: Target,
        delay: Option<DelayMech>,
        rhs: AssignRhs<Waveform>,
    },
    Force {
        target: Target,
        mode: Option<ForceMode>,
        rhs: AssignRhs<Expr>,
    },
    Release {
        target: Target,
        mode: Option<ForceMode>,
    },
    VarAssign {
        target: Target,
        rhs: AssignRhs<Expr>,
    },
    ProcCall(Name),
    If {
        branches: Vec<(Expr, Vec<SeqStmt>)>,
        else_branch: Option<Vec<SeqStmt>>,
    },
    Case {
        matching: bool,
        expr: Expr,
        alts: Vec<(Vec<Choice>, Vec<SeqStmt>)>,
    },
    Loop {
        scheme: LoopScheme,
        body: Vec<SeqStmt>,
    },
    Next {
        label: Option<Ident>,
        cond: Option<Expr>,
    },
    Exit {
        label: Option<Ident>,
        cond: Option<Expr>,
    },
    Return(Option<Expr>),
    Null,
    /// A sequential block statement (VHDL-2019).
    Block {
        decls: Vec<Decl>,
        stmts: Vec<SeqStmt>,
    },
    Unsupported(String),
}

#[derive(Clone, Debug)]
pub struct SeqStmt {
    pub label: Option<Ident>,
    pub kind: SeqKind,
    pub span: Span,
}

// ---- expressions and names -------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinOp {
    And,
    Or,
    Nand,
    Nor,
    Xor,
    Xnor,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    MatchEq,
    MatchNe,
    MatchLt,
    MatchLe,
    MatchGt,
    MatchGe,
    Sll,
    Srl,
    Sla,
    Sra,
    Rol,
    Ror,
    Add,
    Sub,
    Concat,
    Mul,
    Div,
    Mod,
    Rem,
    Pow,
}

impl BinOp {
    /// The operator's designator (`"+"`, `"and"`), as overloads name it.
    pub fn symbol(self) -> &'static str {
        use BinOp::*;
        match self {
            And => "and",
            Or => "or",
            Nand => "nand",
            Nor => "nor",
            Xor => "xor",
            Xnor => "xnor",
            Eq => "=",
            Ne => "/=",
            Lt => "<",
            Le => "<=",
            Gt => ">",
            Ge => ">=",
            MatchEq => "?=",
            MatchNe => "?/=",
            MatchLt => "?<",
            MatchLe => "?<=",
            MatchGt => "?>",
            MatchGe => "?>=",
            Sll => "sll",
            Srl => "srl",
            Sla => "sla",
            Sra => "sra",
            Rol => "rol",
            Ror => "ror",
            Add => "+",
            Sub => "-",
            Concat => "&",
            Mul => "*",
            Div => "/",
            Mod => "mod",
            Rem => "rem",
            Pow => "**",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnOp {
    Plus,
    Minus,
    Abs,
    Not,
    /// Reduction operators (VHDL-2008 §9.2.2): `and x`, `or x`, …
    And,
    Or,
    Nand,
    Nor,
    Xor,
    Xnor,
    /// Condition operator `??` (§9.2.9).
    Cond,
}

impl UnOp {
    pub fn symbol(self) -> &'static str {
        use UnOp::*;
        match self {
            Plus => "+",
            Minus => "-",
            Abs => "abs",
            Not => "not",
            And => "and",
            Or => "or",
            Nand => "nand",
            Nor => "nor",
            Xor => "xor",
            Xnor => "xnor",
            Cond => "??",
        }
    }
}

#[derive(Clone, Debug)]
pub enum Literal {
    /// Integer literal (decimal or based), value as written.
    Int(i128),
    Real(f64),
    /// A physical literal: abstract literal (default 1) and unit name.
    Physical(Box<Literal>, Name),
    Char(u8),
    /// String literal, characters as Latin-1 codes.
    Str(Vec<u8>),
    /// Bit string literal expanded to its string of characters (§15.8).
    BitStr(Vec<u8>),
    Null,
}

#[derive(Clone, Debug)]
pub enum Choice {
    Expr(Expr),
    Range(DiscreteRange),
    Others(Span),
}

#[derive(Clone, Debug)]
pub struct ElemAssoc {
    pub choices: Vec<Choice>,
    pub value: Expr,
}

#[derive(Clone, Debug)]
pub enum Actual {
    Expr(Expr),
    Open(Span),
}

#[derive(Clone, Debug)]
pub struct Assoc {
    pub formal: Option<Name>,
    pub actual: Actual,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum Suffix {
    Ident(Ident),
    Char(u8, Span),
    Op(String, Span),
    All(Span),
}

#[derive(Clone, Debug)]
pub enum NameKind {
    Simple(Ident),
    /// An operator symbol used as a name (`"+"(a, b)`).
    Op(String),
    /// A character literal used as a name (an enumeration literal).
    Char(u8),
    Selected(Box<Name>, Suffix),
    /// `prefix(assoc, …)`: call, index, slice or conversion.
    Call(Box<Name>, Vec<Assoc>),
    /// `prefix'attr` or `prefix'attr(expr)`, with an optional signature.
    Attribute(Box<Name>, Ident, Option<Box<Expr>>),
    External {
        class: ObjClass,
        path: String,
        ty: Box<SubtypeInd>,
    },
}

#[derive(Clone, Debug)]
pub struct Name {
    pub kind: NameKind,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum ExprKind {
    Name(Name),
    Lit(Literal),
    Aggregate(Vec<ElemAssoc>),
    Qualified(Name, Box<Expr>),
    New(Box<Expr>),
    /// `new t` with a subtype indication.
    NewSubtype(Box<SubtypeInd>),
    Binary(BinOp, Box<Expr>, Box<Expr>),
    Unary(UnOp, Box<Expr>),
    Paren(Box<Expr>),
    /// A conditional expression (VHDL-2019 §9.1), `a when c1 else b when c2
    /// else d`: the (value, condition) arms and the final value.
    Cond(Vec<(Expr, Expr)>, Box<Expr>),
    /// A range where an expression was parsed (slice index, choice).
    Range(Box<RangeExpr>),
}

#[derive(Clone, Debug)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}
