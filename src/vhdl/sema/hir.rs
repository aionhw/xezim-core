//! The analysed design: types, objects and subprograms in arenas, and the
//! typed intermediate form (HIR) of expressions and statements. Names are
//! resolved, overloads chosen and implicit conversions made explicit, so the
//! lowering never looks at VHDL visibility or overloading again.

use crate::vhdl::ast::{Dir, Mode, ObjClass, Span};

/// Index of a type or subtype in `Design::types`.
pub type TypeId = usize;
/// Index of an object (signal, variable, constant, port, generic,
/// parameter, loop parameter, file) in `Design::objects`.
pub type ObjId = usize;
/// Index of a subprogram in `Design::subprograms`.
pub type SubId = usize;
/// Index of a source file (`Design::files`).
pub type FileId = usize;

/// A source location: file and byte range.
#[derive(Clone, Debug, PartialEq)]
pub struct Loc {
    pub file: FileId,
    pub span: Span,
}

// ---- values -------------------------------------------------------------------

/// A value known at analysis/elaboration time.
#[derive(Clone, Debug, PartialEq)]
pub enum Value {
    Int(i64),
    Real(f64),
    /// Enumeration position.
    Enum(u32),
    /// Physical value in base units.
    Phys(i64),
    /// Array: bounds and elements (left to right).
    Array(Box<ArrayValue>),
    Record(Vec<Value>),
    Null,
}

#[derive(Clone, Debug, PartialEq)]
pub struct ArrayValue {
    pub left: i64,
    pub dir: Dir,
    pub right: i64,
    pub elems: Vec<Value>,
}

impl Value {
    pub fn as_i64(&self) -> Option<i64> {
        match self {
            Value::Int(v) | Value::Phys(v) => Some(*v),
            Value::Enum(v) => Some(*v as i64),
            _ => None,
        }
    }
}

/// A static discrete or real range.
#[derive(Clone, Debug, PartialEq)]
pub struct StaticRange {
    pub left: Value,
    pub dir: Dir,
    pub right: Value,
}

impl StaticRange {
    /// The number of elements of a discrete range (0 for a null range).
    pub fn length(&self) -> i64 {
        let (l, r) = (
            self.left.as_i64().unwrap_or(0),
            self.right.as_i64().unwrap_or(0),
        );
        let n = match self.dir {
            Dir::To => r - l + 1,
            Dir::Downto => l - r + 1,
        };
        n.max(0)
    }
}

// ---- types ----------------------------------------------------------------------

#[derive(Clone, Debug)]
pub enum TypeKind {
    /// Enumeration literals: identifiers (lower case) or `'c'` characters.
    Enum(Vec<String>),
    Integer,
    Real,
    /// Physical units in base units (the first is the primary unit, 1).
    Physical(Vec<(String, i64)>),
    /// Array: index subtypes (their ranges bound an unconstrained array) and
    /// element subtype.
    Array {
        index: Vec<TypeId>,
        elem: TypeId,
    },
    Record(Vec<(String, TypeId)>),
    Access(TypeId),
    File(TypeId),
    Protected,
    /// A subtype of `base` with a constraint and/or resolution function.
    Subtype {
        base: TypeId,
        constraint: Option<HConstraint>,
        resolution: Option<SubId>,
    },
    Incomplete,
    UniversalInteger,
    UniversalReal,
}

#[derive(Clone, Debug)]
pub enum HConstraint {
    /// Scalar range constraint.
    Range(HRange),
    /// Array index ranges (one per dimension, `None` for `open`) and an
    /// element subtype (for VHDL-2008 element constraints).
    Index(Vec<Option<HRange>>, Option<TypeId>),
    /// Record element subtypes.
    Record(Vec<(usize, TypeId)>),
}

/// A range: explicit bounds (static values where known).
#[derive(Clone, Debug)]
pub struct HRange {
    pub left: Box<HExpr>,
    pub dir: Dir,
    pub right: Box<HExpr>,
    pub static_val: Option<StaticRange>,
    /// `x'range` / `x'reverse_range` of an array object whose bounds are
    /// only known at run time: the object, dimension (0-based) and whether
    /// reversed. `left`/`right`/`dir` are then placeholders.
    pub of_obj: Option<(Box<HExpr>, usize, bool)>,
}

#[derive(Clone, Debug)]
pub struct TypeInfo {
    pub name: String,
    pub kind: TypeKind,
    /// For scalar base types, the type's range (static).
    pub range: Option<StaticRange>,
    pub loc: Option<Loc>,
}

// ---- objects ------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ObjKind {
    Constant,
    Signal,
    Variable,
    SharedVariable,
    File,
    /// An entity port.
    Port(Mode),
    Generic,
    /// A subprogram parameter of the given class and mode.
    Param(ObjClass, Mode),
    /// A `for` loop or for-generate parameter.
    LoopParam,
}

#[derive(Clone, Debug)]
pub struct ObjInfo {
    pub name: String,
    pub kind: ObjKind,
    pub ty: TypeId,
    pub init: Option<HExpr>,
    pub loc: Loc,
    /// The value of a constant or generic when known statically.
    pub static_val: Option<Value>,
}

// ---- subprograms --------------------------------------------------------------

/// A predefined operation (LRM §9.2, §5): no body, lowered natively.
#[derive(Clone, Debug, PartialEq)]
pub enum Builtin {
    /// A predefined operator on its operand types.
    Op(String),
    MinMax(bool),
    ToString,
    RisingEdge,
    FallingEdge,
    Now,
    Deallocate,
    FileOpen,
    FileClose,
    Read,
    Write,
    EndFile,
    Flush,
    /// A subprogram of std.env / std.textio implemented natively.
    Native(String),
}

#[derive(Clone, Debug)]
pub struct SubInfo {
    pub name: String,
    pub is_function: bool,
    pub pure: bool,
    pub params: Vec<ObjId>,
    pub ret: Option<TypeId>,
    pub builtin: Option<Builtin>,
    pub body: Option<Body>,
    pub loc: Option<Loc>,
    /// Full path for unique lowering names, e.g. `ieee.numeric_std."+"`.
    pub path: String,
}

#[derive(Clone, Debug)]
pub struct Body {
    pub locals: Vec<ObjId>,
    pub stmts: Vec<HStmt>,
}

// ---- expressions ----------------------------------------------------------------

#[derive(Clone, Debug)]
pub enum HExprKind {
    Lit(Value),
    Obj(ObjId),
    Call(SubId, Vec<HExpr>),
    Index(Box<HExpr>, Vec<HExpr>),
    Slice(Box<HExpr>, HRange),
    Field(Box<HExpr>, usize),
    /// Array aggregate: positional elements, named choices, `others`.
    ArrayAgg(Vec<(Vec<HChoice>, HExpr)>),
    RecordAgg(Vec<HExpr>),
    /// Type conversion to the target type.
    Convert(Box<HExpr>),
    /// Qualified expression (type check only).
    Qualified(Box<HExpr>),
    /// Predefined attribute of a type or object.
    Attr(String, Box<AttrPrefix>, Option<Box<HExpr>>),
    /// `p.all` (explicit or implicit, §8.3).
    Deref(Box<HExpr>),
    /// `new T'(v)`: the initial value.
    New(Option<Box<HExpr>>),
    /// `new T`: an object of subtype T with its default value.
    NewOf(TypeId),
}

#[derive(Clone, Debug)]
pub enum AttrPrefix {
    Type(TypeId),
    Expr(HExpr),
}

#[derive(Clone, Debug)]
pub enum HChoice {
    Expr(HExpr),
    Range(HRange),
    Others,
}

#[derive(Clone, Debug)]
pub struct HExpr {
    pub kind: HExprKind,
    pub ty: TypeId,
    pub loc: Loc,
}

// ---- statements ------------------------------------------------------------------

#[derive(Clone, Debug)]
pub struct HWave {
    pub value: Option<HExpr>,
    pub after: Option<HExpr>,
}

#[derive(Clone, Debug)]
pub enum HDelay {
    Transport,
    Inertial(Option<HExpr>),
}

#[derive(Clone, Debug)]
pub enum HStmtKind {
    Wait {
        on: Vec<HExpr>,
        until: Option<HExpr>,
        timeout: Option<HExpr>,
    },
    Assert {
        cond: Option<HExpr>,
        report: Option<HExpr>,
        severity: Option<HExpr>,
    },
    SignalAssign {
        target: HExpr,
        delay: Option<HDelay>,
        waves: Vec<HWave>,
    },
    VarAssign {
        target: HExpr,
        value: HExpr,
    },
    Call(SubId, Vec<HExpr>),
    If(Vec<(HExpr, Vec<HStmt>)>, Option<Vec<HStmt>>),
    Case {
        expr: HExpr,
        alts: Vec<(Vec<HChoice>, Vec<HStmt>)>,
    },
    Loop {
        label: usize,
        scheme: HLoop,
        body: Vec<HStmt>,
    },
    Next(usize, Option<HExpr>),
    Exit(usize, Option<HExpr>),
    Return(Option<HExpr>),
    Null,
}

#[derive(Clone, Debug)]
pub enum HLoop {
    Plain,
    While(HExpr),
    For(ObjId, HRange),
}

#[derive(Clone, Debug)]
pub struct HStmt {
    pub kind: HStmtKind,
    pub loc: Loc,
}

// ---- design structure ------------------------------------------------------------

/// A process of an architecture (concurrent statements are rewritten as
/// processes, LRM §11).
#[derive(Clone, Debug)]
pub struct Process {
    pub label: String,
    pub postponed: bool,
    /// Static sensitivity (`process (a, b)`; `process (all)` resolved).
    pub sens: Option<Vec<HExpr>>,
    pub locals: Vec<ObjId>,
    pub stmts: Vec<HStmt>,
    pub loc: Loc,
}

#[derive(Clone, Debug)]
pub struct Architecture {
    pub entity: String,
    pub name: String,
    pub library: String,
    pub generics: Vec<ObjId>,
    pub ports: Vec<ObjId>,
    pub signals: Vec<ObjId>,
    pub constants: Vec<ObjId>,
    pub processes: Vec<Process>,
    pub instances: Vec<Instance>,
    /// A block statement or generate iteration (§11.2, §11.8): a scope
    /// nested in its parent's, instantiated in place.
    pub nested: bool,
    pub loc: Loc,
}

#[derive(Clone, Debug)]
pub struct Instance {
    pub label: String,
    pub library: String,
    pub entity: String,
    pub arch: Option<String>,
    /// The bound architecture (index into `Design::archs`), set once the
    /// design is analysed.
    pub arch_index: Option<usize>,
    pub generic_map: Vec<(ObjId, HExpr)>,
    /// Port (of the instantiated entity) → actual (`None` for `open`).
    pub port_map: Vec<(ObjId, Option<HExpr>)>,
    /// Port associations with a conversion or a partial formal (their
    /// formals have `None` in `port_map` and a signal of their own).
    pub port_conv: Vec<PortConv>,
    /// The block configuration of the bound architecture (index into
    /// `Design::block_configs`), from a configuration declaration.
    pub config: Option<usize>,
    pub loc: Loc,
}

/// A port association with a conversion function, a type conversion or
/// a partial formal (§6.5.7.1). Values pass without a delta (§14.7.3.4).
#[derive(Clone, Debug)]
pub struct PortConv {
    pub formal: ObjId,
    pub mode: Mode,
    /// Mode `in`: the formal or a part of it (instance context).
    /// Mode `out`/`buffer`: the actual signal name (enclosing context).
    pub target: HExpr,
    /// Mode `in`: the actual part (enclosing context); `out`/`buffer`:
    /// the formal part (instance context).
    pub value: HExpr,
}

/// An analysed package: its objects (constants, signals, shared variables)
/// and subprograms, in declaration order.
#[derive(Clone, Debug, Default)]
pub struct Package {
    pub library: String,
    pub name: String,
    pub objects: Vec<ObjId>,
    pub subprograms: Vec<SubId>,
}
