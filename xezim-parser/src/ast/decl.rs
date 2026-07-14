//! SystemVerilog declarations (IEEE 1800-2017 §A.2)


use super::{Identifier, Span};
use super::expr::Expression;
use super::stmt::{Statement, VarDeclarator};
use super::types::*;

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ModuleItem {
    PortDeclaration(PortDeclaration),
    NetDeclaration(NetDeclaration),
    DataDeclaration(DataDeclaration),
    ParameterDeclaration(ParameterDeclaration),
    LocalparamDeclaration(ParameterDeclaration),
    TypedefDeclaration(TypedefDeclaration),
    AlwaysConstruct(AlwaysConstruct),
    InitialConstruct(InitialConstruct),
    FinalConstruct(FinalConstruct),
    ContinuousAssign(ContinuousAssign),
    ModuleInstantiation(ModuleInstantiation),
    GateInstantiation(GateInstantiation),
    GenerateRegion(GenerateRegion),
    /// Generate-if: condition + then-items, and a chain of (condition, items) for else-if/else
    GenerateIf(GenerateIf),
    GenerateFor(GenerateFor),
    /// Generate-case: case (constant_expr) values: items ... endcase
    /// Each arm matches one or more case values; an arm with empty `values`
    /// is the `default` arm. Used to pick between alternative module
    /// instantiations based on a parameter / genvar.
    GenerateCase(GenerateCase),
    GenvarDeclaration(GenvarDeclaration),
    FunctionDeclaration(FunctionDeclaration),
    TaskDeclaration(TaskDeclaration),
    ImportDeclaration(ImportDeclaration),
    TimeunitsDecl(TimeunitsDeclaration),
    ClassDeclaration(ClassDeclaration),
    AssertionItem(super::stmt::AssertionStatement),
    ModportDeclaration(ModportDeclaration),
    PropertyDeclaration(PropertyDeclaration),
    SequenceDeclaration(SequenceDeclaration),
    CovergroupDeclaration(CovergroupDeclaration),
    ClockingDeclaration(ClockingDeclaration),
    CheckerDeclaration(CheckerDeclaration),
    LetDeclaration(LetDeclaration),
    NettypeDeclaration(NettypeDeclaration),
    SpecifyBlock(SpecifyBlock),
    DPIImport(DPIImport),
    DPIExport(DPIExport),
    /// Out-of-class constraint definition: `constraint ClassName::cname { ... }`.
    /// Only the qualified name is tracked; body is not modeled.
    /// §18.5.1 `constraint Class::name { ... }` — the BODY is carried so the
    /// class's extern-constraint prototype can be filled in at elaboration
    /// (it used to be brace-skipped and discarded, so the constraints simply
    /// did not exist at solve time).
    OutOfClassConstraint { class_name: String, constraint_name: String, items: Vec<crate::ast::decl::ConstraintItem> },
    /// `bind <target> <module> <inst>(<ports>);` appearing as a module item
    /// (rather than at compilation-unit scope). Treated by elaboration the
    /// same way as a top-level bind: the wrapped instantiation is appended
    /// to every instance of `target`.
    Bind(BindDirective),
    Null,
}

/// IEEE 1800-2023 §23.11 — `bind` directive. A lightweight, top-level form
/// is supported: `bind <target_module> <bind_module> <inst_name>(.<port>(<expr>), ...);`
/// is desugared by elaboration into a `ModuleInstantiation` appended to
/// `target_module`'s item list, so every instance of `target_module` gets
/// the bound module attached (typically a covergroup / assertion / monitor
/// holder).
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct BindDirective {
    /// Identifier of the module type the bind attaches to.
    pub target_module: Identifier,
    /// The instantiation appended into every instance of `target_module`.
    pub instantiation: ModuleInstantiation,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct CheckerDeclaration {
    pub name: Identifier,
    pub ports: super::module::PortList,
    pub items: Vec<ModuleItem>,
    pub endlabel: Option<Identifier>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct LetDeclaration {
    pub name: Identifier,
    pub ports: super::module::PortList, // let parameters look like ports
    pub expr: Expression,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct NettypeDeclaration {
    pub data_type: DataType,
    pub name: Identifier,
    pub resolver: Option<Identifier>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct SpecifyBlock {
    pub paths: Vec<SpecifyPath>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct SpecifyPath {
    pub src: Identifier,
    pub dst: Identifier,
    pub delay: Expression,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct DPIImport {
    pub property: Option<DPIProperty>,
    pub c_name: Option<String>,
    pub proto: DPIProto,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct DPIExport {
    pub c_name: Option<String>,
    pub proto: DPIProto,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum DPIProto {
    Function(FunctionDeclaration),
    Task(TaskDeclaration),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum DPIProperty { Context, Pure }

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ClockingDeclaration {
    pub name: Identifier,
    /// LRM §14.3: clock event (e.g. `@(posedge clk)`). The signal
    /// expression is captured so the simulator can snapshot input
    /// signals before each clock edge. None when the clocking block
    /// was declared without an event — implementation-defined behavior.
    #[cfg_attr(feature = "serde", serde(default))]
    pub clock_signal: Option<Identifier>,
    pub signals: Vec<ClockingSignal>,
    pub items: Vec<super::stmt::Statement>, // Approximate clocking body as statements
    pub endlabel: Option<Identifier>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ClockingSignal {
    pub direction: PortDirection,
    pub name: Identifier,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct CovergroupDeclaration {
    pub name: Identifier,
    pub event: Option<super::stmt::EventControl>,
    pub items: Vec<CovergroupItem>,
    pub endlabel: Option<Identifier>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum CovergroupItem {
    Coverpoint(Coverpoint),
    Cross(Cross),
    Option { name: String, val: Expression },
    TypeOption { name: String, val: Expression },
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Coverpoint {
    pub name: Option<Identifier>,
    pub expr: Expression,
    /// LRM §19.5 `coverpoint x iff (guard)` — sample is skipped when the
    /// guard evaluates false. `None` means "always sample".
    #[cfg_attr(feature = "serde", serde(default))]
    pub iff_guard: Option<Expression>,
    /// LRM §19.5 explicit bins. Empty when the coverpoint uses the implicit
    /// "every distinct sampled value is its own bin" model.
    #[cfg_attr(feature = "serde", serde(default))]
    pub bins: Vec<CoverBin>,
    pub span: Span,
}

/// LRM §19.5 bin declaration.
///
/// Minimum-viable shape: one of
/// - `bins name = { v1, v2, [lo:hi] };`            → `kind = Bins`
/// - `ignore_bins name = { ... };`                  → `kind = Ignore`
/// - `illegal_bins name = { ... };`                 → `kind = Illegal`
///
/// Not yet covered: `bins name[N] = …` (auto array of N bins),
/// `bins name = ( a => b );` transition bins, `default`, `wildcard`.
/// Those parse-skip and are silently absent from the coverage DB.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct CoverBin {
    pub name: Identifier,
    pub kind: CoverBinKind,
    pub values: Vec<ConstraintRange>,
    /// LRM §19.5 `bins name[]` or `bins name[N]` — the auto-array form
    /// creates one sub-bin per distinct matched value (or N evenly-spread
    /// sub-bins). Sampler records hits under `name[<value>]` keys instead
    /// of one aggregate counter. Today we honor only the `[]` shape;
    /// `[N]` is treated the same. `None` means scalar (single bin).
    #[cfg_attr(feature = "serde", serde(default))]
    pub array_form: bool,
    /// LRM §19.5 `wildcard bins name = { pattern };` — bit-wise match
    /// where `x`/`z`/`?` bits in `pattern` are don't-cares. Sampler
    /// switches to per-bit compare honoring the value's xz_bits mask.
    #[cfg_attr(feature = "serde", serde(default))]
    pub is_wildcard: bool,
    /// LRM §19.5 transition bins `bins name = (prev => cur);` or longer
    /// chains `(a => b => c)`. Each step in the chain may be a single
    /// value or a range (`[lo:hi]`) — stored as a `ConstraintRange` so
    /// the chain can encode `([0:3] => [4:7])` etc. Sampler tracks the
    /// last N samples per coverpoint (N = the longest declared chain)
    /// and increments this bin when the trailing window membership-
    /// matches the chain.
    #[cfg_attr(feature = "serde", serde(default))]
    pub transitions: Vec<Vec<ConstraintRange>>,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum CoverBinKind { Bins, Ignore, Illegal, Default }

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Cross {
    pub name: Option<Identifier>,
    pub items: Vec<Identifier>,
    /// LRM §19.6 `cross x, y iff (guard)` — skip the cross sample when
    /// guard is false. Mirrors `Coverpoint.iff_guard`.
    #[cfg_attr(feature = "serde", serde(default))]
    pub iff_guard: Option<Expression>,
    /// LRM §19.6 cross body bin filters
    ///     `bins NAME = binsof(CP) intersect { ranges };`
    /// Each entry binds a NAME to a coverpoint-reference plus a constant
    /// range list. At sample time, the cross-tuple's component matching
    /// the referenced coverpoint is checked against the ranges; in-range
    /// samples bump that bin's hit count.
    #[cfg_attr(feature = "serde", serde(default))]
    pub bins: Vec<CrossBin>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct CrossBin {
    pub name: Identifier,
    /// The coverpoint identifier referenced by `binsof(<cp>)`.
    pub cp_ref: Identifier,
    pub ranges: Vec<ConstraintRange>,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct PropertyDeclaration {
    pub name: Identifier,
    pub items: Vec<super::stmt::Statement>, // Approximate property body as statements for parsing
    /// LRM §16.6 property body, captured when it matches the common
    /// `@(clk_event) <expr>` shape. Used by `assert property (p_name)`
    /// to inline the body without re-parsing. `None` for property
    /// bodies the parser couldn't structure as a single expression
    /// (those still parse — the items list is exhausted token-by-
    /// token — but the inline-substitution path is skipped).
    #[cfg_attr(feature = "serde", serde(default))]
    pub body: Option<super::expr::Expression>,
    pub endlabel: Option<Identifier>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct SequenceDeclaration {
    pub name: Identifier,
    pub items: Vec<super::stmt::Statement>, // Approximate sequence body as statements
    /// LRM §16.5 — sequence body when it matches the common
    /// `@(clk) <expr>` shape (an `SvaClocked` wrapper). Used for
    /// `assert property (s)` style references.
    #[cfg_attr(feature = "serde", serde(default))]
    pub body: Option<super::expr::Expression>,
    pub endlabel: Option<Identifier>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ModportDeclaration {
    pub items: Vec<ModportItem>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ModportItem {
    pub name: Identifier,
    pub ports: Vec<ModportPort>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ModportPort {
    pub direction: PortDirection,
    pub name: Identifier,
    pub span: Span,
}

/// Verilog gate-level primitive instantiation (IEEE 1800-2017 §28)
/// e.g., `and and0 (out, in1, in2);`  `not not0 (out, in);`
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct GateInstantiation {
    pub gate_type: GateType,
    pub instances: Vec<GateInstance>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct GateInstance {
    pub name: Option<Identifier>,
    /// First element is output, rest are inputs (for most gates).
    /// For buf/not: first is output, last is input.
    pub terminals: Vec<Expression>,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum GateType {
    And, Nand, Or, Nor, Xor, Xnor,
    Buf, Not,
    Bufif0, Bufif1, Notif0, Notif1,
    // §28 switch (MOS/bidirectional/pull) primitives
    Nmos, Pmos, Cmos, Rnmos, Rpmos, Rcmos,
    Tran, Rtran, Tranif0, Tranif1, Rtranif0, Rtranif1,
    Pullup, Pulldown,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct PortDeclaration {
    pub direction: PortDirection,
    pub net_type: Option<NetType>,
    pub data_type: DataType,
    pub declarators: Vec<VarDeclarator>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct NetDeclaration {
    pub net_type: NetType,
    pub strength: Option<String>,
    pub data_type: DataType,
    pub delay: Option<Expression>,
    pub declarators: Vec<NetDeclarator>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct NetDeclarator {
    pub name: Identifier,
    pub dimensions: Vec<UnpackedDimension>,
    pub init: Option<Expression>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct DataDeclaration {
    pub const_kw: bool,
    pub var_kw: bool,
    pub lifetime: Option<Lifetime>,
    pub data_type: DataType,
    pub declarators: Vec<VarDeclarator>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ParameterDeclaration {
    pub local: bool,
    pub kind: ParameterKind,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ParameterKind {
    Data { data_type: DataType, assignments: Vec<ParamAssignment> },
    Type { assignments: Vec<TypeParamAssignment> },
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ParamAssignment {
    pub name: Identifier,
    pub dimensions: Vec<UnpackedDimension>,
    pub init: Option<Expression>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TypeParamAssignment {
    pub name: Identifier,
    /// IEEE 1800-2023 §6.20.2.1: optional `extends <Base>` constraint
    /// that restricts the type argument to a class derived from `Base`.
    pub extends: Option<Identifier>,
    pub init: Option<DataType>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TypedefDeclaration {
    pub data_type: DataType,
    pub name: Identifier,
    pub dimensions: Vec<UnpackedDimension>,
    pub span: Span,
    /// IEEE 1800-2017 §6.18: true for a bare forward type declaration
    /// `typedef name;` (no type body). Such a name must be resolved by a later
    /// full typedef in the same scope; elaboration errors otherwise.
    #[cfg_attr(feature = "serde", serde(default))]
    pub forward: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum AlwaysKind { Always, AlwaysComb, AlwaysFf, AlwaysLatch }

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct AlwaysConstruct {
    pub kind: AlwaysKind,
    pub stmt: Statement,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct InitialConstruct {
    pub stmt: Statement,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct FinalConstruct {
    pub stmt: Statement,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ContinuousAssign {
    pub strength: Option<String>,
    pub delay: Option<Expression>,
    pub assignments: Vec<(Expression, Expression)>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ModuleInstantiation {
    pub module_name: Identifier,
    pub params: Option<Vec<ParamConnection>>,
    pub instances: Vec<HierarchicalInstance>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ParamValue {
    Expr(Expression),
    Type(DataType),
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ParamConnection {
    Ordered(Option<ParamValue>),
    Named { name: Identifier, value: Option<ParamValue> },
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct HierarchicalInstance {
    pub name: Identifier,
    pub dimensions: Vec<UnpackedDimension>,
    pub connections: Vec<PortConnection>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum PortConnection {
    Ordered(Option<Expression>),
    Named { name: Identifier, expr: Option<Expression> },
    Wildcard,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct GenerateRegion {
    pub items: Vec<ModuleItem>,
    pub span: Span,
}

/// A generate-if construct: if (cond) items [else if (cond) items]* [else items]
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct GenerateIf {
    /// Chain of (condition, items). Last entry may have None condition for `else`.
    pub branches: Vec<(Option<super::expr::Expression>, Vec<ModuleItem>)>,
    pub span: Span,
}

/// A single arm of a generate-case construct.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct GenerateCaseArm {
    /// Constant expressions matched against the selector. Empty for the
    /// `default` arm.
    pub values: Vec<super::expr::Expression>,
    /// Generate items elaborated when this arm is selected.
    pub items: Vec<ModuleItem>,
}

/// A generate-case construct: case (selector) <arm>* endcase
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct GenerateCase {
    pub selector: super::expr::Expression,
    pub arms: Vec<GenerateCaseArm>,
    pub span: Span,
}

/// A generate-for loop: for (init; cond; incr) items
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct GenerateFor {
    /// Genvar name
    pub var: String,
    /// Initial value
    pub init_val: i64,
    /// Condition expression
    pub cond: super::expr::Expression,
    /// Increment expression (genvar update)
    pub incr: super::expr::Expression,
    /// Body items to replicate
    pub items: Vec<ModuleItem>,
    /// Optional `begin : <label>` block name. Used to namespace per-iteration
    /// declaration renames so two generate-for blocks that share a genvar name
    /// (e.g. black-parrot's many `for (genvar i …) begin : <label>` blocks)
    /// don't collide on `sig__gf_i_<n>_`.
    #[cfg_attr(feature = "serde", serde(default))]
    pub name: Option<String>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct GenvarDeclaration {
    pub names: Vec<Identifier>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct FunctionDeclaration {
    pub lifetime: Option<Lifetime>,
    /// IEEE 1800-2023 §8.20.5: `function :final/:extends/:initial`.
    #[cfg_attr(feature = "serde", serde(default))]
    pub specifier: Option<MethodSpecifier>,
    pub return_type: DataType,
    pub name: TypeName,
    pub ports: Vec<FunctionPort>,
    pub items: Vec<super::stmt::Statement>,
    pub endlabel: Option<Identifier>,
    /// Non-ANSI body port declarations (`function f; input int x; …`). The
    /// main parser otherwise discards these (they parse to a `Null` stmt);
    /// retained here only for the strict-check pass (duplicate-port detection).
    /// Not consumed by elaboration — behavior-neutral.
    #[cfg_attr(feature = "serde", serde(default))]
    pub strict_body_ports: Vec<Identifier>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TaskDeclaration {
    pub lifetime: Option<Lifetime>,
    /// IEEE 1800-2023 §8.20.5: `task :final/:extends/:initial`.
    #[cfg_attr(feature = "serde", serde(default))]
    pub specifier: Option<MethodSpecifier>,
    pub name: TypeName,
    pub ports: Vec<FunctionPort>,
    pub items: Vec<super::stmt::Statement>,
    pub endlabel: Option<Identifier>,
    /// Non-ANSI body port declarations (`task t; input int x; …`); retained
    /// only for the strict-check pass. Not consumed by elaboration.
    #[cfg_attr(feature = "serde", serde(default))]
    pub strict_body_ports: Vec<Identifier>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct FunctionPort {
    pub direction: PortDirection,
    pub var_kw: bool,
    pub data_type: DataType,
    pub name: Identifier,
    pub dimensions: Vec<UnpackedDimension>,
    pub default: Option<Expression>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ImportDeclaration {
    pub items: Vec<ImportItem>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ImportItem {
    pub package: Identifier,
    pub item: Option<Identifier>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TimeunitsDeclaration {
    pub unit: Option<String>,
    pub precision: Option<String>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ClassDeclaration {
    pub virtual_kw: bool,
    #[cfg_attr(feature = "serde", serde(default))]
    pub is_interface: bool,
    /// IEEE 1800-2023 §8.20.5: `class :final <name>` — class cannot
    /// be extended.
    #[cfg_attr(feature = "serde", serde(default))]
    pub is_final: bool,
    pub name: Identifier,
    pub params: Vec<ParameterDeclaration>,
    pub extends: Option<ClassExtends>,
    pub implements: Vec<Identifier>,
    pub items: Vec<ClassItem>,
    pub endlabel: Option<Identifier>,
    pub span: Span,
}

/// extends clause: `extends base_class [(args)]`
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ClassExtends {
    pub name: Identifier,
    pub args: Vec<ParamValue>,
    pub span: Span,
}

/// Items that can appear inside a class body.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ClassItem {
    /// Property: class member variable
    Property(ClassProperty),
    /// Method: function or task
    Method(ClassMethod),
    /// Constraint declaration
    Constraint(ClassConstraint),
    /// Typedef inside class
    Typedef(TypedefDeclaration),
    /// Parameter/localparam inside class
    Parameter(ParameterDeclaration),
    /// Class inside class (nested)
    Class(ClassDeclaration),
    /// Covergroup inside class
    Covergroup(CovergroupDeclaration),
    /// Import statement
    Import(ImportDeclaration),
    /// Empty item (stray semicolons)
    Empty,
}

/// Class property (member variable).
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ClassProperty {
    pub qualifiers: Vec<ClassQualifier>,
    pub data_type: super::types::DataType,
    pub declarators: Vec<VarDeclarator>,
    pub span: Span,
}

/// Class method (function/task).
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ClassMethod {
    pub qualifiers: Vec<ClassQualifier>,
    pub kind: ClassMethodKind,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ClassMethodKind {
    Function(FunctionDeclaration),
    Task(TaskDeclaration),
    /// Pure virtual prototype: `pure virtual function ...;`
    PureVirtual(FunctionDeclaration),
    /// extern method (body defined outside class)
    Extern(FunctionDeclaration),
}

/// Class constraint.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ClassConstraint {
    pub is_static: bool,
    #[cfg_attr(feature = "serde", serde(default))]
    pub is_extern: bool,
    #[cfg_attr(feature = "serde", serde(default))]
    pub has_body: bool,
    pub name: Identifier,
    pub items: Vec<ConstraintItem>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ConstraintItem {
    Expr(Expression),
    Inside {
        expr: Expression,
        range: Vec<ConstraintRange>,
        #[cfg_attr(feature = "serde", serde(default))]
        is_dist: bool,
        /// Parallel to `range`. Only populated when `is_dist`; absent entries
        /// (or all-`None` entries) mean "uniform weight 1 per LRM default".
        #[cfg_attr(feature = "serde", serde(default))]
        dist_weights: Vec<Option<DistWeight>>,
        span: Span,
    },
    Implication { condition: Expression, constraint: Box<ConstraintItem>, span: Span },
    IfElse { condition: Expression, then_item: Box<ConstraintItem>, else_item: Option<Box<ConstraintItem>>, span: Span },
    Foreach { array: Expression, vars: Vec<Option<Identifier>>, item: Box<ConstraintItem>, span: Span },
    Solve { before: Vec<Identifier>, after: Vec<Identifier>, span: Span },
    Soft(Box<ConstraintItem>),
    Block(Vec<ConstraintItem>),
    /// LRM §18.5.5 `unique {expr_list}` where the list could not be fully
    /// desugared to pairwise `!=` at parse time — i.e. a single expression
    /// naming a whole array, whose element count is only known at solve
    /// time (`unique {gpr}` over `rand reg_t gpr[4]`). Multi-expression
    /// lists are still desugared by the parser and never reach this variant.
    Unique { exprs: Vec<Expression>, span: Span },
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ConstraintRange {
    Value(Expression),
    Range { lo: Expression, hi: Expression },
}

/// LRM §18.5.4 weight specifier in `dist { item := w, item :/ w }`.
/// `Each` (`:=`) — the weight applies independently to every value in the
/// range (so a range expands to N items each with weight w).
/// `Total` (`:/`) — the weight is split evenly across the values in the
/// range (so each individual value gets w/N).
/// Stored as a parallel `Vec<DistWeight>` on the `Inside { is_dist: true }`
/// variant, indexed parallel to `range: Vec<ConstraintRange>`. `None` means
/// "no explicit weight" (the LRM default of `:= 1`).
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum DistWeight {
    Each(Expression),
    Total(Expression),
}

/// Qualifiers for class properties and methods.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ClassQualifier {
    Static,
    Protected,
    Local,
    Rand,
    Randc,
    Virtual,
    Pure,
    Extern,
    Const,
}

/// IEEE 1800-2023 §8.20.5: colon-prefixed method specifier on
/// `function` / `task`. Three variants:
/// - `:final`   — locks the method against further override.
/// - `:extends` — explicit override marker (must be overriding).
/// - `:initial` — explicit non-override marker (must not be overriding).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum MethodSpecifier {
    Final,
    Extends,
    Initial,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum PackageItem {
    Parameter(ParameterDeclaration),
    Typedef(TypedefDeclaration),
    Function(FunctionDeclaration),
    Task(TaskDeclaration),
    Import(ImportDeclaration),
    DPIImport(DPIImport),
    DPIExport(DPIExport),
    Data(DataDeclaration),
    Class(ClassDeclaration),
    Checker(CheckerDeclaration),
    Let(LetDeclaration),
    Nettype(NettypeDeclaration),
    /// Placeholder for package items that the parser consumed but does not
    /// model (e.g. non-DPI `export pkg::*;` re-exports). Lets
    /// `parse_package_declaration`'s item loop consume them without falling
    /// through to its `else { self.bump(); }` recovery, which would otherwise
    /// eat the `endpackage` keyword and corrupt parsing.
    Null,
}
