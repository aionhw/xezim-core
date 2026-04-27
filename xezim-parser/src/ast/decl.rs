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
    OutOfClassConstraint { class_name: String, constraint_name: String },
    Null,
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
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Cross {
    pub name: Option<Identifier>,
    pub items: Vec<Identifier>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct PropertyDeclaration {
    pub name: Identifier,
    pub items: Vec<super::stmt::Statement>, // Approximate property body as statements for parsing
    pub endlabel: Option<Identifier>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct SequenceDeclaration {
    pub name: Identifier,
    pub items: Vec<super::stmt::Statement>, // Approximate sequence body as statements
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
    pub return_type: DataType,
    pub name: TypeName,
    pub ports: Vec<FunctionPort>,
    pub items: Vec<super::stmt::Statement>,
    pub endlabel: Option<Identifier>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TaskDeclaration {
    pub lifetime: Option<Lifetime>,
    pub name: TypeName,
    pub ports: Vec<FunctionPort>,
    pub items: Vec<super::stmt::Statement>,
    pub endlabel: Option<Identifier>,
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
    Inside { expr: Expression, range: Vec<ConstraintRange>, #[cfg_attr(feature = "serde", serde(default))] is_dist: bool, span: Span },
    Implication { condition: Expression, constraint: Box<ConstraintItem>, span: Span },
    IfElse { condition: Expression, then_item: Box<ConstraintItem>, else_item: Option<Box<ConstraintItem>>, span: Span },
    Foreach { array: Expression, vars: Vec<Option<Identifier>>, item: Box<ConstraintItem>, span: Span },
    Solve { before: Vec<Identifier>, after: Vec<Identifier>, span: Span },
    Soft(Box<ConstraintItem>),
    Block(Vec<ConstraintItem>),
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ConstraintRange {
    Value(Expression),
    Range { lo: Expression, hi: Expression },
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
}
