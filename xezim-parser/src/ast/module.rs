//! Module, interface, program, and package declarations.


use super::{Identifier, AttributeInstance, Span};
use super::expr::Expression;
use super::types::*;
use super::decl::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ModuleKind { Module, Macromodule }

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ModuleDeclaration {
    pub attrs: Vec<AttributeInstance>,
    pub kind: ModuleKind,
    pub lifetime: Option<Lifetime>,
    pub name: Identifier,
    pub params: Vec<ParameterDeclaration>,
    pub ports: PortList,
    pub items: Vec<ModuleItem>,
    pub endlabel: Option<Identifier>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct InterfaceDeclaration {
    pub attrs: Vec<AttributeInstance>,
    pub lifetime: Option<Lifetime>,
    pub name: Identifier,
    pub params: Vec<ParameterDeclaration>,
    pub ports: PortList,
    pub items: Vec<ModuleItem>,
    pub endlabel: Option<Identifier>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ProgramDeclaration {
    pub attrs: Vec<AttributeInstance>,
    pub lifetime: Option<Lifetime>,
    pub name: Identifier,
    pub params: Vec<ParameterDeclaration>,
    pub ports: PortList,
    pub items: Vec<ModuleItem>,
    pub endlabel: Option<Identifier>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct PackageDeclaration {
    pub attrs: Vec<AttributeInstance>,
    pub lifetime: Option<Lifetime>,
    pub name: Identifier,
    pub items: Vec<PackageItem>,
    pub endlabel: Option<Identifier>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum PortList {
    Empty,
    Ansi(Vec<AnsiPort>),
    NonAnsi(Vec<Identifier>),
}

impl PortList {
    pub fn get(&self, i: usize) -> Option<GenericPort> {
        match self {
            PortList::Ansi(ports) => ports.get(i).map(|p| GenericPort::Ansi(p)),
            PortList::NonAnsi(names) => names.get(i).map(|n| GenericPort::NonAnsi(n)),
            PortList::Empty => None,
        }
    }
}

pub enum GenericPort<'a> {
    Ansi(&'a AnsiPort),
    NonAnsi(&'a Identifier),
}

impl<'a> GenericPort<'a> {
    pub fn name(&self) -> &str {
        match self {
            GenericPort::Ansi(p) => &p.name.name,
            GenericPort::NonAnsi(n) => &n.name,
        }
    }
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct AnsiPort {
    pub attrs: Vec<AttributeInstance>,
    pub direction: Option<PortDirection>,
    pub net_type: Option<NetType>,
    pub var_kw: bool,
    pub data_type: Option<DataType>,
    pub name: Identifier,
    pub dimensions: Vec<UnpackedDimension>,
    pub default: Option<Expression>,
    pub span: Span,
}
