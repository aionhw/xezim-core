//! IEEE 1364-2005 §6.2.1: a module variable declaration assignment is an
//! initial procedure. The default SystemVerilog semantics initialize first.

use super::*;
use crate::ast::{Description, Identifier};
use crate::ast::module::PortList;

thread_local! {
    static LEGACY_INITIALIZERS: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Enable declaration assignments as initial procedures in Verilog inputs.
pub fn set_verilog_2005_initializers(enabled: bool) {
    LEGACY_INITIALIZERS.with(|flag| flag.set(enabled));
}

pub fn verilog_2005_initializers() -> bool {
    LEGACY_INITIALIZERS.with(|flag| flag.get())
}

pub(crate) fn lower_verilog_2005_initializers(
    path: Option<&std::path::Path>,
    descriptions: &mut [Description],
) {
    if !verilog_2005_initializers()
        || !path.and_then(std::path::Path::extension)
            .is_some_and(|ext| ext.eq_ignore_ascii_case("v"))
    {
        return;
    }
    for description in descriptions {
        if let Description::Module(module) = description {
            lower_module(module);
        }
    }
}

fn legacy_variable_type(data_type: &DataType) -> bool {
    matches!(data_type,
        DataType::IntegerVector { kind: IntegerVectorType::Reg, .. }
        | DataType::IntegerAtom { kind: IntegerAtomType::Integer | IntegerAtomType::Time, .. }
        | DataType::Real { kind: RealType::Real | RealType::RealTime, .. }
    )
}

fn initial_assignment(name: &Identifier, value: Expression) -> ModuleItem {
    let mut lvalue = make_ident_expr(&name.name);
    lvalue.span = value.span;
    if let ExprKind::Ident(ident) = &mut lvalue.kind {
        ident.span = value.span;
        ident.path[0].name.span = value.span;
    }
    ModuleItem::InitialConstruct(InitialConstruct {
        stmt: Statement::new(
            StatementKind::BlockingAssign {
                lvalue,
                rvalue: value,
            },
            name.span,
        ),
        span: name.span,
        gen_scope: String::new(),
    })
}

fn lower_module(module: &mut crate::ast::module::ModuleDeclaration) {
    let mut port_initials = Vec::new();
    if let PortList::Ansi(ports) = &mut module.ports {
        let mut output = false;
        let mut variable = false;
        for port in ports {
            if let Some(direction) = port.direction {
                output = direction == PortDirection::Output;
                variable = false;
            }
            if port.data_type.is_some() || port.net_type.is_some() {
                variable = port.net_type.is_none()
                    && port.data_type.as_ref().is_some_and(legacy_variable_type);
            }
            if output && variable && let Some(value) = port.default.take() {
                port_initials.push(initial_assignment(&port.name, value));
            }
        }
    }
    lower_items(&mut module.items);
    module.items.splice(..0, port_initials);
}

fn lower_items(items: &mut Vec<ModuleItem>) {
    let mut lowered = Vec::with_capacity(items.len());
    for mut item in std::mem::take(items) {
        let declarations = match &mut item {
            ModuleItem::DataDeclaration(data)
                if data.net_type.is_none() && !data.const_kw
                    && data.lifetime != Some(Lifetime::Automatic)
                    && legacy_variable_type(&data.data_type) =>
                Some(&mut data.declarators),
            ModuleItem::PortDeclaration(port)
                if port.direction == PortDirection::Output && port.net_type.is_none()
                    && legacy_variable_type(&port.data_type) =>
                Some(&mut port.declarators),
            ModuleItem::GenerateRegion(region) => {
                lower_items(&mut region.items);
                None
            }
            ModuleItem::GenerateIf(generate) => {
                for (_, branch) in &mut generate.branches {
                    lower_items(branch);
                }
                None
            }
            ModuleItem::GenerateCase(generate) => {
                for arm in &mut generate.arms {
                    lower_items(&mut arm.items);
                }
                None
            }
            ModuleItem::GenerateFor(generate) => {
                lower_items(&mut generate.items);
                None
            }
            ModuleItem::NestedModule(module) => {
                lower_module(module);
                None
            }
            _ => None,
        };
        let first_initial = lowered.len();
        if let Some(declarations) = declarations {
            for decl in declarations {
                if let Some(value) = decl.init.take() {
                    lowered.push(initial_assignment(&decl.name, *value));
                }
            }
        }
        lowered.push(item);
        lowered[first_initial..].rotate_right(1);
    }
    *items = lowered;
}
