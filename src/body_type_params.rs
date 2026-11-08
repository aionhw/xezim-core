//! Constant body type parameters (IEEE 1800 §6.20.3 / §8.3).

use crate::ast::{Description, decl::*};

/// Class-body parameters are local constants, and package parameters have
/// no instance override interface. Route their type aliases through the same
/// scoped registration as typedefs. Module body parameters stay parameters:
/// an instance may override them.
pub(crate) fn normalize(descriptions: &mut [Description]) {
    for description in descriptions {
        match description {
            Description::Class(c) => class(c),
            Description::Module(m) => module_items(&mut m.items),
            Description::Interface(i) => module_items(&mut i.items),
            Description::Program(p) => module_items(&mut p.items),
            Description::Package(p) => {
                let mut items = Vec::new();
                for mut item in std::mem::take(&mut p.items) {
                    if let PackageItem::Parameter(pd) = &item
                        && let Some(aliases) = aliases(pd)
                    {
                        items.extend(aliases.into_iter().map(PackageItem::Typedef));
                        continue;
                    }
                    if let PackageItem::Class(c) = &mut item {
                        class(c);
                    }
                    items.push(item);
                }
                p.items = items;
            }
            _ => {}
        }
    }
}

fn aliases(pd: &ParameterDeclaration) -> Option<Vec<TypedefDeclaration>> {
    let ParameterKind::Type { assignments } = &pd.kind else {
        return None;
    };
    assignments
        .iter()
        .map(|a| {
            Some(TypedefDeclaration {
                data_type: a.init.clone()?,
                name: a.name.clone(),
                dimensions: Vec::new(),
                span: pd.span,
                forward: false,
                decl: Default::default(),
            })
        })
        .collect()
}

fn class(c: &mut ClassDeclaration) {
    let mut items = Vec::new();
    for mut item in std::mem::take(&mut c.items) {
        if let ClassItem::Parameter(pd) = &item
            && let Some(aliases) = aliases(pd)
        {
            items.extend(aliases.into_iter().map(ClassItem::Typedef));
            continue;
        }
        if let ClassItem::Class(c) = &mut item {
            class(c);
        }
        items.push(item);
    }
    c.items = items;
}

fn module_items(items: &mut [ModuleItem]) {
    for item in items {
        match item {
            ModuleItem::ClassDeclaration(c) => class(c),
            ModuleItem::NestedModule(m) => module_items(&mut m.items),
            ModuleItem::GenerateRegion(g) => module_items(&mut g.items),
            ModuleItem::GenerateFor(g) => module_items(&mut g.items),
            ModuleItem::GenerateIf(g) => {
                for (_, items) in &mut g.branches {
                    module_items(items);
                }
            }
            ModuleItem::GenerateCase(g) => {
                for arm in &mut g.arms {
                    module_items(&mut arm.items);
                }
            }
            _ => {}
        }
    }
}
