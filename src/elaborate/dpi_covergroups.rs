use super::*;

pub(super) fn get_type_name(dt: &DataType) -> Option<String> {
    match dt {
        DataType::Real { kind: crate::ast::types::RealType::ShortReal, .. } => Some("shortreal".into()),
        DataType::TypeReference { name, .. } => Some(name.name.name.clone()),
        DataType::Interface { name, .. } => Some(name.name.clone()),
        _ => None,
    }
}

pub(super) fn dpi_proto_sv_name(proto: &DPIProto) -> String {
    match proto {
        DPIProto::Function(fd) => fd.name.name.name.clone(),
        DPIProto::Task(td) => td.name.name.name.clone(),
    }
}

/// §19.3: a covergroup declared inside a class body is a type of that
/// class. Register it under its bare name (the property's declared type,
/// what `cg = new` resolves) and under `Class::cg` (what disambiguates two
/// classes that both declare a `cg`). The bare key keeps the FIRST
/// definition; the qualified key is exact.
pub(super) fn register_class_covergroups(c: &ClassDeclaration, elab: &mut ElaboratedModule) {
    for item in &c.items {
        if let ClassItem::Covergroup(cg) = item {
            elab.covergroups
                .entry(cg.name.name.clone())
                .or_insert_with(|| cg.clone());
            elab.covergroups
                .insert(format!("{}::{}", c.name.name, cg.name.name), cg.clone());
        }
    }
}

/// §19.3: a covergroup declared in a package, under its bare name (what an
/// importing scope's `cg c = new;` resolves; the first package wins) and
/// under `pkg::cg`.
pub(super) fn register_package_covergroup(
    pkg: &str,
    cg: &CovergroupDeclaration,
    elab: &mut ElaboratedModule,
) {
    elab.covergroups
        .entry(cg.name.name.clone())
        .or_insert_with(|| cg.clone());
    elab.covergroups
        .insert(format!("{}::{}", pkg, cg.name.name), cg.clone());
}

/// §35.5.4 `export "DPI-C" [c_name =] task|function sv_name;` — record the
/// SV subroutine and the C linkage name the loaded library will call.
pub(super) fn register_dpi_export(e: &crate::ast::decl::DPIExport, elab: &mut ElaboratedModule) {
    let name = dpi_proto_sv_name(&e.proto);
    if elab.dpi_exports.contains(&name) {
        return;
    }
    let c_name = e.c_name.clone().unwrap_or_else(|| name.clone());
    elab.dpi_exports.push(name);
    elab.dpi_export_c_names.push(c_name);
}

/// `register_dpi_export` for an export inside an instantiated module: the SV
/// subroutine is the instance's (`u_a.sv_fn`, as the instance's subroutines
/// are registered), the C linkage name stays the declared one, so several
/// entries can share a C name — one per instance.
pub(super) fn register_instance_dpi_export(
    e: &crate::ast::decl::DPIExport,
    inst_prefix: &str,
    elab: &mut ElaboratedModule,
) {
    let sv = dpi_proto_sv_name(&e.proto);
    let name = cat2(inst_prefix, &sv);
    if elab.dpi_exports.contains(&name) {
        return;
    }
    let c_name = e.c_name.clone().unwrap_or(sv);
    elab.dpi_exports.push(name);
    elab.dpi_export_c_names.push(c_name);
}

/// `pkg`: the package the declaration is in, None for any other scope.
pub(super) fn register_dpi_import(
    di: &DPIImport,
    elab: &mut ElaboratedModule,
    pkg: Option<&str>,
) -> Result<(), String> {
    let sv_name = dpi_proto_sv_name(&di.proto);
    // §26.3 / §35.5.4: the SV declaration belongs to its package; the
    // optional C identifier is a separate linkage name.
    let key = pkg.map_or_else(|| sv_name.clone(), |p| format!("{p}::{sv_name}"));
    let c_name = di.c_name.clone().unwrap_or_else(|| sv_name.clone());
    // A design declaration shadows the compatibility alias of a package
    // declaration. The package's qualified entry remains available.
    if pkg.is_none()
        && !elab.dpi_import_in_design.contains(&sv_name)
        && elab.dpi_import_pkg.remove(&sv_name).is_some()
    {
        elab.dpi_imports.remove(&sv_name);
    }
    if let Some(existing) = elab.dpi_imports.get(&key) {
        if existing.c_name == c_name && existing.property == di.property {
            return Ok(());
        }
        return Err(format!(
            "Conflicting DPI import declaration '{}': already imported as \
             (c=\"{}\", {:?}), redeclared as (c=\"{}\", {:?})",
            key, existing.c_name, existing.property, c_name, di.property
        ));
    }
    let spec = DpiImportSpec {
        c_name,
        property: di.property,
        proto: di.proto.clone(),
    };
    elab.dpi_imports.insert(key.clone(), spec.clone());
    match pkg {
        Some(p) => {
            elab.dpi_import_pkg.insert(key, p.to_string());
            if !elab.dpi_imports.contains_key(&sv_name) {
                elab.dpi_imports.insert(sv_name.clone(), spec);
                elab.dpi_import_pkg.insert(sv_name, p.to_string());
            }
        }
        None => {
            elab.dpi_import_in_design.insert(sv_name);
        }
    }
    Ok(())
}
