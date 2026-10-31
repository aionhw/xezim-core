//! Optional compiled-artifact navigation metadata. No source text or AST is stored.
//!
//! The simulation bincode layout remains v0x32. Metadata is a separately versioned
//! trailer INSIDE the existing compressed/uncompressed payload. Legacy readers
//! finish after ElaboratedModule; new readers also accept EOF (legacy artifacts).
use crate::ast::{Identifier, Span, decl::*, module::PortList};
use crate::elaborate::{Definition, ElaboratedModule};
use serde::{Deserialize, Serialize};
use std::io::{Read, Write};

const MAGIC: &[u8; 8] = b"XEZINAV\x01";
const MAX_TRAILER: u64 = 256 * 1024 * 1024;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SourcePosition {
    pub file: u32,
    pub line: u32,
    pub column: u32,
    pub macro_expansion: bool,
}
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NavigationSymbol {
    /// Flat simulator name, relative to top. Empty for the root scope.
    pub path: String,
    /// Original leaf identifier, even when it contains dots.
    pub name: String,
    pub parent: String,
    /// 0 = signal, 1 = parameter, 2 = module/interface/program, 3 = generate.
    pub kind: u8,
    pub location: Option<SourcePosition>,
    /// Only true for value parameters that may be overridden on an instance.
    pub overridable: bool,
    /// Safe to render as an integral -G override (excludes enum/aggregate/real/string types).
    pub scalar: bool,
}
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NavigationDefinition {
    pub name: String,
    pub kind: String,
    pub location: Option<SourcePosition>,
}
#[derive(Debug, Default, Serialize, Deserialize)]
pub struct NavigationInfo {
    pub files: Vec<String>,
    pub compilation_directory: Option<String>,
    pub definitions: Vec<NavigationDefinition>,
    pub symbols: Vec<NavigationSymbol>,
    #[serde(skip)]
    scope_paths: crate::hasher::HashSet<String>,
}

pub(crate) fn write<W: Write>(elab: &ElaboratedModule, writer: &mut W) -> Result<(), String> {
    if elab.navigation.definitions.is_empty() {
        return Ok(());
    }
    let bytes = bincode::serde::encode_to_vec(&elab.navigation, crate::xez_bincode_config())
        .map_err(|e| format!("navigation serialize: {e}"))?;
    if bytes.len() as u64 > MAX_TRAILER {
        return Err("navigation metadata exceeds 256 MiB".into());
    }
    writer
        .write_all(MAGIC)
        .and_then(|_| writer.write_all(&(bytes.len() as u64).to_le_bytes()))
        .and_then(|_| writer.write_all(&bytes))
        .map_err(|e| format!("navigation write: {e}"))
}
pub(crate) fn read<R: Read>(reader: &mut R) -> Result<NavigationInfo, String> {
    let mut magic = [0; 8];
    if reader
        .read(&mut magic[..1])
        .map_err(|e| format!("navigation read: {e}"))?
        == 0
    {
        return Ok(NavigationInfo::default());
    }
    reader
        .read_exact(&mut magic[1..])
        .map_err(|e| format!("truncated navigation header: {e}"))?;
    if &magic != MAGIC {
        return Err("unsupported xezim navigation trailer version or magic".into());
    }
    let mut len = [0; 8];
    reader
        .read_exact(&mut len)
        .map_err(|e| format!("truncated navigation length: {e}"))?;
    let len = u64::from_le_bytes(len);
    if len > MAX_TRAILER {
        return Err("navigation metadata exceeds 256 MiB".into());
    }
    let mut bytes = Vec::new();
    reader
        .take(len)
        .read_to_end(&mut bytes)
        .map_err(|e| format!("navigation read: {e}"))?;
    if bytes.len() as u64 != len {
        return Err("truncated navigation payload".into());
    }
    let (info, consumed) = bincode::serde::decode_from_slice(
        &bytes,
        bincode::config::standard().with_limit::<268435456>(),
    )
    .map_err(|e| format!("navigation deserialize: {e}"))?;
    if consumed != bytes.len() {
        return Err("trailing data in navigation metadata".into());
    }
    Ok(info)
}

fn position(elab: &mut ElaboratedModule, owner: &str, span: Span) -> Option<SourcePosition> {
    let loc = crate::elaborate::navigation_location(elab, owner, span)?;
    let path = std::path::Path::new(&loc.file);
    let file = if path.is_absolute() {
        path.to_path_buf()
    } else {
        std::env::current_dir().ok()?.join(path)
    }
    .to_string_lossy()
    .into_owned();
    let id = elab
        .navigation
        .files
        .iter()
        .position(|f| f == &file)
        .unwrap_or_else(|| {
            elab.navigation.files.push(file);
            elab.navigation.files.len() - 1
        });
    Some(SourcePosition {
        file: id as u32,
        line: loc.line,
        column: loc.col,
        macro_expansion: loc.macro_name.is_some(),
    })
}

fn generated_parts(
    items: &[ModuleItem],
    path: &str,
    ordinal: &mut u32,
) -> Option<Vec<(String, Span)>> {
    fn descend(
        items: &[ModuleItem],
        path: &str,
        label: &str,
        span: Span,
        indexed: bool,
    ) -> Option<Vec<(String, Span)>> {
        let mut tail = path.strip_prefix(label)?;
        let mut segment = label.to_owned();
        if indexed {
            let end = tail.strip_prefix('[')?.find(']')? + 2;
            tail.get(1..end - 1)?.parse::<i64>().ok()?;
            segment.push_str(tail.get(..end)?);
            tail = tail.get(end..)?;
        }
        let mut parts = vec![(segment, span)];
        if !tail.is_empty() {
            parts.extend(generated_parts(items, tail.strip_prefix('.')?, &mut 0)?);
        }
        Some(parts)
    }
    for item in items {
        match item {
            ModuleItem::GenerateRegion(g) => {
                if let Some(parts) = generated_parts(&g.items, path, ordinal) {
                    return Some(parts);
                }
            }
            ModuleItem::GenerateFor(g) => {
                *ordinal += 1;
                let default = format!("genblk{}", ordinal);
                if let Some(parts) = descend(
                    &g.items,
                    path,
                    g.name.as_deref().unwrap_or(&default),
                    g.span,
                    true,
                ) {
                    return Some(parts);
                }
            }
            ModuleItem::GenerateIf(g) => {
                *ordinal += 1;
                let default = format!("genblk{}", ordinal);
                for (i, (_, items)) in g.branches.iter().enumerate() {
                    let label = g
                        .branch_labels
                        .get(i)
                        .and_then(|s| s.as_deref())
                        .unwrap_or(&default);
                    if let Some(parts) = descend(items, path, label, g.span, false) {
                        return Some(parts);
                    }
                }
            }
            ModuleItem::GenerateCase(g) => {
                *ordinal += 1;
                let default = format!("genblk{}", ordinal);
                for arm in &g.arms {
                    if let Some(parts) = descend(
                        &arm.items,
                        path,
                        arm.label.as_deref().unwrap_or(&default),
                        g.span,
                        false,
                    ) {
                        return Some(parts);
                    }
                }
            }
            _ => {}
        }
    }
    None
}

fn symbol(
    elab: &mut ElaboratedModule,
    def: Definition<'_>,
    prefix: &str,
    id: &Identifier,
    kind: u8,
    overridable: bool,
) {
    let original = crate::elaborate::navigation_identifier(elab, def.name(), id.span);
    let leaf = original
        .as_deref()
        .filter(|s| id.name.ends_with(s))
        .unwrap_or(&id.name);
    let generated = id
        .name
        .strip_suffix(leaf)
        .unwrap_or("")
        .trim_end_matches('.');
    let mut parent = prefix.trim_end_matches('.').to_owned();
    if !generated.is_empty() {
        // Resolve boundaries through the existing AST labels, which can themselves
        // contain dots. Do not infer hierarchy by splitting escaped identifiers.
        if let Some(parts) = generated_parts(def.items(), generated, &mut 0) {
            for (segment, span) in parts {
                let path = if parent.is_empty() {
                    segment.clone()
                } else {
                    format!("{parent}.{segment}")
                };
                if elab.navigation.scope_paths.insert(path.clone()) {
                    let location = position(elab, def.name(), span);
                    elab.navigation.symbols.push(NavigationSymbol {
                        path: path.clone(),
                        name: segment,
                        parent: parent.clone(),
                        kind: 3,
                        location,
                        overridable: false,
                        scalar: false,
                    });
                }
                parent = path;
            }
        } else {
            // Unknown synthesized naming: keep an opaque leaf under the known module.
            let location = position(elab, def.name(), id.span);
            elab.navigation.symbols.push(NavigationSymbol {
                path: format!("{prefix}{}", id.name),
                name: id.name.clone(),
                parent,
                kind,
                location,
                overridable,
                scalar: false,
            });
            return;
        }
    }
    let location = position(elab, def.name(), id.span);
    elab.navigation.symbols.push(NavigationSymbol {
        path: format!("{prefix}{}", id.name),
        name: leaf.into(),
        parent,
        kind,
        location,
        overridable,
        scalar: false,
    });
}

fn parameters(
    elab: &mut ElaboratedModule,
    def: Definition<'_>,
    prefix: &str,
    params: &[ParameterDeclaration],
    overridable: bool,
) {
    for p in params {
        if let ParameterKind::Data {
            assignments,
            data_type,
            ..
        } = &p.kind
        {
            for a in assignments {
                symbol(elab, def, prefix, &a.name, 1, overridable);
                if let Some(last) = elab.navigation.symbols.last_mut() {
                    last.scalar = a.dimensions.is_empty()
                        && matches!(
                            data_type,
                            crate::ast::types::DataType::IntegerVector { .. }
                                | crate::ast::types::DataType::IntegerAtom { .. }
                                | crate::ast::types::DataType::Implicit { .. }
                        );
                }
            }
        }
    }
}

/// Called at the existing per-instance elaboration boundary, while original
/// source maps and the parameter-specialized body are still resident.
pub(crate) fn record_body(
    elab: &mut ElaboratedModule,
    def: Definition<'_>,
    prefix: &str,
    items: &[ModuleItem],
) {
    if elab.navigation.compilation_directory.is_none() {
        elab.navigation.compilation_directory = std::env::current_dir()
            .ok()
            .map(|p| p.to_string_lossy().into_owned());
    }
    if !elab
        .navigation
        .definitions
        .iter()
        .any(|d| d.name == def.name())
    {
        let (id, kind) = match def {
            Definition::Module(m) => (&m.name, "module"),
            Definition::Interface(m) => (&m.name, "interface"),
            Definition::Program(m) => (&m.name, "program"),
            _ => return,
        };
        let location = position(elab, def.name(), id.span);
        elab.navigation.definitions.push(NavigationDefinition {
            name: def.name().into(),
            kind: kind.into(),
            location,
        });
    }
    parameters(elab, def, prefix, def.params(), true);
    match def.ports() {
        PortList::Ansi(ports) => {
            for p in ports {
                symbol(elab, def, prefix, &p.name, 0, false);
            }
        }
        PortList::NonAnsi(ids) => {
            for id in ids {
                symbol(elab, def, prefix, id, 0, false);
            }
        }
        _ => {}
    }
    for item in items {
        match item {
            ModuleItem::DataDeclaration(d) => {
                for v in &d.declarators {
                    symbol(elab, def, prefix, &v.name, 0, false);
                }
            }
            ModuleItem::NetDeclaration(d) => {
                for v in &d.declarators {
                    symbol(elab, def, prefix, &v.name, 0, false);
                }
            }
            ModuleItem::PortDeclaration(d) => {
                for v in &d.declarators {
                    symbol(elab, def, prefix, &v.name, 0, false);
                }
            }
            ModuleItem::ParameterDeclaration(p) => parameters(
                elab,
                def,
                prefix,
                std::slice::from_ref(p),
                def.params().is_empty(),
            ),
            ModuleItem::LocalparamDeclaration(p) => {
                parameters(elab, def, prefix, std::slice::from_ref(p), false)
            }
            ModuleItem::ModuleInstantiation(m) => {
                for inst in &m.instances {
                    symbol(elab, def, prefix, &inst.name, 2, false);
                }
            }
            _ => {}
        }
    }
}

/// Drop compile-only deduplication state before the model becomes resident.
pub(crate) fn finish(elab: &mut ElaboratedModule) {
    elab.navigation.scope_paths.clear();
    elab.navigation.scope_paths.shrink_to_fit();
}
