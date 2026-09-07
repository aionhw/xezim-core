//! IEEE 1801 (Unified Power Format) — a simulation subset.
//!
//! What is modelled, and where the standard says so (IEEE 1801-2015):
//! * supply nets / ports / `connect_supply_net` / `set_domain_supply_net`
//!   (§6.23, §6.24, §6.10, §6.39): a supply net is a 1-bit state signal
//!   (1 = FULL_ON, 0 = OFF, x = UNDETERMINED) plus a voltage; the testbench
//!   drives the top-level supply ports through the `UPF` package functions
//!   `supply_on` / `supply_off` / `supply_partial_on` and reads them back with
//!   `get_supply_on_state` / `get_supply_voltage` (§B.2 UPF package).
//! * `create_power_switch` (§6.20): the output supply follows the input
//!   supply while an `-on_state` boolean over the control ports holds and is
//!   OFF otherwise; an x control gives UNDETERMINED.
//! * `create_power_domain` (§6.11) with `-elements`: the domain is powered
//!   when its primary power AND ground nets are on (§4.4 simulation
//!   semantics). While it is not, every variable, net and output of the
//!   domain's elements (recursively) is corrupted to x and holds x until the
//!   next write after power-up — modelled with `force`/`release`.
//! * `set_isolation` (§6.41) / `set_isolation_control`: while the isolation
//!   control is active the isolated output ports read their clamp value at
//!   the domain boundary (the parent-side net); element-specific strategies
//!   take precedence over `-applies_to outputs`. A domain switching OFF with
//!   its isolation control inactive is reported (the classic missing-
//!   isolation-enable check).
//! * `set_retention` (§6.49): the retention elements are exempt from
//!   corruption (their value survives power-down).
//! * `set_level_shifter`, `add_port_state`, `create_pst`, `add_pst_state`,
//!   `add_power_state`, supply sets: parsed and reported, no simulation
//!   effect (level shifters are functionally transparent; PST analysis is a
//!   static check).
//! * `load_upf` (relative to the including file), `set_design_top`,
//!   `set_scope`, `set`/`$var`, `puts`, comments, brace lists, backslash
//!   continuations.
//!
//! Implementation: the UPF files are read before elaboration and turned into
//! SystemVerilog glue — a `UPF` package (supply functions writing the top
//! module's supply state hierarchically) and processes appended to the TOP
//! module (switch/domain state, corruption, isolation, messages). Everything
//! downstream is ordinary elaboration and simulation.
use std::collections::HashMap;
use std::sync::Mutex;

use crate::ast::decl::{ModuleItem, PortConnection};
use crate::ast::expr::ExprKind;
use crate::ast::module::{ModuleDeclaration, PortList};
use crate::ast::types::{DataType, SimpleType};
use crate::ast::types::PortDirection;
use crate::ast::Description;

#[derive(Default)]
struct Config {
    files: Vec<String>,
    top: Option<String>,
}

static CONFIG: Mutex<Option<Config>> = Mutex::new(None);

/// `--upf <file>` (repeatable).
pub fn add_upf_file(path: String) {
    CONFIG.lock().unwrap().get_or_insert_with(Config::default).files.push(path);
}

/// `--upf-top </path/to/instance>`: the design instance the UPF scope refers
/// to (else the first instance of the `set_design_top` module is used).
pub fn set_upf_top(path: String) {
    CONFIG.lock().unwrap().get_or_insert_with(Config::default).top = Some(path);
}

pub fn upf_configured() -> bool {
    CONFIG.lock().unwrap().as_ref().is_some_and(|c| !c.files.is_empty())
}

// ---------------------------------------------------------------------------
// Tcl-subset reader
// ---------------------------------------------------------------------------

/// Split UPF text into commands (word lists). Handles `#` comments, `;` and
/// newline separators, backslash continuations, `{...}` (nested) and
/// `"..."` words, and `$var` substitution from `set`.
fn read_commands(text: &str, vars: &HashMap<String, String>) -> Vec<Vec<String>> {
    let joined = text.replace("\\\r\n", " ").replace("\\\n", " ");
    let chars: Vec<char> = joined.chars().collect();
    let mut out: Vec<Vec<String>> = Vec::new();
    let mut cur: Vec<String> = Vec::new();
    let mut i = 0;
    let n = chars.len();
    while i < n {
        let c = chars[i];
        if c == '\n' || c == ';' {
            if !cur.is_empty() {
                out.push(std::mem::take(&mut cur));
            }
            i += 1;
            continue;
        }
        if c.is_whitespace() {
            i += 1;
            continue;
        }
        if c == '#' && cur.is_empty() {
            while i < n && chars[i] != '\n' {
                i += 1;
            }
            continue;
        }
        if c == '{' {
            let mut depth = 0;
            let start = i + 1;
            let mut j = i;
            while j < n {
                match chars[j] {
                    '{' => depth += 1,
                    '}' => {
                        depth -= 1;
                        if depth == 0 {
                            break;
                        }
                    }
                    _ => {}
                }
                j += 1;
            }
            let word: String = chars[start..j.min(n)].iter().collect();
            cur.push(word);
            i = j + 1;
            continue;
        }
        if c == '"' {
            let mut j = i + 1;
            let mut word = String::new();
            while j < n && chars[j] != '"' {
                if chars[j] == '\\' && j + 1 < n {
                    j += 1;
                }
                word.push(chars[j]);
                j += 1;
            }
            cur.push(substitute_vars(&word, vars));
            i = j + 1;
            continue;
        }
        if c == '[' {
            let mut depth = 0;
            let mut j = i;
            while j < n {
                match chars[j] {
                    '[' => depth += 1,
                    ']' => {
                        depth -= 1;
                        if depth == 0 {
                            break;
                        }
                    }
                    _ => {}
                }
                j += 1;
            }
            let word: String = chars[i..(j + 1).min(n)].iter().collect();
            cur.push(word);
            i = j + 1;
            continue;
        }
        let mut j = i;
        let mut word = String::new();
        while j < n && !chars[j].is_whitespace() && chars[j] != ';' {
            word.push(chars[j]);
            j += 1;
        }
        cur.push(substitute_vars(&word, vars));
        i = j;
    }
    if !cur.is_empty() {
        out.push(cur);
    }
    out
}

fn substitute_vars(word: &str, vars: &HashMap<String, String>) -> String {
    if !word.contains('$') {
        return word.to_string();
    }
    let mut out = String::new();
    let chars: Vec<char> = word.chars().collect();
    let mut i = 0;
    while i < chars.len() {
        if chars[i] == '$' {
            let mut j = i + 1;
            let braced = j < chars.len() && chars[j] == '{';
            if braced {
                j += 1;
            }
            let start = j;
            while j < chars.len() && (chars[j].is_alphanumeric() || chars[j] == '_') {
                j += 1;
            }
            let name: String = chars[start..j].iter().collect();
            if braced && j < chars.len() && chars[j] == '}' {
                j += 1;
            }
            match vars.get(&name) {
                Some(v) if !name.is_empty() => out.push_str(v),
                _ => out.push_str(&chars[i..j].iter().collect::<String>()),
            }
            i = j;
        } else {
            out.push(chars[i]);
            i += 1;
        }
    }
    out
}

fn list(word: &str) -> Vec<String> {
    read_commands(word, &HashMap::new())
        .into_iter()
        .flatten()
        .collect()
}

/// `-opt value` / `-flag` parsing: options with a following non-dash word
/// take it as their value; the rest are flags. Positional words are kept.
struct Args {
    positional: Vec<String>,
    opts: HashMap<String, String>,
    flags: Vec<String>,
}

fn parse_args(words: &[String]) -> Args {
    let mut a = Args { positional: Vec::new(), opts: HashMap::new(), flags: Vec::new() };
    let mut i = 0;
    while i < words.len() {
        let w = &words[i];
        if let Some(opt) = w.strip_prefix('-') {
            if !opt.is_empty() && !opt.chars().next().unwrap().is_ascii_digit() {
                if i + 1 < words.len() && !is_option_word(&words[i + 1]) {
                    a.opts.insert(opt.to_string(), words[i + 1].clone());
                    i += 2;
                    continue;
                }
                a.flags.push(opt.to_string());
                i += 1;
                continue;
            }
        }
        a.positional.push(w.clone());
        i += 1;
    }
    a
}

fn is_option_word(w: &str) -> bool {
    w.starts_with('-') && w.len() > 1 && !w.as_bytes()[1].is_ascii_digit()
}

// ---------------------------------------------------------------------------
// Model
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
struct Domain {
    name: String,
    elements: Vec<String>,
    power: Option<String>,
    ground: Option<String>,
    scope: String,
    file: String,
}

#[derive(Debug, Clone)]
struct Switch {
    name: String,
    domain: Option<String>,
    input: (String, String),
    output: (String, String),
    controls: Vec<(String, String)>,
    on_states: Vec<(String, String, String)>,
    off_states: Vec<(String, String)>,
}

#[derive(Debug, Clone)]
struct Isolation {
    name: String,
    domain: String,
    applies_to: Option<String>,
    elements: Vec<String>,
    clamp: String,
    signal: Option<String>,
    sense: String,
    power: Option<String>,
    ground: Option<String>,
}

#[derive(Debug, Clone)]
struct Retention {
    name: String,
    domain: String,
    elements: Vec<String>,
}

#[derive(Debug, Clone)]
struct Pst {
    name: String,
    supplies: Vec<String>,
    states: Vec<(String, Vec<String>)>,
}

#[derive(Default, Debug)]
struct Model {
    design_top: Option<String>,
    scope: String,
    domains: Vec<Domain>,
    nets: Vec<String>,
    ports: Vec<(String, String)>,
    net_of_port: HashMap<String, String>,
    switches: Vec<Switch>,
    isolations: Vec<Isolation>,
    retentions: Vec<Retention>,
    level_shifters: Vec<(String, String)>,
    port_states: Vec<(String, Vec<(String, String)>)>,
    psts: Vec<Pst>,
    warnings: Vec<String>,
}

impl Model {
    fn scoped(&self, name: &str) -> String {
        if name == "." {
            return self.scope.clone();
        }
        if self.scope.is_empty() {
            name.to_string()
        } else {
            format!("{}/{}", self.scope, name)
        }
    }
}

fn parse_upf_file(
    path: &str,
    model: &mut Model,
    vars: &mut HashMap<String, String>,
    depth: usize,
) -> Result<(), String> {
    if depth > 16 {
        return Err(format!("UPF: load_upf nesting too deep at '{}'", path));
    }
    let text = std::fs::read_to_string(path)
        .map_err(|e| format!("UPF: cannot read '{}': {}", path, e))?;
    let dir = std::path::Path::new(path).parent().map(|p| p.to_path_buf());
    let file_label = path.to_string();
    for words in read_commands(&text, vars) {
        let Some(cmd) = words.first() else { continue };
        let a = parse_args(&words[1..]);
        let name = a.positional.first().cloned().unwrap_or_default();
        let lst = |k: &str| a.opts.get(k).map(|v| list(v)).unwrap_or_default();
        match cmd.as_str() {
            "set" => {
                if a.positional.len() >= 2 {
                    vars.insert(a.positional[0].clone(), a.positional[1].clone());
                }
            }
            "puts" => eprintln!("[UPF] {}", a.positional.last().cloned().unwrap_or_default()),
            "load_upf" => {
                let p = std::path::Path::new(&name);
                let full = if p.is_absolute() {
                    p.to_path_buf()
                } else {
                    dir.clone().unwrap_or_default().join(p)
                };
                let full = full.to_string_lossy().to_string();
                // `-scope <inst>`: the nested file's commands apply below that
                // instance (its own `set_design_top` names that instance's
                // module, not a new root). `-implementation`/`-version` flags
                // carry no simulation meaning.
                let saved_scope = model.scope.clone();
                let saved_top = model.design_top.clone();
                if let Some(sc) = a.opts.get("scope") {
                    model.scope = if sc == "." || sc == "/" {
                        model.scope.clone()
                    } else if let Some(rest) = sc.strip_prefix('/') {
                        rest.to_string()
                    } else {
                        model.scoped(sc)
                    };
                }
                parse_upf_file(&full, model, vars, depth + 1)?;
                model.scope = saved_scope;
                if saved_top.is_some() {
                    model.design_top = saved_top;
                }
            }
            "set_design_top" => {
                // Only the outermost file names the design root; a
                // `set_design_top` inside a `load_upf -scope` file names the
                // sub-instance's module and is checked, not adopted.
                if model.scope.is_empty() && model.design_top.is_none() {
                    model.design_top = Some(name.clone());
                }
            }
            "set_scope" => {
                model.scope = if name == "." || name.is_empty() {
                    String::new()
                } else if name == ".." {
                    match model.scope.rsplit_once('/') {
                        Some((h, _)) => h.to_string(),
                        None => String::new(),
                    }
                } else if let Some(rest) = name.strip_prefix('/') {
                    rest.to_string()
                } else {
                    model.scoped(&name)
                };
            }
            "create_power_domain" => {
                let mut elements: Vec<String> =
                    lst("elements").iter().map(|e| model.scoped(e)).collect();
                if a.flags.iter().any(|f| f == "include_scope") {
                    elements.push(model.scope.clone());
                }
                model.domains.push(Domain {
                    name: name.clone(),
                    elements,
                    power: None,
                    ground: None,
                    scope: model.scope.clone(),
                    file: file_label.clone(),
                });
            }
            "create_supply_net" => {
                let n = model.scoped(&name);
                if !model.nets.contains(&n) {
                    model.nets.push(n);
                }
            }
            "create_supply_port" => {
                let dir = a.opts.get("direction").cloned().unwrap_or_else(|| "in".into());
                model.ports.push((model.scoped(&name), dir));
            }
            "connect_supply_net" => {
                for p in lst("ports") {
                    model.net_of_port.insert(model.scoped(&p), model.scoped(&name));
                }
            }
            "set_domain_supply_net" => {
                let pw = a.opts.get("primary_power_net").map(|s| model.scoped(s));
                let gd = a.opts.get("primary_ground_net").map(|s| model.scoped(s));
                match model.domains.iter_mut().find(|d| d.name == name) {
                    Some(d) => {
                        d.power = pw;
                        d.ground = gd;
                    }
                    None => model.warnings.push(format!(
                        "set_domain_supply_net: unknown power domain '{}'", name
                    )),
                }
            }
            "create_supply_set" | "associate_supply_set" | "add_power_state"
            | "set_port_attributes" | "set_design_attributes" | "upf_version"
            | "create_logic_net" | "create_logic_port" | "connect_logic_net"
            | "set_partial_on_translation" | "set_simstate_behavior" => {
                model.warnings.push(format!("'{}' parsed but not simulated", cmd));
            }
            "create_power_switch" => {
                let pair = |k: &str| -> (String, String) {
                    let l = lst(k);
                    (
                        l.first().cloned().unwrap_or_default(),
                        l.get(1).map(|s| model.scoped(s)).unwrap_or_default(),
                    )
                };
                let controls: Vec<(String, String)> = {
                    let l = lst("control_port");
                    let mut v = Vec::new();
                    let mut it = l.into_iter();
                    while let (Some(p), Some(s)) = (it.next(), it.next()) {
                        v.push((p, s));
                    }
                    v
                };
                let mut on_states = Vec::new();
                let mut off_states = Vec::new();
                // Several -on_state/-off_state may appear: parse_args keeps
                // only the last per key, so rescan the raw words.
                let mut i = 0;
                while i + 1 < words.len() {
                    match words[i].as_str() {
                        "-on_state" => {
                            let l = list(&words[i + 1]);
                            on_states.push((
                                l.first().cloned().unwrap_or_default(),
                                l.get(1).cloned().unwrap_or_default(),
                                l.get(2).cloned().unwrap_or_default(),
                            ));
                            i += 2;
                        }
                        "-off_state" => {
                            let l = list(&words[i + 1]);
                            off_states.push((
                                l.first().cloned().unwrap_or_default(),
                                l.get(1).cloned().unwrap_or_default(),
                            ));
                            i += 2;
                        }
                        _ => i += 1,
                    }
                }
                model.switches.push(Switch {
                    name: name.clone(),
                    domain: a.opts.get("domain").cloned(),
                    input: pair("input_supply_port"),
                    output: pair("output_supply_port"),
                    controls,
                    on_states,
                    off_states,
                });
            }
            "set_isolation" => {
                let domain = a.opts.get("domain").cloned().unwrap_or_default();
                let elements: Vec<String> =
                    lst("elements").iter().map(|e| model.scoped(e)).collect();
                if a.flags.iter().any(|f| f == "no_isolation") {
                    model.warnings.push(format!("set_isolation {}: -no_isolation, ignored", name));
                    continue;
                }
                if a.flags.iter().any(|f| f == "update") {
                    if let Some(st) = model
                        .isolations
                        .iter_mut()
                        .find(|st| st.name == name && (domain.is_empty() || st.domain == domain))
                    {
                        if let Some(v) = a.opts.get("applies_to") { st.applies_to = Some(v.clone()); }
                        if !elements.is_empty() { st.elements = elements; }
                        if let Some(v) = a.opts.get("clamp_value") { st.clamp = v.clone(); }
                        if let Some(v) = a.opts.get("isolation_signal") { st.signal = Some(v.clone()); }
                        if let Some(v) = a.opts.get("isolation_sense") { st.sense = v.clone(); }
                        if let Some(v) = a.opts.get("isolation_power_net") { st.power = Some(v.clone()); }
                        if let Some(v) = a.opts.get("isolation_ground_net") { st.ground = Some(v.clone()); }
                        continue;
                    }
                }
                model.isolations.push(Isolation {
                    name: name.clone(),
                    domain,
                    applies_to: a.opts.get("applies_to").cloned(),
                    elements,
                    clamp: a.opts.get("clamp_value").cloned().unwrap_or_else(|| "0".into()),
                    signal: a.opts.get("isolation_signal").cloned(),
                    sense: a.opts.get("isolation_sense").cloned().unwrap_or_else(|| "high".into()),
                    power: a.opts.get("isolation_power_net").cloned(),
                    ground: a.opts.get("isolation_ground_net").cloned(),
                });
            }
            "set_isolation_control" => {
                let domain = a.opts.get("domain").cloned().unwrap_or_default();
                match model
                    .isolations
                    .iter_mut()
                    .find(|s| s.name == name && (domain.is_empty() || s.domain == domain))
                {
                    Some(s) => {
                        if let Some(sig) = a.opts.get("isolation_signal") {
                            s.signal = Some(sig.clone());
                        }
                        if let Some(sense) = a.opts.get("isolation_sense") {
                            s.sense = sense.clone();
                        }
                    }
                    None => model.warnings.push(format!(
                        "set_isolation_control: unknown isolation strategy '{}'", name
                    )),
                }
            }
            "set_retention" => {
                model.retentions.push(Retention {
                    name: name.clone(),
                    domain: a.opts.get("domain").cloned().unwrap_or_default(),
                    elements: lst("elements").iter().map(|e| model.scoped(e)).collect(),
                });
            }
            "set_retention_control" => {}
            "set_level_shifter" => {
                model.level_shifters.push((name.clone(), a.opts.get("domain").cloned().unwrap_or_default()));
            }
            "add_port_state" => {
                let mut states = Vec::new();
                let mut i = 0;
                while i + 1 < words.len() {
                    if words[i] == "-state" {
                        let l = list(&words[i + 1]);
                        states.push((
                            l.first().cloned().unwrap_or_default(),
                            l.get(1).cloned().unwrap_or_default(),
                        ));
                        i += 2;
                    } else {
                        i += 1;
                    }
                }
                model.port_states.push((model.scoped(&name), states));
            }
            "create_pst" => {
                model.psts.push(Pst {
                    name: name.clone(),
                    supplies: lst("supplies").iter().map(|s| model.scoped(s)).collect(),
                    states: Vec::new(),
                });
            }
            "add_pst_state" => {
                let pst = a.opts.get("pst").cloned().unwrap_or_default();
                let st = lst("state");
                match model.psts.iter_mut().find(|p| p.name == pst) {
                    Some(p) => p.states.push((name.clone(), st)),
                    None => model.warnings.push(format!("add_pst_state: unknown PST '{}'", pst)),
                }
            }
            other => {
                if !other.starts_with("query_") {
                    model.warnings.push(format!("unsupported UPF command '{}' ignored", other));
                }
            }
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Design resolution
// ---------------------------------------------------------------------------

struct Design<'a> {
    modules: HashMap<String, &'a ModuleDeclaration>,
}

impl<'a> Design<'a> {
    fn instances(m: &'a ModuleDeclaration) -> Vec<(String, String, &'a crate::ast::decl::HierarchicalInstance)> {
        let mut out = Vec::new();
        fn walk<'b>(
            items: &'b [ModuleItem],
            out: &mut Vec<(String, String, &'b crate::ast::decl::HierarchicalInstance)>,
        ) {
            for it in items {
                match it {
                    ModuleItem::ModuleInstantiation(mi) => {
                        for hi in &mi.instances {
                            out.push((hi.name.name.clone(), mi.module_name.name.clone(), hi));
                        }
                    }
                    ModuleItem::GenerateRegion(gr) => walk(&gr.items, out),
                    _ => {}
                }
            }
        }
        walk(&m.items, &mut out);
        out
    }

    /// Module type of the instance at `path` (segments) below `from`.
    fn module_at(&self, from: &'a ModuleDeclaration, path: &[String]) -> Option<&'a ModuleDeclaration> {
        let mut cur = from;
        for seg in path {
            let (_, mname, _) = Self::instances(cur).into_iter().find(|(n, _, _)| n == seg)?;
            cur = self.modules.get(&mname)?;
        }
        Some(cur)
    }

    /// First instance path (from `top`) whose module type is `target`.
    fn find_by_type(&self, top: &'a ModuleDeclaration, target: &str, depth: usize) -> Option<Vec<String>> {
        if depth > 32 {
            return None;
        }
        for (iname, mname, _) in Self::instances(top) {
            if mname == target {
                return Some(vec![iname]);
            }
            if let Some(m) = self.modules.get(&mname) {
                if let Some(mut rest) = self.find_by_type(m, target, depth + 1) {
                    rest.insert(0, iname);
                    return Some(rest);
                }
            }
        }
        None
    }

    fn port_order(m: &ModuleDeclaration) -> Vec<String> {
        match &m.ports {
            PortList::Ansi(ps) => ps.iter().map(|p| p.name.name.clone()).collect(),
            PortList::NonAnsi(ids) => ids.iter().map(|i| i.name.clone()).collect(),
            PortList::Empty => Vec::new(),
        }
    }

    fn output_ports(m: &ModuleDeclaration) -> Vec<String> {
        let mut out = Vec::new();
        if let PortList::Ansi(ps) = &m.ports {
            let mut last = None;
            for p in ps {
                if p.direction.is_some() {
                    last = p.direction;
                }
                if matches!(last, Some(PortDirection::Output)) {
                    out.push(p.name.name.clone());
                }
            }
        }
        for it in &m.items {
            if let ModuleItem::PortDeclaration(pd) = it {
                if pd.direction == PortDirection::Output {
                    for d in &pd.declarators {
                        if !out.contains(&d.name.name) {
                            out.push(d.name.name.clone());
                        }
                    }
                }
            }
        }
        out
    }

    fn input_ports(m: &ModuleDeclaration) -> Vec<String> {
        let mut out = Vec::new();
        if let PortList::Ansi(ps) = &m.ports {
            let mut last = None;
            for p in ps {
                if p.direction.is_some() {
                    last = p.direction;
                }
                if !matches!(last, Some(PortDirection::Output)) {
                    out.push(p.name.name.clone());
                }
            }
        }
        for it in &m.items {
            if let ModuleItem::PortDeclaration(pd) = it {
                if pd.direction != PortDirection::Output {
                    for d in &pd.declarators {
                        out.push(d.name.name.clone());
                    }
                }
            }
        }
        out
    }

    /// Hierarchical names (relative to `prefix`) of everything in `m` that a
    /// power-down corrupts: scalar/vector variables, nets and outputs, and
    /// the same inside sub-instances. Inputs are the parent's nets and are
    /// left alone; arrays and non-integral types are skipped.
    fn corruptible(&self, m: &'a ModuleDeclaration, prefix: &str, skip: &[String], out: &mut Vec<String>, depth: usize) {
        if depth > 32 || skip.iter().any(|s| s == prefix) {
            return;
        }
        let inputs = Self::input_ports(m);
        let ok_type = |dt: &DataType| {
            !matches!(
                dt,
                DataType::Real { .. }
                    | DataType::Simple { kind: SimpleType::String, .. }
                    | DataType::Simple { kind: SimpleType::Event, .. }
                    | DataType::Simple { kind: SimpleType::Chandle, .. }
            )
        };
        let mut push = |name: &str, out: &mut Vec<String>| {
            if !inputs.iter().any(|i| i == name) {
                let full = format!("{}.{}", prefix, name);
                if !out.contains(&full) {
                    out.push(full);
                }
            }
        };
        for p in Self::output_ports(m) {
            push(&p, out);
        }
        for it in &m.items {
            match it {
                ModuleItem::NetDeclaration(nd) => {
                    if ok_type(&nd.data_type) {
                        for d in &nd.declarators {
                            if d.dimensions.is_empty() {
                                push(&d.name.name, out);
                            }
                        }
                    }
                }
                ModuleItem::DataDeclaration(dd) => {
                    if ok_type(&dd.data_type) {
                        for d in &dd.declarators {
                            if d.dimensions.is_empty() {
                                push(&d.name.name, out);
                            }
                        }
                    }
                }
                ModuleItem::PortDeclaration(pd) if pd.direction == PortDirection::Output => {
                    for d in &pd.declarators {
                        if d.dimensions.is_empty() {
                            push(&d.name.name, out);
                        }
                    }
                }
                _ => {}
            }
        }
        for (iname, mname, hi) in Self::instances(m) {
            if !hi.dimensions.is_empty() {
                continue;
            }
            if let Some(sub) = self.modules.get(&mname) {
                self.corruptible(sub, &format!("{}.{}", prefix, iname), skip, out, depth + 1);
            }
        }
    }

    /// Parent-side net an instance's output port drives, when the actual is
    /// a plain identifier.
    fn output_actual(m: &ModuleDeclaration, hi: &crate::ast::decl::HierarchicalInstance, sub: &ModuleDeclaration, port: &str) -> Option<String> {
        let _ = m;
        let order = Self::port_order(sub);
        let wildcard = hi.connections.iter().any(|c| matches!(c, PortConnection::Wildcard));
        for (idx, c) in hi.connections.iter().enumerate() {
            let (pname, expr) = match c {
                PortConnection::Wildcard => continue,
                PortConnection::Named { name, expr, implicit } => {
                    if name.name != port {
                        continue;
                    }
                    if *implicit {
                        return Some(port.to_string());
                    }
                    (name.name.clone(), expr.as_ref()?)
                }
                PortConnection::Ordered(e) => {
                    if order.get(idx).map(|s| s.as_str()) != Some(port) {
                        continue;
                    }
                    (port.to_string(), e.as_ref()?)
                }
            };
            let _ = pname;
            if let ExprKind::Ident(h) = &expr.kind {
                if h.root.is_none() && h.path.len() == 1 && h.path[0].selects.is_empty() {
                    return Some(h.path[0].name.name.clone());
                }
            }
            return None;
        }
        if wildcard {
            return Some(port.to_string());
        }
        None
    }
}

// ---------------------------------------------------------------------------
// Generation
// ---------------------------------------------------------------------------

fn mangle(s: &str) -> String {
    s.chars().map(|c| if c.is_alphanumeric() { c } else { '_' }).collect()
}

fn sv_str(s: &str) -> String {
    s.replace('\\', "\\\\").replace('"', "\\\"")
}

/// Translate a UPF `-on_state` boolean (`!ctrl_alu_sd`, `a && !b`) into SV,
/// mapping control port names to their hierarchical signals.
fn bool_expr(expr: &str, ctrl: &HashMap<String, String>, warnings: &mut Vec<String>) -> String {
    let mut out = String::new();
    let chars: Vec<char> = expr.chars().collect();
    let mut i = 0;
    while i < chars.len() {
        let c = chars[i];
        if c.is_alphanumeric() || c == '_' {
            let mut j = i;
            while j < chars.len() && (chars[j].is_alphanumeric() || chars[j] == '_') {
                j += 1;
            }
            let word: String = chars[i..j].iter().collect();
            match ctrl.get(&word) {
                Some(sig) => out.push_str(sig),
                None => {
                    if word.chars().all(|c| c.is_ascii_digit()) {
                        out.push_str(&word);
                    } else {
                        warnings.push(format!("power switch state uses unknown control port '{}'", word));
                        out.push_str("1'bx");
                    }
                }
            }
            i = j;
        } else {
            out.push(c);
            i += 1;
        }
    }
    out
}

struct Glue {
    package: String,
    items: String,
    report: Vec<String>,
}

fn generate(model: &Model, design: &Design, top_name: &str, top: &ModuleDeclaration, top_override: Option<&str>) -> Result<Glue, String> {
    let mut warnings: Vec<String> = model.warnings.clone();
    // Scope instance path (segments below the top module).
    let scope_path: Vec<String> = if let Some(p) = top_override {
        let mut segs: Vec<String> = p.trim_start_matches('/').split(['/', '.']).filter(|s| !s.is_empty()).map(|s| s.to_string()).collect();
        if segs.first().map(|s| s.as_str()) == Some(top_name) {
            segs.remove(0);
        }
        segs
    } else if let Some(dt) = &model.design_top {
        if dt == top_name {
            Vec::new()
        } else {
            design.find_by_type(top, dt, 0).ok_or_else(|| {
                format!("UPF: no instance of design top '{}' found below '{}'", dt, top_name)
            })?
        }
    } else {
        Vec::new()
    };
    let scope_mod = design
        .module_at(top, &scope_path)
        .ok_or_else(|| format!("UPF: scope path '{}' does not exist", scope_path.join(".")))?;
    let scope_dot = if scope_path.is_empty() { String::new() } else { format!("{}.", scope_path.join(".")) };
    let hier = |rel: &str| -> String {
        // rel is scope-relative with '/' separators
        let r = rel.replace('/', ".");
        if r.is_empty() { scope_dot.trim_end_matches('.').to_string() } else { format!("{}{}", scope_dot, r) }
    };
    let slash_path = |rel: &str| -> String {
        let mut p = format!("/{}", top_name);
        for s in &scope_path {
            p.push('/');
            p.push_str(s);
        }
        if !rel.is_empty() {
            p.push('/');
            p.push_str(rel);
        }
        p
    };
    let sup = |net: &str| format!("upf__{}", mangle(net));

    let mut nets: Vec<String> = model.nets.clone();
    for (p, _) in &model.ports {
        let n = model.net_of_port.get(p).cloned().unwrap_or_else(|| p.clone());
        if !nets.contains(&n) {
            nets.push(n);
        }
    }
    // Switch output ports are supply objects too (add_port_state names them).
    for sw in &model.switches {
        for n in [&sw.input.1, &sw.output.1] {
            if !n.is_empty() && !nets.contains(n) {
                nets.push(n.clone());
            }
        }
    }

    let mut items = String::new();
    let mut report = Vec::new();
    items.push_str("  // ---- IEEE 1801 power intent (generated by xezim from UPF) ----\n");
    for n in &nets {
        items.push_str(&format!("  logic {} = 1'b0;\n  real {}_v = 0.0;\n", sup(n), sup(n)));
        items.push_str(&format!(
            "  always @({s}) begin\n    if ({s} === 1'b1) $display(\"[UPF] Time: %0t, Supply net '{p}' toggled to '{{FULL_ON %0.2f V}}'\", $time, {s}_v);\n    else if ({s} === 1'b0) $display(\"[UPF] Time: %0t, Supply net '{p}' toggled to '{{OFF 0 V}}'\", $time);\n    else $display(\"[UPF] Time: %0t, Supply net '{p}' toggled to '{{UNDETERMINED}}'\", $time);\n  end\n",
            s = sup(n),
            p = slash_path(n)
        ));
    }

    // Power switches.
    for sw in &model.switches {
        let mut ctrl: HashMap<String, String> = HashMap::new();
        for (port, sig) in &sw.controls {
            ctrl.insert(port.clone(), hier(sig));
        }
        let mut conds: Vec<String> = Vec::new();
        for (_, in_port, b) in &sw.on_states {
            if in_port != &sw.input.0 {
                warnings.push(format!("power switch '{}': on_state uses input port '{}' (expected '{}')", sw.name, in_port, sw.input.0));
            }
            conds.push(format!("({})", bool_expr(b, &ctrl, &mut warnings)));
        }
        let cond = if conds.is_empty() { "1'b0".to_string() } else { conds.join(" || ") };
        let (i, o) = (sup(&sw.input.1), sup(&sw.output.1));
        items.push_str(&format!(
            "  assign {o} = ({c}) ? {i} : (({c}) === 1'b0 ? 1'b0 : 1'bx);\n  always @* {o}_v = ({c}) ? {i}_v : 0.0;\n",
            o = o, i = i, c = cond
        ));
        let st = format!("upf_swst__{}", mangle(&sw.name));
        items.push_str(&format!("  logic [1:0] {st} = 2'd3;\n"));
        for (port, sig) in &sw.controls {
            let h = hier(sig);
            items.push_str(&format!(
                "  always @({h}) begin\n    if (({c}) === 1'b1) begin if ({st} != 2'd1) $display(\"[UPF] Time: %0t, Power switch '{n}': control '{p}' = %b, state FULL_ON\", $time, {h}); {st} = 2'd1; end\n    else if (({c}) === 1'b0) begin if ({st} != 2'd0) $display(\"[UPF] Time: %0t, Power switch '{n}': control '{p}' = %b, state OFF\", $time, {h}); {st} = 2'd0; end\n    else begin if ({st} != 2'd2) $display(\"[UPF] Time: %0t, Power switch '{n}': control '{p}' = %b, state UNDETERMINED\", $time, {h}); {st} = 2'd2; end\n  end\n",
                h = h, c = cond, n = sw.name, p = port, st = st
            ));
        }
        report.push(format!(
            "power switch {}: {} -> {} controlled by {}",
            sw.name,
            sw.input.1,
            sw.output.1,
            sw.controls.iter().map(|(p, s)| format!("{}={}", p, s)).collect::<Vec<_>>().join(",")
        ));
    }

    // Retention: elements exempt from corruption.
    let retained: Vec<String> = model
        .retentions
        .iter()
        .flat_map(|r| r.elements.iter().map(|e| format!("{}{}", scope_dot, e.replace('/', "."))))
        .collect();

    // Isolation: resolve ports to parent nets.
    struct IsoPort {
        strategy: String,
        port_path: String,
        parent: String,
        clamp: String,
        signal: String,
        active: &'static str,
    }
    let mut iso_ports: Vec<IsoPort> = Vec::new();
    let mut covered: Vec<String> = Vec::new();
    let mut iso_sorted: Vec<&Isolation> = model.isolations.iter().collect();
    // Element-specific strategies first: they take precedence.
    iso_sorted.sort_by_key(|s| s.elements.is_empty());
    for iso in iso_sorted {
        let Some(sig) = &iso.signal else {
            warnings.push(format!("isolation strategy '{}' has no -isolation_signal; not simulated", iso.name));
            continue;
        };
        let sig_h = hier(sig);
        let active = if iso.sense.eq_ignore_ascii_case("low") { "1'b0" } else { "1'b1" };
        let clamp = match iso.clamp.to_ascii_lowercase().as_str() {
            "0" => "'0".to_string(),
            "1" => "'1".to_string(),
            "z" => "'z".to_string(),
            other => {
                warnings.push(format!("isolation strategy '{}': clamp value '{}' not simulated", iso.name, other));
                continue;
            }
        };
        let Some(dom) = model.domains.iter().find(|d| d.name == iso.domain) else {
            warnings.push(format!("isolation strategy '{}': unknown domain '{}'", iso.name, iso.domain));
            continue;
        };
        // (element instance path, port) pairs
        let mut targets: Vec<(String, String)> = Vec::new();
        if !iso.elements.is_empty() {
            for e in &iso.elements {
                match e.rsplit_once('/') {
                    Some((inst, port)) => targets.push((inst.to_string(), port.to_string())),
                    None => {
                        // whole element: all its outputs
                        if let Some(m) = design.module_at(scope_mod, &e.split('/').map(String::from).collect::<Vec<_>>()) {
                            for p in Design::output_ports(m) {
                                targets.push((e.clone(), p));
                            }
                        }
                    }
                }
            }
        } else {
            let applies = iso.applies_to.clone().unwrap_or_else(|| "outputs".into());
            if applies != "outputs" && applies != "both" {
                warnings.push(format!("isolation strategy '{}': -applies_to {} not simulated (outputs only)", iso.name, applies));
                continue;
            }
            for e in &dom.elements {
                if let Some(m) = design.module_at(scope_mod, &e.split('/').map(String::from).collect::<Vec<_>>()) {
                    for p in Design::output_ports(m) {
                        targets.push((e.clone(), p));
                    }
                }
            }
        }
        for (inst_rel, port) in targets {
            let key = format!("{}/{}", inst_rel, port);
            if covered.contains(&key) {
                continue;
            }
            let segs: Vec<String> = inst_rel.split('/').map(String::from).collect();
            let Some((leaf, parent_segs)) = segs.split_last() else { continue };
            let Some(parent_mod) = design.module_at(scope_mod, parent_segs) else { continue };
            let Some(sub_mod) = design.module_at(scope_mod, &segs) else { continue };
            let Some((_, _, hi)) = Design::instances(parent_mod).into_iter().find(|(n, _, _)| n == leaf) else { continue };
            let Some(actual) = Design::output_actual(parent_mod, hi, sub_mod, &port) else {
                warnings.push(format!("isolation strategy '{}': port '{}/{}' actual is not a plain net; not simulated", iso.name, inst_rel, port));
                continue;
            };
            let parent_rel = if parent_segs.is_empty() { actual.clone() } else { format!("{}/{}", parent_segs.join("/"), actual) };
            covered.push(key);
            iso_ports.push(IsoPort {
                strategy: iso.name.clone(),
                port_path: slash_path(&format!("{}/{}", inst_rel, port)),
                parent: hier(&parent_rel),
                clamp: clamp.clone(),
                signal: sig_h.clone(),
                active,
            });
        }
        report.push(format!(
            "isolation {} on {}: clamp {} control {} sense {}",
            iso.name, iso.domain, iso.clamp, sig, iso.sense
        ));
    }
    // One process per control signal.
    let mut by_signal: Vec<(String, &'static str, Vec<&IsoPort>)> = Vec::new();
    for p in &iso_ports {
        match by_signal.iter_mut().find(|(s, a, _)| *s == p.signal && *a == p.active) {
            Some((_, _, v)) => v.push(p),
            None => by_signal.push((p.signal.clone(), p.active, vec![p])),
        }
    }
    for (sig, active, ports) in &by_signal {
        items.push_str(&format!("  always @({sig}) begin\n    if ({sig} === {active}) begin\n"));
        for p in ports {
            items.push_str(&format!("      force {} = {};\n", p.parent, p.clamp));
            items.push_str(&format!(
                "      $display(\"[UPF] Time: %0t, Isolation enabled (strategy {}) on port '{}', clamp {}\", $time);\n",
                p.strategy, p.port_path, p.clamp.trim_start_matches('\'')
            ));
        }
        items.push_str("    end else begin\n");
        for p in ports {
            items.push_str(&format!("      release {};\n", p.parent));
            items.push_str(&format!(
                "      $display(\"[UPF] Time: %0t, Isolation disabled (strategy {}) on port '{}'\", $time);\n",
                p.strategy, p.port_path
            ));
        }
        items.push_str("    end\n  end\n");
    }

    // Power domains: state, corruption, messages.
    for dom in &model.domains {
        let (Some(pw), Some(gd)) = (&dom.power, &dom.ground) else {
            report.push(format!("power domain {}: no primary supplies (always on)", dom.name));
            continue;
        };
        let pd = format!("upf_pd__{}", mangle(&dom.name));
        items.push_str(&format!("  wire {} = {} & {};\n", pd, sup(pw), sup(gd)));
        let mut targets: Vec<String> = Vec::new();
        for e in &dom.elements {
            let segs: Vec<String> = e.split('/').filter(|s| !s.is_empty()).map(String::from).collect();
            // `-elements {.}`: the scope instance itself.
            match design.module_at(scope_mod, &segs) {
                Some(m) => {
                    let prefix = hier(e);
                    design.corruptible(m, &prefix, &retained, &mut targets, 0);
                }
                None => warnings.push(format!("power domain '{}': element '{}' not found", dom.name, e)),
            }
        }
        let iso_checks: Vec<String> = iso_ports
            .iter()
            .filter(|p| model.isolations.iter().any(|s| s.name == p.strategy && s.domain == dom.name))
            .map(|p| (p.signal.clone(), p.active, p.strategy.clone()))
            .collect::<std::collections::BTreeSet<_>>()
            .into_iter()
            .map(|(sig, active, strat)| format!(
                "      if ({sig} !== {active}) $display(\"[UPF] Warning: Time: %0t, Isolation control '{sig}' (%b) is not enabled when power domain '{d}' is switched OFF (strategy {strat})\", $time, {sig});\n",
                sig = sig, active = active, d = dom.name, strat = strat
            ))
            .collect();
        let mut forces = String::new();
        let mut releases = String::new();
        for t in &targets {
            forces.push_str(&format!("      force {} = 'x;\n", t));
            releases.push_str(&format!("      release {};\n", t));
        }
        items.push_str(&format!(
            "  always @({pd}) begin\n    if ({pd} === 1'b1) begin\n{rel}      $display(\"[UPF] Time: %0t, Power domain '{d}' is powered up\", $time);\n    end else begin\n      if ($time != 0) begin\n{iso}      end\n{frc}      if ($time != 0) $display(\"[UPF] Time: %0t, Power domain '{d}' is powered down\", $time);\n    end\n  end\n  initial begin\n    if ({pd} !== 1'b1) begin\n{frc}    end\n  end\n",
            pd = pd, d = dom.name, rel = releases, frc = forces, iso = iso_checks.concat()
        ));
        report.push(format!(
            "power domain {}: elements [{}], power {}, ground {}, {} corruptible signals{}",
            dom.name,
            dom.elements.join(", "),
            pw,
            gd,
            targets.len(),
            {
                // Only this domain's retention strategies.
                let mine: Vec<String> = model
                    .retentions
                    .iter()
                    .filter(|r| r.domain == dom.name)
                    .flat_map(|r| r.elements.iter().map(|e| format!("{}{}", scope_dot, e.replace('/', "."))))
                    .collect();
                if mine.is_empty() { String::new() } else { format!(", retention exempt: {}", mine.join(",")) }
            }
        ));
    }
    for (n, d) in &model.level_shifters {
        report.push(format!("level shifter {} on {}: transparent", n, d));
    }
    for p in &model.psts {
        report.push(format!(
            "PST {} over [{}]: {}",
            p.name,
            p.supplies.join(", "),
            p.states.iter().map(|(n, s)| format!("{}={{{}}}", n, s.join(" "))).collect::<Vec<_>>().join(" ")
        ));
    }
    for w in &warnings {
        report.push(format!("warning: {}", w));
    }

    // UPF package: supply functions write the top module's state hierarchically.
    let mut pkg = String::new();
    pkg.push_str("package UPF;\n");
    pkg.push_str("  function automatic int upf_apply(string path, bit on, real v);\n    case (path)\n");
    for n in &nets {
        let s = sup(n);
        pkg.push_str(&format!(
            "      \"{}\", \"{}\", \"{}\": begin\n        {t}.{s}_v = on ? v : 0.0;\n        {t}.{s} = on ? 1'b1 : 1'b0;\n      end\n",
            sv_str(&slash_path(n)),
            sv_str(&slash_path(n).trim_start_matches('/').replace('/', ".")),
            sv_str(n),
            t = top_name,
            s = s
        ));
    }
    pkg.push_str("      default: begin $display(\"[UPF] Time: %0t, unknown supply '%s'\", $time, path); return 0; end\n    endcase\n    return 1;\n  endfunction\n");
    pkg.push_str("  function automatic int supply_on(string path, real value = 1.0);\n    $display(\"[UPF] Time: %0t, Supply ON applied on '%s', Voltage = %0f\", $time, path, value);\n    return upf_apply(path, 1'b1, value);\n  endfunction\n");
    pkg.push_str("  function automatic int supply_partial_on(string path, real value = 1.0);\n    $display(\"[UPF] Time: %0t, Supply PARTIAL_ON applied on '%s', Voltage = %0f\", $time, path, value);\n    return upf_apply(path, 1'b1, value);\n  endfunction\n");
    pkg.push_str("  function automatic int supply_off(string path);\n    $display(\"[UPF] Time: %0t, Supply OFF applied on '%s'\", $time, path);\n    return upf_apply(path, 1'b0, 0.0);\n  endfunction\n");
    pkg.push_str("  function automatic int get_supply_on_state(string path);\n    case (path)\n");
    for n in &nets {
        pkg.push_str(&format!(
            "      \"{}\", \"{}\", \"{}\": return ({t}.{s} === 1'b1) ? 1 : 0;\n",
            sv_str(&slash_path(n)),
            sv_str(&slash_path(n).trim_start_matches('/').replace('/', ".")),
            sv_str(n),
            t = top_name,
            s = sup(n)
        ));
    }
    pkg.push_str("      default: return 0;\n    endcase\n  endfunction\n");
    pkg.push_str("  function automatic real get_supply_voltage(string path);\n    case (path)\n");
    for n in &nets {
        pkg.push_str(&format!(
            "      \"{}\", \"{}\", \"{}\": return {t}.{s}_v;\n",
            sv_str(&slash_path(n)),
            sv_str(&slash_path(n).trim_start_matches('/').replace('/', ".")),
            sv_str(n),
            t = top_name,
            s = sup(n)
        ));
    }
    pkg.push_str("      default: return 0.0;\n    endcase\n  endfunction\n");
    pkg.push_str("endpackage\n");

    report.insert(0, format!(
        "scope /{}{} ({}), {} supply nets: {}",
        top_name,
        scope_path.iter().map(|s| format!("/{}", s)).collect::<String>(),
        scope_mod.name.name,
        nets.len(),
        nets.join(", ")
    ));
    Ok(Glue { package: pkg, items, report })
}

/// Read the configured UPF files, generate the glue and splice it into the
/// parsed design: the `UPF` package is prepended, the glue processes are
/// appended to the top module. No-op when no `--upf` was given.
pub fn inject(descriptions: &mut Vec<Description>, top_module_name: Option<&str>) -> Result<(), String> {
    let (files, top_override) = {
        let g = CONFIG.lock().unwrap();
        match g.as_ref() {
            Some(c) if !c.files.is_empty() => (c.files.clone(), c.top.clone()),
            _ => return Ok(()),
        }
    };
    let top_name = top_module_name.ok_or("UPF: --upf requires the top module (-s <top>)")?;
    let mut model = Model::default();
    let mut vars = HashMap::new();
    for f in &files {
        parse_upf_file(f, &mut model, &mut vars, 0)?;
    }
    let mut modules: HashMap<String, &ModuleDeclaration> = HashMap::new();
    for d in descriptions.iter() {
        if let Description::Module(m) = d {
            modules.entry(m.name.name.clone()).or_insert(m);
        }
    }
    let design = Design { modules };
    let top = *design
        .modules
        .get(top_name)
        .ok_or_else(|| format!("UPF: top module '{}' not found", top_name))?;
    let glue = generate(&model, &design, top_name, top, top_override.as_deref())?;
    if std::env::var_os("XEZIM_UPF_DUMP").is_some() {
        eprintln!("{}\nmodule __upf_glue;\n{}endmodule\n", glue.package, glue.items);
    }
    let text = format!("{}\nmodule __upf_glue;\n{}endmodule\n", glue.package, glue.items);
    let parsed = crate::sv_parser::parse(&text);
    if !parsed.errors.is_empty() {
        let e = &parsed.errors[0];
        return Err(format!(
            "UPF: generated glue failed to parse: {} (set XEZIM_UPF_DUMP=1 to see it)",
            e.message
        ));
    }
    let mut pkg = None;
    let mut glue_items = Vec::new();
    for d in parsed.source.descriptions {
        match d {
            Description::Package(p) => pkg = Some(p),
            Description::Module(m) if m.name.name == "__upf_glue" => glue_items = m.items,
            _ => {}
        }
    }
    let Some(pkg) = pkg else { return Err("UPF: glue package missing".into()) };
    // Replace any user-provided UPF package (the standard's is a stub).
    descriptions.retain(|d| !matches!(d, Description::Package(p) if p.name.name == "UPF"));
    descriptions.insert(0, Description::Package(pkg));
    let top = descriptions
        .iter_mut()
        .find_map(|d| match d {
            Description::Module(m) if m.name.name == top_name => Some(m),
            _ => None,
        })
        .ok_or_else(|| format!("UPF: top module '{}' not found", top_name))?;
    top.items.extend(glue_items);
    eprintln!("[UPF] loaded {} file(s): {}", files.len(), files.join(", "));
    for line in &glue.report {
        eprintln!("[UPF] {}", line);
    }
    Ok(())
}
