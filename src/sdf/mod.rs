//! SDF (Standard Delay Format) parser and annotator.
//! IEEE 1497-2001: Standard Delay Format (SDF) for the Electronic Design Process.
//!
//! Parses SDF files and annotates gate-level netlists with pin-to-pin delays
//! for timing-accurate simulation.
//!
//! Supported constructs:
//!   - IOPATH delays (rise/fall, min:typ:max)
//!   - INTERCONNECT delays
//!   - TIMINGCHECK limits (SETUP, HOLD, SETUPHOLD, RECOVERY, REMOVAL, RECREM,
//!     SKEW, WIDTH, PERIOD, NOCHANGE)
//!   - TIMESCALE
//!   - CELL/INSTANCE hierarchy

use crate::hasher::HashMap;

/// A parsed SDF delay file.
#[derive(Debug, Clone)]
pub struct SdfFile {
    pub version: String,
    pub design: String,
    pub timescale: f64, // in seconds (e.g., 1e-9 for 1ns)
    pub cells: Vec<SdfCell>,
}

/// A CELL entry in the SDF file.
#[derive(Debug, Clone)]
pub struct SdfCell {
    pub cell_type: String,
    pub instance: String, // hierarchical instance path
    pub delays: Vec<SdfDelay>,
}

/// A single delay specification.
#[derive(Debug, Clone)]
pub enum SdfDelay {
    /// IOPATH: one input and output, with an output transition delay list.
    IoPath {
        input: SdfTimingPort,
        output: String,
        values: Vec<DelayTriple>,
        increment: bool,
        ifnone: bool,
    },
    /// INTERCONNECT: source → destination wire delay.
    Interconnect {
        source: String,
        dest: String,
        values: Vec<DelayTriple>,
        increment: bool,
    },
    /// TIMINGCHECK entry (`SETUP`, `HOLD`, `SETUPHOLD`, ...) with its ports
    /// in SDF order and its limit values; an empty `()` value is `None`.
    TimingCheck {
        kind: String,
        ports: Vec<SdfTimingPort>,
        values: Vec<Option<DelayTriple>>,
    },
}

/// A TIMINGCHECK port: `D`, `(posedge CK)` or `(COND expr (posedge CK))`.
#[derive(Debug, Clone, PartialEq)]
pub struct SdfTimingPort {
    pub port: String,
    /// Edge identifier as written (`posedge`, `negedge`, `01`, ...).
    pub edge: Option<String>,
    /// `COND` expression text.
    pub cond: Option<String>,
}

/// A TIMINGCHECK limit for one cell instance, scaled to simulation ticks.
#[derive(Debug, Clone)]
pub struct SdfTimingLimit {
    pub cell_type: String,
    /// Instance path as written (`*` for every instance of `cell_type`).
    pub instance: String,
    pub kind: String,
    pub ports: Vec<SdfTimingPort>,
    pub limits: Vec<Option<i64>>,
}

/// A min:typ:max delay triple. Values in SDF timescale units.
#[derive(Debug, Clone, Copy)]
pub struct DelayTriple {
    pub min: Option<f64>,
    pub typ: Option<f64>,
    pub max: Option<f64>,
}

impl DelayTriple {
    pub fn single(v: f64) -> Self {
        Self {
            min: Some(v),
            typ: Some(v),
            max: Some(v),
        }
    }
}
/// Which delay value to use from the min:typ:max triple.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DelaySelect {
    Min,
    Typ,
    Max,
}

impl DelaySelect {
    pub fn pick(&self, triple: &DelayTriple) -> Option<f64> {
        match self {
            DelaySelect::Min => triple.min,
            DelaySelect::Typ => triple.typ,
            DelaySelect::Max => triple.max,
        }
    }
}

/// Annotated delays for simulation: maps (signal_id) → delay in simulation time units.
/// For each output signal, stores the delay from any input change to output update.
#[derive(Debug, Clone)]
pub struct SdfAnnotation {
    /// Map from output signal name → delay in simulation time units (integer).
    pub signal_delays: HashMap<String, u64>,
    /// Detailed per-pin delays keyed by destination.
    pub pin_delays: HashMap<String, Vec<PinDelay>>,
    /// Interconnect entries keyed by receiving terminal.
    pub interconnect_delays: HashMap<String, Vec<PinDelay>>,
    /// TIMINGCHECK limits, applied to the matching specify timing checks.
    pub timing_limits: Vec<SdfTimingLimit>,
}

#[derive(Debug, Clone)]
pub struct PinDelay {
    pub input: SdfTimingPort,
    pub values: Vec<Option<i64>>,
    pub increment: bool,
    pub ifnone: bool,
}

impl Default for SdfAnnotation {
    fn default() -> Self {
        Self::new()
    }
}

impl SdfAnnotation {
    pub fn new() -> Self {
        Self {
            signal_delays: HashMap::default(),
            pin_delays: HashMap::default(),
            interconnect_delays: HashMap::default(),
            timing_limits: Vec::new(),
        }
    }

    /// Get the maximum delay for an output signal (conservative for settle).
    pub fn get_delay(&self, signal_name: &str) -> u64 {
        self.signal_delays.get(signal_name).copied().unwrap_or(0)
    }
}

// ═══════════════════════════════════════════════════════════════════
// SDF Parser
// ═══════════════════════════════════════════════════════════════════

/// Parse an SDF file from string content.
pub fn parse_sdf(content: &str) -> Result<SdfFile, String> {
    let mut parser = SdfParser::new(content);
    parser.parse()
}

struct SdfParser<'a> {
    input: &'a str,
    pos: usize,
    divider: char,
}

impl<'a> SdfParser<'a> {
    fn new(input: &'a str) -> Self {
        Self {
            input,
            pos: 0,
            divider: '.',
        }
    }

    fn skip_ws(&mut self) {
        while self.pos < self.input.len() {
            let ch = self.input.as_bytes()[self.pos];
            if ch == b' ' || ch == b'\t' || ch == b'\n' || ch == b'\r' {
                self.pos += 1;
            } else if self.input[self.pos..].starts_with("//") {
                // Line comment
                while self.pos < self.input.len() && self.input.as_bytes()[self.pos] != b'\n' {
                    self.pos += 1;
                }
            } else if self.input[self.pos..].starts_with("/*") {
                // Block comment
                self.pos += 2;
                while self.pos + 1 < self.input.len() {
                    if self.input[self.pos..].starts_with("*/") {
                        self.pos += 2;
                        break;
                    }
                    self.pos += 1;
                }
            } else {
                break;
            }
        }
    }

    fn peek(&self) -> Option<char> {
        self.input[self.pos..].chars().next()
    }

    fn expect_char(&mut self, ch: char) -> Result<(), String> {
        self.skip_ws();
        if self.peek() == Some(ch) {
            self.pos += 1;
            Ok(())
        } else {
            Err(format!("SDF: expected '{}' at pos {}", ch, self.pos))
        }
    }

    fn read_token(&mut self) -> String {
        self.skip_ws();
        let start = self.pos;
        while self.pos < self.input.len() {
            let ch = self.input.as_bytes()[self.pos];
            if ch == b' '
                || ch == b'\t'
                || ch == b'\n'
                || ch == b'\r'
                || ch == b'('
                || ch == b')'
                || ch == b'"'
            {
                break;
            }
            self.pos += 1;
        }
        self.input[start..self.pos].to_string()
    }

    fn read_quoted_string(&mut self) -> Result<String, String> {
        self.skip_ws();
        if self.peek() != Some('"') {
            return Err(format!("SDF: expected '\"' at pos {}", self.pos));
        }
        self.pos += 1;
        let start = self.pos;
        while self.pos < self.input.len() && self.input.as_bytes()[self.pos] != b'"' {
            self.pos += 1;
        }
        let s = self.input[start..self.pos].to_string();
        if self.pos < self.input.len() {
            self.pos += 1;
        } // skip closing "
        Ok(s)
    }

    fn read_number(&mut self) -> f64 {
        self.skip_ws();
        let start = self.pos;
        while self.pos < self.input.len() {
            let ch = self.input.as_bytes()[self.pos];
            if ch.is_ascii_digit()
                || ch == b'.'
                || ch == b'-'
                || ch == b'+'
                || ch == b'e'
                || ch == b'E'
            {
                self.pos += 1;
            } else {
                break;
            }
        }
        self.input[start..self.pos].parse().unwrap_or(0.0)
    }

    fn at_end(&self) -> bool {
        self.pos >= self.input.len()
    }

    fn parse(&mut self) -> Result<SdfFile, String> {
        let mut file = SdfFile {
            version: String::new(),
            design: String::new(),
            timescale: 1e-9, // default 1ns
            cells: Vec::new(),
        };

        self.skip_ws();
        self.expect_char('(')?;
        let keyword = self.read_token();
        if keyword != "DELAYFILE" {
            return Err(format!("SDF: expected DELAYFILE, got {}", keyword));
        }

        loop {
            self.skip_ws();
            if self.at_end() {
                break;
            }
            match self.peek() {
                Some(')') => {
                    self.pos += 1;
                    break;
                }
                Some('(') => {
                    self.pos += 1;
                    let kw = self.read_token();
                    match kw.as_str() {
                        "SDFVERSION" => {
                            file.version = self.read_quoted_string()?;
                            self.expect_char(')')?;
                        }
                        "DESIGN" => {
                            file.design = self.read_quoted_string()?;
                            self.expect_char(')')?;
                        }
                        "DIVIDER" => {
                            let divider = self.read_token();
                            self.divider = match divider.as_str() {
                                "/" => '/',
                                "." => '.',
                                _ => return Err(format!("SDF: invalid DIVIDER '{divider}'")),
                            };
                            self.expect_char(')')?;
                        }
                        "DATE" | "VENDOR" | "PROGRAM" | "VERSION" | "VOLTAGE" | "PROCESS"
                        | "TEMPERATURE" => {
                            // Skip value
                            self.skip_to_close_paren();
                        }
                        "TIMESCALE" => {
                            file.timescale = self.parse_timescale()?;
                            self.expect_char(')')?;
                        }
                        "CELL" => {
                            file.cells.push(self.parse_cell()?);
                        }
                        _ => {
                            self.skip_to_close_paren();
                        }
                    }
                }
                _ => {
                    self.pos += 1;
                }
            }
        }

        Ok(file)
    }

    fn skip_to_close_paren(&mut self) {
        let mut depth = 1;
        while self.pos < self.input.len() && depth > 0 {
            match self.input.as_bytes()[self.pos] {
                b'(' => depth += 1,
                b')' => depth -= 1,
                b'"' => {
                    self.pos += 1;
                    while self.pos < self.input.len() && self.input.as_bytes()[self.pos] != b'"' {
                        self.pos += 1;
                    }
                }
                _ => {}
            }
            self.pos += 1;
        }
    }

    fn parse_timescale(&mut self) -> Result<f64, String> {
        self.skip_ws();
        let num = self.read_number();
        let unit = self.read_token();
        let scale = match unit.as_str() {
            "s" => 1.0,
            "ms" => 1e-3,
            "us" => 1e-6,
            "ns" => 1e-9,
            "ps" => 1e-12,
            "fs" => 1e-15,
            _ => return Err(format!("SDF: unknown timescale unit '{}'", unit)),
        };
        Ok(num * scale)
    }

    fn parse_cell(&mut self) -> Result<SdfCell, String> {
        let mut cell = SdfCell {
            cell_type: String::new(),
            instance: String::new(),
            delays: Vec::new(),
        };

        loop {
            self.skip_ws();
            match self.peek() {
                Some(')') => {
                    self.pos += 1;
                    break;
                }
                Some('(') => {
                    self.pos += 1;
                    let kw = self.read_token();
                    match kw.as_str() {
                        "CELLTYPE" => {
                            cell.cell_type = self.read_quoted_string()?;
                            self.expect_char(')')?;
                        }
                        "INSTANCE" => {
                            self.skip_ws();
                            // Instance can be empty (for wildcard) or a path
                            if self.peek() == Some(')') {
                                self.pos += 1;
                            } else {
                                cell.instance = self.read_path();
                                self.expect_char(')')?;
                            }
                        }
                        "DELAY" => {
                            self.parse_delay_section(&mut cell)?;
                        }
                        "TIMINGCHECK" => {
                            self.parse_timingcheck_section(&mut cell)?;
                        }
                        _ => {
                            self.skip_to_close_paren();
                        }
                    }
                }
                None => break,
                _ => {
                    self.pos += 1;
                }
            }
        }

        Ok(cell)
    }

    fn parse_delay_section(&mut self, cell: &mut SdfCell) -> Result<(), String> {
        loop {
            self.skip_ws();
            match self.peek() {
                Some(')') => {
                    self.pos += 1;
                    return Ok(());
                }
                Some('(') => {
                    self.pos += 1;
                    let kw = self.read_token();
                    match kw.as_str() {
                        "ABSOLUTE" | "INCREMENT" => {
                            self.parse_delay_entries(cell, kw == "INCREMENT")?;
                        }
                        _ => {
                            self.skip_to_close_paren();
                        }
                    }
                }
                None => return Ok(()),
                _ => {
                    self.pos += 1;
                }
            }
        }
    }

    fn parse_delay_entries(&mut self, cell: &mut SdfCell, increment: bool) -> Result<(), String> {
        loop {
            self.skip_ws();
            match self.peek() {
                Some(')') => {
                    self.pos += 1;
                    return Ok(());
                }
                Some('(') => {
                    self.pos += 1;
                    let kw = self.read_token();
                    match kw.as_str() {
                        "IOPATH" | "COND" | "CONDELSE" => {
                            let mut cond = None;
                            if kw == "COND" || kw == "CONDELSE" {
                                if kw == "COND" {
                                    cond = Some(self.read_iopath_condition()?);
                                }
                                self.expect_char('(')?;
                                if self.read_token() != "IOPATH" {
                                    return Err(format!(
                                        "SDF: expected IOPATH at pos {}",
                                        self.pos
                                    ));
                                }
                            }
                            let mut input = self.parse_timing_port()?;
                            input.cond = cond;
                            let output = self.read_path();
                            let values = self.parse_delay_list()?;
                            if kw != "IOPATH" {
                                self.expect_char(')')?;
                            }
                            cell.delays.push(SdfDelay::IoPath {
                                input,
                                output,
                                values,
                                increment,
                                ifnone: kw == "CONDELSE",
                            });
                        }
                        "INTERCONNECT" => {
                            let source = self.read_path();
                            let dest = self.read_path();
                            let values = self.parse_delay_list()?;
                            cell.delays.push(SdfDelay::Interconnect {
                                source,
                                dest,
                                values,
                                increment,
                            });
                        }
                        _ => {
                            self.skip_to_close_paren();
                        }
                    }
                }
                None => return Ok(()),
                _ => {
                    self.pos += 1;
                }
            }
        }
    }

    fn read_path(&mut self) -> String {
        let token = self.read_token();
        if self.divider == '.' {
            token
        } else {
            let mut escaped = false;
            token
                .chars()
                .filter_map(|c| {
                    if escaped {
                        escaped = false;
                        Some(c)
                    } else if c == '\\' {
                        escaped = true;
                        None
                    } else {
                        Some(if c == self.divider { '.' } else { c })
                    }
                })
                .collect()
        }
    }

    fn read_iopath_condition(&mut self) -> Result<String, String> {
        self.skip_ws();
        if self.peek() == Some('"') {
            self.read_quoted_string()?;
            self.skip_ws();
        }
        let start = self.pos;
        while let Some(c) = self.peek() {
            if c == '(' {
                let save = self.pos;
                self.pos += 1;
                if self.read_token() == "IOPATH" {
                    self.pos = save;
                    return Ok(self.input[start..save].trim().to_owned());
                }
                self.pos = save + 1;
                self.skip_to_close_paren();
            } else if c == ')' {
                break;
            } else {
                self.pos += c.len_utf8();
            }
        }
        Err(format!("SDF: COND without IOPATH at pos {start}"))
    }

    fn parse_delay_list(&mut self) -> Result<Vec<DelayTriple>, String> {
        let mut values = Vec::new();
        self.skip_ws();
        while self.peek().is_some_and(|c| c != ')') {
            let start = self.pos;
            values.push(self.parse_delay_value()?);
            if self.pos == start {
                return Err(format!("SDF: expected delay at pos {start}"));
            }
            self.skip_ws();
        }
        self.expect_char(')')?;
        if !matches!(values.len(), 1 | 2 | 3 | 6 | 12) {
            return Err(format!(
                "SDF: invalid delay list of {} values",
                values.len()
            ));
        }
        Ok(values)
    }

    /// `(TIMINGCHECK tchk ...)`: each check's ports and values; trailing
    /// SCOND/CCOND and unknown checks are skipped.
    fn parse_timingcheck_section(&mut self, cell: &mut SdfCell) -> Result<(), String> {
        loop {
            self.skip_ws();
            match self.peek() {
                Some(')') => {
                    self.pos += 1;
                    return Ok(());
                }
                Some('(') => {
                    self.pos += 1;
                    let kind = self.read_token().to_ascii_uppercase();
                    let (n_ports, n_values) = match kind.as_str() {
                        "SETUP" | "HOLD" | "RECOVERY" | "REMOVAL" | "SKEW" => (2, 1),
                        "SETUPHOLD" | "RECREM" | "NOCHANGE" => (2, 2),
                        "WIDTH" | "PERIOD" => (1, 1),
                        _ => {
                            self.skip_to_close_paren();
                            continue;
                        }
                    };
                    let mut ports = Vec::with_capacity(n_ports);
                    for _ in 0..n_ports {
                        ports.push(self.parse_timing_port()?);
                    }
                    let mut values = Vec::with_capacity(n_values);
                    for _ in 0..n_values {
                        self.skip_ws();
                        values.push(if self.input[self.pos..].starts_with("()") {
                            self.pos += 2;
                            None
                        } else {
                            Some(self.parse_delay_value()?)
                        });
                    }
                    self.skip_to_close_paren();
                    cell.delays.push(SdfDelay::TimingCheck {
                        kind,
                        ports,
                        values,
                    });
                }
                None => return Ok(()),
                _ => {
                    self.pos += 1;
                }
            }
        }
    }

    /// `port`, `(edge port)` or `(COND [name] expr port_spec)`.
    fn parse_timing_port(&mut self) -> Result<SdfTimingPort, String> {
        self.skip_ws();
        if self.peek() != Some('(') {
            return Ok(SdfTimingPort {
                port: self.read_token(),
                edge: None,
                cond: None,
            });
        }
        let open = self.pos;
        self.pos += 1;
        let kw = self.read_token();
        if kw.eq_ignore_ascii_case("COND") {
            // Balanced body; the port spec is its last element.
            let start = self.pos;
            self.skip_to_close_paren();
            let body = self.input[start..self.pos - 1].trim();
            let (cond, spec) = match body.strip_suffix(')') {
                Some(inner) => {
                    let mut depth = 0i32;
                    let mut at = None;
                    for (i, c) in inner.char_indices().rev() {
                        match c {
                            ')' => depth += 1,
                            '(' if depth == 0 => {
                                at = Some(i);
                                break;
                            }
                            '(' => depth -= 1,
                            _ => {}
                        }
                    }
                    let at = at.ok_or_else(|| format!("SDF: bad COND at pos {}", open))?;
                    (&body[..at], &body[at..])
                }
                None => match body.rfind(char::is_whitespace) {
                    Some(i) => (&body[..i], &body[i + 1..]),
                    None => return Err(format!("SDF: bad COND at pos {}", open)),
                },
            };
            let mut sub = SdfParser::new(spec);
            let mut p = sub.parse_timing_port()?;
            let cond = cond.trim();
            // An optional QSTRING name precedes the condition.
            let cond = match cond.strip_prefix('"').and_then(|c| c.split_once('"')) {
                Some((_, rest)) => rest.trim(),
                None => cond,
            };
            p.cond = Some(cond.to_string());
            return Ok(p);
        }
        let port = self.read_token();
        self.expect_char(')')?;
        Ok(SdfTimingPort {
            port,
            edge: Some(kw.to_ascii_lowercase()),
            cond: None,
        })
    }

    /// Parse a delay value: either (min:typ:max) or (value)
    fn parse_delay_value(&mut self) -> Result<DelayTriple, String> {
        self.skip_ws();
        if self.peek() != Some('(') {
            // Bare number
            let v = self.read_number();
            return Ok(DelayTriple::single(v));
        }
        self.pos += 1; // skip (
        self.skip_ws();

        let read_part = |p: &mut Self| {
            p.skip_ws();
            (!matches!(p.peek(), Some(':' | ')') | None)).then(|| p.read_number())
        };
        let first = read_part(self);
        self.skip_ws();
        if self.peek() == Some(':') {
            self.pos += 1;
            let typ = read_part(self);
            self.expect_char(':')?;
            let max = read_part(self);
            self.expect_char(')')?;
            Ok(DelayTriple {
                min: first,
                typ,
                max,
            })
        } else if self.peek() == Some(')') {
            self.pos += 1;
            Ok(DelayTriple {
                min: first,
                typ: first,
                max: first,
            })
        } else {
            Err(format!(
                "SDF: unexpected char in delay value at pos {}",
                self.pos
            ))
        }
    }
}

// ═══════════════════════════════════════════════════════════════════
// Annotation: convert SDF delays into simulation-ready form
// ═══════════════════════════════════════════════════════════════════

/// Annotate an elaborated design with SDF delays.
/// `sim_timescale` is the simulation timescale in seconds (e.g., 1e-9 for 1ns).
/// `delay_select` chooses min/typ/max from the SDF triples.
pub fn annotate_sdf(sdf: &SdfFile, sim_timescale: f64, delay_select: DelaySelect) -> SdfAnnotation {
    let mut annotation = SdfAnnotation::new();
    let scale = sdf.timescale / sim_timescale;

    let ticks = |values: &[DelayTriple]| {
        values
            .iter()
            .map(|v| delay_select.pick(v).map(|n| (n * scale).round() as i64))
            .collect::<Vec<_>>()
    };
    let name = |scope: &str, terminal: &str| {
        if scope.is_empty() {
            terminal.to_owned()
        } else {
            format!("{scope}.{terminal}")
        }
    };
    for cell in &sdf.cells {
        for delay in &cell.delays {
            match delay {
                SdfDelay::IoPath {
                    input,
                    output,
                    values,
                    increment,
                    ifnone,
                } => {
                    let dst = name(&cell.instance, output);
                    let mut input = input.clone();
                    input.port = name(&cell.instance, &input.port);
                    annotation
                        .pin_delays
                        .entry(dst)
                        .or_default()
                        .push(PinDelay {
                            input,
                            values: ticks(values),
                            increment: *increment,
                            ifnone: *ifnone,
                        });
                }
                SdfDelay::Interconnect {
                    source,
                    dest,
                    values,
                    increment,
                } => {
                    let dst = name(&cell.instance, dest);
                    let input = SdfTimingPort {
                        port: name(&cell.instance, source),
                        edge: None,
                        cond: None,
                    };
                    annotation
                        .interconnect_delays
                        .entry(dst)
                        .or_default()
                        .push(PinDelay {
                            input,
                            values: ticks(values),
                            increment: *increment,
                            ifnone: false,
                        });
                }
                SdfDelay::TimingCheck {
                    kind,
                    ports,
                    values,
                } => {
                    annotation.timing_limits.push(SdfTimingLimit {
                        cell_type: cell.cell_type.clone(),
                        instance: cell.instance.clone(),
                        kind: kind.clone(),
                        ports: ports.clone(),
                        limits: values
                            .iter()
                            .map(|v| {
                                v.and_then(|t| delay_select.pick(&t))
                                    .map(|n| (n * scale).round() as i64)
                            })
                            .collect(),
                    });
                }
            }
        }
    }

    for table in [&annotation.pin_delays, &annotation.interconnect_delays] {
        for (net, paths) in table {
            if let Some(value) = paths.iter().flat_map(|p| p.values.iter().flatten()).max() {
                let old = annotation.signal_delays.entry(net.clone()).or_default();
                *old = (*old).max((*value).max(0) as u64);
            }
        }
    }
    annotation
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_sdf() {
        let sdf_content = r#"
(DELAYFILE
  (SDFVERSION "4.0")
  (DESIGN "test")
  (TIMESCALE 1ns)
  (CELL
    (CELLTYPE "INV")
    (INSTANCE u1)
    (DELAY
      (ABSOLUTE
        (IOPATH A Y (0.05:0.1:0.15) (0.04:0.08:0.12))
      )
    )
  )
)
"#;
        let sdf = parse_sdf(sdf_content).unwrap();
        assert_eq!(sdf.version, "4.0");
        assert_eq!(sdf.design, "test");
        assert_eq!(sdf.cells.len(), 1);
        assert_eq!(sdf.cells[0].cell_type, "INV");
        assert_eq!(sdf.cells[0].instance, "u1");
        assert_eq!(sdf.cells[0].delays.len(), 1);
        if let SdfDelay::IoPath {
            input,
            output,
            values,
            ..
        } = &sdf.cells[0].delays[0]
        {
            assert_eq!(input.port, "A");
            assert_eq!(output, "Y");
            assert!((values[0].typ.unwrap() - 0.1).abs() < 1e-9);
            assert!((values[1].typ.unwrap() - 0.08).abs() < 1e-9);
        } else {
            panic!("expected IoPath");
        }
    }

    #[test]
    fn test_annotate_typ() {
        let sdf_content = r#"
(DELAYFILE
  (SDFVERSION "4.0")
  (TIMESCALE 1ns)
  (CELL
    (CELLTYPE "BUF")
    (INSTANCE top.buf1)
    (DELAY
      (ABSOLUTE
        (IOPATH A X (0.1:0.2:0.3) (0.15:0.25:0.35))
      )
    )
  )
)
"#;
        let sdf = parse_sdf(sdf_content).unwrap();
        let ann = annotate_sdf(&sdf, 1e-9, DelaySelect::Typ);
        // 0.25ns max(rise=0.2, fall=0.25) in 1ns timescale → rounds to 0 ticks
        assert_eq!(ann.get_delay("top.buf1.X"), 0);
        // With ps timescale (1e-12), 0.25ns = 250ps = 250 ticks
        let ann_ps = annotate_sdf(&sdf, 1e-12, DelaySelect::Typ);
        assert_eq!(ann_ps.get_delay("top.buf1.X"), 250);
    }

    #[test]
    fn test_timingcheck_entries() {
        let sdf_content = r#"
(DELAYFILE
  (TIMESCALE 1ns)
  (CELL
    (CELLTYPE "DFF")
    (INSTANCE top.u1)
    (TIMINGCHECK
      (SETUPHOLD D (posedge CK) (0.3:0.4:0.5) (-0.1))
      (HOLD (COND SE==0 D) (posedge CK) ())
      (WIDTH (negedge CK) (1.2))
      (BIDIRECTSKEW A B (1) (1))
    )
  )
)
"#;
        let sdf = parse_sdf(sdf_content).unwrap();
        assert_eq!(sdf.cells[0].delays.len(), 3);
        let ann = annotate_sdf(&sdf, 1e-12, DelaySelect::Typ);
        let l = &ann.timing_limits;
        assert_eq!(l.len(), 3);
        assert_eq!(
            (l[0].kind.as_str(), l[0].instance.as_str()),
            ("SETUPHOLD", "top.u1")
        );
        assert_eq!(
            l[0].ports[0],
            SdfTimingPort {
                port: "D".into(),
                edge: None,
                cond: None
            }
        );
        assert_eq!(l[0].ports[1].edge.as_deref(), Some("posedge"));
        assert_eq!(l[0].limits, vec![Some(400), Some(-100)]);
        assert_eq!(l[1].ports[0].cond.as_deref(), Some("SE==0"));
        assert_eq!(l[1].ports[0].port, "D");
        assert_eq!(l[1].limits, vec![None]);
        assert_eq!(l[2].ports[0].edge.as_deref(), Some("negedge"));
        assert_eq!(l[2].limits, vec![Some(1200)]);
    }
}
