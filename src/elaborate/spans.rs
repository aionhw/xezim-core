use super::*;

/// §6.6.2/§6.6.3 net kinds that need something other than plain wire
/// resolution. `Wand`/`Wor` cover their `triand`/`trior` synonyms.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum ResolvedNetKind {
    /// Wired AND: all drivers ANDed together.
    Wand,
    /// Wired OR: all drivers ORed together.
    Wor,
    /// Pulls to 0 on bits no driver is driving.
    Tri0,
    /// Pulls to 1 on bits no driver is driving.
    Tri1,
    /// §6.6.4 `trireg` charge storage: bits no driver is driving HOLD the
    /// last driven value (modeled as an implicit weak self-driver).
    ChargeStorage,
    /// Verilog-AMS `wreal`: drivers are SUMMED rather than resolved
    /// bitwise. Verilog-AMS leaves multi-driver `wreal` resolution to the
    /// tool; summing is the one that makes a current-summing wrapper mean
    /// what it says -- several stages each drive their contribution onto a
    /// shared node and the node integrator sees the total, which is exactly
    /// Kirchhoff's current law. Bitwise `$__wres` would instead call two
    /// drivers a conflict and yield x.
    RealSum,
}

impl ResolvedNetKind {
    pub(super) fn from_net_type(nt: NetType) -> Option<Self> {
        match nt {
            NetType::Wand | NetType::TriAnd => Some(Self::Wand),
            NetType::Wor | NetType::TriOr => Some(Self::Wor),
            NetType::Tri0 => Some(Self::Tri0),
            NetType::Tri1 => Some(Self::Tri1),
            NetType::TriReg => Some(Self::ChargeStorage),
            NetType::Wreal => Some(Self::RealSum),
            _ => None,
        }
    }
}

thread_local! {
    /// Preprocessed source texts + file names, published BEFORE elaboration so
    /// elaboration-time diagnostics can resolve a span to `file:line`.
    /// `ElaboratedModule::source_texts` is only assigned once elaboration has
    /// already returned, which is too late for an error raised during it.
    /// Moved in and back out (never cloned) so this costs no extra memory.
    static ELAB_SOURCES_TLS: std::cell::RefCell<(Vec<String>, Vec<String>)> =
        const { std::cell::RefCell::new((Vec::new(), Vec::new())) };
    /// Which source file defined each module/interface/program, by name.
    /// Published alongside the sources for the same reason: a `Span` is a byte
    /// offset into ITS OWN file, so with several files retained the offset
    /// alone cannot say which one it belongs to. Knowing the file of the
    /// module being elaborated resolves that.
    static ELAB_MODULE_FILES_TLS: std::cell::RefCell<HashMap<String, u32>> =
        std::cell::RefCell::new(HashMap::default());
    /// Line maps of the published sources (parallel to them).
    static ELAB_LINE_MAPS_TLS: std::cell::RefCell<Vec<Option<sv_parser::source_map::LineMap>>> =
        const { std::cell::RefCell::new(Vec::new()) };
    /// The `-v`/`-y` library files a definition was adopted from. They are
    /// not among the published sources, so a span inside an adopted module
    /// fitted some PRIMARY file instead and was reported there.
    static ELAB_LIB_SOURCES_TLS: std::cell::RefCell<LibrarySources> =
        std::cell::RefCell::new(LibrarySources::default());
}

/// The library files adopted definitions came from, and the packages those
/// files declared (a library file supplies no packages).
#[derive(Default)]
pub struct LibrarySources {
    /// (file label, preprocessed text, line map) per adopted library file.
    /// The text is shared with `preprocess_adopted_lib`.
    pub files: Vec<(String, std::sync::Arc<str>, Option<sv_parser::source_map::LineMap>)>,
    /// Adopted definition name -> index into `files`.
    pub def_file: HashMap<String, u32>,
    /// Package name -> where a library file declared it, as
    /// (`file:line:col` of the declaration, library file label).
    pub ignored_packages: HashMap<String, (String, String)>,
}

/// Publish the library files of this run's adopted definitions.
pub fn set_elab_library_sources(lib: LibrarySources) {
    ELAB_LIB_SOURCES_TLS.with(|c| *c.borrow_mut() = lib);
}

/// The note for a package that is missing because only a library file
/// declared it, or an empty string.
pub(super) fn ignored_library_package_note(pkg: &str) -> String {
    ELAB_LIB_SOURCES_TLS.with(|c| match c.borrow().ignored_packages.get(pkg) {
        Some((at, lib)) => format!(
            "\nnote: package '{pkg}' is declared at {at}, in library file '{lib}'; a -v/-y \
             library file supplies only modules, interfaces, programs and primitives, so the \
             package was not compiled. Pass that file as a source file, or, for a -v file, \
             compile its packages with --relax-library-packages"
        ),
        None => String::new(),
    })
}

/// The location of `span` inside the library file definition `owner` was
/// adopted from, when it was adopted from one.
fn library_span_locate(owner: &str, span: Span) -> Option<Option<SpanLoc>> {
    ELAB_LIB_SOURCES_TLS.with(|c| {
        let lib = c.borrow();
        let i = *lib.def_file.get(owner)? as usize;
        let (file, text, map) = lib.files.get(i)?;
        if span.start >= text.len() {
            return Some(None);
        }
        if let Some(loc) = map.as_ref().and_then(|m| m.locate(text, span)) {
            return Some(Some(SpanLoc::Mapped(loc)));
        }
        let line = 1 + text.as_bytes()[..span.start]
            .iter()
            .filter(|&&b| b == b'\n')
            .count();
        Some(Some(SpanLoc::Plain(format!("{}:{}", file, line))))
    })
}

/// Publish the line maps of the sources passed to `set_elab_sources`.
pub fn set_elab_line_maps(maps: Vec<Option<sv_parser::source_map::LineMap>>) {
    ELAB_LINE_MAPS_TLS.with(|c| *c.borrow_mut() = maps);
}

/// Move the published line maps back out.
pub fn take_elab_line_maps() -> Vec<Option<sv_parser::source_map::LineMap>> {
    ELAB_LINE_MAPS_TLS.with(|c| std::mem::take(&mut *c.borrow_mut()))
}

/// Publish the preprocessed sources for elaboration-time diagnostics. Takes
/// ownership; call `take_elab_sources` afterwards to move them into the
/// elaborated module.
pub fn set_elab_sources(texts: Vec<String>, files: Vec<String>) {
    ELAB_SOURCES_TLS.with(|c| *c.borrow_mut() = (texts, files));
}

/// Publish the module→source-file index map for elaboration-time diagnostics.
/// Cloned rather than moved: unlike the source texts this map is small, and
/// the caller still needs it for `ElaboratedModule::src_file_of_module`.
pub fn set_elab_module_files(map: HashMap<String, u32>) {
    ELAB_MODULE_FILES_TLS.with(|c| *c.borrow_mut() = map);
}

/// Move the published sources back out (leaving the slot empty).
pub fn take_elab_sources() -> (Vec<String>, Vec<String>) {
    ELAB_MODULE_FILES_TLS.with(|c| c.borrow_mut().clear());
    ELAB_SOURCES_TLS.with(|c| std::mem::take(&mut *c.borrow_mut()))
}

/// `file:line` of a span of a definition in the primary sources; `def@offset`
/// for one adopted from a library, whose text is not published yet.
pub(crate) fn audit_location(def: &str, span: Span) -> String {
    let at = ELAB_MODULE_FILES_TLS
        .with(|c| c.borrow().get(def).copied())
        .and_then(|i| {
            let i = i as usize;
            ELAB_SOURCES_TLS.with(|s| {
                ELAB_LINE_MAPS_TLS.with(|m| {
                    let s = s.borrow();
                    let text = s.0.get(i)?;
                    let loc = m.borrow().get(i)?.as_ref()?.location_string(text, span)?;
                    loc.rsplit_once(':').map(|(l, _)| l.to_string())
                })
            })
        });
    at.unwrap_or_else(|| format!("{def}@{}", span.start))
}

/// Resolve a `Span` (a byte offset into its own file's PREPROCESSED text) to
/// `file:line:col` (`file:line` without a line map), for elaboration
/// diagnostics. The file is the one the text came from — an `include`d file,
/// not the file that included it. Mirrors the simulator's
/// `span_file_line_in`: when several retained sources could contain the
/// offset the location is ambiguous, and printing a wrong file is worse than
/// printing none.
pub fn span_location(elab: &ElaboratedModule, span: Span) -> Option<String> {
    span_location_impl(elab, span, true)
}

/// As `span_location`, but WITHOUT preferring the file of the module being
/// elaborated. For a span that may belong to another file — a package's enum
/// member, an imported parameter — the hint would name the wrong file with
/// full confidence, which is worse than saying nothing.
pub fn span_location_unhinted(elab: &ElaboratedModule, span: Span) -> Option<String> {
    span_location_impl(elab, span, false)
}

/// As `span_location`, but hinting with the file of a NAMED definition
/// (a package, module or interface) instead of the module being elaborated.
/// A package subroutine's span is an offset into the PACKAGE's file, so
/// hinting with the elaboration root would name the wrong file.
pub fn span_location_of(elab: &ElaboratedModule, span: Span, owner: &str) -> Option<String> {
    span_location_impl_owned(elab, span, true, Some(owner))
}

fn span_location_impl(elab: &ElaboratedModule, span: Span, hint: bool) -> Option<String> {
    span_location_impl_owned(elab, span, hint, None)
}

fn span_location_impl_owned(
    elab: &ElaboratedModule,
    span: Span,
    hint: bool,
    owner: Option<&str>,
) -> Option<String> {
    span_locate_owned(elab, span, hint, owner).map(|l| match l {
        SpanLoc::Mapped(loc) => loc.short(),
        SpanLoc::Plain(s) => s,
    })
}

/// Where a span resolved to: through a line map (full location), or only to
/// `file:line` of the preprocessed text.
enum SpanLoc {
    Mapped(sv_parser::diagnostics::Location),
    Plain(String),
}

fn span_locate_owned(
    elab: &ElaboratedModule,
    span: Span,
    hint: bool,
    owner: Option<&str>,
) -> Option<SpanLoc> {
    if span.start == 0 && span.end == 0 {
        return None; // Span::dummy() — synthesized, no source
    }
    // Which file the module being elaborated came from. A `Span` is an offset
    // into its OWN file, so with several files retained almost every offset
    // fits inside more than one of them — the old "unique fit wins, otherwise
    // give up" scan therefore reported NOTHING for any multi-file design,
    // which is every real one. Prefer the file that actually defines this
    // module and fall back to the scan only when it is unknown.
    let hint_name: &str = owner.unwrap_or(elab.name.as_str());
    // A definition adopted from a library file: its spans index THAT file.
    if hint && !hint_name.is_empty() {
        if let Some(loc) = library_span_locate(hint_name, span) {
            return loc;
        }
    }
    let preferred: Option<usize> = if !hint || hint_name.is_empty() {
        None
    } else {
        elab.src_file_of_module
            .get(hint_name)
            .copied()
            .or_else(|| ELAB_MODULE_FILES_TLS.with(|c| c.borrow().get(hint_name).copied()))
            .map(|i| i as usize)
    };
    // During elaboration the module's own copy is still empty; the sources
    // live in the TLS published by `set_elab_sources`.
    let resolve = |texts: &[String],
                   files: &[String],
                   maps: &[Option<sv_parser::source_map::LineMap>]|
     -> Option<SpanLoc> {
        let mut hit: Option<usize> = None;
        if let Some(p) = preferred {
            if texts.get(p).is_some_and(|t| span.start < t.len()) {
                hit = Some(p);
            }
        }
        if hit.is_none() {
            for (i, t) in texts.iter().enumerate() {
                if span.start < t.len() {
                    if hit.is_some() {
                        return None; // ambiguous across files
                    }
                    hit = Some(i);
                }
            }
        }
        let i = hit?;
        if let Some(loc) = maps
            .get(i)
            .and_then(|m| m.as_ref())
            .and_then(|m| m.locate(&texts[i], span))
        {
            return Some(SpanLoc::Mapped(loc));
        }
        let line = 1 + texts[i].as_bytes()[..span.start]
            .iter()
            .filter(|&&b| b == b'\n')
            .count();
        match files.get(i).filter(|f| !f.is_empty()) {
            Some(f) => Some(SpanLoc::Plain(format!("{}:{}", f, line))),
            None => Some(SpanLoc::Plain(format!("line {}", line))),
        }
    };
    if !elab.source_texts.is_empty() {
        return resolve(
            &elab.source_texts,
            &elab.source_files,
            &elab.source_line_maps,
        );
    }
    ELAB_SOURCES_TLS.with(|c| {
        let b = c.borrow();
        ELAB_LINE_MAPS_TLS.with(|m| resolve(&b.0, &b.1, &m.borrow()))
    })
}

/// `file:line:col` of `span` from the sources published for the current
/// elaboration, when exactly one of them can hold it (no module to hint
/// with); otherwise `byte N`.
pub(super) fn published_span_location(span: Span) -> String {
    let found = ELAB_SOURCES_TLS.with(|c| {
        let b = c.borrow();
        let mut fits = b.0.iter().enumerate().filter(|(_, t)| span.start < t.len());
        let (i, text) = fits.next()?;
        if fits.next().is_some() {
            return None;
        }
        ELAB_LINE_MAPS_TLS.with(|m| m.borrow().get(i)?.as_ref()?.location_string(text, span))
    });
    found.unwrap_or_else(|| format!("byte {}", span.start))
}

/// An elaboration error at `span`, rendered like a parser diagnostic: the
/// `file:line:col:` header, the source line and a caret under the span.
/// Without a location it is just the message.
pub fn span_error(elab: &ElaboratedModule, span: Span, message: &str) -> String {
    span_error_impl(elab, span, None, message)
}

/// As `span_error`, for a span inside the NAMED definition `owner` (a
/// package or another module), whose file is not the elaboration root's.
pub fn span_error_of(elab: &ElaboratedModule, span: Span, owner: &str, message: &str) -> String {
    span_error_impl(elab, span, Some(owner), message)
}

fn span_error_impl(
    elab: &ElaboratedModule,
    span: Span,
    owner: Option<&str>,
    message: &str,
) -> String {
    match span_locate_owned(elab, span, true, owner) {
        Some(SpanLoc::Mapped(loc)) => sv_parser::diagnostics::render("error", message, &loc),
        Some(SpanLoc::Plain(s)) => format!("{} at {}", message, s),
        None => message.to_string(),
    }
}

/// Build the message for an illegal re-declaration (§6.x). The bare
/// "duplicate declaration of 'X'" gave a user no way to find either
/// declaration in a large multi-file design, so report WHERE the offending
/// declaration is, WHAT the name already refers to (a signal/net or a
/// parameter — often the actual surprise, e.g. a wildcard-imported package
/// parameter), and how to downgrade the check.
pub fn duplicate_decl_error(elab: &ElaboratedModule, name: &str, span: Span, kind: &str) -> String {
    let mut m = format!("duplicate declaration of '{}' in the same scope", name);

    // The FIRST declaration — the one the user usually cannot find, because
    // the error is raised at the second. Its recorded kind ("enum member of
    // 'state_e'", "imported from package 'p'") is often the whole answer.
    let first = elab.decl_sites.get(name);
    // Resolved WITHOUT the "prefer this module's file" hint: the first
    // declaration is often in another file entirely (an enum member of a
    // package, say), and preferring the module's file would confidently
    // print a line number from the wrong file. Fall back to naming only
    // WHAT it is, which is the more useful half anyway.
    let first_loc = first.and_then(|(sp, _, own)| {
        if *own {
            span_location(elab, *sp)
        } else {
            span_location_unhinted(elab, *sp)
        }
    });
    match (first, &first_loc) {
        (Some((_, what, _)), Some(loc)) => {
            m.push_str(&format!("\n  first declaration ({}) is at {}", what, loc));
        }
        (Some((_, what, _)), None) => {
            m.push_str(&format!("\n  first declaration: {}", what));
        }
        (None, _) => {}
    }

    if let Some(loc) = span_location(elab, span) {
        m.push_str(&format!("\n  duplicate {} declaration is at {}", kind, loc));
    }
    let prior = if elab.parameters.contains_key(name) {
        Some("a parameter/localparam")
    } else if elab.nets.contains(name) {
        Some("a net")
    } else if elab.signals.contains_key(name) {
        Some("a variable/signal")
    } else {
        None
    };
    if let Some(p) = prior {
        m.push_str(&format!(
            "\n  '{}' is already declared as {} in this scope",
            name, p
        ));
        if elab.wildcard_shadowed.contains(name) {
            m.push_str(" (via a wildcard package import)");
        }
    }
    if !elab.name.is_empty() {
        m.push_str(&format!("\n  while elaborating '{}'", elab.name));
    }
    m.push_str(
        "\n  hint: rename one declaration, or pass --no-strict to downgrade this to a warning",
    );
    m
}

/// The declared type NAME of a net or variable.
///
/// `signals[..].type_name` is the usual home, but a declaration inside an
/// INSTANCE that resolves to an unpacked struct (§7.2) leaves no signal under
/// its own name at all — `register_unpacked_aggregate` registers the member
/// leaves and the sub-module path returns, recording the declared type in
/// `var_decl_types` instead. A §6.6.7(d) nettype over an unpacked struct is
/// stored that way too, so every lookup that goes only through `signals`
/// silently misses those nets: their drivers are never gathered and their
/// members never written, below the top level only.
pub(super) fn declared_type_name(elab: &ElaboratedModule, name: &str) -> Option<String> {
    if let Some(tn) = elab.signals.get(name).and_then(|sig| sig.type_name.clone()) {
        return Some(tn);
    }
    elab.var_decl_types.get(name).and_then(get_type_name)
}
