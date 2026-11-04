//! Lexer/Scanner for SystemVerilog (IEEE 1800-2017 §5)

use super::token::{Token, TokenKind, keyword};
use crate::ast::Span;

/// `String::from_utf8_lossy(b).to_string()`, validating with the fast
/// `str::from_utf8` first (token text is almost always valid).
fn lossy_string(b: &[u8]) -> String {
    match std::str::from_utf8(b) {
        Ok(s) => s.to_owned(),
        Err(_) => String::from_utf8_lossy(b).into_owned(),
    }
}

pub struct Lexer<'a> {
    input: &'a [u8],
    pos: usize,
    /// IEEE 1800-2023 §22.14: stack of active `begin_keywords` regions. The
    /// innermost region wins — in a `1364-*` (legacy Verilog) set,
    /// SystemVerilog-only keywords (`logic`, `bit`, …) lex as ordinary
    /// identifiers, and in a set without configurations so do `instance`,
    /// `cell`, ….
    kw_stack: Vec<KwRegion>,
    /// The set outside every region, read once (`default_region` locks).
    default_kw: KwRegion,
}

#[derive(Clone, Copy)]
struct KwRegion {
    /// The version whose keywords are reserved, an index into
    /// `KEYWORD_VERSIONS`: the words a later version added are names.
    version: u8,
    /// `-noconfig`: the configuration keywords are names too.
    no_config: bool,
}

/// `KEYWORD_VERSIONS` indices of the versions that added keywords.
const V1364_2001: u8 = 1;
const V1364_2005: u8 = 2;
const V1800_2005: u8 = 3;
const V1800_2009: u8 = 4;
const V1800_2012: u8 = 5;
const V_LATEST: u8 = KEYWORD_VERSIONS.len() as u8 - 1;

impl Default for KwRegion {
    fn default() -> Self {
        KwRegion {
            version: V_LATEST,
            no_config: false,
        }
    }
}

impl KwRegion {
    /// The keyword set of a §22.14 version specifier, `None` for an unknown
    /// one. A `-noconfig` suffix on any version leaves the configuration
    /// keywords out, as 1364-2001-noconfig does.
    fn of_version(ver: &str) -> Option<Self> {
        let (base, no_config) = match ver.strip_suffix("-noconfig") {
            Some(b) => (b, true),
            None => (ver, false),
        };
        let version = KEYWORD_VERSIONS.iter().position(|v| *v == base)? as u8;
        Some(KwRegion { version, no_config })
    }

    /// §22.14, Table 22-2: whether a reserved word is a name in this set —
    /// a word a later version added, or a configuration keyword in a
    /// `-noconfig` set or before 1364-2001 brought them.
    fn frees(self, s: &str) -> bool {
        let before = |v: u8| self.version < v;
        ((self.no_config || before(V1364_2001)) && is_config_keyword(s))
            || (before(V1364_2001) && is_1364_2001_keyword(s))
            || (before(V1364_2005) && s == "uwire")
            || (before(V1800_2005) && is_sv_only_keyword(s))
            || (before(V1800_2009) && is_1800_2009_keyword(s))
            || (before(V1800_2012) && is_1800_2012_keyword(s))
    }
}

/// The §22.14 version specifiers.
pub const KEYWORD_VERSIONS: &[&str] = &[
    "1364-1995",
    "1364-2001",
    "1364-2005",
    "1800-2005",
    "1800-2009",
    "1800-2012",
    "1800-2017",
    "1800-2023",
];

/// The keyword set outside every `begin_keywords` region (#608): set by
/// `set_default_keywords` / `set_no_config_keywords`, else from
/// `XEZIM_KEYWORDS` / `XEZIM_NO_CONFIG_KEYWORDS=1`, else the full set.
static DEFAULT_KEYWORDS: std::sync::Mutex<Option<KwRegion>> = std::sync::Mutex::new(None);

fn default_region() -> KwRegion {
    DEFAULT_KEYWORDS
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .unwrap_or_else(env_region)
}

/// The default set the environment chooses. A setter starts from it, so
/// `XEZIM_KEYWORDS` survives `set_no_config_keywords` and
/// `XEZIM_NO_CONFIG_KEYWORDS=1` survives `set_default_keywords`.
fn env_region() -> KwRegion {
    static ENV: std::sync::OnceLock<KwRegion> = std::sync::OnceLock::new();
    *ENV.get_or_init(|| {
        let mut r = std::env::var("XEZIM_KEYWORDS")
            .ok()
            .and_then(|v| KwRegion::of_version(v.trim()))
            .unwrap_or_default();
        r.no_config |= std::env::var("XEZIM_NO_CONFIG_KEYWORDS").ok().as_deref() == Some("1");
        r
    })
}

/// §22.14 leaves the keyword set outside `begin_keywords` regions to the
/// implementation: choose it by version specifier (`1364-1995`, ...,
/// `1800-2023`, each also with `-noconfig`). An unknown one is an error that
/// lists the valid ones.
pub fn set_default_keywords(version: &str) -> Result<(), String> {
    let r = KwRegion::of_version(version).ok_or_else(|| {
        format!(
            "unknown keyword set '{version}'; one of {} (each also with -noconfig) \
             (IEEE 1800-2023 §22.14)",
            KEYWORD_VERSIONS.join(", ")
        )
    })?;
    let mut d = DEFAULT_KEYWORDS.lock().unwrap_or_else(|e| e.into_inner());
    let keep = d.unwrap_or_else(env_region).no_config;
    *d = Some(KwRegion {
        no_config: r.no_config || keep,
        ..r
    });
    Ok(())
}

/// Outside `begin_keywords` regions, read the ten configuration keywords
/// (`instance`, `cell`, `use`, ...) as names (#608).
pub fn set_no_config_keywords(on: bool) {
    let mut d = DEFAULT_KEYWORDS.lock().unwrap_or_else(|e| e.into_inner());
    let mut r = d.unwrap_or_else(env_region);
    r.no_config = on;
    *d = Some(r);
}

/// The default keyword set, for cache keys: how many versions back it is
/// (0 for the full set), with bit 4 for `-noconfig`.
pub fn default_keywords_key() -> u8 {
    let r = default_region();
    (V_LATEST - r.version) | (r.no_config as u8) << 4
}

impl<'a> Lexer<'a> {
    pub fn new(source: &'a str) -> Self {
        Self {
            input: source.as_bytes(),
            pos: 0,
            kw_stack: Vec::new(),
            default_kw: default_region(),
        }
    }

    pub fn tokenize(mut self) -> Vec<Token> {
        let mut tokens = Vec::new();
        loop {
            self.skip_whitespace();
            if self.pos >= self.input.len() {
                tokens.push(Token::new(
                    TokenKind::Eof,
                    String::new(),
                    Span::new(self.pos, self.pos),
                ));
                break;
            }
            // Skip comments
            if self.pos + 1 < self.input.len() && self.input[self.pos] == b'/' {
                if self.input[self.pos + 1] == b'/' {
                    while self.pos < self.input.len() && self.input[self.pos] != b'\n' {
                        self.pos += 1;
                    }
                    continue;
                }
                if self.input[self.pos + 1] == b'*' {
                    self.pos += 2;
                    while self.pos + 1 < self.input.len() {
                        if self.input[self.pos] == b'*' && self.input[self.pos + 1] == b'/' {
                            self.pos += 2;
                            break;
                        }
                        self.pos += 1;
                    }
                    if self.pos >= self.input.len() {
                        // Unclosed block comment - just stop
                    }
                    continue;
                }
            }
            tokens.push(self.scan_token());
        }
        tokens
    }

    fn peek(&self) -> Option<u8> {
        self.input.get(self.pos + 1).copied()
    }

    fn skip_whitespace(&mut self) {
        // Blanked comments leave long runs of spaces: skip them eight at a time.
        while self.pos + 8 <= self.input.len() && self.input[self.pos..self.pos + 8] == [b' '; 8] {
            self.pos += 8;
        }
        while self.pos < self.input.len() {
            let ch = self.input[self.pos];
            if ch.is_ascii_whitespace() {
                self.pos += 1;
                continue;
            }
            // Handle line continuation: \ followed by optional spaces and then newline
            if ch == b'\\' && self.pos + 1 < self.input.len() {
                let mut p = self.pos + 1;
                while p < self.input.len()
                    && (self.input[p] == b' ' || self.input[p] == b'\t' || self.input[p] == b'\r')
                {
                    p += 1;
                }
                if p < self.input.len() && self.input[p] == b'\n' {
                    self.pos = p + 1;
                    continue;
                }
            }
            break;
        }
    }

    fn make_token(&mut self, start: usize, kind: TokenKind) -> Token {
        self.pos += 1;
        let text = lossy_string(&self.input[start..self.pos]);
        Token::new(kind, text, Span::new(start, self.pos))
    }

    fn scan_token(&mut self) -> Token {
        let start = self.pos;
        let ch = self.input[self.pos];
        match ch {
            // String literal
            b'"' => self.scan_string(start),
            // Compiler directive
            b'`' => self.scan_directive(start),
            // System identifier
            b'$' => {
                if self
                    .peek()
                    .map_or(false, |c| c.is_ascii_alphabetic() || c == b'_')
                {
                    self.scan_system_id(start)
                } else {
                    self.make_token(start, TokenKind::Dollar)
                }
            }
            // Escaped identifier
            b'\\' => self.scan_escaped_id(start),
            // Number starting with apostrophe: 'b, 'h, 'o, 'd, 's, '0, '1, 'x, 'z
            b'\'' => {
                if self.peek().map_or(false, |c| matches!(c, b'{')) {
                    self.pos += 2;
                    Token::new(
                        TokenKind::ApostropheLBrace,
                        "'{".into(),
                        Span::new(start, self.pos),
                    )
                } else if self.peek().map_or(false, |c| {
                    matches!(c, b'0' | b'1' | b'x' | b'X' | b'z' | b'Z')
                }) {
                    self.pos += 2;
                    let text = lossy_string(&self.input[start..self.pos]);
                    Token::new(
                        TokenKind::UnbasedUnsizedLiteral,
                        text,
                        Span::new(start, self.pos),
                    )
                } else {
                    self.scan_based_number(start)
                }
            }
            // Numbers
            b'0'..=b'9' => self.scan_number(start),
            // Identifiers / keywords
            b'a'..=b'z' | b'A'..=b'Z' | b'_' => self.scan_identifier(start),
            // Operators and punctuation
            b'(' => self.make_token(start, TokenKind::LParen),
            b')' => self.make_token(start, TokenKind::RParen),
            b'[' => self.make_token(start, TokenKind::LBracket),
            b']' => self.make_token(start, TokenKind::RBracket),
            b'{' => self.make_token(start, TokenKind::LBrace),
            b'}' => self.make_token(start, TokenKind::RBrace),
            b';' => self.make_token(start, TokenKind::Semicolon),
            b',' => self.make_token(start, TokenKind::Comma),
            b'.' => self.make_token(start, TokenKind::Dot),
            b'@' => self.make_token(start, TokenKind::At),
            b'?' => self.make_token(start, TokenKind::Question),
            b'~' => {
                self.pos += 1;
                match self.input.get(self.pos) {
                    Some(b'&') => {
                        self.pos += 1;
                        Token::new(TokenKind::BitNand, "~&".into(), Span::new(start, self.pos))
                    }
                    Some(b'|') => {
                        self.pos += 1;
                        Token::new(TokenKind::BitNor, "~|".into(), Span::new(start, self.pos))
                    }
                    Some(b'^') => {
                        self.pos += 1;
                        Token::new(TokenKind::BitXnor, "~^".into(), Span::new(start, self.pos))
                    }
                    _ => Token::new(TokenKind::BitNot, "~".into(), Span::new(start, self.pos)),
                }
            }
            b'+' => {
                self.pos += 1;
                match self.input.get(self.pos) {
                    Some(b'+') => {
                        self.pos += 1;
                        Token::new(
                            TokenKind::Increment,
                            "++".into(),
                            Span::new(start, self.pos),
                        )
                    }
                    Some(b'=') => {
                        self.pos += 1;
                        Token::new(
                            TokenKind::PlusAssign,
                            "+=".into(),
                            Span::new(start, self.pos),
                        )
                    }
                    Some(b':') => {
                        self.pos += 1;
                        Token::new(
                            TokenKind::PlusColon,
                            "+:".into(),
                            Span::new(start, self.pos),
                        )
                    }
                    _ => Token::new(TokenKind::Plus, "+".into(), Span::new(start, self.pos)),
                }
            }
            b'-' => {
                self.pos += 1;
                match self.input.get(self.pos) {
                    Some(b'-') => {
                        self.pos += 1;
                        Token::new(
                            TokenKind::Decrement,
                            "--".into(),
                            Span::new(start, self.pos),
                        )
                    }
                    Some(b'=') => {
                        self.pos += 1;
                        Token::new(
                            TokenKind::MinusAssign,
                            "-=".into(),
                            Span::new(start, self.pos),
                        )
                    }
                    Some(b'>') => {
                        self.pos += 1;
                        if self.input.get(self.pos) == Some(&b'>') {
                            self.pos += 1;
                            Token::new(
                                TokenKind::DoubleArrow,
                                "->>".into(),
                                Span::new(start, self.pos),
                            )
                        } else {
                            Token::new(TokenKind::Arrow, "->".into(), Span::new(start, self.pos))
                        }
                    }
                    Some(b':') => {
                        self.pos += 1;
                        Token::new(
                            TokenKind::MinusColon,
                            "-:".into(),
                            Span::new(start, self.pos),
                        )
                    }
                    _ => Token::new(TokenKind::Minus, "-".into(), Span::new(start, self.pos)),
                }
            }
            b'*' => {
                self.pos += 1;
                match self.input.get(self.pos) {
                    Some(b'*') => {
                        self.pos += 1;
                        Token::new(
                            TokenKind::DoubleStar,
                            "**".into(),
                            Span::new(start, self.pos),
                        )
                    }
                    Some(b'=') => {
                        self.pos += 1;
                        Token::new(
                            TokenKind::StarAssign,
                            "*=".into(),
                            Span::new(start, self.pos),
                        )
                    }
                    _ => Token::new(TokenKind::Star, "*".into(), Span::new(start, self.pos)),
                }
            }
            b'/' => {
                self.pos += 1;
                match self.input.get(self.pos) {
                    Some(b'=') => {
                        self.pos += 1;
                        Token::new(
                            TokenKind::SlashAssign,
                            "/=".into(),
                            Span::new(start, self.pos),
                        )
                    }
                    _ => Token::new(TokenKind::Slash, "/".into(), Span::new(start, self.pos)),
                }
            }
            b'%' => {
                self.pos += 1;
                if self.input.get(self.pos) == Some(&b'=') {
                    self.pos += 1;
                    Token::new(
                        TokenKind::PercentAssign,
                        "%=".into(),
                        Span::new(start, self.pos),
                    )
                } else {
                    Token::new(TokenKind::Percent, "%".into(), Span::new(start, self.pos))
                }
            }
            b'!' => {
                self.pos += 1;
                match self.input.get(self.pos) {
                    Some(b'=') => {
                        self.pos += 1;
                        match self.input.get(self.pos) {
                            Some(b'=') => {
                                self.pos += 1;
                                Token::new(
                                    TokenKind::CaseNeq,
                                    "!==".into(),
                                    Span::new(start, self.pos),
                                )
                            }
                            Some(b'?') => {
                                self.pos += 1;
                                Token::new(
                                    TokenKind::WildcardNeq,
                                    "!=?".into(),
                                    Span::new(start, self.pos),
                                )
                            }
                            _ => {
                                Token::new(TokenKind::Neq, "!=".into(), Span::new(start, self.pos))
                            }
                        }
                    }
                    _ => Token::new(TokenKind::LogNot, "!".into(), Span::new(start, self.pos)),
                }
            }
            b'=' => {
                self.pos += 1;
                match self.input.get(self.pos) {
                    Some(b'=') => {
                        self.pos += 1;
                        match self.input.get(self.pos) {
                            Some(b'=') => {
                                self.pos += 1;
                                Token::new(
                                    TokenKind::CaseEq,
                                    "===".into(),
                                    Span::new(start, self.pos),
                                )
                            }
                            Some(b'?') => {
                                self.pos += 1;
                                Token::new(
                                    TokenKind::WildcardEq,
                                    "==?".into(),
                                    Span::new(start, self.pos),
                                )
                            }
                            _ => Token::new(TokenKind::Eq, "==".into(), Span::new(start, self.pos)),
                        }
                    }
                    Some(b'>') => {
                        self.pos += 1;
                        Token::new(TokenKind::FatArrow, "=>".into(), Span::new(start, self.pos))
                    }
                    _ => Token::new(TokenKind::Assign, "=".into(), Span::new(start, self.pos)),
                }
            }
            b'<' => {
                self.pos += 1;
                match self.input.get(self.pos) {
                    Some(b'=') => {
                        self.pos += 1;
                        Token::new(TokenKind::Leq, "<=".into(), Span::new(start, self.pos))
                    }
                    Some(b'<') => {
                        self.pos += 1;
                        match self.input.get(self.pos) {
                            Some(b'<') => {
                                self.pos += 1;
                                if self.input.get(self.pos) == Some(&b'=') {
                                    self.pos += 1;
                                    Token::new(
                                        TokenKind::ArithShiftLeftAssign,
                                        "<<<=".into(),
                                        Span::new(start, self.pos),
                                    )
                                } else {
                                    Token::new(
                                        TokenKind::ArithShiftLeft,
                                        "<<<".into(),
                                        Span::new(start, self.pos),
                                    )
                                }
                            }
                            Some(b'=') => {
                                self.pos += 1;
                                Token::new(
                                    TokenKind::ShiftLeftAssign,
                                    "<<=".into(),
                                    Span::new(start, self.pos),
                                )
                            }
                            _ => Token::new(
                                TokenKind::ShiftLeft,
                                "<<".into(),
                                Span::new(start, self.pos),
                            ),
                        }
                    }
                    Some(b'-') => {
                        self.pos += 1;
                        if self.input.get(self.pos) == Some(&b'>') {
                            self.pos += 1;
                            Token::new(
                                TokenKind::LogEquiv,
                                "<->".into(),
                                Span::new(start, self.pos),
                            )
                        } else {
                            self.pos -= 1;
                            Token::new(TokenKind::Lt, "<".into(), Span::new(start, self.pos))
                        }
                    }
                    _ => Token::new(TokenKind::Lt, "<".into(), Span::new(start, self.pos)),
                }
            }
            b'>' => {
                self.pos += 1;
                match self.input.get(self.pos) {
                    Some(b'=') => {
                        self.pos += 1;
                        Token::new(TokenKind::Geq, ">=".into(), Span::new(start, self.pos))
                    }
                    Some(b'>') => {
                        self.pos += 1;
                        match self.input.get(self.pos) {
                            Some(b'>') => {
                                self.pos += 1;
                                if self.input.get(self.pos) == Some(&b'=') {
                                    self.pos += 1;
                                    Token::new(
                                        TokenKind::ArithShiftRightAssign,
                                        ">>>=".into(),
                                        Span::new(start, self.pos),
                                    )
                                } else {
                                    Token::new(
                                        TokenKind::ArithShiftRight,
                                        ">>>".into(),
                                        Span::new(start, self.pos),
                                    )
                                }
                            }
                            Some(b'=') => {
                                self.pos += 1;
                                Token::new(
                                    TokenKind::ShiftRightAssign,
                                    ">>=".into(),
                                    Span::new(start, self.pos),
                                )
                            }
                            _ => Token::new(
                                TokenKind::ShiftRight,
                                ">>".into(),
                                Span::new(start, self.pos),
                            ),
                        }
                    }
                    _ => Token::new(TokenKind::Gt, ">".into(), Span::new(start, self.pos)),
                }
            }
            b'&' => {
                self.pos += 1;
                match self.input.get(self.pos) {
                    Some(b'&') => {
                        self.pos += 1;
                        Token::new(TokenKind::LogAnd, "&&".into(), Span::new(start, self.pos))
                    }
                    Some(b'=') => {
                        self.pos += 1;
                        Token::new(
                            TokenKind::AndAssign,
                            "&=".into(),
                            Span::new(start, self.pos),
                        )
                    }
                    _ => Token::new(TokenKind::BitAnd, "&".into(), Span::new(start, self.pos)),
                }
            }
            b'|' => {
                self.pos += 1;
                match self.input.get(self.pos) {
                    Some(b'|') => {
                        self.pos += 1;
                        Token::new(TokenKind::LogOr, "||".into(), Span::new(start, self.pos))
                    }
                    Some(b'=') => {
                        self.pos += 1;
                        if self.input.get(self.pos) == Some(&b'>') {
                            self.pos += 1;
                            Token::new(
                                TokenKind::OrFatArrow,
                                "|=>".into(),
                                Span::new(start, self.pos),
                            )
                        } else {
                            Token::new(TokenKind::OrAssign, "|=".into(), Span::new(start, self.pos))
                        }
                    }
                    Some(b'-') => {
                        self.pos += 1;
                        if self.input.get(self.pos) == Some(&b'>') {
                            self.pos += 1;
                            Token::new(
                                TokenKind::OrMinusArrow,
                                "|->".into(),
                                Span::new(start, self.pos),
                            )
                        } else {
                            // Backtrack or just bitwise or and minus. Since `-` isn't assignment, return `|` and leave `-`
                            self.pos -= 1;
                            Token::new(TokenKind::BitOr, "|".into(), Span::new(start, self.pos))
                        }
                    }
                    _ => Token::new(TokenKind::BitOr, "|".into(), Span::new(start, self.pos)),
                }
            }
            b'^' => {
                self.pos += 1;
                match self.input.get(self.pos) {
                    Some(b'~') => {
                        self.pos += 1;
                        Token::new(TokenKind::BitXnor, "^~".into(), Span::new(start, self.pos))
                    }
                    Some(b'=') => {
                        self.pos += 1;
                        Token::new(
                            TokenKind::XorAssign,
                            "^=".into(),
                            Span::new(start, self.pos),
                        )
                    }
                    _ => Token::new(TokenKind::BitXor, "^".into(), Span::new(start, self.pos)),
                }
            }
            b'#' => {
                self.pos += 1;
                if matches!(self.input.get(self.pos), Some(b'-' | b'='))
                    && self.input.get(self.pos + 1) == Some(&b'#')
                {
                    let kind = if self.input[self.pos] == b'-' {
                        TokenKind::HashMinusHash
                    } else {
                        TokenKind::HashEqualHash
                    };
                    self.pos += 2;
                    let text = if kind == TokenKind::HashMinusHash {
                        "#-#"
                    } else {
                        "#=#"
                    };
                    Token::new(kind, text.into(), Span::new(start, self.pos))
                } else if self.input.get(self.pos) == Some(&b'#') {
                    self.pos += 1;
                    Token::new(TokenKind::HashHash, "##".into(), Span::new(start, self.pos))
                } else {
                    Token::new(TokenKind::Hash, "#".into(), Span::new(start, self.pos))
                }
            }
            b':' => {
                self.pos += 1;
                match self.input.get(self.pos) {
                    Some(b':') => {
                        self.pos += 1;
                        Token::new(
                            TokenKind::DoubleColon,
                            "::".into(),
                            Span::new(start, self.pos),
                        )
                    }
                    Some(b'/') => {
                        self.pos += 1;
                        Token::new(
                            TokenKind::ColonSlash,
                            ":/".into(),
                            Span::new(start, self.pos),
                        )
                    }
                    Some(b'=') => {
                        self.pos += 1;
                        Token::new(
                            TokenKind::ColonAssign,
                            ":=".into(),
                            Span::new(start, self.pos),
                        )
                    }
                    _ => Token::new(TokenKind::Colon, ":".into(), Span::new(start, self.pos)),
                }
            }
            _ => self.make_token(start, TokenKind::Unknown),
        }
    }

    fn scan_string(&mut self, start: usize) -> Token {
        // IEEE 1800-2023 §5.9: triple-quoted string literal (""" ... """).
        // Newlines are preserved and a lone `"` (or `""`) inside does not
        // terminate the literal — only `"""` does. Gated on the SV-2023
        // mode flag; in 2017 mode `"""x"""` lexes as two empty strings.
        if crate::is_sv2023()
            && self.input.get(self.pos + 1) == Some(&b'"')
            && self.input.get(self.pos + 2) == Some(&b'"')
        {
            self.pos += 3; // skip opening """
            while self.pos < self.input.len() {
                if self.input[self.pos] == b'\\' && self.pos + 1 < self.input.len() {
                    self.pos += 2;
                    continue;
                }
                if self.input[self.pos] == b'"'
                    && self.input.get(self.pos + 1) == Some(&b'"')
                    && self.input.get(self.pos + 2) == Some(&b'"')
                {
                    self.pos += 3;
                    break;
                }
                self.pos += 1;
            }
            let text = lossy_string(&self.input[start..self.pos]);
            return Token::new(
                TokenKind::TripleStringLiteral,
                text,
                Span::new(start, self.pos),
            );
        }

        self.pos += 1; // skip opening "
        while self.pos < self.input.len() {
            if self.input[self.pos] == b'\\' {
                self.pos += 2;
                continue;
            }
            if self.input[self.pos] == b'"' {
                self.pos += 1;
                break;
            }
            self.pos += 1;
        }
        let text = lossy_string(&self.input[start..self.pos]);
        Token::new(TokenKind::StringLiteral, text, Span::new(start, self.pos))
    }

    fn scan_directive(&mut self, start: usize) -> Token {
        self.pos += 1; // skip `
        while self.pos < self.input.len()
            && (self.input[self.pos].is_ascii_alphanumeric() || self.input[self.pos] == b'_')
        {
            self.pos += 1;
        }
        let text = lossy_string(&self.input[start..self.pos]);
        // §22.14: track `begin_keywords "<version>"` / `end_keywords` so the
        // identifier scanner can downgrade SV-only keywords in legacy regions.
        // The version string is consumed here (not emitted as a separate token).
        if text == "`begin_keywords" {
            let save = self.pos;
            while self.pos < self.input.len()
                && (self.input[self.pos] == b' ' || self.input[self.pos] == b'\t')
            {
                self.pos += 1;
            }
            if self.pos < self.input.len() && self.input[self.pos] == b'"' {
                self.pos += 1; // opening quote
                let vstart = self.pos;
                while self.pos < self.input.len() && self.input[self.pos] != b'"' {
                    self.pos += 1;
                }
                let ver = lossy_string(&self.input[vstart..self.pos]);
                if self.pos < self.input.len() {
                    self.pos += 1;
                } // closing quote
                self.kw_stack
                    .push(KwRegion::of_version(&ver).unwrap_or(KwRegion {
                        version: if ver.starts_with("1364") {
                            V1364_2005
                        } else {
                            V_LATEST
                        },
                        no_config: ver.ends_with("-noconfig"),
                    }));
            } else {
                // Malformed (no version) — keep the stack balanced anyway.
                self.pos = save;
                self.kw_stack.push(KwRegion::default());
            }
            return Token::new(TokenKind::Directive, text, Span::new(start, self.pos));
        }
        if text == "`end_keywords" {
            self.kw_stack.pop();
            return Token::new(TokenKind::Directive, text, Span::new(start, self.pos));
        }
        Token::new(TokenKind::Directive, text, Span::new(start, self.pos))
    }

    fn scan_system_id(&mut self, start: usize) -> Token {
        self.pos += 1; // skip $
        while self.pos < self.input.len()
            && (self.input[self.pos].is_ascii_alphanumeric()
                || self.input[self.pos] == b'_'
                || self.input[self.pos] == b'$')
        {
            self.pos += 1;
        }
        let text = lossy_string(&self.input[start..self.pos]);
        Token::new(
            TokenKind::SystemIdentifier,
            text,
            Span::new(start, self.pos),
        )
    }

    fn scan_escaped_id(&mut self, start: usize) -> Token {
        self.pos += 1; // skip backslash
        while self.pos < self.input.len() && !self.input[self.pos].is_ascii_whitespace() {
            self.pos += 1;
        }
        let text = lossy_string(&self.input[start..self.pos]);
        Token::new(
            TokenKind::EscapedIdentifier,
            text,
            Span::new(start, self.pos),
        )
    }

    fn scan_identifier(&mut self, start: usize) -> Token {
        while self.pos < self.input.len()
            && (self.input[self.pos].is_ascii_alphanumeric()
                || self.input[self.pos] == b'_'
                || self.input[self.pos] == b'$')
        {
            self.pos += 1;
        }
        let text = lossy_string(&self.input[start..self.pos]);
        let mut kind = keyword(&text).unwrap_or(TokenKind::Identifier);
        // §22.14: inside a `begin_keywords "1364-*"` region, a SystemVerilog-
        // only keyword is a legal identifier (e.g. `reg logic;` declares a reg
        // named `logic` in Verilog-2001).
        let region = self.kw_stack.last().copied().unwrap_or(self.default_kw);
        if region.frees(&text) {
            kind = TokenKind::Identifier;
        }
        Token::new(kind, text, Span::new(start, self.pos))
    }

    fn scan_number(&mut self, start: usize) -> Token {
        // Consume decimal digits (and underscores)
        while self.pos < self.input.len()
            && (self.input[self.pos].is_ascii_digit() || self.input[self.pos] == b'_')
        {
            self.pos += 1;
        }
        // Check for based literal: <size>'<base><value>. IEEE 1800-2017
        // §5.7.1 permits whitespace between the size and the base specifier
        // (`32 'h ff`), so probe past spaces/tabs before the apostrophe and
        // only commit if a real base specifier follows.
        // §5.3: white space is spaces, tabs, newlines and form feeds, so a
        // line break may separate the size from the base too (`{2\n'd1}`).
        let mut probe = self.pos;
        while probe < self.input.len() && is_literal_space(self.input[probe]) {
            probe += 1;
        }
        if probe < self.input.len() && self.input[probe] == b'\'' {
            // `'b`, `'sb`: only a base letter (after an optional `s`) makes
            // this a based literal; `N '(...)` and `N '{...}` are not.
            let mut b = probe + 1;
            if matches!(self.input.get(b), Some(b's' | b'S')) {
                b += 1;
            }
            if matches!(
                self.input.get(b).copied().unwrap_or(0),
                b'b' | b'B' | b'o' | b'O' | b'd' | b'D' | b'h' | b'H'
            ) {
                self.pos = probe; // consume the inter-token whitespace
                self.pos += 1; // skip '
                if matches!(self.input.get(self.pos), Some(b's' | b'S')) {
                    self.pos += 1;
                }
                if self.pos < self.input.len()
                    && matches!(
                        self.input[self.pos],
                        b'b' | b'B' | b'o' | b'O' | b'd' | b'D' | b'h' | b'H'
                    )
                {
                    self.pos += 1;
                }
                // IEEE 1800-2017 §5.7.1: whitespace allowed between base and value
                while self.pos < self.input.len() && is_literal_space(self.input[self.pos]) {
                    self.pos += 1;
                }
                while self.pos < self.input.len()
                    && (self.input[self.pos].is_ascii_alphanumeric()
                        || self.input[self.pos] == b'_'
                        || self.input[self.pos] == b'?'
                        || self.input[self.pos] == b'x'
                        || self.input[self.pos] == b'X'
                        || self.input[self.pos] == b'z'
                        || self.input[self.pos] == b'Z')
                {
                    self.pos += 1;
                }
                let text = literal_text(&self.input[start..self.pos]);
                return Token::new(TokenKind::IntegerLiteral, text, Span::new(start, self.pos));
            }
        }
        // Check for real literal: digits.digits or digitsEexp
        if self.pos < self.input.len()
            && self.input[self.pos] == b'.'
            && self
                .input
                .get(self.pos + 1)
                .map_or(false, |c| c.is_ascii_digit())
        {
            self.pos += 1;
            while self.pos < self.input.len()
                && (self.input[self.pos].is_ascii_digit() || self.input[self.pos] == b'_')
            {
                self.pos += 1;
            }
            // Optional exponent. IEEE 1800-2017 §5.7.2: the exponent REQUIRES
            // at least one digit after `e[+-]`. Mirror the no-dot path below and
            // backtrack when it is missing, so `1.0e+`/`1.0e`/`1.0e-` do not
            // silently consume `e[+-]` into a token that later parses to 0.
            // Leaving `e...` unconsumed re-lexes it as an identifier, yielding a
            // real syntax error rather than silent garbage.
            if self.pos < self.input.len() && matches!(self.input[self.pos], b'e' | b'E') {
                let exp_start = self.pos;
                self.pos += 1;
                if self.pos < self.input.len() && matches!(self.input[self.pos], b'+' | b'-') {
                    self.pos += 1;
                }
                if self.pos < self.input.len() && self.input[self.pos].is_ascii_digit() {
                    while self.pos < self.input.len()
                        && (self.input[self.pos].is_ascii_digit() || self.input[self.pos] == b'_')
                    {
                        self.pos += 1;
                    }
                } else {
                    self.pos = exp_start; // malformed exponent: no digits after e[+-]
                }
            }
            // Time-unit suffix on a real (1800-2017 §3.14.2): treat
            // `1.250ns` as a single TimeLiteral, not Real + Ident.
            if self.pos + 1 < self.input.len() {
                let rest = &self.input[self.pos..];
                for suffix in &[b"ns" as &[u8], b"us", b"ms", b"ps", b"fs", b"s"] {
                    if rest.starts_with(suffix)
                        && !rest
                            .get(suffix.len())
                            .map_or(false, |c| c.is_ascii_alphanumeric())
                    {
                        self.pos += suffix.len();
                        let text = lossy_string(&self.input[start..self.pos]);
                        return Token::new(
                            TokenKind::TimeLiteral,
                            text,
                            Span::new(start, self.pos),
                        );
                    }
                }
            }
            let text = lossy_string(&self.input[start..self.pos]);
            return Token::new(TokenKind::RealLiteral, text, Span::new(start, self.pos));
        }
        // Exponent without decimal point
        if self.pos < self.input.len() && matches!(self.input[self.pos], b'e' | b'E') {
            let saved = self.pos;
            self.pos += 1;
            if self.pos < self.input.len() && matches!(self.input[self.pos], b'+' | b'-') {
                self.pos += 1;
            }
            if self.pos < self.input.len() && self.input[self.pos].is_ascii_digit() {
                while self.pos < self.input.len()
                    && (self.input[self.pos].is_ascii_digit() || self.input[self.pos] == b'_')
                {
                    self.pos += 1;
                }
                let text = lossy_string(&self.input[start..self.pos]);
                return Token::new(TokenKind::RealLiteral, text, Span::new(start, self.pos));
            }
            self.pos = saved;
        }
        // Time literal check
        if self.pos + 1 < self.input.len() {
            let rest = &self.input[self.pos..];
            for suffix in &[b"ns" as &[u8], b"us", b"ms", b"ps", b"fs", b"s"] {
                if rest.starts_with(suffix)
                    && !rest
                        .get(suffix.len())
                        .map_or(false, |c| c.is_ascii_alphanumeric())
                {
                    self.pos += suffix.len();
                    let text = lossy_string(&self.input[start..self.pos]);
                    return Token::new(TokenKind::TimeLiteral, text, Span::new(start, self.pos));
                }
            }
        }
        let text = lossy_string(&self.input[start..self.pos]);
        Token::new(TokenKind::IntegerLiteral, text, Span::new(start, self.pos))
    }

    fn scan_based_number(&mut self, start: usize) -> Token {
        self.pos += 1; // skip '
        let mut p = self.pos;
        if p < self.input.len() && matches!(self.input[p], b's' | b'S') {
            p += 1;
        }
        let has_base = p < self.input.len()
            && matches!(
                self.input[p],
                b'b' | b'B' | b'o' | b'O' | b'd' | b'D' | b'h' | b'H'
            );
        if !has_base {
            // No base specifier after `'` — this is a cast operator (`expr'(…)`)
            // or an assignment pattern, NOT a based literal. Emit a bare `'`
            // token WITHOUT consuming any following whitespace, so a spaced
            // cast like `(w) ' (v)` still has `text == "'"` for the parser's
            // cast handler. (Consuming the space here was tokenizing `"' "`,
            // breaking real-world RTL such as basejump's `(nodes_p) ' (0)`.)
            return Token::new(
                TokenKind::IntegerLiteral,
                "'".into(),
                Span::new(start, self.pos),
            );
        }
        self.pos = p + 1; // consume optional sign + base specifier
        // IEEE 1800-2017 §5.7.1: whitespace allowed between base and value
        while self.pos < self.input.len() && is_literal_space(self.input[self.pos]) {
            self.pos += 1;
        }
        while self.pos < self.input.len()
            && (self.input[self.pos].is_ascii_alphanumeric()
                || self.input[self.pos] == b'_'
                || self.input[self.pos] == b'?'
                || self.input[self.pos] == b'x'
                || self.input[self.pos] == b'X'
                || self.input[self.pos] == b'z'
                || self.input[self.pos] == b'Z')
        {
            self.pos += 1;
        }
        let text = literal_text(&self.input[start..self.pos]);
        Token::new(TokenKind::IntegerLiteral, text, Span::new(start, self.pos))
    }
}

/// §5.3: the white space that may separate the size, the base and the value
/// of a based literal (§5.7.1): blanks, tabs, newlines and form feeds.
fn is_literal_space(c: u8) -> bool {
    matches!(c, b' ' | b'\t' | b'\n' | b'\r' | b'\x0c')
}

/// A based literal's text without the white space between its tokens, so
/// `2 'd 1` reads as `2'd1`: the size was parsed from `"2 "` and lost.
fn literal_text(bytes: &[u8]) -> String {
    if bytes.iter().any(|&c| is_literal_space(c)) {
        let kept: Vec<u8> = bytes
            .iter()
            .copied()
            .filter(|&c| !is_literal_space(c))
            .collect();
        lossy_string(&kept)
    } else {
        lossy_string(bytes)
    }
}

/// §22.14: the library-map/configuration keywords, reserved from 1364-2001
/// on but not in the 1364-1995 or "1364-2001-noconfig" sets.
fn is_config_keyword(s: &str) -> bool {
    matches!(
        s,
        "cell"
            | "config"
            | "design"
            | "endconfig"
            | "incdir"
            | "include"
            | "instance"
            | "liblist"
            | "library"
            | "use"
    )
}

/// §22.14, Table 22-2: a keyword 1800-2009 added over 1800-2005.
fn is_1800_2009_keyword(s: &str) -> bool {
    matches!(
        s,
        "accept_on"
            | "checker"
            | "endchecker"
            | "eventually"
            | "global"
            | "implies"
            | "let"
            | "nexttime"
            | "reject_on"
            | "restrict"
            | "s_always"
            | "s_eventually"
            | "s_nexttime"
            | "s_until"
            | "s_until_with"
            | "strong"
            | "sync_accept_on"
            | "sync_reject_on"
            | "unique0"
            | "until"
            | "until_with"
            | "untyped"
            | "weak"
    )
}

/// §22.14, Table 22-2: a keyword 1800-2012 added over 1800-2009.
fn is_1800_2012_keyword(s: &str) -> bool {
    matches!(s, "implements" | "interconnect" | "nettype" | "soft")
}

/// §22.14 Table 22-2: a keyword 1364-2001 added over 1364-1995, other than
/// the configuration keywords.
fn is_1364_2001_keyword(s: &str) -> bool {
    matches!(
        s,
        "automatic"
            | "endgenerate"
            | "generate"
            | "genvar"
            | "localparam"
            | "noshowcancelled"
            | "pulsestyle_ondetect"
            | "pulsestyle_onevent"
            | "showcancelled"
            | "signed"
            | "unsigned"
    )
}

/// IEEE 1800-2023 §B.1 vs §22.14: a keyword that SystemVerilog adds over
/// Verilog-1364 (2001). Inside a `begin_keywords "1364-*"` region these are not
/// reserved and lex as ordinary identifiers. Verilog-2001 keywords (`reg`,
/// `wire`, `module`, `begin`, `if`, …) are deliberately excluded so they stay
/// reserved. The set is generous — it only ever applies inside a (rare) legacy
/// keyword region, so over-inclusion is harmless while under-inclusion would
/// leave a legacy identifier wrongly reserved.
fn is_sv_only_keyword(s: &str) -> bool {
    matches!(
        s,
        // data types
        "logic" | "bit" | "byte" | "shortint" | "int" | "longint"
        | "shortreal" | "void" | "chandle" | "string" | "var" | "type"
        | "enum" | "struct" | "union" | "packed" | "tagged" | "const"
        // classes / OOP
        | "class" | "endclass" | "extends" | "implements" | "super" | "this"
        | "virtual" | "pure" | "local" | "protected" | "rand" | "randc"
        | "constraint" | "solve" | "before" | "null" | "new" | "extern"
        | "forkjoin" | "interface" | "endinterface" | "modport"
        // procedural / control additions
        | "always_comb" | "always_ff" | "always_latch" | "final" | "do"
        | "return" | "break" | "continue" | "unique" | "unique0" | "priority"
        | "iff" | "inside" | "dist" | "with" | "throughout" | "within"
        | "first_match" | "matches" | "ref" | "context" | "import" | "export"
        // assertions / coverage
        | "assert" | "assume" | "cover" | "property" | "endproperty"
        | "sequence" | "endsequence" | "expect" | "covergroup" | "endgroup"
        | "coverpoint" | "cross" | "bins" | "binsof" | "intersect" | "wildcard"
        | "ignore_bins" | "illegal_bins"
        // clocking / programs / packages
        | "clocking" | "endclocking" | "program" | "endprogram" | "package"
        | "endpackage" | "timeunit" | "timeprecision"
    )
}
