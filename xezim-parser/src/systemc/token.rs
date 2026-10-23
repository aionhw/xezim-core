//! Tokens of the SystemC (C++ subset) front end.
//!
//! Unlike the SystemVerilog lexer, punctuators and keywords keep their
//! spelling in `text` instead of one enum variant each: the C++ grammar the
//! parser accepts is matched by spelling (`p.is_punct("::")`), and the
//! preprocessor needs the exact spelling anyway to stringize and paste.

/// A byte range in one of the files of an [`super::ScParseResult`].
/// `file` indexes [`super::ScParseResult::files`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ScSpan {
    pub file: u32,
    pub start: u32,
    pub end: u32,
}

impl ScSpan {
    pub fn new(file: u32, start: usize, end: usize) -> Self {
        Self {
            file,
            start: start as u32,
            end: end as u32,
        }
    }

    /// The smallest span covering `self` and `other` when both lie in the
    /// same file; `self` otherwise (a construct split across files by an
    /// `#include` keeps its start location).
    pub fn to(self, other: ScSpan) -> ScSpan {
        if self.file != other.file {
            return self;
        }
        ScSpan {
            file: self.file,
            start: self.start.min(other.start),
            end: self.end.max(other.end),
        }
    }

    /// This span as the SystemVerilog-side [`crate::ast::Span`] (file id
    /// dropped), for the shared diagnostic renderer.
    pub fn bytes(self) -> crate::ast::Span {
        crate::ast::Span::new(self.start as usize, self.end as usize)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ScTokenKind {
    Ident,
    Keyword,
    IntLit,
    FloatLit,
    CharLit,
    StringLit,
    /// Operators and punctuation, including `#` and `##`.
    Punct,
    Eof,
}

#[derive(Debug, Clone)]
pub struct ScToken {
    pub kind: ScTokenKind,
    pub text: String,
    pub span: ScSpan,
    /// First token on its (logical) line — where a `#` starts a directive.
    pub line_start: bool,
    /// Whitespace or a comment precedes the token. Tells `#define F(x)`
    /// (function-like) from `#define F (x)` (object-like).
    pub space_before: bool,
}

impl ScToken {
    pub fn is_punct(&self, p: &str) -> bool {
        self.kind == ScTokenKind::Punct && self.text == p
    }

    pub fn is_keyword(&self, k: &str) -> bool {
        self.kind == ScTokenKind::Keyword && self.text == k
    }

    pub fn is_ident(&self, name: &str) -> bool {
        self.kind == ScTokenKind::Ident && self.text == name
    }
}

/// C++17 keywords (ISO/IEC 14882:2017 §5.11) plus the C++20 ones a
/// SystemC 3.0 design may spell. Alternative operator spellings (`and`,
/// `or`, …) are lexed as their operators instead (§5.5).
pub const KEYWORDS: &[&str] = &[
    "alignas",
    "alignof",
    "asm",
    "auto",
    "bool",
    "break",
    "case",
    "catch",
    "char",
    "char16_t",
    "char32_t",
    "char8_t",
    "class",
    "co_await",
    "co_return",
    "co_yield",
    "concept",
    "const",
    "const_cast",
    "consteval",
    "constexpr",
    "constinit",
    "continue",
    "decltype",
    "default",
    "delete",
    "do",
    "double",
    "dynamic_cast",
    "else",
    "enum",
    "explicit",
    "export",
    "extern",
    "false",
    "float",
    "for",
    "friend",
    "goto",
    "if",
    "inline",
    "int",
    "long",
    "mutable",
    "namespace",
    "new",
    "noexcept",
    "nullptr",
    "operator",
    "private",
    "protected",
    "public",
    "register",
    "reinterpret_cast",
    "requires",
    "return",
    "short",
    "signed",
    "sizeof",
    "static",
    "static_assert",
    "static_cast",
    "struct",
    "switch",
    "template",
    "this",
    "thread_local",
    "throw",
    "true",
    "try",
    "typedef",
    "typeid",
    "typename",
    "union",
    "unsigned",
    "using",
    "virtual",
    "void",
    "volatile",
    "wchar_t",
    "while",
];

pub fn is_keyword(s: &str) -> bool {
    KEYWORDS.binary_search(&s).is_ok()
}

/// The operator an alternative token spells (§5.5), if `s` is one.
pub fn alternative_token(s: &str) -> Option<&'static str> {
    Some(match s {
        "and" => "&&",
        "and_eq" => "&=",
        "bitand" => "&",
        "bitor" => "|",
        "compl" => "~",
        "not" => "!",
        "not_eq" => "!=",
        "or" => "||",
        "or_eq" => "|=",
        "xor" => "^",
        "xor_eq" => "^=",
        _ => return None,
    })
}

#[cfg(test)]
mod tests {
    #[test]
    fn keyword_table_is_sorted() {
        let mut sorted = super::KEYWORDS.to_vec();
        sorted.sort_unstable();
        assert_eq!(sorted, super::KEYWORDS);
    }
}
