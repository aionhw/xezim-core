//! §22.14: `XEZIM_NO_CONFIG_KEYWORDS=1` leaves the configuration keywords
//! out of the default set, and a later `set_default_keywords` keeps that
//! (#608). The environment is read once per process, so this file holds a
//! single test.

use sv_parser::lexer::scanner::set_default_keywords;
use sv_parser::lexer::{Lexer, TokenKind};

fn kind(word: &str) -> TokenKind {
    Lexer::new(word).tokenize()[0].kind
}

#[test]
fn version_setter_keeps_the_env_no_config() {
    // SAFETY: the only test in this process; nothing reads the
    // environment concurrently.
    unsafe { std::env::set_var("XEZIM_NO_CONFIG_KEYWORDS", "1") };
    assert_eq!(kind("cell"), TokenKind::Identifier);
    set_default_keywords("1800-2009").unwrap();
    assert_eq!(kind("cell"), TokenKind::Identifier, "still -noconfig");
    assert_eq!(kind("nettype"), TokenKind::Identifier);
    assert_ne!(kind("until"), TokenKind::Identifier);
}
