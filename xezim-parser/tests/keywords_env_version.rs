//! §22.14: `XEZIM_KEYWORDS` chooses the default keyword set, and a later
//! `set_no_config_keywords` keeps that version (#608). The environment is
//! read once per process, so this file holds a single test.

use sv_parser::lexer::scanner::set_no_config_keywords;
use sv_parser::lexer::{Lexer, TokenKind};

fn kind(word: &str) -> TokenKind {
    Lexer::new(word).tokenize()[0].kind
}

#[test]
fn no_config_setter_keeps_the_env_version() {
    // SAFETY: the only test in this process; nothing reads the
    // environment concurrently.
    unsafe { std::env::set_var("XEZIM_KEYWORDS", "1364-2001") };
    assert_eq!(kind("logic"), TokenKind::Identifier);
    assert_ne!(kind("cell"), TokenKind::Identifier);
    set_no_config_keywords(true);
    assert_eq!(kind("cell"), TokenKind::Identifier);
    assert_eq!(kind("logic"), TokenKind::Identifier, "still 1364-2001");
}
