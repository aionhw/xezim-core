//! Regression tests for compact 8-byte source-backed tokens and segmented `TokenStream` (aionhw/xezim-core#190).

use std::fmt::Write;
use sv_parser::ast::Description;
use sv_parser::ast::decl::{ModuleItem, PackageItem};
use sv_parser::ast::expr::ExprKind;
use sv_parser::lexer::{Lexer, Token, TokenKind, TokenStream};
use sv_parser::parse;

/// `Token` stays 8 bytes and `TokenKind` stays 2 bytes so large files avoid
/// per-token `String` heap allocations and oversized token buffers.
#[test]
fn compact_token_layout_sizes() {
    assert_eq!(std::mem::size_of::<Token>(), 8);
    assert_eq!(std::mem::size_of::<TokenKind>(), 2);
}

/// Multi-chunk streams trim their final chunk to exact length and iterate
/// seamlessly across 4,096-token chunk boundaries.
#[test]
fn multi_chunk_stream_exact_capacity_and_iteration() {
    let mut src = String::from("package p;\n");
    for i in 0..2500 {
        writeln!(src, "localparam int c{i} = {i};").unwrap();
    }
    src.push_str("endpackage\n");

    let tokens = Lexer::new(&src).tokenize();
    assert!(
        tokens.len() > TokenStream::CHUNK_LEN * 2,
        "expected >2 chunks, got {} tokens",
        tokens.len()
    );
    assert_eq!(tokens.capacity(), tokens.len());

    let collected: Vec<Token> = tokens.iter().collect();
    assert_eq!(collected.len(), tokens.len());
    for (idx, tok) in collected.iter().enumerate() {
        assert_eq!(Some(*tok), tokens.get(idx));
        assert_eq!(*tok, tokens[idx]);
        let sp = tokens.span(*tok);
        assert_eq!(sp, tokens.span_at(idx));
        assert_eq!(tokens.text(*tok), tokens.text_at(idx));
    }

    let boundary = TokenStream::CHUNK_LEN - 2;
    let tail: Vec<Token> = tokens.iter_from(boundary).collect();
    assert_eq!(tail.len(), tokens.len() - boundary);
    assert_eq!(tail[0], collected[boundary]);
    assert_eq!(tail[2], collected[TokenStream::CHUNK_LEN]);
    assert_eq!(tail.last().copied(), collected.last().copied());
    assert_eq!(tokens.iter_from(tokens.len()).count(), 0);
}

/// Escaped identifiers, whitespace-split based literals, and spaced casts
/// produce identical token text and spans under `TokenStream`.
#[test]
fn escaped_identifiers_based_literals_and_spaced_casts() {
    let src = "\\my-id \\a.b 2 'd 1 12 'sh 3 {2\n  'd1} (w) ' (v)";
    let tokens = Lexer::new(src).tokenize();
    let pairs: Vec<(TokenKind, String, (u32, u32))> = tokens
        .iter()
        .filter(|t| t.kind != TokenKind::Eof)
        .map(|t| {
            let sp = tokens.span(t);
            (t.kind, tokens.text(t).into_owned(), (sp.start, sp.end))
        })
        .collect();

    assert_eq!(pairs[0].0, TokenKind::EscapedIdentifier);
    assert_eq!(pairs[0].1, "\\my-id");
    assert_eq!(pairs[1].0, TokenKind::EscapedIdentifier);
    assert_eq!(pairs[1].1, "\\a.b");

    let ints: Vec<&str> = pairs
        .iter()
        .filter(|(k, _, _)| *k == TokenKind::IntegerLiteral)
        .map(|(_, text, _)| text.as_str())
        .collect();
    assert_eq!(ints, ["2'd1", "12'sh3", "2'd1", "'"]);
}

/// `` `begin_keywords `` normalizes its token text while retaining the full
/// version-string span, and custom directives keep their full spelling.
#[test]
fn begin_keywords_directive_text_and_span() {
    let src = "`begin_keywords \"1364-2001\"\nreg logic;\n`end_keywords\n`begin_keywords_custom\n";
    let tokens = Lexer::new(src).tokenize();

    let dir = tokens[0];
    assert_eq!(dir.kind, TokenKind::Directive);
    assert_eq!(tokens.text(dir), "`begin_keywords");
    let dir_sp = tokens.span(dir);
    assert_eq!(
        &src[dir_sp.start as usize..dir_sp.end as usize],
        "`begin_keywords \"1364-2001\""
    );

    assert_eq!(tokens[1].kind, TokenKind::KwReg);
    assert_eq!(tokens[2].kind, TokenKind::Identifier);
    assert_eq!(tokens[2].kind, TokenKind::Identifier);
    assert_eq!(tokens.text(tokens[2]), "logic");
    assert_eq!(tokens[4].kind, TokenKind::Directive);
    assert_eq!(tokens.text(tokens[4]), "`end_keywords");
    assert_eq!(tokens[5].kind, TokenKind::Directive);
    assert_eq!(tokens.text(tokens[5]), "`begin_keywords_custom");
}

/// Joining `#1step` and `#(1step)` succeeds even when `1` and `step` straddle
/// a 4,096-token chunk boundary.
#[test]
fn one_step_joined_across_chunk_boundary() {
    // Prefix tokens before `# 1 step`: find exact filler count so `1` lands at
    // index `CHUNK_LEN - 1` and `step` lands at `CHUNK_LEN`.
    let mut prefix = String::from("module m; logic a, b; initial begin\n");
    let pre_tokens = Lexer::new(&prefix).tokenize().len() - 1; // exclude Eof
    // Each `a = 0;` is 4 tokens. Leave room for `#` (1 token) before `1`.
    let target_before_one = TokenStream::CHUNK_LEN - 1;
    let needed = target_before_one - pre_tokens - 1;
    assert_eq!(needed % 4, 0, "unexpected prefix token count {pre_tokens}");
    for _ in 0..(needed / 4) {
        prefix.push_str("a = 0;\n");
    }
    prefix.push_str("#1step a = # ( 1step ) b;\nend endmodule\n");

    let raw = Lexer::new(&prefix).tokenize();
    assert_eq!(raw.text_at(TokenStream::CHUNK_LEN - 1), "1");
    assert_eq!(raw.text_at(TokenStream::CHUNK_LEN), "step");

    let parsed = parse(&prefix);
    assert!(parsed.errors.is_empty(), "{:?}", parsed.errors);
    let tree = format!("{:?}", parsed.source);
    assert!(tree.contains("1step"), "expected 1step delay in AST: {tree}");
}

/// Non-ASCII bytes in `Unknown` tokens and unclosed strings ending in `\`
/// never panic during lexing, text materialization, or parsing.
#[test]
fn non_ascii_unknown_and_trailing_backslash_unclosed_string() {
    let non_ascii = "module m; \u{00e9} endmodule";
    let tokens = Lexer::new(non_ascii).tokenize();
    assert!(tokens.iter().any(|t| t.kind == TokenKind::Unknown));
    for tok in &tokens {
        let _ = tokens.span(tok);
        let _ = tokens.text(tok);
    }

    let trailing_bs = "module m; string s = \"abc\\";
    let tokens2 = Lexer::new(trailing_bs).tokenize();
    let str_tok = tokens2
        .iter()
        .find(|t| t.kind == TokenKind::StringLiteral)
        .expect("string literal");
    assert_eq!(tokens2.span(str_tok).end as usize, trailing_bs.len());
    assert_eq!(tokens2.text(str_tok), "\"abc\\");
}

/// Tokens >= 65,535 bytes spill into the stream's overflow table and preserve
/// exact span, text, and AST payload.
#[test]
fn long_token_overflow_table() {
    let payload = "a".repeat(70_000);
    let src = format!("module m; string s = \"{payload}\"; endmodule\n");
    let tokens = Lexer::new(&src).tokenize();
    let str_tok = tokens
        .iter()
        .find(|t| t.kind == TokenKind::StringLiteral)
        .expect("long string token");
    let sp = tokens.span(str_tok);
    assert_eq!(sp.end - sp.start, 70_002);
    assert_eq!(tokens.text(str_tok).len(), 70_002);

    let parsed = parse(&src);
    assert!(parsed.errors.is_empty(), "{:?}", parsed.errors);
    let Description::Module(m) = &parsed.source.descriptions[0] else {
        panic!("expected module");
    };
    let ModuleItem::DataDeclaration(dd) = &m.items[0] else {
        panic!("expected data decl");
    };
    let init = dd.declarators[0].init.as_ref().expect("init expr");
    let ExprKind::StringLiteral(decoded) = &init.kind else {
        panic!("expected string literal");
    };
    assert_eq!(decoded.len(), 70_000);
    assert!(decoded.bytes().all(|b| b == b'a'));
}

/// Multi-chunk parsing with progressive chunk release handles large packages,
/// modules, UDPs, timing checks, and virtual-interface specializations.
#[test]
fn multi_chunk_parsing_with_chunk_release() {
    let mut src = String::from("interface bus_if; endinterface\nclass C #(type T = int); endclass\n");
    src.push_str("package big_pkg;\n");
    for i in 0..2200 {
        writeln!(src, "localparam int p{i} = {i};").unwrap();
    }
    src.push_str("endpackage\n");

    src.push_str("primitive my_and (z, a, b); output z; input a, b; table 00:0; 11:1; endtable endprimitive\n");
    src.push_str("module big_mod(input clk, input data, input en);\n");
    src.push_str("C #(virtual bus_if) c_inst;\n");
    for i in 0..2200 {
        writeln!(src, "wire w{i} = 1'b0;").unwrap();
    }
    src.push_str("specify\n  $setup(posedge clk &&& en, data, 1:2:3);\nendspecify\nendmodule\n");

    let parsed = parse(&src);
    assert!(parsed.errors.is_empty(), "{:?}", parsed.errors);
    assert_eq!(parsed.source.descriptions.len(), 5);

    let Description::Package(pkg) = &parsed.source.descriptions[2] else {
        panic!("expected package");
    };
    assert_eq!(pkg.items.len(), 2200);
    assert!(matches!(pkg.items[2199], PackageItem::Parameter(_)));

    let Description::Udp(udp) = &parsed.source.descriptions[3] else {
        panic!("expected udp");
    };
    assert_eq!(udp.rows.len(), 2);

    let Description::Module(m) = &parsed.source.descriptions[4] else {
        panic!("expected module");
    };
    assert!(m.items.iter().any(|it| matches!(it, ModuleItem::SpecifyBlock(sb) if sb.timing_checks.len() == 1)));
}
