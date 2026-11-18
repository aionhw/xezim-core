//! Parse generated module items without retaining the complete token stream.
//!
//! The lowerer emits independent declarations, subroutines and procedural
//! blocks (§A.1.4). Parse complete groups through the ordinary parser, then
//! join their items in source order. Constructs needing cross-item parser
//! scope, such as lets and generate blocks, use the ordinary whole parser.

use super::{GENERATED_SPAN_BASE, parse_generated_tokens};
use crate::ast::{Description, Span, module::PortList};
use crate::sv_parser::lexer::{Lexer, Token, TokenKind as K};

struct Stream<'a> {
    lexer: Lexer<'a>,
    next: Token,
}

impl<'a> Stream<'a> {
    fn new(text: &'a str) -> Self {
        let mut lexer = Lexer::new(text);
        let next = Self::offset(lexer.next_token());
        Self { lexer, next }
    }

    fn offset(mut token: Token) -> Token {
        token.span.start += GENERATED_SPAN_BASE;
        token.span.end += GENERATED_SPAN_BASE;
        token
    }

    fn take(&mut self) -> Token {
        let next = Self::offset(self.lexer.next_token());
        std::mem::replace(&mut self.next, next)
    }

    /// A header or simple item ends at a semicolon outside delimiters.
    fn simple(&mut self, out: &mut Vec<Token>) -> Option<()> {
        let mut depth = 0usize;
        loop {
            let kind = self.next.kind;
            if matches!(kind, K::Eof | K::KwEndmodule) {
                return None;
            }
            match kind {
                K::LParen | K::LBracket | K::LBrace | K::ApostropheLBrace => depth += 1,
                K::RParen | K::RBracket | K::RBrace => depth = depth.checked_sub(1)?,
                _ => {}
            }
            out.push(self.take());
            if kind == K::Semicolon && depth == 0 {
                return Some(());
            }
        }
    }

    fn item(&mut self, out: &mut Vec<Token>) -> Option<()> {
        match self.next.kind {
            K::KwFunction | K::KwTask => {
                let end = if self.next.kind == K::KwFunction {
                    K::KwEndfunction
                } else {
                    K::KwEndtask
                };
                loop {
                    let kind = self.next.kind;
                    if matches!(kind, K::Eof | K::KwEndmodule) {
                        return None;
                    }
                    out.push(self.take());
                    if kind == end {
                        return Some(());
                    }
                }
            }
            K::KwInitial | K::KwAlways | K::KwAlways_comb | K::KwAlways_ff => {
                let mut delimiters = 0usize;
                let mut blocks = Vec::new();
                loop {
                    let kind = self.next.kind;
                    if matches!(kind, K::Eof | K::KwEndmodule) {
                        return None;
                    }
                    match kind {
                        K::LParen | K::LBracket | K::LBrace | K::ApostropheLBrace => {
                            delimiters += 1
                        }
                        K::RParen | K::RBracket | K::RBrace => {
                            delimiters = delimiters.checked_sub(1)?
                        }
                        K::KwBegin => blocks.push(K::KwEnd),
                        K::KwCase | K::KwCasez | K::KwCasex => blocks.push(K::KwEndcase),
                        K::KwFork => return None,
                        K::KwEnd | K::KwEndcase => {
                            if blocks.pop()? != kind {
                                return None;
                            }
                        }
                        _ => {}
                    }
                    out.push(self.take());
                    if delimiters == 0
                        && blocks.is_empty()
                        && matches!(kind, K::Semicolon | K::KwEnd | K::KwEndcase)
                        && self.next.kind != K::KwElse
                    {
                        return Some(());
                    }
                }
            }
            K::KwTypedef
            | K::KwLocalparam
            | K::KwParameter
            | K::KwAssign
            | K::KwBit
            | K::KwLogic
            | K::KwReg
            | K::KwWire
            | K::KwTri
            | K::KwByte
            | K::KwInt
            | K::KwInteger
            | K::KwLongint
            | K::KwReal
            | K::KwShortreal
            | K::KwString
            | K::KwTime
            | K::KwTimeunit
            | K::KwTimeprecision
            | K::Identifier
            | K::EscapedIdentifier => self.simple(out),
            // No guess at a construct with persistent parser scope.
            _ => None,
        }
    }
}

/// `None` means use the whole parser; never approximate an unknown item.
pub(super) fn parse(text: &str, batch_target: usize) -> Option<Vec<Description>> {
    let mut stream = Stream::new(text);
    let mut result = Vec::new();
    let mut batches = 0usize;
    let mut max_batch_tokens = 0usize;
    while stream.next.kind != K::Eof {
        if stream.next.kind != K::KwModule {
            return None;
        }
        let mut header = Vec::new();
        stream.simple(&mut header)?;
        // The emitted modules have ANSI or empty ports and baked generics.
        if header
            .iter()
            .any(|t| matches!(t.kind, K::KwImport | K::Hash))
        {
            return None;
        }
        let mut assembled = None;
        loop {
            let mut tokens = header.clone();
            while stream.next.kind != K::KwEndmodule
                && (tokens.len() == header.len() || tokens.len() < batch_target)
            {
                stream.item(&mut tokens)?;
            }
            let end = stream.next.span;
            tokens.push(Token::new(K::KwEndmodule, "endmodule".into(), end));
            tokens.push(Token::new(K::Eof, String::new(), end));
            max_batch_tokens = max_batch_tokens.max(tokens.len());
            let mut descriptions = parse_generated_tokens(tokens, text).ok()?;
            let Description::Module(mut module) = descriptions.pop()? else {
                return None;
            };
            if !descriptions.is_empty() || matches!(module.ports, PortList::NonAnsi(_)) {
                return None;
            }
            if let Some(previous) = &mut assembled {
                let previous: &mut crate::ast::module::ModuleDeclaration = previous;
                previous.items.append(&mut module.items);
            } else {
                assembled = Some(module);
            }
            batches += 1;
            if batches == 1 || batches % 64 == 0 {
                crate::oom_trace::checkpoint(
                    "vhdl.generated_batches",
                    &[
                        ("generated_sv_bytes", text.len()),
                        ("parsed_batches", batches),
                        ("max_batch_tokens", max_batch_tokens),
                    ],
                );
            }
            if stream.next.kind == K::KwEndmodule {
                let end = stream.take();
                let mut module = assembled?;
                module.span = Span::new(header[0].span.start, end.span.end);
                let capacity_before = module.items.capacity();
                if capacity_before > module.items.len() {
                    // Drop the large batch-growth allocation before building
                    // elaboration tables. Move values without cloning their
                    // contextual caches; the completed AST is not yet indexed.
                    let mut compact = Vec::with_capacity(module.items.len());
                    compact.append(&mut module.items);
                    module.items = compact;
                }
                crate::oom_trace::checkpoint(
                    "vhdl.generated_item_capacity",
                    &[
                        ("items", module.items.len()),
                        ("capacity_before", capacity_before),
                        ("capacity_after", module.items.capacity()),
                        (
                            "item_bytes",
                            std::mem::size_of::<crate::ast::decl::ModuleItem>(),
                        ),
                    ],
                );
                result.push(Description::Module(module));
                // End labels are not emitted; leave them to the whole parser.
                if stream.next.kind == K::Colon {
                    return None;
                }
                break;
            }
        }
    }
    crate::oom_trace::checkpoint(
        "vhdl.generated_batches",
        &[
            ("generated_sv_bytes", text.len()),
            ("parsed_batches", batches),
            ("max_batch_tokens", max_batch_tokens),
        ],
    );
    Some(result)
}
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn item_batches_preserve_syntax_and_spans() {
        let text = r#"module one(input wire logic clk, output logic [7:0] q);
          timeunit 1fs; timeprecision 1fs;
          typedef struct { int n; byte d[]; } row;
          row a;
          function automatic int f(input int x);
            case (x) 0: return 1; default: return x + 2; endcase
          endfunction
          always @(clk) begin if (clk) q = f(3); else q = 0; end
          initial begin : start
            for (int i=0; i<3; i++) begin q = i; #1; end
          end
          assign q = clk ? 8'h3b : 0;
        endmodule
        module two; string s = "endfunction; endmodule"; endmodule"#;
        let whole = super::super::parse_generated_whole(text).unwrap();
        for target in [1, 8, 64, 65_536] {
            let batched = parse(text, target).unwrap();
            assert_eq!(format!("{whole:?}"), format!("{batched:?}"));
        }
    }

    #[test]
    fn persistent_scope_constructs_keep_the_whole_parser() {
        assert!(parse("module m; let f(x)=x+1; int q=f(2); endmodule", 8).is_none());
        assert!(parse("module m(a); input a; endmodule", 8).is_none());
        assert!(parse("module m; initial fork begin end join endmodule", 8).is_none());
        assert!(parse("module m; int q endmodule", 8).is_none());
    }

    #[test]
    fn lowered_runtime_and_record_design_have_identical_ast() {
        let source = br#"
library ieee; use ieee.std_logic_1164.all;
entity t is end;
architecture a of t is
  type row is record value : std_logic_vector(7 downto 0); count : integer; end record;
  type rows is array (0 to 1) of row;
  signal r : rows;
begin
  process begin
    r(0).value <= x"a5";
    r(0).count <= 7 after 1 ns;
    wait for 2 ns;
    report "item; endfunction";
    std.env.finish;
  end process;
end;
"#;
        let text = super::super::lower_design(&[("work", "records.vhd", source)]).unwrap();
        let whole = super::super::parse_generated_whole(&text).unwrap();
        let batched = parse(&text, 64).expect("generated items must use bounded token groups");
        assert_eq!(format!("{whole:?}"), format!("{batched:?}"));
    }
}
