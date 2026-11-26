//! Parse generated module items without retaining the complete token stream.
//!
//! The lowerer emits independent declarations, subroutines and procedural
//! blocks (§A.1.4). Parse complete groups through the ordinary parser, then
//! join their items in source order. Constructs needing cross-item parser
//! scope, such as lets and generate blocks, use the ordinary whole parser.

use super::{GENERATED_SPAN_BASE, parse_generated_tokens};
use crate::ast::{Description, Span, module::PortList};
use crate::sv_parser::lexer::{Lexer, TokenKind as K, TokenStream};

type ScannedToken = (K, Span);

struct Stream<'a> {
    lexer: Lexer<'a>,
    next: ScannedToken,
}

impl<'a> Stream<'a> {
    fn new(text: &'a str) -> Self {
        let mut lexer = Lexer::new(text);
        let next = lexer.next_token();
        Self { lexer, next }
    }

    fn take(&mut self) -> ScannedToken {
        let next = self.lexer.next_token();
        std::mem::replace(&mut self.next, next)
    }

    /// A header or simple item ends at a semicolon outside delimiters.
    fn simple(&mut self, out: &mut Vec<ScannedToken>) -> Option<()> {
        let mut depth = 0usize;
        loop {
            let kind = self.next.0;
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

    fn item(&mut self, out: &mut Vec<ScannedToken>) -> Option<()> {
        match self.next.0 {
            K::KwFunction | K::KwTask => {
                let end = if self.next.0 == K::KwFunction {
                    K::KwEndfunction
                } else {
                    K::KwEndtask
                };
                loop {
                    let kind = self.next.0;
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
                    let kind = self.next.0;
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
                        && self.next.0 != K::KwElse
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
    while stream.next.0 != K::Eof {
        if stream.next.0 != K::KwModule {
            return None;
        }
        let mut header = Vec::new();
        stream.simple(&mut header)?;
        // The emitted modules have ANSI or empty ports and baked generics.
        if header
            .iter()
            .any(|t| matches!(t.0, K::KwImport | K::Hash))
        {
            return None;
        }
        let mut assembled = None;
        let mut item_batches = Vec::new();
        let mut capacity_before = 0;
        loop {
            let mut tokens = header.clone();
            while stream.next.0 != K::KwEndmodule
                && (tokens.len() == header.len() || tokens.len() < batch_target)
            {
                stream.item(&mut tokens)?;
            }
            let end = stream.next.1;
            tokens.push((K::KwEndmodule, end));
            tokens.push((K::Eof, Span::new(end.start, end.start)));
            max_batch_tokens = max_batch_tokens.max(tokens.len());
            let mut descriptions = parse_generated_tokens(TokenStream::from_spans(text, tokens), text).ok()?;
            let Description::Module(mut module) = descriptions.pop()? else {
                return None;
            };
            if !descriptions.is_empty() || matches!(module.ports, PortList::NonAnsi(_)) {
                return None;
            }
            // Keep each parser batch in its own buffer until the total item
            // count is known. Growing a single Vec here copies the preceding
            // batches and can reserve millions of unused ModuleItem slots.
            // Parsing is finished for this batch. Release its spare slots now,
            // while later batches and their token buffers are still unallocated.
            capacity_before += module.items.capacity();
            item_batches.push(std::mem::take(&mut module.items).into_boxed_slice());
            if assembled.is_none() {
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
            if stream.next.0 == K::KwEndmodule {
                let end = stream.take();
                let mut module = assembled?;
                module.span = Span::new(
                    GENERATED_SPAN_BASE + header[0].1.start,
                    GENERATED_SPAN_BASE + end.1.end,
                );
                module.items = if item_batches.len() == 1 {
                    item_batches.pop()?.into_vec()
                } else {
                    let len = item_batches.iter().map(|batch| batch.len()).sum();
                    let mut items = Vec::with_capacity(len);
                    for batch in item_batches {
                        items.extend(batch.into_vec());
                    }
                    items
                };
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
                if stream.next.0 == K::Colon {
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
    fn short_lists_in_generated_helpers_have_no_spare_slots() {
        use crate::ast::{decl::ModuleItem, expr::ExprKind, stmt::StatementKind, types::DataType};

        let text =
            "module m; function int f(input logic [7:0] a[2]); return g(a); endfunction endmodule";
        let descriptions = parse(text, 1).unwrap();
        let Description::Module(module) = &descriptions[0] else {
            panic!()
        };
        let ModuleItem::FunctionDeclaration(f) = &module.items[0] else {
            panic!()
        };
        let port = &f.ports[0];
        let DataType::IntegerVector { dimensions, .. } = &port.data_type else {
            panic!()
        };
        let StatementKind::Return(Some(expr)) = &f.items[0].kind else {
            panic!()
        };
        let ExprKind::Call { args, .. } = &expr.kind else {
            panic!()
        };
        for capacity in [
            f.ports.capacity(),
            dimensions.capacity(),
            port.dimensions.capacity(),
            args.capacity(),
        ] {
            assert_eq!(capacity, 1);
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
