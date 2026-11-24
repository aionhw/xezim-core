//! Segmented, source-backed token storage.
//!
//! Tokens are stored in fixed-size 4,096-element chunks (32 KiB per chunk at
//! 8 bytes per [`Token`]), avoiding both per-token `String` heap allocations
//! and whole-stream doubling reallocations.

use std::borrow::Cow;
use std::iter::FusedIterator;
use std::ops::Index;

use super::scanner::is_literal_space;
use super::token::{OwnedToken, Token, TokenKind};
use crate::ast::Span;

const CHUNK_SHIFT: usize = 12;
const CHUNK_SIZE: usize = 1 << CHUNK_SHIFT;
const CHUNK_MASK: usize = CHUNK_SIZE - 1;

/// Chunked sequence of compact source-backed [`Token`] values.
#[derive(Debug, Clone)]
pub struct TokenStream<'a> {
    source: &'a str,
    chunks: Vec<Vec<Token>>,
    len: usize,
    released_chunks: usize,
    /// Overflow `(start, end)` byte offsets for rare tokens with byte length
    /// `>= Token::LONG_LEN`, kept in strictly increasing `start` order.
    long_ends: Vec<(u32, u32)>,
}

impl<'a> TokenStream<'a> {
    /// Chunk width in tokens, exported for tests that probe chunk boundaries.
    pub const CHUNK_LEN: usize = CHUNK_SIZE;

    pub(crate) fn new(source: &'a str) -> Self {
        Self {
            source,
            chunks: Vec::new(),
            len: 0,
            released_chunks: 0,
            long_ends: Vec::new(),
        }
    }

    pub(crate) fn with_long_ends(source: &'a str, long_ends: Vec<(u32, u32)>) -> Self {
        Self {
            source,
            chunks: Vec::new(),
            len: 0,
            released_chunks: 0,
            long_ends,
        }
    }

    pub(crate) fn push_token(&mut self, kind: TokenKind, start: usize, end: usize) {
        let byte_len = end.saturating_sub(start);
        let len_u16 = if byte_len < Token::LONG_LEN as usize {
            byte_len as u16
        } else {
            self.long_ends.push((start as u32, end as u32));
            Token::LONG_LEN
        };
        self.push_raw(Token::from_raw(kind, start as u32, len_u16));
    }

    pub(crate) fn push_raw(&mut self, tok: Token) {
        if (self.len & CHUNK_MASK) == 0 {
            let cap = if self.chunks.is_empty() {
                (self.source.len() / 6 + 4).clamp(4, CHUNK_SIZE)
            } else {
                CHUNK_SIZE
            };
            self.chunks.push(Vec::with_capacity(cap));
        }
        let chunk = self.chunks.last_mut().expect("chunk pushed above");
        if chunk.len() == chunk.capacity() {
            let next_cap = (chunk.capacity() * 2).min(CHUNK_SIZE);
            chunk.reserve_exact(next_cap - chunk.len());
        }
        chunk.push(tok);
        self.len += 1;
    }

    /// Release spare capacity on the final partial chunk and outer chunk list.
    pub(crate) fn finish(&mut self) {
        if let Some(last) = self.chunks.last_mut()
            && last.len() < last.capacity()
        {
            let mut exact = Vec::with_capacity(last.len());
            exact.extend_from_slice(last);
            *last = exact;
        }
        self.chunks.shrink_to_fit();
        self.long_ends.shrink_to_fit();
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn capacity(&self) -> usize {
        self.chunks.iter().map(Vec::capacity).sum()
    }

    #[inline]
    pub fn source(&self) -> &'a str {
        self.source
    }

    #[inline]
    pub fn get(&self, idx: usize) -> Option<Token> {
        if idx >= self.len {
            return None;
        }
        self.chunks[idx >> CHUNK_SHIFT]
            .get(idx & CHUNK_MASK)
            .copied()
    }

    #[inline]
    pub(crate) fn get_clamped(&self, idx: usize) -> Token {
        if self.len == 0 {
            Token::from_raw(TokenKind::Eof, self.source.len() as u32, 0)
        } else {
            self[idx.min(self.len - 1)]
        }
    }

    #[inline]
    pub fn span(&self, tok: Token) -> Span {
        let start = tok.start();
        let end = tok
            .inline_end()
            .unwrap_or_else(|| self.long_end(start as u32));
        Span::from_usize(start, end)
    }

    #[inline]
    pub fn span_at(&self, idx: usize) -> Span {
        self.span(self[idx])
    }

    #[cold]
    fn long_end(&self, start: u32) -> usize {
        let idx = self
            .long_ends
            .binary_search_by_key(&start, |&(s, _)| s)
            .expect("long token end missing from overflow table");
        self.long_ends[idx].1 as usize
    }

    #[inline]
    pub fn text(&self, tok: Token) -> Cow<'a, str> {
        let Span { start, end } = self.span(tok);
        let (start, end) = (start as usize, end as usize);
        let raw: Cow<'a, str> = match self.source.get(start..end) {
            Some(s) => Cow::Borrowed(s),
            None => String::from_utf8_lossy(&self.source.as_bytes()[start..end]),
        };
        match tok.kind {
            TokenKind::Directive
                if raw.len() > 15
                    && raw.starts_with("`begin_keywords")
                    && !matches!(
                        raw.as_bytes()[15],
                        b'a'..=b'z' | b'A'..=b'Z' | b'0'..=b'9' | b'_'
                    ) =>
            {
                Cow::Borrowed("`begin_keywords")
            }
            TokenKind::IntegerLiteral if raw.as_bytes().iter().any(|&b| is_literal_space(b)) => {
                let kept: Vec<u8> = raw
                    .as_bytes()
                    .iter()
                    .copied()
                    .filter(|&b| !is_literal_space(b))
                    .collect();
                Cow::Owned(match String::from_utf8(kept) {
                    Ok(s) => s,
                    Err(e) => String::from_utf8_lossy(e.as_bytes()).into_owned(),
                })
            }
            _ => raw,
        }
    }

    #[inline]
    pub fn text_at(&self, idx: usize) -> Cow<'a, str> {
        self.text(self[idx])
    }

    /// Drop backing vectors of chunks strictly preceding `keep_from`.
    pub(crate) fn release_before(&mut self, keep_from: usize) {
        let keep_chunk = (keep_from >> CHUNK_SHIFT).min(self.chunks.len());
        while self.released_chunks < keep_chunk {
            self.chunks[self.released_chunks] = Vec::new();
            self.released_chunks += 1;
        }
    }

    pub(crate) fn take_long_ends(&mut self) -> Vec<(u32, u32)> {
        std::mem::take(&mut self.long_ends)
    }

    pub(crate) fn sub_stream_with_eof(&self, toks: &[Token], eof_offset: usize) -> TokenStream<'a> {
        let mut out = TokenStream::new(self.source);
        for &tok in toks {
            let sp = self.span(tok);
            out.push_token(tok.kind, sp.start as usize, sp.end as usize);
        }
        out.push_token(TokenKind::Eof, eof_offset, eof_offset);
        out.finish();
        out
    }

    /// Materialize standalone owned tokens (for callers that drop `source`).
    pub fn to_owned_tokens(&self) -> Vec<OwnedToken> {
        let mut out = Vec::with_capacity(self.len);
        for tok in self.iter() {
            out.push(OwnedToken {
                kind: tok.kind,
                text: self.text(tok).into_owned(),
                span: self.span(tok),
            });
        }
        out
    }

    pub fn iter(&self) -> TokenIter<'_, 'a> {
        self.iter_from(0)
    }

    pub fn iter_from(&self, start: usize) -> TokenIter<'_, 'a> {
        if start >= self.len {
            return TokenIter {
                stream: self,
                chunk_idx: self.chunks.len(),
                in_chunk: 0,
                remaining: 0,
            };
        }
        TokenIter {
            stream: self,
            chunk_idx: start >> CHUNK_SHIFT,
            in_chunk: start & CHUNK_MASK,
            remaining: self.len - start,
        }
    }
}

impl Index<usize> for TokenStream<'_> {
    type Output = Token;

    #[inline]
    fn index(&self, idx: usize) -> &Self::Output {
        &self.chunks[idx >> CHUNK_SHIFT][idx & CHUNK_MASK]
    }
}

impl<'s, 'a> IntoIterator for &'s TokenStream<'a> {
    type Item = Token;
    type IntoIter = TokenIter<'s, 'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// Chunk-by-chunk iterator over a [`TokenStream`].
pub struct TokenIter<'s, 'a> {
    stream: &'s TokenStream<'a>,
    chunk_idx: usize,
    in_chunk: usize,
    remaining: usize,
}

impl Iterator for TokenIter<'_, '_> {
    type Item = Token;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining == 0 {
            return None;
        }
        let chunk = &self.stream.chunks[self.chunk_idx];
        let tok = chunk[self.in_chunk];
        self.in_chunk += 1;
        self.remaining -= 1;
        if self.in_chunk == chunk.len() {
            self.chunk_idx += 1;
            self.in_chunk = 0;
        }
        Some(tok)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining, Some(self.remaining))
    }
}

impl ExactSizeIterator for TokenIter<'_, '_> {}
impl FusedIterator for TokenIter<'_, '_> {}
