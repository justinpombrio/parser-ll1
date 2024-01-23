//! A lexer (a.k.a. tokenizer) that produces an iterator of (token, lexeme) pairs.
//!
//! Whitespace is skipped. If there is a lexing error, it is represented as an item in the
//! iterator whose `token` is `TOKEN_ERROR`.
//!
//! The "iterator" doesn't actually implement the `Iterator` trait, because at the end
//! of the lexeme stream it yields `TOKEN_EOF` forever. The user is expected to notice.
//!
//! If there are multiple possible matches:
//!
//! - The longest match is used.
//! - If there is a tie, whichever token is a 'string' pattern instead of a 'regex' pattern
//!   will be used.
//! - If there is _still_ a tie, the regex that's first in the list provided to `Lexer::new()` will
//! be used.

use regex::{escape, Error as RegexError, Regex, RegexSet};
use std::fmt;

/// A category of lexeme, such as "INTEGER" or "VARIABLE" or "OPEN_PAREN". The special Token called
/// [`TOKEN_ERROR`] represents a lexing error.
pub type Token = usize;

// Must match use in `LexerBuilder::new()`
pub const TOKEN_ERROR: Token = 0;
pub const TOKEN_EOF: Token = 1;

/*========================================*/
/*          Pattern                       */
/*========================================*/

#[derive(Debug, Clone)]
pub struct Pattern {
    /// Display name
    name: String,
    /// Regex to match tokens
    regex: Regex,
    /// Exact length that the match must be, if known
    length: Option<usize>,
}

impl PartialEq for Pattern {
    fn eq(&self, other: &Pattern) -> bool {
        self.regex.as_str() == other.regex.as_str() && self.length == other.length
    }
}

impl Eq for Pattern {}

fn new_regex(regex: &str) -> Result<Regex, RegexError> {
    match Regex::new(&format!("^({})", regex)) {
        Ok(regex) => Ok(regex),
        Err(err) => match Regex::new(regex) {
            // This error message is better because it doesn't have the ^({}) wrapper in it.
            Err(err) => Err(err),
            // Not sure why this wasn't an error too but there's still an issue.
            Ok(_) => Err(err),
        },
    }
}

/*========================================*/
/*          LexerBuilder                  */
/*========================================*/

#[derive(Debug, Clone)]
pub struct LexerBuilder {
    whitespace: Regex,
    patterns: Vec<Pattern>,
}

impl LexerBuilder {
    pub fn new(whitespace_regex: &str) -> Result<LexerBuilder, RegexError> {
        let error_pattern = Pattern {
            name: "ERROR".to_owned(),
            regex: Regex::new("^[a&&b]").unwrap(), // never used
            length: None,
        };
        let eof_pattern = Pattern {
            name: "end of file".to_owned(),
            regex: Regex::new("^[a&&b]").unwrap(), // never used
            length: None,
        };
        Ok(LexerBuilder {
            whitespace: new_regex(whitespace_regex)?,
            // Must match definitions of TOKEN_ERROR and TOKEN_EOF
            patterns: vec![error_pattern, eof_pattern],
        })
    }

    /// Add a pattern that matches exactly the string provided. Returns the token that will be
    /// produced whenever this pattern matches.
    pub fn string(&mut self, constant: &str) -> Result<Token, RegexError> {
        let pattern = Pattern {
            name: format!("'{}'", constant),
            regex: new_regex(&escape(constant))?,
            length: Some(constant.len()),
        };

        for (existing_token, existing_pattern) in self.patterns.iter().enumerate() {
            if &pattern == existing_pattern {
                return Ok(existing_token);
            }
        }

        let token = self.patterns.len();
        self.patterns.push(pattern);
        Ok(token)
    }

    /// Add a pattern that matches the given regex. Returns the token that will be produced whenever
    /// this pattern matches.
    ///
    /// The syntax is that of the `regex` crate. You do not need to begin the pattern with a
    /// start-of-string character `^`.
    pub fn regex(&mut self, name: &str, regex: &str) -> Result<Token, RegexError> {
        let pattern = Pattern {
            name: name.to_owned(),
            regex: new_regex(regex)?,
            length: None,
        };

        for (existing_token, existing_pattern) in self.patterns.iter().enumerate() {
            if &pattern == existing_pattern {
                return Ok(existing_token);
            }
        }

        let token = self.patterns.len();
        self.patterns.push(pattern);
        Ok(token)
    }

    /// Call this when you're done adding token patterns, to construct the lexer.
    pub fn finish(self) -> Lexer {
        Lexer {
            whitespace: self.whitespace,
            regex_set: RegexSet::new(self.patterns.iter().map(|p| p.regex.as_str())).unwrap(),
            patterns: self.patterns,
        }
    }
}

/*========================================*/
/*          Lexer                         */
/*========================================*/

#[derive(Debug, Clone)]
pub struct Lexer {
    whitespace: Regex,
    patterns: Vec<Pattern>,
    regex_set: RegexSet,
}

impl Lexer {
    /// Split `source` into a stream of lexemes. It is frequently useful to wrap this in
    /// [`iter::Peekable`](https://doc.rust-lang.org/stable/std/iter/struct.Peekable.html).
    pub fn lex<'l, 's: 'l>(&'l self, source: &'s str) -> LexemeIter {
        LexemeIter {
            source,
            lexer: self,
            position: Position {
                offset: 0,
                line: 0,
                col: 0,
                utf8_col: 0,
            },
            peeked: None,
        }
    }
}

/*========================================*/
/*          Lexeme                        */
/*========================================*/

/// One "word" in the stream returned by the lexer.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Lexeme<'s> {
    pub token: Token,
    pub lexeme: &'s str,
    /// The position just before the first character in the lexeme.
    pub start: Position,
    /// The position just after the last character in the lexeme.
    pub end: Position,
}

/*========================================*/
/*          Position                      */
/*========================================*/

pub type Offset = usize;
pub type Line = u32;
pub type Col = u32;

/// A position in the input text, _between_ two characters (or at the
/// start or end of a line). For example, "xyz" has 4 possible positions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Position {
    /// Byte offset from the beginning of the source string.
    pub offset: Offset,
    /// Line number.
    pub line: Line,
    /// Column number, counted in bytes.
    pub col: Col,
    /// Column number, counted in utf8 codepoints.
    pub utf8_col: Col,
}

impl fmt::Display for Position {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}:{}", self.line, self.utf8_col)
    }
}

impl Position {
    fn advance(&mut self, ch: char) {
        self.offset += ch.len_utf8() as Offset;
        if ch == '\n' {
            self.col = 0;
            self.utf8_col = 0;
            self.line += 1;
        } else {
            self.col += ch.len_utf8() as Col;
            self.utf8_col += 1;
        }
    }
}

/*========================================*/
/*          LexemeIter                    */
/*========================================*/

#[derive(Debug, Clone)]
pub struct LexemeIter<'l, 's> {
    position: Position,
    // The _remaining, unlexed_ source text
    source: &'s str,
    lexer: &'l Lexer,
    peeked: Option<(Position, &'s str, Lexeme<'s>)>,
}

impl<'l, 's> LexemeIter<'l, 's> {
    pub fn pos(&self) -> Position {
        self.position
    }

    pub fn remaining_source(&self) -> &'s str {
        &self.source
    }

    pub fn peek(&mut self) -> Lexeme<'s> {
        if let Some((_, _, lexeme)) = self.peeked {
            return lexeme;
        }

        // Save current state
        let old_pos = self.position;
        let old_src = self.source;

        // Lex one token and save what we find
        let lexeme = self.next();
        self.peeked = Some((self.position, self.source, lexeme));

        // Restore previous state
        self.position = old_pos;
        self.source = old_src;

        // Return lexed token
        lexeme
    }

    pub fn token_name(&self, token: Token) -> &str {
        &self.lexer.patterns[token].name
    }

    pub fn consume_whitespace(&mut self) {
        if let Some(span) = self.lexer.whitespace.find(self.source) {
            self.consume(span.end());
        }
    }

    pub fn next(&mut self) -> Lexeme<'s> {
        if let Some((pos, source, lexeme)) = self.peeked.take() {
            self.position = pos;
            self.source = source;
            return lexeme;
        }

        let pos = self.position;
        self.consume_whitespace();

        // If we're at the end of the file, return TOKEN::EOF.
        if self.source.is_empty() {
            return Lexeme {
                token: TOKEN_EOF,
                lexeme: "",
                start: pos,
                end: pos,
            };
        }

        // Find the best match (longest, with a tie-breaker of is_str)
        let mut best_match: Option<(Token, usize, bool)> = None;
        for token in &self.lexer.regex_set.matches(self.source) {
            let pattern = &self.lexer.patterns[token];

            // Find the length (and tie-breaker is_str) of this match.
            let (len, is_str) = if let Some(len) = pattern.length {
                (len, true)
            } else {
                (pattern.regex.find(self.source).unwrap().end(), false)
            };

            // If this is longer (or tie breaks) the best match so far, replace it.
            let is_best_match = if let Some((_, best_len, best_is_str)) = best_match {
                (len, is_str) > (best_len, best_is_str)
            } else {
                true
            };
            if is_best_match {
                best_match = Some((token, len, is_str));
            }
        }

        // If there was a best match, consume and return it.
        if let Some((token, len, _)) = best_match {
            let (lexeme, start, end) = self.consume(len);
            return Lexeme {
                token,
                lexeme,
                start,
                end,
            };
        }

        // Otherwise, nothing matched. Lex error! By definition we can't lex, but let's say the
        // problem lies in the current chunk of non-basic-whitespace characters.
        let basic_whitespace = &[' ', '\t', '\r', '\n'];
        let len = if let Some(len) = self.source.find(basic_whitespace) {
            len
        } else {
            self.source.len()
        };
        let (lexeme, start, end) = self.consume(len);
        Lexeme {
            token: TOKEN_ERROR,
            lexeme,
            start,
            end,
        }
    }

    fn consume(&mut self, len: usize) -> (&'s str, Position, Position) {
        let start = self.position;
        for ch in self.source[..len].chars() {
            self.position.advance(ch);
        }
        let end = self.position;

        let lexeme = &self.source[..len];
        self.source = &self.source[len..];
        (lexeme, start, end)
    }
}
