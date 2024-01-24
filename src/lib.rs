// TODO:
// [x] Make something nicer than seq_n and choice_n for users
// [x] Have recur's interface use mutation, and panic on drop
// [x] Have recur validate, but only to depth 2, using an atomic u8
// [x] ParseError: fancy underlines
// [x] GrammarError: fix message on choice
// [x] Test errors: give line number, better error message
// [x] Review&test error messages
// [x] Review combinator names
// [-] Add iterator combinator for streaming parsing?
// [ ] Add context() combinator?
// [x] Change Parser<Output = T> to Parser<T>
// [x] Try having parsers lex directly instead of having a separate lexer;
//     see if that dramatically improves the speed. Yes: by 20%.
// [x] Make things run on stable Rust, it's a feature. Don't need `trait =`.
// [x] Docs
// [x] Internal docs
// [-] impl Fn -> impl FnMut?
// [ ] Hunt down remaining todos
// [x] Delete hand-crafted combinators that really didn't need to be hand-crafted
// [x] Extensive testing
// [x] Review docs, add example
// [ ] Better error messages: use information from higher in the stack.
//     (Then check off of "Future Features" list.)
// [ ] Error recover for multiple errors:
//     - For lexing, scan ahead to next char that starts a lexeme
//     - For parsing, have certain constructs like `many` discard & recover
//     (Then check off of "Future Features" list.)

// NOTE: Current time to parse dummy.json: 5.75 ms
//       Most of this time is lexing! If this library is to be faster,
//       it's the lexer that needs to be sped up.

// This design achieves all of the following:
//
// - The lexer isn't exposed (i.e. `Token` isn't in the interface).
// - The types of parsers is nice `impl Parser<T>`.
// - The implementation of recursive parsers doesn't threaten to summon Cthulu.
// - Parsers can be cloned without having the illegal `Box<Trait + Clone>`.
// - Implementing a parser combinator isn't too onerous.
// - `FirstSet`s aren't needlessly cloned (except if you call `compile_parser`
//   many times, but whatever).
// - No unnecessary boxing.
//
// Any change to the design is liable to break one of these properties, so if
// considering a change check this list first.
//
// It's tempting to remove the lexer. Doing so yields a ~20% speedup, but it
// would make the parse error messages worse. Not worth it!

//! # parser_ll1
//!
//! **Guaranteed linear time parsing with typed parser combinators.**
//!
//! ```
//! use parser_ll1::{Grammar, Parser, CompiledParser};
//! use std::str::FromStr;
//!
//! // Easy parsers
//!
//! let mut g = Grammar::with_whitespace("[ \t\n]+").unwrap();
//!
//! let number = g.regex("number", "[0-9]+").unwrap()
//!     .try_span(|s| i32::from_str(s.substr));
//!
//! let numbers = number.clone().many_sep1(g.string("+").unwrap())
//!     .map(|nums| nums.into_iter().sum());
//!
//! let parser = g.compile_parser(numbers).unwrap();
//!
//! assert_eq!(parser.parse("test_case", "1 + 2 + 3"), Ok(6));
//!
//! assert_eq!(format!("{}", parser.parse("test_case", "1 + + 2").unwrap_err()),
//! "parse error: expected number but found '+'
//!  --> test_case:1:5
//!   |
//! 1 |1 + + 2
//!   |    ^ expected number
//!   |");
//!
//! // Guaranteed LL1
//!
//! let ambiguous = number.clone().opt().and(number);
//! assert_eq!(
//!     format!("{}", g.compile_parser(ambiguous).unwrap_err()),
//!     "ambiguous grammar: in number.opt().and(number), token number could either continue number.opt() or start number");
//! ```
//!
//!
//! ## Overview
//!
//! This crate centers around the trait `Parser<T>` which represents a parser that,
//! if successful, produces a value of type `T`. These parsers are combined together
//! using _combinators_ to create larger parsers with different type parameters `T`.
//!
//!
//! ### Lexing
//!
//! To begin, create a [`Grammar`] with `Grammar::with_whitesapce` to define your
//! whitespace or `Grammar::new()` to use Unicode's whitespace definition.
//!
//! Once you have a `Grammar`, you can start to make parsers:
//!
//! - [`Grammar::string`] makes a `Parser<()>` that matches a literal string
//!   and produces the value `()`.
//! - [`Grammar::regex`] makes a `Parser<()>` that matches a regex and produces
//!   the value `()`.
//!
//! These are the building blocks from which all other parsers will be built.
//! They're called _tokens_.
//!
//! It's possible that multiple `string`s and `regex`s will match. For example:
//!
//! - If your parsing a language with addition `grammar.string("+")` and increment
//! `grammar.string("++")`, then `++` could lex as either `+` or `++`.
//! - As a more insidious example, if you're parsing a language with a keyword
//! `grammar.string("struct")` and identifiers `grammar.regex("identifier", "[_a-zA-Z]+")`,
//! then `struct` could lex as either the `string` or the `regex`.
//!
//! Ties like this are resolved by the following rules:
//!
//! 1. Longer matches win.
//! 2. In case of tie, `string` beats `regex`.
//! 3. If there's still a tie, the `string` or `regex` defined first wins.
//!
//! ### Parsing
//!
//! Larger parsers are built up from smaller parsers. For example,
//! `grammar.regex("int", "0|[1-9][0-9]*")?` produces a parser that matches a
//! single integer and produces `()`, which isn't very useful. The `try_span`
//! combinator can be used to turn the numeral into an actual `i32`:
//!
//! ```
//! # use parser_ll1::{Grammar, GrammarError, Parser};
//! # use std::str::FromStr;
//! # let mut grammar = Grammar::new();
//! let int_parser = grammar.regex("int", "0|[1-9][0-9]*")?
//!     .try_span(|span| i32::from_str(span.substr));
//! # Ok::<(), GrammarError>(())
//! ```
//!
//! (The [`Span`] struct contains the substring that was parsed, as well as
//! the start and end line and column numbers.)
//!
//! If you then want to parse a sequence of integers separated by commas, you
//! can combine the integer parser with a comma parser using the `many_sep1`
//! combinator:
//!
//! ```
//! # use parser_ll1::{Grammar, GrammarError, Parser};
//! # use std::str::FromStr;
//! # let mut grammar = Grammar::new();
//! # let int_parser = grammar.regex("int", "0|[1-9][0-9]*")?
//! #     .try_span(|span| i32::from_str(span.substr));
//! let int_list_parser = int_parser.many_sep1(grammar.string(",")?);
//! # Ok::<(), GrammarError>(())
//! ```
//!
//! To see the docs for the combinators, take a look at:
//!
//! - [`Parser`]
//! - [`tuple()`]
//! - [`choice()`]
//! - [`Recursive`]
//!
//! ### Compiling Parsers
//!
//! Parsers can't be run directly, you need to compile them first. This is as
//! easy as:
//!
//! ```
//! # use parser_ll1::{Grammar, GrammarError, Parser};
//! # use std::str::FromStr;
//! # let mut grammar = Grammar::new();
//! # let int_parser = grammar.regex("int", "0|[1-9][0-9]*")?
//! #     .try_span(|span| i32::from_str(span.substr));
//! # let int_list_parser = int_parser.many_sep1(grammar.string(",")?);
//! let parser = grammar.compile_parser(int_list_parser)?;
//! # Ok::<(), GrammarError>(())
//! ```
//!
//! If you need multiple entry points into your parser (perhaps you sometimes want
//! to parse a full program, but sometimes want to only parse an expression),
//! simply call `compile_parser` on multiple parsers.
//!
//! The compiled `parser` is invoked with `parser.parse(filename: &str, file_contents: &str)`.
//! `filename` is used solely in error messages. `file_contents` is the actual input
//! string to parse.
//!
//! ### LL1 Validation
//!
//! The call to `compile_parser` is when your parser will be checked for conformance
//! with the LL1 criteria. If it isn't LL1, you'll get a [`GrammarError`].
//! There are three rules for LL1 grammars that you must obey:
//!
//! - If you have a choice between multiple alternatives, they must all start
//!   with distinct tokens. (If two of them start with the same token, then the
//!   parser won't know which alternative to pick if it encounters that token.)
//! - If you have a choice between multiple alternatives, at most one of those
//!   alternatives can parse nothing. (If the parser sees that none of the
//!   alternatives' start tokens match, it will pick the alternative that can
//!   parse nothing. If there are multiple such alternatives, it won't know which
//!   one to pick.)
//! - You can't _first_ parse either a token T or nothing, and _then_ parse a
//!   token T. (Otherwise, if the _first_ parser encounters T, it won't know
//!   whether to parse it, or to parse nothing and leave the T for the second parser.)
//!
//!
//! ## Reference
//!
//! Here's a quick reference table of the types of all the parser combinators.
//!
//! ```text
//! COMBINATOR           OUTPUT-TYPE    NOTES
//!
//! ~~ lexemes ~~
//! Grammar.string()     ()
//! Grammar.regex()      ()
//!
//! ~~ mapping ~~
//! P.constant(V)        V
//! P.map(f)             f(P)
//! P.try_map(f)         f(P)?
//! P.span(f)            f(Span)
//! P.try_span(f)        f(Span)?
//! P.map_span(f)        f(Span, P)
//! P.try_map_span(f)    f(Span, P)?
//!
//! ~~ combination ~~
//! P.and(Q)             (P, Q)
//! P.preceded(Q)        P
//! P.terminated(Q)      P
//!
//! ~~ repetition ~~
//! P.opt()              Option<P>
//! P.many0()            Vec<P>
//! P.many1()            Vec<P>
//! P.fold_many0(V, f)   V              f: Fn(V, P) -> V
//! P.fold_many1(Q, f)   P              f: Fn(P, Q) -> P
//! P.many_sep0(Q)       Vec<P>
//! P.many_sep1(Q)       Vec<P>
//!
//! ~~ other ~~
//! empty()
//!   makes a parser that matches nothing and outputs ()
//! tuple(name, (P1, ..., Pn))
//!   makes a parser of output type (P1, ..., Pn)
//! choice(name, (P1, ..., Pn))
//!   requires that P1 though Pn all have the same output type,
//!   and makes a parser of that output type
//!
//! ~~ recursion ~~
//! see struct Recursive
//! ```

mod first_set;
mod lexer;
mod parse_error;
mod parser_recur;
mod vec_map;

use dyn_clone::{clone_box, DynClone};
use first_set::FirstSet;
use lexer::{LexemeIter, Lexer, LexerBuilder, Token, TOKEN_EOF, TOKEN_ERROR};
use parse_error::ParseErrorCause;
use std::error::Error;
use std::fmt;
use std::marker::PhantomData;

#[cfg(feature = "flamegraphs")]
use no_nonsense_flamegraphs::span;

/*========================================*/
/*          Interface                     */
/*========================================*/

pub use first_set::GrammarError;
pub use lexer::Position;
pub use parse_error::ParseError;
pub use parser_recur::Recursive;

#[doc(hidden)]
pub enum ParseResult<T> {
    /// The parse succeeded, and has output a T.
    Success(T),
    /// The parse failed, but in a recoverable way. There's no error message
    /// here b.c. our caller is going to try parsing something else instead.
    Failure,
    /// A fatal error. We're going to abort the entire parse with this message.
    Error(ParseErrorCause),
}

/// A parser that outputs type `T` on a successful parse.
///
/// You cannot use this parser directly; you must call [`Grammar::compile_parser`] first.
pub trait Parser<T>: DynClone {
    /// A descriptive name for this parser. Used in error messages.
    fn name(&self) -> String;
    /// Compute which tokens can come first in inputs that this parser matches.
    #[doc(hidden)]
    fn validate(&self) -> Result<FirstSet, GrammarError>;
    /// Parse the lexeme stream. If `required` is true, the `ParseResult` is
    /// not allowed to be `ParseResult::failure`!
    #[doc(hidden)]
    fn parse(&self, stream: &mut LexemeIter, required: bool) -> ParseResult<T>;

    // ========== Mapping ========== //

    /// Ignore this parser's output, replacing it with `value`.
    fn constant<T2: Clone>(self, value: T2) -> impl Parser<T2> + Clone
    where
        Self: Clone,
    {
        self.map(move |_| value.clone())
    }

    /// Transform this parser's output value with `func`.
    fn map<T2>(self, func: impl Fn(T) -> T2 + Clone) -> impl Parser<T2> + Clone
    where
        Self: Clone,
    {
        MapP {
            parser: self,
            func,
            phantom: PhantomData,
        }
    }

    /// Transform this parser's output value with `func`, producing a parse
    /// error if `func` returns an `Err`.
    fn try_map<T2, E: Error>(
        self,
        func: impl Fn(T) -> Result<T2, E> + Clone,
    ) -> impl Parser<T2> + Clone
    where
        Self: Clone,
    {
        TryMapP {
            parser: self,
            func,
            phantom: PhantomData,
        }
    }

    /// Ignore this parser's output, replacing it with `func(Span)` instead.
    ///
    /// The `Span` gives the region of the input text which was matched, including
    /// the substring.
    fn span<T2>(self, func: impl Fn(Span) -> T2 + Clone) -> impl Parser<T2> + Clone
    where
        Self: Clone,
    {
        self.map_span(move |span, _| func(span))
    }

    /// Ignore this parser's output, replacing it with `func(Span)` instead.
    /// Produce a parse error if `func` returns an `Err`.
    ///
    /// The `Span` gives the region of the input text which was matched, including
    /// the substring.
    fn try_span<T2, E: Error>(
        self,
        func: impl Fn(Span) -> Result<T2, E> + Clone,
    ) -> impl Parser<T2> + Clone
    where
        Self: Clone,
    {
        self.try_map_span(move |span, _| func(span))
    }

    /// Combine this parser's output (of type `T`) together with the matched `Span`,
    /// to produce an output of type `T2`.
    ///
    /// The `Span` gives the region of the input text which was matched, including
    /// the substring.
    fn map_span<T2>(self, func: impl Fn(Span, T) -> T2 + Clone) -> impl Parser<T2> + Clone
    where
        Self: Clone,
    {
        SpanP {
            parser: self,
            func,
            phantom: PhantomData,
        }
    }

    /// Combine this parser's output (of type `T`) together with the matched `Span`,
    /// to produce an output of type `T2`. Produce a parse error if `func` returns an `Err`.
    ///
    /// The `Span` gives the region of the input text which was matched, including
    /// the substring.
    fn try_map_span<T2, E: Error>(
        self,
        func: impl Fn(Span, T) -> Result<T2, E> + Clone,
    ) -> impl Parser<T2> + Clone
    where
        Self: Clone,
    {
        TrySpanP {
            parser: self,
            func,
            phantom: PhantomData,
        }
    }

    // ========== Repetition ========== //

    /// Either parse `self`, or parse nothing.
    fn opt(self) -> impl Parser<Option<T>> + Clone
    where
        Self: Clone,
    {
        OptP(self, PhantomData)
    }

    /// Parse `self` zero or more times.
    fn many0(self) -> impl Parser<Vec<T>> + Clone
    where
        T: Clone,
        Self: Clone,
    {
        fn push<E>(mut vec: Vec<E>, elem: E) -> Vec<E> {
            vec.push(elem);
            vec
        }
        Fold0P {
            name: format!("{}.many0()", self.name()),
            parser: self,
            initial_value: Vec::new(),
            fold: push,
            phantom: PhantomData,
        }
    }

    /// Parse `self` one or more times.
    fn many1(self) -> impl Parser<Vec<T>> + Clone
    where
        T: Clone,
        Self: Clone,
    {
        fn push<E>(mut vec: Vec<E>, elem: E) -> Vec<E> {
            vec.push(elem);
            vec
        }
        Fold1P {
            name: format!("{}.many1()", self.name()),
            first_parser: self.clone().map(|elem| vec![elem]),
            many_parser: self,
            fold: push,
            phantom: PhantomData,
        }
    }

    /// Parse zero or more occurrences of `self`.
    /// Combine the outputs, starting with `initial_value`, using `fold`.
    fn fold_many0<V: Clone>(
        self,
        initial_value: V,
        fold: impl Fn(V, T) -> V + Clone,
    ) -> impl Parser<V> + Clone
    where
        Self: Clone,
    {
        Fold0P {
            name: format!("{}.fold_many0()", self.name()),
            parser: self,
            initial_value,
            fold,
            phantom: PhantomData,
        }
    }

    /// Parse `self`, followed by zero or more occurrences of `parser`.
    /// Combine the outputs using `fold`.
    fn fold_many1<T2>(
        self,
        parser: impl Parser<T2> + Clone,
        fold: impl Fn(T, T2) -> T + Clone,
    ) -> impl Parser<T> + Clone
    where
        Self: Clone,
    {
        Fold1P {
            name: format!("{}.fold_many1({})", self.name(), parser.name()),
            first_parser: self,
            many_parser: parser,
            fold,
            phantom: PhantomData,
        }
    }

    /// Parse `self` zero or more times, separated by `sep`s.
    ///
    /// Collects the `self` outputs into a vector, and ignores the `sep` outputs.
    fn many_sep0<T2>(self, sep: impl Parser<T2> + Clone) -> impl Parser<Vec<T>> + Clone
    where
        T: Clone,
        Self: Clone,
    {
        SepP {
            elem: self,
            sep,
            phantom: PhantomData,
        }
    }

    /// Parse `self` one or more times, separated by `sep`s.
    ///
    /// Collects the `self` outputs into a vector, and ignores the `sep` outputs.
    fn many_sep1<T2>(self, sep: impl Parser<T2> + Clone) -> impl Parser<Vec<T>> + Clone
    where
        T: Clone,
        Self: Clone,
    {
        fn push<E>(mut vec: Vec<E>, elem: E) -> Vec<E> {
            vec.push(elem);
            vec
        }
        Fold1P {
            name: format!("{}.many_sep1({})", self.name(), sep.name()),
            first_parser: self.clone().map(|elem| vec![elem]),
            many_parser: self.preceded(sep),
            fold: push,
            phantom: PhantomData,
        }
    }

    // ========== Sequencing ========== //

    /// Parse `self` followed by `next`, producing a tuple of their outputs.
    fn and<T2>(self, next: impl Parser<T2> + Clone) -> impl Parser<(T, T2)> + Clone
    where
        Self: Clone,
    {
        let name = format!("{}.and({})", self.name(), next.name());
        tuple(&name, (self, next))
    }

    /// Parse `prev` followed by `self`, keeping only the output of `self`.
    fn preceded<T2>(self, prev: impl Parser<T2> + Clone) -> impl Parser<T> + Clone
    where
        Self: Clone,
    {
        let name = format!("{}.preceded({})", self.name(), prev.name());
        tuple(&name, (prev, self)).map(|(_, v)| v)
    }

    /// Parse `self` followed by `next`, keeping only the output of `self`.
    fn terminated<T2>(self, next: impl Parser<T2> + Clone) -> impl Parser<T> + Clone
    where
        Self: Clone,
    {
        let name = format!("{}.terminated({})", self.name(), next.name());
        tuple(&name, (self, next)).map(|(v, _)| v)
    }
}

impl<T> Clone for Box<dyn Parser<T>> {
    fn clone(&self) -> Self {
        clone_box(self.as_ref())
    }
}

impl<T> Parser<T> for Box<dyn Parser<T>> {
    fn name(&self) -> String {
        self.as_ref().name()
    }

    fn validate(&self) -> Result<FirstSet, GrammarError> {
        self.as_ref().validate()
    }

    fn parse(&self, stream: &mut LexemeIter, required: bool) -> ParseResult<T> {
        self.as_ref().parse(stream, required)
    }
}

/*========================================*/
/*          Grammar                       */
/*========================================*/

/// Start here! Used to create parsers for tokens, from which all other parsers are
/// built, and to "compile" a finished parser to get a parsing function.
#[derive(Debug, Clone)]
pub struct Grammar(LexerBuilder);

/// White space as defined by the Pattern_White_Space Unicode property.
const UNICODE_WHITESPACE_REGEX: &str =
    "[\\u0009\\u000A\\u000B\\u000C\\u000D\\u0020\\u0085\\u200E\\u200F\\u2028\\u2029]*";

/// A compiled parsing function, ready to use.
pub trait CompiledParser<T> {
    /// Parse the `input` text. `filename` is used only for error messages.
    fn parse(&self, filename: &str, input: &str) -> Result<T, ParseError>;
}

impl Grammar {
    /// Construct a new grammar that uses the `Pattern_White_Space` Unicode property
    /// for whitespace.
    pub fn new() -> Grammar {
        let lexer_builder = LexerBuilder::new(UNICODE_WHITESPACE_REGEX).unwrap();
        Grammar(lexer_builder)
    }

    /// Construct a new grammar with a custom regex for matching whitespace.
    pub fn with_whitespace(whitespace_regex: &str) -> Result<Grammar, GrammarError> {
        let lexer_builder =
            LexerBuilder::new(whitespace_regex).map_err(GrammarError::RegexError)?;
        Ok(Grammar(lexer_builder))
    }

    /// Create a parser that matches a string exactly.
    ///
    /// If the input could parse as _either_ a [`Grammar::string`] or a [`Grammar::regex`],
    /// then (i) the longest match wins, and (ii) `string`s win ties.
    pub fn string(&mut self, string: &str) -> Result<impl Parser<()> + Clone, GrammarError> {
        let name = format!("'{}'", string);
        let token = self.0.string(string).map_err(GrammarError::RegexError)?;
        Ok(TokenP { name, token })
    }

    /// Create a parser that matches a regex. The regex syntax is that from the
    /// [regex](https://docs.rs/regex/latest/regex/) crate.
    ///
    /// If the input could parse as _either_ a [`Grammar::string`] or a [`Grammar::regex`],
    /// then (i) the longest match wins, and (ii) `string`s win ties.
    pub fn regex(
        &mut self,
        name: &str,
        regex: &str,
    ) -> Result<impl Parser<()> + Clone, GrammarError> {
        let token = self
            .0
            .regex(name, regex)
            .map_err(GrammarError::RegexError)?;
        let name = name.to_owned();
        Ok(TokenP { name, token })
    }

    /// Validate that a parser is LL1, and if so produce a parsing function.
    ///
    /// Call this once but invoke the function it returns every time you parse.
    pub fn compile_parser<T2, P: Parser<T2> + Clone>(
        &self,
        parser: P,
    ) -> Result<impl CompiledParser<T2> + fmt::Debug, GrammarError> {
        use ParseResult::{Error, Failure, Success};

        struct CompiledParserImpl<T, P: Parser<T> + Clone> {
            lexer: Lexer,
            parser: P,
            phantom: PhantomData<T>,
        }
        impl<T, P: Parser<T> + Clone> fmt::Debug for CompiledParserImpl<T, P> {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                write!(f, "Compiled parser for '{}'", self.parser.name())
            }
        }

        impl<T, P: Parser<T> + Clone> CompiledParser<T> for CompiledParserImpl<T, P> {
            fn parse(&self, filename: &str, input: &str) -> Result<T, ParseError> {
                let mut lexeme_iter = self.lexer.lex(input);
                match self.parser.parse(&mut lexeme_iter, true) {
                    Success(succ) => Ok(succ),
                    Failure => panic!("Bug in CompiledParser"),
                    Error(err) => Err(err.build_error(filename, input)),
                }
            }
        }

        let lexer = self.clone().0.finish();
        // ensure the whole stream is consuemd
        let parser = tuple(&parser.name(), (parser, eof())).map(|(v, _)| v);
        parser.validate()?;

        Ok(CompiledParserImpl {
            lexer,
            parser,
            phantom: PhantomData,
        })
    }
}

/*========================================*/
/*          Parser: Empty                 */
/*========================================*/

#[derive(Clone)]
struct EmptyP;

impl Parser<()> for EmptyP {
    fn name(&self) -> String {
        "empty".to_owned()
    }

    fn validate(&self) -> Result<FirstSet, GrammarError> {
        Ok(FirstSet::empty("empty".to_owned()))
    }

    fn parse(&self, _stream: &mut LexemeIter, _required: bool) -> ParseResult<()> {
        ParseResult::Success(())
    }
}

/// The most boring parser, which parses nothing and outputs `()`.
pub fn empty() -> impl Parser<()> + Clone {
    EmptyP
}

/*========================================*/
/*          Parser: Token                 */
/*========================================*/

#[derive(Clone)]
struct TokenP {
    name: String,
    token: Token,
}

impl Parser<()> for TokenP {
    fn name(&self) -> String {
        self.name.clone()
    }

    fn validate(&self) -> Result<FirstSet, GrammarError> {
        Ok(FirstSet::token(self.name(), self.token))
    }

    fn parse(&self, stream: &mut LexemeIter, required: bool) -> ParseResult<()> {
        use ParseResult::{Error, Failure, Success};

        #[cfg(feature = "flamegraphs")]
        span!("Token");

        let lexeme = stream.peek();
        if lexeme.token == self.token {
            stream.next();
            Success(())
        } else if required {
            let token_name = if lexeme.token == TOKEN_ERROR {
                format!("'{}'", lexeme.lexeme)
            } else {
                stream.token_name(lexeme.token).to_owned()
            };
            Error(ParseErrorCause::new(
                &self.name,
                &token_name,
                (lexeme.start, lexeme.end),
            ))
        } else {
            Failure
        }
    }
}

fn eof() -> impl Parser<()> + Clone {
    TokenP {
        name: "end of file".to_owned(),
        token: TOKEN_EOF,
    }
}

/*========================================*/
/*          Parser: Try Map               */
/*========================================*/

struct TryMapP<T0, P0, T1, E1, F>
where
    P0: Parser<T0> + Clone,
    E1: Error,
    F: Fn(T0) -> Result<T1, E1> + Clone,
{
    parser: P0,
    func: F,
    phantom: PhantomData<(T0, T1)>,
}

impl<T0, P0, T1, E1, F> Clone for TryMapP<T0, P0, T1, E1, F>
where
    P0: Parser<T0> + Clone,
    E1: Error,
    F: Fn(T0) -> Result<T1, E1> + Clone,
{
    fn clone(&self) -> TryMapP<T0, P0, T1, E1, F> {
        TryMapP {
            parser: self.parser.clone(),
            func: self.func.clone(),
            phantom: PhantomData,
        }
    }
}

impl<T0, P0, T1, E1, F> Parser<T1> for TryMapP<T0, P0, T1, E1, F>
where
    P0: Parser<T0> + Clone,
    E1: Error,
    F: Fn(T0) -> Result<T1, E1> + Clone,
{
    fn name(&self) -> String {
        self.parser.name()
    }

    fn validate(&self) -> Result<FirstSet, GrammarError> {
        self.parser.validate()
    }

    fn parse(&self, stream: &mut LexemeIter, required: bool) -> ParseResult<T1> {
        use ParseResult::{Error, Failure, Success};

        #[cfg(feature = "flamegraphs")]
        span!("TryMap");

        let mut skipped_whitespace = stream.clone();
        skipped_whitespace.consume_whitespace();
        let start = skipped_whitespace.pos();
        match self.parser.parse(stream, required) {
            Success(result) => match (self.func)(result) {
                Ok(succ) => ParseResult::Success(succ),
                Err(err) => {
                    let end = stream.pos();
                    ParseResult::Error(ParseErrorCause {
                        message: err.to_string(),
                        caret_message: err.to_string(),
                        span: (start, end),
                    })
                }
            },
            Failure => Failure,
            Error(err) => Error(err),
        }
    }
}

/*========================================*/
/*          Parser: Map                   */
/*========================================*/

struct MapP<T0, P0: Parser<T0> + Clone, T1, F: Fn(T0) -> T1 + Clone> {
    parser: P0,
    func: F,
    phantom: PhantomData<(T0, T1)>,
}

impl<T0, P0: Parser<T0> + Clone, T1, F: Fn(T0) -> T1 + Clone> Clone for MapP<T0, P0, T1, F> {
    fn clone(&self) -> MapP<T0, P0, T1, F> {
        MapP {
            parser: self.parser.clone(),
            func: self.func.clone(),
            phantom: PhantomData,
        }
    }
}

impl<T0, P0: Parser<T0> + Clone, T1, F: Fn(T0) -> T1 + Clone> Parser<T1> for MapP<T0, P0, T1, F> {
    fn name(&self) -> String {
        self.parser.name()
    }

    fn validate(&self) -> Result<FirstSet, GrammarError> {
        self.parser.validate()
    }

    fn parse(&self, stream: &mut LexemeIter, required: bool) -> ParseResult<T1> {
        use ParseResult::{Error, Failure, Success};

        #[cfg(feature = "flamegraphs")]
        span!("Map");

        match self.parser.parse(stream, required) {
            Success(result) => Success((self.func)(result)),
            Failure => Failure,
            Error(err) => Error(err),
        }
    }
}

/*========================================*/
/*          Parser: Try Span              */
/*========================================*/

/// A region of the input text, provided by method [`Parser::span`] and friends.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Span<'s> {
    /// The input text from `start` to `end`.
    pub substr: &'s str,
    /// The start of the span, just before its first character.
    pub start: Position,
    /// The end of the span, just after its last character.
    pub end: Position,
}

impl<'s> fmt::Display for Span<'s> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}-{}", self.start, self.end)
    }
}

struct TrySpanP<T0, P0, T1, E1, F>
where
    P0: Parser<T0> + Clone,
    E1: Error,
    F: Fn(Span, T0) -> Result<T1, E1> + Clone,
{
    parser: P0,
    func: F,
    phantom: PhantomData<(T0, T1, E1)>,
}

impl<T0, P0, T1, E1, F> Clone for TrySpanP<T0, P0, T1, E1, F>
where
    P0: Parser<T0> + Clone,
    E1: Error,
    F: Fn(Span, T0) -> Result<T1, E1> + Clone,
{
    fn clone(&self) -> TrySpanP<T0, P0, T1, E1, F> {
        TrySpanP {
            parser: self.parser.clone(),
            func: self.func.clone(),
            phantom: PhantomData,
        }
    }
}

impl<T0, P0, T1, E1, F> Parser<T1> for TrySpanP<T0, P0, T1, E1, F>
where
    P0: Parser<T0> + Clone,
    E1: Error,
    F: Fn(Span, T0) -> Result<T1, E1> + Clone,
{
    fn name(&self) -> String {
        self.parser.name()
    }

    fn validate(&self) -> Result<FirstSet, GrammarError> {
        self.parser.validate()
    }

    fn parse(&self, stream: &mut LexemeIter, required: bool) -> ParseResult<T1> {
        use ParseResult::{Error, Failure, Success};

        #[cfg(feature = "flamegraphs")]
        span!("TrySpan");

        let mut skipped_whitespace = stream.clone();
        skipped_whitespace.consume_whitespace();
        let start = skipped_whitespace.pos();
        let source = skipped_whitespace.remaining_source();

        let result = match self.parser.parse(stream, required) {
            Success(succ) => succ,
            Failure => return Failure,
            Error(err) => return Error(err),
        };

        let end = stream.pos();
        let substr = &source[0..end.offset - start.offset];
        let span = Span { substr, start, end };

        match (self.func)(span, result) {
            Ok(succ) => ParseResult::Success(succ),
            Err(err) => ParseResult::Error(ParseErrorCause {
                message: err.to_string(),
                caret_message: err.to_string(),
                span: (span.start, span.end),
            }),
        }
    }
}

/*========================================*/
/*          Parser: Span                  */
/*========================================*/

struct SpanP<T0, P0, T1, F>
where
    P0: Parser<T0> + Clone,
    F: Fn(Span, T0) -> T1 + Clone,
{
    parser: P0,
    func: F,
    phantom: PhantomData<(T0, T1)>,
}

impl<T0, P0, T1, F> Clone for SpanP<T0, P0, T1, F>
where
    P0: Parser<T0> + Clone,
    F: Fn(Span, T0) -> T1 + Clone,
{
    fn clone(&self) -> SpanP<T0, P0, T1, F> {
        SpanP {
            parser: self.parser.clone(),
            func: self.func.clone(),
            phantom: PhantomData,
        }
    }
}

impl<T0, P0, T1, F> Parser<T1> for SpanP<T0, P0, T1, F>
where
    P0: Parser<T0> + Clone,
    F: Fn(Span, T0) -> T1 + Clone,
{
    fn name(&self) -> String {
        self.parser.name()
    }

    fn validate(&self) -> Result<FirstSet, GrammarError> {
        self.parser.validate()
    }

    fn parse(&self, stream: &mut LexemeIter, required: bool) -> ParseResult<T1> {
        use ParseResult::{Error, Failure, Success};

        #[cfg(feature = "flamegraphs")]
        span!("Span");

        let mut skipped_whitespace = stream.clone();
        skipped_whitespace.consume_whitespace();
        let start = skipped_whitespace.pos();
        let source = skipped_whitespace.remaining_source();

        let result = match self.parser.parse(stream, required) {
            Success(succ) => succ,
            Failure => return Failure,
            Error(err) => return Error(err),
        };

        let end = stream.pos();
        let substr = &source[0..end.offset - start.offset];
        let span = Span { substr, start, end };

        ParseResult::Success((self.func)(span, result))
    }
}

/*========================================*/
/*          Parser: Seq                   */
/*========================================*/

/// Parse a sequence of things in order, collecting their outputs in a tuple.
///
/// - `name` is used in error messages to refer to this parser.
/// - `tuple` is a tuple of parsers all with the same output type.
pub fn tuple<T>(name: &str, tuple: impl SeqTuple<T>) -> impl Parser<T> + Clone {
    tuple.make_seq(name.to_owned())
}

/// A tuple of parsers for [`tuple()`] to try. Each tuple element must be a parser.
/// They may have different output types. Can have length up to 10.
pub trait SeqTuple<T> {
    fn make_seq(self, name: String) -> impl Parser<T> + Clone;
}

macro_rules! define_seq {
    ($struct:ident, $( ($idx:tt, $type:ident, $parser:ident) ),*) => {
        struct $struct<$( $type ),*, $( $parser ),*>
        where $( $parser: Parser<$type> + Clone ),*
        {
            name: String,
            parsers: ($( $parser ),*),
            phantom: PhantomData<($( $type ),*)>,
        }

        impl<$( $type ),*, $( $parser ),*> Clone
        for $struct<$( $type ),*, $( $parser ),*>
        where $( $parser: Parser<$type> + Clone ),*
        {
            fn clone(&self) -> Self {
                $struct {
                    name: self.name.clone(),
                    parsers: self.parsers.clone(),
                    phantom: PhantomData,
                }
            }
        }

        impl<$( $type ),*, $( $parser ),*> Parser<($( $type ),*)>
        for $struct<$( $type ),*, $( $parser ),*>
        where $( $parser: Parser<$type> + Clone ),*
        {
            fn name(&self) -> String {
                self.name.clone()
            }

            fn validate(&self) -> Result<FirstSet, GrammarError> {
                FirstSet::sequence(
                    self.name(),
                    vec![$( self.parsers.$idx.validate()? ),*],
                )
            }

            fn parse(&self, stream: &mut LexemeIter, required: bool) -> ParseResult<($( $type ),*)> {
                use ParseResult::{Error, Failure, Success};

                #[cfg(feature = "flamegraphs")]
                span!("Seq");

                let start_pos = stream.pos().offset;
                let mut required = required;
                #[allow(unused_assignments)] // last `required` assignment is never read
                let results = ( $(
                    match self.parsers.$idx.parse(stream, required) {
                        Success(succ) => {
                            // As soon as a parser has consumed anything, set required
                            required = required || stream.pos().offset != start_pos;
                            succ
                        }
                        Error(err) => return Error(err),
                        Failure => return Failure,
                    }
                ),* );
                ParseResult::Success(results)
            }
        }

        impl<$( $type ),*, $( $parser ),*> SeqTuple<($( $type ),*)> for ($( $parser ),*)
        where $( $parser: Parser<$type> + Clone ),*
        {
            fn make_seq(self, name: String) -> impl Parser<($( $type ),*)> + Clone {
                $struct {
                    name,
                    parsers: self,
                    phantom: PhantomData,
                }
            }
        }
    }
}

define_seq!(SeqP2, (0, T0, P0), (1, T1, P1));
define_seq!(SeqP3, (0, T0, P0), (1, T1, P1), (2, T2, P2));
define_seq!(SeqP4, (0, T0, P0), (1, T1, P1), (2, T2, P2), (3, T3, P3));
define_seq!(
    SeqP5,
    (0, T0, P0),
    (1, T1, P1),
    (2, T2, P2),
    (3, T3, P3),
    (4, T4, P4)
);
define_seq!(
    SeqP6,
    (0, T0, P0),
    (1, T1, P1),
    (2, T2, P2),
    (3, T3, P3),
    (4, T4, P4),
    (5, T5, P5)
);
define_seq!(
    SeqP7,
    (0, T0, P0),
    (1, T1, P1),
    (2, T2, P2),
    (3, T3, P3),
    (4, T4, P4),
    (5, T5, P5),
    (6, T6, P6)
);
define_seq!(
    SeqP8,
    (0, T0, P0),
    (1, T1, P1),
    (2, T2, P2),
    (3, T3, P3),
    (4, T4, P4),
    (5, T5, P5),
    (6, T6, P6),
    (7, T7, P7)
);
define_seq!(
    SeqP9,
    (0, T0, P0),
    (1, T1, P1),
    (2, T2, P2),
    (3, T3, P3),
    (4, T4, P4),
    (5, T5, P5),
    (6, T6, P6),
    (7, T7, P7),
    (8, T8, P8)
);
define_seq!(
    SeqP10,
    (0, T0, P0),
    (1, T1, P1),
    (2, T2, P2),
    (3, T3, P3),
    (4, T4, P4),
    (5, T5, P5),
    (6, T6, P6),
    (7, T7, P7),
    (8, T8, P8),
    (9, T9, P9)
);

/*========================================*/
/*          Parser: Choice                */
/*========================================*/

/// Parse exactly one of the options.
///
/// - `name` is used in error messages to refer to this `choice`.
/// - `tuple` is a tuple of parsers all with the same output type.
pub fn choice<T>(name: &str, tuple: impl ChoiceTuple<T>) -> impl Parser<T> + Clone {
    tuple.make_choice(name.to_owned())
}

/// A tuple of parsers for [`choice`] to try. Each tuple element must be a parser,
/// and they must all have the same output type. Can have length up to 10.
pub trait ChoiceTuple<T> {
    #[doc(hidden)]
    fn make_choice(self, name: String) -> impl Parser<T> + Clone;
}

macro_rules! define_choice {
    ($struct:ident, $type:ident, $( ($idx:tt, $parser:ident) ),*) => {
        struct $struct<$type, $( $parser ),*>
        where $( $parser: Parser<$type> + Clone ),*
        {
            name: String,
            parsers: ($( $parser ),*),
            phantom: PhantomData<$type>,
        }

        impl<$type, $( $parser ),*> Clone
        for $struct<$type, $( $parser ),*>
        where $( $parser: Parser<$type> + Clone ),*
        {
            fn clone(&self) -> Self {
                $struct {
                    name: self.name.clone(),
                    parsers: self.parsers.clone(),
                    phantom: PhantomData,
                }
            }
        }

        impl<$type, $( $parser ),*> Parser<$type>
        for $struct<$type, $( $parser ),*>
        where $( $parser: Parser<$type> + Clone ),*
        {
            fn name(&self) -> String {
                self.name.clone()
            }

            fn validate(&self) -> Result<FirstSet, GrammarError> {
                FirstSet::choice(
                    self.name(),
                    vec![$( self.parsers.$idx.validate()? ),*],
                )
            }

            fn parse(&self, stream: &mut LexemeIter, required: bool) -> ParseResult<$type> {
                use ParseResult::{Error, Failure, Success};

                #[cfg(feature = "flamegraphs")]
                span!("Choice");

                $(
                    match self.parsers.$idx.parse(stream, false) {
                        Success(succ) => return Success(succ),
                        Error(err) => return Error(err),
                        Failure => (),
                    }
                )*
                if required {
                    let lexeme = stream.next();
                    let token_name = if lexeme.token == TOKEN_ERROR {
                        format!("'{}'", lexeme.lexeme)
                    } else {
                        stream.token_name(lexeme.token).to_owned()
                    };
                    Error(ParseErrorCause::new(
                        &self.name,
                        &token_name,
                        (lexeme.start, lexeme.end),
                    ))
                } else {
                    Failure
                }
            }
        }

        impl<$type, $( $parser ),*> ChoiceTuple<$type> for ($( $parser ),*)
        where $( $parser: Parser<$type> + Clone ),*
        {
            fn make_choice(self, name: String) -> impl Parser<$type> + Clone {
                $struct {
                    name,
                    parsers: self,
                    phantom: PhantomData,
                }
            }
        }
    }
}

define_choice!(ChoiceP2, T, (0, P0), (1, P1));
define_choice!(ChoiceP3, T, (0, P0), (1, P1), (2, P2));
define_choice!(ChoiceP4, T, (0, P0), (1, P1), (2, P2), (3, P3));
define_choice!(ChoiceP5, T, (0, P0), (1, P1), (2, P2), (3, P3), (4, P4));
define_choice!(
    ChoiceP6,
    T,
    (0, P0),
    (1, P1),
    (2, P2),
    (3, P3),
    (4, P4),
    (5, P5)
);
define_choice!(
    ChoiceP7,
    T,
    (0, P0),
    (1, P1),
    (2, P2),
    (3, P3),
    (4, P4),
    (5, P5),
    (6, P6)
);
define_choice!(
    ChoiceP8,
    T,
    (0, P0),
    (1, P1),
    (2, P2),
    (3, P3),
    (4, P4),
    (5, P5),
    (6, P6),
    (7, P7)
);
define_choice!(
    ChoiceP9,
    T,
    (0, P0),
    (1, P1),
    (2, P2),
    (3, P3),
    (4, P4),
    (5, P5),
    (6, P6),
    (7, P7),
    (8, P8)
);
define_choice!(
    ChoiceP10,
    T,
    (0, P0),
    (1, P1),
    (2, P2),
    (3, P3),
    (4, P4),
    (5, P5),
    (6, P6),
    (7, P7),
    (8, P8),
    (9, P9)
);

/*========================================*/
/*          Parser: Optional              */
/*========================================*/

struct OptP<T, P: Parser<T> + Clone>(P, PhantomData<T>);

impl<T, P: Parser<T> + Clone> Clone for OptP<T, P> {
    fn clone(&self) -> Self {
        OptP(self.0.clone(), PhantomData)
    }
}

impl<T, P: Parser<T> + Clone> Parser<Option<T>> for OptP<T, P> {
    fn name(&self) -> String {
        format!("{}.opt()", self.0.name())
    }

    fn validate(&self) -> Result<FirstSet, GrammarError> {
        // If `self.0` accepts empty then this union will produce an error.
        // Otherwise the initial set is simply `self.0`s initial set
        // together with empty.
        FirstSet::choice(
            self.name(),
            vec![FirstSet::empty(self.name()), self.0.validate()?],
        )
    }

    fn parse(&self, stream: &mut LexemeIter, _required: bool) -> ParseResult<Option<T>> {
        use ParseResult::{Error, Failure, Success};

        #[cfg(feature = "flamegraphs")]
        span!("Opt");

        match self.0.parse(stream, false) {
            Success(succ) => Success(Some(succ)),
            Error(err) => Error(err),
            Failure => Success(None),
        }
    }
}

/*========================================*/
/*          Parser: Many                  */
/*========================================*/

struct ManyP<T, P: Parser<T> + Clone>(P, PhantomData<T>);

impl<T, P: Parser<T> + Clone> Clone for ManyP<T, P> {
    fn clone(&self) -> Self {
        ManyP(self.0.clone(), PhantomData)
    }
}

impl<T, P: Parser<T> + Clone> Parser<Vec<T>> for ManyP<T, P> {
    fn name(&self) -> String {
        format!("{}.many0()", self.0.name())
    }

    fn validate(&self) -> Result<FirstSet, GrammarError> {
        FirstSet::choice(
            self.name(),
            vec![FirstSet::empty(self.name()), self.0.validate()?],
        )
    }

    fn parse(&self, stream: &mut LexemeIter, _required: bool) -> ParseResult<Vec<T>> {
        use ParseResult::{Error, Failure, Success};

        #[cfg(feature = "flamegraphs")]
        span!("Many");

        let mut results = Vec::new();
        loop {
            match self.0.parse(stream, false) {
                Success(succ) => results.push(succ),
                Error(err) => return Error(err),
                Failure => return Success(results),
            }
        }
    }
}

/*========================================*/
/*          Parser: Fold                  */
/*========================================*/

struct Fold1P<T0, P0, T1, P1, F>
where
    P0: Parser<T0> + Clone,
    P1: Parser<T1> + Clone,
    F: Fn(T0, T1) -> T0 + Clone,
{
    name: String,
    first_parser: P0,
    many_parser: P1,
    fold: F,
    phantom: PhantomData<(T0, T1)>,
}

impl<T0, P0, T1, P1, F> Clone for Fold1P<T0, P0, T1, P1, F>
where
    P0: Parser<T0> + Clone,
    P1: Parser<T1> + Clone,
    F: Fn(T0, T1) -> T0 + Clone,
{
    fn clone(&self) -> Self {
        Fold1P {
            name: self.name.clone(),
            first_parser: self.first_parser.clone(),
            many_parser: self.many_parser.clone(),
            fold: self.fold.clone(),
            phantom: PhantomData,
        }
    }
}

impl<T0, P0, T1, P1, F> Parser<T0> for Fold1P<T0, P0, T1, P1, F>
where
    P0: Parser<T0> + Clone,
    P1: Parser<T1> + Clone,
    F: Fn(T0, T1) -> T0 + Clone,
{
    fn name(&self) -> String {
        self.name.clone()
    }

    fn validate(&self) -> Result<FirstSet, GrammarError> {
        let init_first = self.first_parser.validate()?;
        let init_many = self.many_parser.validate()?;
        FirstSet::sequence(
            self.name(),
            vec![
                init_first,
                FirstSet::choice(
                    self.name(),
                    vec![
                        FirstSet::empty(self.name()),
                        FirstSet::sequence(
                            self.name(),
                            vec![
                                init_many.clone(),
                                FirstSet::choice(
                                    self.name(),
                                    vec![FirstSet::empty(self.name()), init_many],
                                )?,
                            ],
                        )?,
                    ],
                )?,
            ],
        )
    }

    fn parse(&self, stream: &mut LexemeIter, required: bool) -> ParseResult<T0> {
        use ParseResult::{Error, Failure, Success};

        #[cfg(feature = "flamegraphs")]
        span!("Fold1");

        let mut result = match self.first_parser.parse(stream, required) {
            Success(succ) => succ,
            Error(err) => return Error(err),
            Failure => return Failure,
        };
        loop {
            match self.many_parser.parse(stream, false) {
                Success(succ) => result = (self.fold)(result, succ),
                Error(err) => return Error(err),
                Failure => return Success(result),
            }
        }
    }
}

struct Fold0P<T, P: Parser<T> + Clone, V: Clone, F: Fn(V, T) -> V + Clone> {
    name: String,
    parser: P,
    initial_value: V,
    fold: F,
    phantom: PhantomData<T>,
}

impl<T, P: Parser<T> + Clone, V: Clone, F: Fn(V, T) -> V + Clone> Clone for Fold0P<T, P, V, F> {
    fn clone(&self) -> Self {
        Fold0P {
            name: self.name.clone(),
            parser: self.parser.clone(),
            initial_value: self.initial_value.clone(),
            fold: self.fold.clone(),
            phantom: PhantomData,
        }
    }
}

impl<T, P: Parser<T> + Clone, V: Clone, F: Fn(V, T) -> V + Clone> Parser<V> for Fold0P<T, P, V, F> {
    fn name(&self) -> String {
        self.name.clone()
    }

    fn validate(&self) -> Result<FirstSet, GrammarError> {
        FirstSet::choice(
            self.name(),
            vec![FirstSet::empty(self.name()), self.parser.validate()?],
        )
    }

    fn parse(&self, stream: &mut LexemeIter, _required: bool) -> ParseResult<V> {
        use ParseResult::{Error, Failure, Success};

        #[cfg(feature = "flamegraphs")]
        span!("Fold0");

        let mut result = self.initial_value.clone();
        loop {
            match self.parser.parse(stream, false) {
                Success(succ) => result = (self.fold)(result, succ),
                Error(err) => return Error(err),
                Failure => return Success(result),
            }
        }
    }
}

/*========================================*/
/*          Parser: Sep                   */
/*========================================*/

struct SepP<T0, P0, T1, P1>
where
    P0: Parser<T0> + Clone,
    P1: Parser<T1> + Clone,
{
    elem: P0,
    sep: P1,
    phantom: PhantomData<(T0, T1)>,
}

impl<T0, P0, T1, P1> Clone for SepP<T0, P0, T1, P1>
where
    P0: Parser<T0> + Clone,
    P1: Parser<T1> + Clone,
{
    fn clone(&self) -> Self {
        SepP {
            elem: self.elem.clone(),
            sep: self.sep.clone(),
            phantom: PhantomData,
        }
    }
}

impl<T0, P0, T1, P1> Parser<Vec<T0>> for SepP<T0, P0, T1, P1>
where
    P0: Parser<T0> + Clone,
    P1: Parser<T1> + Clone,
{
    fn name(&self) -> String {
        format!("{}.many_sep0({})", self.elem.name(), self.sep.name())
    }

    fn validate(&self) -> Result<FirstSet, GrammarError> {
        let elem_init = self.elem.validate()?;
        let sep_init = self.sep.validate()?;

        // SepBy(E, S) = (.|E(SE)*) ~= (.|E(.|SE))
        let name = self.name();
        let sep_elem = FirstSet::sequence(name.clone(), vec![sep_init, elem_init.clone()])?;
        let tail = FirstSet::choice(
            name.clone(),
            vec![FirstSet::empty(self.sep.name()), sep_elem],
        )?;
        let nonempty = FirstSet::sequence(name.clone(), vec![elem_init, tail])?;
        FirstSet::choice(name.clone(), vec![FirstSet::empty(name), nonempty])
    }

    fn parse(&self, stream: &mut LexemeIter, _required: bool) -> ParseResult<Vec<T0>> {
        use ParseResult::{Error, Failure, Success};

        #[cfg(feature = "flamegraphs")]
        span!("Many");

        let mut results = Vec::new();
        match self.elem.parse(stream, false) {
            Success(succ) => results.push(succ),
            Error(err) => return Error(err),
            Failure => return Success(results),
        }
        loop {
            match self.sep.parse(stream, false) {
                Success(_succ) => match self.elem.parse(stream, true) {
                    Success(succ) => results.push(succ),
                    Error(err) => return Error(err),
                    Failure => unreachable!(),
                },
                Error(err) => return Error(err),
                Failure => return Success(results),
            }
        }
    }
}
