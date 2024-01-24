# parser-ll1

**Guaranteed linear time parsing with typed parser combinators.**

```rust
use parser_ll1::{Grammar, Parser, CompiledParser};
use std::str::FromStr;

// Easy parsers

let mut g = Grammar::with_whitespace("[ \t\n]+").unwrap();

let number = g.regex("number", "[0-9]+").unwrap()
    .try_span(|s| i32::from_str(s.substr));

let numbers = number.clone().many_sep1(g.string("+").unwrap())
    .map(|nums| nums.into_iter().sum());

let parser = g.compile_parser(numbers).unwrap();

assert_eq!(parser.parse("test_case", "1 + 2 + 3"), Ok(6));

assert_eq!(format!("{}", parser.parse("test_case", "1 + + 2").unwrap_err()),
"parse error: expected number but found '+'
 --> test_case:1:5
  |
1 |1 + + 2
  |    ^ expected number
  |");

// Guaranteed LL1

let ambiguous = number.clone().opt().and(number);
assert_eq!(
    format!("{}", g.compile_parser(ambiguous).unwrap_err()),
    "ambiguous grammar: in number.opt().and(number), token number could either continue number.opt() or start number");
```

## Documentation

- [Reference documentation](https://docs.rs/parser-ll1)
- [Sample parsers](examples/)

## Features

- Guaranteed linear time parsing, due to `parse_ll1` checking that
  your grammar is LL1. You won't find guaranteed linear time parsing in
  any other (complete) Rust parser library.
  [`nom`](https://docs.rs/nom/latest/nom/) and
  [`parsell`](https://docs.rs/parsell/latest/parsell/) can take
  exponential time to parse if they're given a poorly structured grammar.
- Typed parser combinators, so that you build your parser in Rust code,
  and it produces a result directly. You don't have to write separate
  code to walk a parse tree like in [`pest`](https://pest.rs/).
- Good error messages, with no effort required from you. This is due
  to the fact that `parer_ll1` enforces that grammars are LL1 (so it
  always knows exactly what's being parsed), and that under the hood
  it lexes before it parses (so it knows what to point at if the next
  token is unexpected).
- Provides source locations (line, column, and UTF8-column).
- Easier to use than `nom` or `pest`.
- Runs on stable Rust.

## Non-Features

- Grammars that aren't LL1!
- Byte-level parsing. Use [`nom`](https://docs.rs/nom/latest/nom/)
  instead.
- Streaming parsing. Use [`nom`](https://docs.rs/nom/latest/nom/)
  or [`parsell`](https://docs.rs/parsell/latest/parsell/) instead.
- Extraordinary speed. Use [`nom`](https://docs.rs/nom/latest/nom/)
  instead. A preliminary benchmark puts `parse_ll1` at ~half the speed
  of `nom`, which is still very fast.
- There's no separate grammar file, which some people like because
  it's so declarative. Use [`pest`](https://pest.rs/) instead.

## Possible Future Features

- Error recovery, to return multiple parse errors and partial parses.
  (I believe the parser already has enough information to do this
   fairly well, without needing to change any parser definition.)
- Better parsing error messages.
