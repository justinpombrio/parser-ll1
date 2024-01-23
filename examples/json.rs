use parser_ll1::{choice, tuple, CompiledParser, Grammar, GrammarError, Parser, Recursive};
use std::fmt;

// A simple JSON parser. Does not handle things like string escapes or numbers with
// exponents in them, as those would make this example more verbose without elucidating
// much of anything about _ll1 parsing_.

// cat examples/sample.json | cargo run --release --example json

#[derive(Debug, Clone)]
pub enum Json {
    Null,
    Bool(bool),
    Number(f64),
    String(String),
    Array(Vec<Json>),
    Object(Vec<(String, Json)>),
}

impl Json {
    fn write(&self, f: &mut fmt::Formatter, indent: usize) -> fmt::Result {
        use Json::*;

        match self {
            Null => write!(f, "null"),
            Bool(false) => write!(f, "false"),
            Bool(true) => write!(f, "true"),
            Number(n) => write!(f, "{}", n),
            String(s) => write!(f, "\"{}\"", s),
            Array(elems) => {
                writeln!(f, "[")?;
                for (i, elem) in elems.iter().enumerate() {
                    write!(f, "{:indent$}", "", indent = 4 * (indent + 1))?;
                    elem.write(f, indent + 1)?;
                    if i + 1 != elems.len() {
                        writeln!(f, ",")?;
                    } else {
                        writeln!(f)?;
                    }
                }
                write!(f, "{:indent$}", "", indent = 4 * indent)?;
                write!(f, "]")
            }
            Object(entries) => {
                writeln!(f, "{{")?;
                for (i, entry) in entries.iter().enumerate() {
                    write!(f, "{:indent$}", "", indent = 4 * (indent + 1))?;
                    write!(f, "\"{}\": ", entry.0,)?;
                    entry.1.write(f, indent + 1)?;
                    if i + 1 != entries.len() {
                        writeln!(f, ",")?;
                    } else {
                        writeln!(f)?;
                    }
                }
                write!(f, "{:indent$}", "", indent = 4 * indent)?;
                write!(f, "}}")
            }
        }
    }
}

impl fmt::Display for Json {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.write(f, 0)
    }
}

fn make_json_parser() -> Result<impl CompiledParser<Json>, GrammarError> {
    use std::str::FromStr;

    let mut g = Grammar::with_whitespace("[ \t\r\n]+")?;

    let json_p = Recursive::new("json value");

    // Null
    let null_p = g.string("null")?.constant(Json::Null);

    // Bools
    let true_p = g.string("true")?.constant(Json::Bool(true));
    let false_p = g.string("false")?.constant(Json::Bool(false));
    let bool_p = choice("boolean", (true_p, false_p));

    // Numbers. This is a bad regex that only works for some numbers
    let number_p = g
        .regex("number", "[1-9][0-9]*(\\.[0-9]*)?|\\.[0-9]*")?
        .try_span(|s| f64::from_str(s.substr))
        .map(Json::Number);

    // Strings. Not implementing Json string escapes for this small test case.
    let plain_string_p = g
        .regex("string", r#""([^"\\]|\\.)*""#)?
        .span(|span| span.substr[1..span.substr.len() - 1].to_owned());
    let string_p = plain_string_p.clone().map(Json::String);

    // Arrays
    let array_elems_p = json_p.refn().many_sep0(g.string(",")?);
    let array_p = tuple("array", (g.string("[")?, array_elems_p, g.string("]")?))
        .map(|(_, elems, _)| Json::Array(elems));

    // Objects
    let entry_p = tuple(
        "dictionary entry",
        (plain_string_p, g.string(":")?, json_p.refn()),
    )
    .map(|(key, _, val)| (key, val));
    let entries_p = entry_p.many_sep0(g.string(",")?);
    let dict_p = tuple("dictionary", (g.string("{")?, entries_p, g.string("}")?))
        .map(|(_, entries, _)| Json::Object(entries));

    let json_p = json_p.define(choice(
        "json value",
        (null_p, bool_p, number_p, string_p, array_p, dict_p),
    ));

    g.compile_parser(json_p)
}

fn main() {
    use std::io;

    let parser = make_json_parser().unwrap();
    let input = io::read_to_string(io::stdin()).unwrap();
    match parser.parse("stdin", &input) {
        Err(err) => println!("{}", err),
        Ok(json) => println!("{}", json),
    }
}
