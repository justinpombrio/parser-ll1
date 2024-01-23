use parser_ll1::{choice, tuple, CompiledParser, Grammar, GrammarError, Parser, Recursive};

// > echo "(1 - 2 - 3) * sqrt(4) / 6" | cargo run --example calc
// -1.3333333333333333

fn make_calculator() -> Result<impl CompiledParser<f64>, GrammarError> {
    use std::str::FromStr;

    let mut g = Grammar::with_whitespace("[ \t\r\n]+")?;

    let calc = Recursive::<f64>::new("arithmetic expression");

    let num = g
        .regex("number", r#"[-+]?[0-9]*\.?[0-9]+([eE][-+]?[0-9]+)?"#)?
        .try_span(|span| f64::from_str(span.substr));

    let parens = tuple(
        "parenthesized expression",
        (g.string("(")?, calc.refn(), g.string(")")?),
    )
    .map(|(_, n, _)| n);

    let sqrt = tuple(
        "square root expression",
        (
            g.string("sqrt")?,
            g.string("(")?,
            calc.refn(),
            g.string(")")?,
        ),
    )
    .map(|(_, _, n, _)| n.sqrt());

    let expr_0 = choice("numeric expression", (num, parens, sqrt));

    // Multiplication and Division
    #[derive(Clone, Copy)]
    enum MultOp {
        Mult,
        Div,
    }
    let mult_op = choice(
        "'*' or '/'",
        (
            g.string("*")?.constant(MultOp::Mult),
            g.string("/")?.constant(MultOp::Div),
        ),
    );
    let expr_1 = expr_0
        .clone()
        .fold_many1(mult_op.and(expr_0), |n, (op, m)| match op {
            MultOp::Mult => n * m,
            MultOp::Div => n / m,
        });

    // Addition and Subtraction
    #[derive(Clone, Copy)]
    enum AddOp {
        Add,
        Sub,
    }
    let add_op = choice(
        "'+' or '-'",
        (
            g.string("+")?.constant(AddOp::Add),
            g.string("-")?.constant(AddOp::Sub),
        ),
    );
    let expr_2 = expr_1
        .clone()
        .fold_many1(add_op.and(expr_1), |n, (op, m)| match op {
            AddOp::Add => n + m,
            AddOp::Sub => n - m,
        });

    let calc = calc.define(expr_2);
    g.compile_parser(calc)
}

fn main() {
    use std::io;

    let parser = make_calculator().unwrap();
    let input = io::read_to_string(io::stdin()).unwrap();
    match parser.parse("stdin", &input) {
        Err(err) => println!("{}", err),
        Ok(n) => println!("{}", n),
    }
}
