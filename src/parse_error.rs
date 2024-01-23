use crate::lexer::Position;
#[cfg(doc)]
use crate::Parser;
use std::fmt;

/*========================================*/
/*          Parse Error Cause             */
/*========================================*/

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseErrorCause {
    pub message: String,
    pub caret_message: String,
    pub span: (Position, Position),
}

impl ParseErrorCause {
    pub fn new(expected: &str, token_name: &str, span: (Position, Position)) -> ParseErrorCause {
        if expected == "end of file" {
            // "expected end of file" isn't a very helpful phrase
            ParseErrorCause {
                message: format!("did not expect {}", token_name),
                caret_message: "unexpected".to_owned(),
                span,
            }
        } else {
            ParseErrorCause {
                message: format!("expected {} but found {}", expected, token_name),
                caret_message: format!("expected {}", expected),
                span,
            }
        }
    }

    pub fn build_error(self, filename: &str, source: &str) -> ParseError {
        let line_contents = match source.lines().nth(self.span.0.line as usize) {
            Some(line) => line.to_owned(),
            None => "".to_owned(),
        };
        ParseError {
            message: self.message,
            caret_message: self.caret_message,
            filename: filename.to_owned(),
            line_contents,
            span: self.span,
        }
    }
}

/*========================================*/
/*          Parse Error                   */
/*========================================*/

/// An error encountered while parsing.
///
/// There are two kinds of errors:
///
/// - An error because the input didn't match the grammar, saying what was
///   expected and what token was found instead.
/// - A user-written error thrown from a method like [`Parser::try_map`] or
///   [`Parser::try_span`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseError {
    message: String,
    caret_message: String,
    filename: String,
    line_contents: String,
    span: (Position, Position),
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use colored::Colorize;

        let (start, end) = self.span;
        let line_num = format!("{}", start.line + 1);
        let margin_width = line_num.len();
        let num_carets = if start.line == end.line {
            (end.utf8_col - start.utf8_col).max(1) as usize
        } else {
            self.line_contents.chars().count() - start.utf8_col as usize
        };

        writeln!(
            f,
            "{}{} {}",
            "parse error".red().bold(),
            ":".bold(),
            self.message.bold(),
        )?;
        writeln!(
            f,
            "{:indent$}{} {}:{}:{}",
            "",
            "-->".blue().bold(),
            self.filename,
            start.line + 1,
            start.utf8_col + 1,
            indent = margin_width,
        )?;
        writeln!(
            f,
            "{:indent$}{}",
            "",
            "|".blue().bold(),
            indent = margin_width + 1
        )?;
        writeln!(
            f,
            "{} {}{}",
            line_num.blue().bold(),
            "|".blue().bold(),
            self.line_contents,
        )?;
        writeln!(
            f,
            "{:indent$}{}{:start$}{} {}",
            "",
            "|".blue().bold(),
            "",
            &"^".repeat(num_carets).red().bold(),
            self.caret_message.red().bold(),
            start = start.utf8_col as usize,
            indent = margin_width + 1
        )?;
        write!(
            f,
            "{:indent$}{}",
            "",
            "|".blue().bold(),
            indent = margin_width + 1
        )?;
        Ok(())
    }
}

impl std::error::Error for ParseError {}
