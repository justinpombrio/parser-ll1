use crate::vec_map::VecMap;
use crate::Token;
use regex::Error as RegexError;
use std::error::Error;
use std::fmt;

/// Used for checking the LL1 property of a grammar.
/// https://www.cs.princeton.edu/courses/archive/spring20/cos320/LL1/
///
/// The standard formulation of LL1 uses first_set vs. follow_set.
/// I'm instead using first_set vs. continuation_set. I came up with
/// this as an alternative that's easier to compute, and very much
/// hope it's equivalent!
#[derive(Debug, Clone)]
pub struct FirstSet {
    name: String,
    /// `true` iff `X -> ε`
    nullable: bool,
    /// The set of tokens `t` such that `X -> t α`
    first_tokens: VecMap<String>,
    /// The set of tokens `t` such that `X -> α` and `X -> α t β`
    continuation_tokens: VecMap<String>,
}

/// An issue with the grammar defined by a parser.
#[derive(Debug)]
pub enum GrammarError {
    /// Invalid regex.
    RegexError(RegexError),
    /// The defined grammar is not LL1: two alternatives accept empty.
    AmbiguityOnEmpty {
        name: String,
        case_1: String,
        case_2: String,
    },
    /// The defined grammar is not LL1: two alternatives accept the same start token.
    AmbiguityOnFirstToken {
        name: String,
        case_1: String,
        case_2: String,
        token: String,
    },
    /// The defined grammar is not LL1: `token` could continue `case_1` or start `case_2`.
    AmbiguityOnContinuationToken {
        name: String,
        case_1: String,
        case_2: String,
        token: String,
    },
}

impl FirstSet {
    pub fn void() -> FirstSet {
        FirstSet {
            name: "void".to_owned(), // unreachable
            nullable: false,
            first_tokens: VecMap::new(),
            continuation_tokens: VecMap::new(),
        }
    }

    pub fn empty(name: String) -> FirstSet {
        FirstSet {
            name,
            nullable: true,
            first_tokens: VecMap::new(),
            continuation_tokens: VecMap::new(),
        }
    }

    pub fn token(name: String, token: Token) -> FirstSet {
        let mut first_tokens = VecMap::new();
        first_tokens.set(token, name.clone());
        FirstSet {
            name,
            nullable: false,
            first_tokens,
            continuation_tokens: VecMap::new(),
        }
    }

    pub fn sequence(name: String, elems: Vec<FirstSet>) -> Result<FirstSet, GrammarError> {
        let mut nullable = true;
        let mut first_tokens: VecMap<(String, usize)> = VecMap::new();
        let mut continuation_tokens: VecMap<(String, usize)> = VecMap::new();
        for (i, init) in elems.iter().enumerate() {
            for (token, pattern) in &init.first_tokens {
                // Check if `token` is in `continuation_tokens` and error if so
                if let Some((_patt, j)) = continuation_tokens.get(token) {
                    return Err(GrammarError::AmbiguityOnContinuationToken {
                        token: pattern.to_owned(),
                        name,
                        case_1: elems[*j].name.clone(),
                        case_2: elems[i].name.clone(),
                    });
                }
                // Add `token` to `first_tokens`, erroring if it's already present
                if nullable {
                    if let Some((_patt, j)) = first_tokens.get(token) {
                        return Err(GrammarError::AmbiguityOnFirstToken {
                            token: pattern.to_owned(),
                            name,
                            case_1: elems[*j].name.clone(),
                            case_2: elems[i].name.clone(),
                        });
                    }
                    first_tokens.set(token, (pattern.to_owned(), i));
                }
            }
            if !init.nullable {
                nullable = false;
                continuation_tokens.clear();
            }
            for (token, pattern) in &init.continuation_tokens {
                continuation_tokens.set(token, (pattern.clone(), i));
            }
        }

        Ok(FirstSet {
            name,
            nullable,
            first_tokens: first_tokens.map(|(pattern, _)| pattern),
            continuation_tokens: continuation_tokens.map(|(pattern, _)| pattern),
        })
    }

    pub fn choice(name: String, elems: Vec<FirstSet>) -> Result<FirstSet, GrammarError> {
        let mut nullable: Option<usize> = None;
        let mut first_tokens: VecMap<(String, usize)> = VecMap::new();
        let mut continuation_tokens: VecMap<String> = VecMap::new();
        for (i, init) in elems.iter().enumerate() {
            if init.nullable {
                if let Some(j) = nullable {
                    return Err(GrammarError::AmbiguityOnEmpty {
                        name,
                        case_1: elems[j].name.clone(),
                        case_2: elems[i].name.clone(),
                    });
                }
                nullable = Some(i);
            }
            for (token, pattern) in &init.first_tokens {
                if let Some((_patt, j)) = first_tokens.get(token) {
                    return Err(GrammarError::AmbiguityOnFirstToken {
                        token: pattern.to_owned(),
                        name,
                        case_1: elems[*j].name.clone(),
                        case_2: elems[i].name.clone(),
                    });
                }
                first_tokens.set(token, (pattern.to_owned(), i));
            }
            for (token, pattern) in &init.continuation_tokens {
                continuation_tokens.set(token, pattern.to_owned());
            }
        }
        if nullable.is_some() {
            for (token, (pattern, _)) in &first_tokens {
                if continuation_tokens.get(token).is_none() {
                    continuation_tokens.set(token, pattern.clone());
                }
            }
        }

        Ok(FirstSet {
            name,
            nullable: nullable.is_some(),
            first_tokens: first_tokens.map(|(pattern, _)| pattern),
            continuation_tokens,
        })
    }

    #[cfg(test)]
    fn nullable(&self) -> bool {
        self.nullable
    }

    #[cfg(test)]
    fn is_first_token(&self, token: Token) -> bool {
        self.first_tokens.get(token).is_some()
    }
}

impl fmt::Display for GrammarError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use colored::Colorize;
        use GrammarError::{
            AmbiguityOnContinuationToken, AmbiguityOnEmpty, AmbiguityOnFirstToken, RegexError,
        };

        match self {
            RegexError(err) => write!(f, "{}", err),
            AmbiguityOnEmpty {
                name,
                case_1,
                case_2,
            } => {
                let message = format!(
                    "in {}, either {} or {} could be empty",
                    name, case_1, case_2
                );
                write!(
                    f,
                    "{}{} {}",
                    "ambiguous grammar".red().bold(),
                    ":".bold(),
                    message.bold()
                )
            }
            AmbiguityOnFirstToken {
                name,
                token,
                case_1,
                case_2,
            } => {
                let message = format!(
                    "in {}, token {} could start either {} or {}",
                    name, token, case_1, case_2
                );
                write!(
                    f,
                    "{}{} {}",
                    "ambiguous grammar".red().bold(),
                    ":".bold(),
                    message.bold()
                )
            }
            AmbiguityOnContinuationToken {
                name,
                token,
                case_1,
                case_2,
            } => {
                let message = format!(
                    "in {}, token {} could either continue {} or start {}",
                    name, token, case_1, case_2
                );
                write!(
                    f,
                    "{}{} {}",
                    "ambiguous grammar".red().bold(),
                    ":".bold(),
                    message.bold()
                )
            }
        }
    }
}

impl Error for GrammarError {}

#[test]
fn test_first_sets() {
    let name = String::new();

    let set_a = FirstSet::token("A".to_owned(), 65);
    let set_b = FirstSet::token("B".to_owned(), 66);
    let set_c = FirstSet::token("C".to_owned(), 67);
    let set_d = FirstSet::token("D".to_owned(), 68);
    let set_empty = FirstSet::empty("empty".to_owned());

    let set_a_empty =
        FirstSet::choice(name.clone(), vec![set_a.clone(), set_empty.clone()]).unwrap();
    assert!(FirstSet::choice(name.clone(), vec![set_a_empty.clone(), set_empty.clone()]).is_err());
    assert!(set_a_empty.nullable());
    assert!(set_a_empty.is_first_token(65));
    assert!(!set_a_empty.is_first_token(66));

    let set_bc = FirstSet::choice(name.clone(), vec![set_b.clone(), set_c.clone()]).unwrap();
    assert!(FirstSet::choice(name.clone(), vec![set_bc.clone(), set_c.clone()]).is_err());
    assert!(!set_bc.nullable());
    assert!(!set_bc.is_first_token(65));
    assert!(set_bc.is_first_token(66));
    assert!(set_bc.is_first_token(67));

    let set_d_empty = FirstSet::choice(
        name.clone(),
        vec![set_d, FirstSet::empty("empty".to_owned())],
    )
    .unwrap();
    assert!(set_d_empty.nullable());
    assert!(set_d_empty.is_first_token(68));

    let set_seq = FirstSet::sequence(name.clone(), vec![set_d_empty, set_bc, set_a_empty]).unwrap();
    assert!(!set_seq.nullable());
    assert!(!set_seq.is_first_token(65));
    assert!(set_seq.is_first_token(66));
    assert!(set_seq.is_first_token(67));
    assert!(set_seq.is_first_token(68));
}
