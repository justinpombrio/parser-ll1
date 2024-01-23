use crate::first_set::FirstSet;
use crate::lexer::LexemeIter;
#[cfg(doc)]
use crate::Grammar;
use crate::{GrammarError, ParseResult, Parser};
use std::cell::{Cell, OnceCell};
use std::rc::{Rc, Weak};

/*========================================*/
/*          Parser: Recursion             */
/*========================================*/

/// Used to define recursive parsers.
///
/// The key is that you can [`Recursive::refn`] it before you [`Recursive::define`] it!
pub struct Recursive<T: Clone>(Rc<RecurP<T>>);

impl<T: Clone> Recursive<T> {
    /// Declare a new recursive parser. **You must [`Recursive::define`] it later!**
    ///
    /// # Panics
    ///
    /// The recursive parser will panic if you attempt to [`Grammar::compile_parser`]
    /// it before it has been `define`d.
    pub fn new(name: &str) -> Recursive<T> {
        Recursive(Rc::new(RecurP {
            name: name.to_owned(),
            parser: OnceCell::new(),
            initial_set: Cell::new(None),
        }))
    }

    /// Construct a reference to this recursive parser. Importantly, you may use this
    /// reference _before_ `define`ing the parser.
    pub fn refn(&self) -> impl Parser<T> + Clone {
        RecurPWeak {
            name: self.0.name.clone(),
            weak: Rc::downgrade(&self.0),
        }
    }

    /// Define this recursive parser to be equal to `parser`. `parser` may make use
    /// of [`Recursive::refn`]s inside of itself (and indeed it ought to; otherwise
    /// there was no need to use `Recursive`).
    pub fn define(self, parser: impl Parser<T> + Clone + 'static) -> impl Parser<T> + Clone {
        match self.0.parser.set(Box::new(parser)) {
            Ok(()) => (),
            Err(_) => panic!("Bug in recur: failed to set OnceCell"),
        }
        RecurPStrong(self.0)
    }
}

struct RecurP<T: Clone> {
    name: String,
    parser: OnceCell<Box<dyn Parser<T>>>,
    initial_set: Cell<Option<FirstSet>>,
}

impl<T: Clone> Clone for RecurP<T> {
    fn clone(&self) -> RecurP<T> {
        RecurP {
            name: self.name.clone(),
            parser: self.parser.clone(),
            initial_set: Cell::new(None),
        }
    }
}

impl<T: Clone> Parser<T> for RecurP<T> {
    fn name(&self) -> String {
        self.name.clone()
    }

    fn validate(&self) -> Result<FirstSet, GrammarError> {
        if let Some(initial_set) = self.initial_set.take() {
            // We're currently in a recursive case of validate() (see `else` branch).
            // Use the initial_set we set for ourselves.
            self.initial_set.set(Some(initial_set.clone()));
            Ok(initial_set)
        } else {
            // Compute our initial set with a recursive depth limited to 2.
            // This is guaranteed to be the same as the limit as the depth goes to infinity.
            let initial_set_0 = FirstSet::void();
            self.initial_set.set(Some(initial_set_0));
            let initial_set_1 = self.parser.get().unwrap().validate()?;
            self.initial_set.set(Some(initial_set_1));
            let initial_set_2 = self.parser.get().unwrap().validate()?;
            self.initial_set.set(None);
            Ok(initial_set_2)
        }
    }

    fn parse(&self, stream: &mut LexemeIter, required: bool) -> ParseResult<T> {
        self.parser.get().unwrap().parse(stream, required)
    }
}

/* ========== Recur: Weak ========== */

/// Private. The type returned by `Recursive.refn()`.
/// This is a _weak_ pointer so that if the outer `RecurPStrong` pointer is dropped,
/// the RecurP can be dropped. I.e., these are the self-references.
#[derive(Clone)]
struct RecurPWeak<T: Clone> {
    name: String,
    weak: Weak<RecurP<T>>,
}

impl<T: Clone> RecurPWeak<T> {
    fn unwrap<R>(&self, cb: impl FnOnce(&RecurP<T>) -> R) -> R {
        match self.weak.upgrade() {
            None => panic!(
                "Recursive: you must call 'define()' before using recursive parser '{}'",
                self.name
            ),
            Some(rc) => cb(rc.as_ref()),
        }
    }
}

impl<T: Clone> Parser<T> for RecurPWeak<T> {
    fn name(&self) -> String {
        self.unwrap(|p| p.name())
    }

    fn validate(&self) -> Result<FirstSet, GrammarError> {
        self.unwrap(|p| p.validate())
    }

    fn parse(&self, stream: &mut LexemeIter, required: bool) -> ParseResult<T> {
        self.unwrap(|p| p.parse(stream, required))
    }
}

/* ========== Recur: Strong ========== */

/// Private. The type returned by `Recursive.define()`.
/// Once the Recursive has been defined, this is the unique strong pointer to its RecurP.
#[derive(Clone)]
struct RecurPStrong<T: Clone>(Rc<RecurP<T>>);

impl<T: Clone> Parser<T> for RecurPStrong<T> {
    fn name(&self) -> String {
        self.0.as_ref().name()
    }

    fn validate(&self) -> Result<FirstSet, GrammarError> {
        self.0.as_ref().validate()
    }

    fn parse(&self, stream: &mut LexemeIter, required: bool) -> ParseResult<T> {
        self.0.as_ref().parse(stream, required)
    }
}
