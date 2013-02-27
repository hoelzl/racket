#lang scribble/doc
@(require (for-label swindle/base))

@title{Swindle Base}

@defmodulelang[swindle/base]

 (#%module-begin ...)
  `base' is a language module -- it redefines `#%module-begin' to load
  itself for syntax definitions.

 (#%top . id)
  This special syntax is redefined to make keywords (symbols whose names
  begin with a ":") evaluate to themselves.

 (#%app ...)
  Redefined so it is possible to apply using dot notation: `(foo x . y)'
  is the same as `(apply foo x y)'.  This is possible only when the last
  (dotted) element is an identifier.

 (define id-or-list ...)
  The standard `define' form is modified so defining :keywords is
  forbidden, and if a list is used instead of an identifier name for a
  function then a curried function is defined.
    => (define (((plus x) y) z) (+ x y z))
    => plus
    #<procedure:plus>
    => (plus 5)
    #<procedure:plus:1>
    => ((plus 5) 6)
    #<procedure:plus:2>
    => (((plus 5) 6) 7)
    18
  Note the names of intermediate functions.

  In addition, the following form can be used to define multiple values:
    => (define (values a b) (values 1 2))

 (let ([id-or-list ...] ...) ...)
 (let* ([id-or-list ...] ...) ...)
 (letrec ([id-or-list ...] ...) ...)
  All standard forms of `let' are redefined so they can generate
  functions using the same shortcut that `define' allows.  This includes
  the above extension to the standard `define'.  For example:
    => (let ([((f x) y) (+ x y)]) ((f 1) 2))
    3
  It also includes the `values' keyword in a similar way to `define'.
  For example:
    => (let ([(values i o) (make-pipe)]) i)
    #<pipe-input-port>

 (lambda formals body ...)
  The standard `lambda' is extended with Lisp-like &-keywords in its
  argument list.  This extension is available using the above short
  syntax.  There is one important difference between these keywords and
  Lisp: some &-keywords are used to access arguments that follow the
  keyword part of the arguments.  This makes it possible to write
  procedures that can be invoked as follows:
    (f <required-args> <optional-args> <keyword-args> <additional-args>)
  (Note: do not use more keywords after the <additional-args>!)

  Available &-keywords are:

  * &optional, &opt, &opts: denote an optional argument, possibly with a
    default value (if the variable is specified as `(var val)').
      => ((lambda (x &optional y [z 3]) (list x y z)) 1)
      (1 #f 3)
      => ((lambda (x &optional y [z 3]) (list x y z)) 1 2 #f)
      (1 2 #f)

  * &keys, &key: a keyword argument -- the variable should be specified
    as `x' or `(x)' to be initialized by an `:x' keyword, `(x v)' to
    specify a default value `v', and `(x k v)' to further specify an
    arbitrary keyword `k'.
      => ((lambda (&key x [y 2] [z :zz 3]) (list x y z)) :x 'x :zz 'z)
      (x 2 z)
    Note that keyword values take precedence on the left, and that
    keywords are not verified:
      => ((lambda (&key y) y) :y 1 :z 3 :y 2)
      1

  * &rest: a `rest' argument which behaves exactly like the Scheme dot
    formal parameter (actually a synonym for it: can't use both).  Note
    that in case of optional arguments, the rest variable holds any
    arguments that were not used for defaults, but using keys doesn't
    change its value.  For example:
      => ((lambda (x &rest r) r) 1 2 3)
      (2 3)
      => ((lambda (x &optional y &rest r) r) 1)
      ()
      => ((lambda (x &optional y &rest r) r) 1 2 3)
      (3)
      => ((lambda (x &optional y . r) r) 1 2 3)
      (3)
      => ((lambda (x &key y &rest r) (list y r)) 1 :y 2 3 4)
      (2 (:y 2 3 4))
      => ((lambda (x &key y &rest r) (list y r)) 1 :y 2 3 4 5)
      (2 (:y 2 3 4 5))
    Note that the last two examples indicate that there is no error if
    the given argument list is not balanced.

  * &rest-keys: similar to `&rest', but all specified keys are removed
    with their values.
      => ((lambda (x &key y &rest r) r) 1 :x 2 :y 3)
      (:x 2 :y 3)
      => ((lambda (x &key y &rest-keys r) r) 1 :x 2 :y 3)
      (:x 2)

  * &body: similar to `&rest-keys', but all key/values are removed one
    by one until a non-key is encountered.  (Warning: this is *not* the
    same as in Common Lisp!)
      => ((lambda (x &key y &body r) r) 1 :x 2 :y 3)
      ()
      => ((lambda (x &key y &body r) r) 1 :x 2 :y 3 5 6)
      (5 6)

  * &all-keys: the list of all keys+vals, without a trailing body.
      => ((lambda (&keys x y &all-keys r) r) :x 1 :z 2 3 4)
      (:x 1 :z 2)

  * &other-keys: the list of unprocessed keys+vals, without a trailing
    body.
      => ((lambda (&keys x y &other-keys r) r) :x 1 :z 2 3 4)
      (:z 2)

  Finally, here is an example where all &rest-like arguments are
  different:
    => ((lambda (&keys x y
                 &rest r
                 &rest-keys rk
                 &body b
                 &all-keys ak
                 &other-keys ok)
          (list r rk b ak ok))
        :z 1 :x 2 2 3 4)
    ((:z 1 :x 2 2 3 4) (:z 1 2 3 4) (2 3 4) (:z 1 :x 2) (:z 1))
  Note that the following invariants hold:
  * rest = (append all-keys body)
  * rest-keys = (append other-keys body)

 (keyword? x)
  A predicate for keyword symbols (symbols that begin with a ":").
  (Note: this is different from Racket's keywords!)

 (syntax-keyword? x)
  Similar to `keyword?' but also works for an identifier (a syntax
  object) that contains a keyword.

 (keyword->string k)
 (string->keyword s)
  Convert a Swindle keyword to a string and back.

 (getarg args keyword [not-found])
  Searches the given list of arguments for a value matched with the
  given keyword.  Similar to CL's `getf', except no error checking is
  done for an unbalanced list.  In case no value is found, the optional
  default value can be used -- this can be either a thunk, a promise, or
  any other value that will be used as is.  For a repeated keyword the
  leftmost occurrence is used.

 (syntax-getarg syntax-args keyword [not-found])
  Similar to `getarg' above, but the input is a syntax object of a
  keyword-value list.

 (getargs initargs keyword)
  The same as `getarg' but return the list of all key values matched --
  no need for a default value.  The result is in the same order as in
  the input.

 (keys/args args)
  The given argument list is scanned and split at the point where there
  are no more keyword-values, and the two parts are returned as two
  values.
    => (keys/args '(:a 1 :b 2 3 4 5))
    (:a 1 :b 2)
    (3 4 5)

 (filter-out-keys outs args)
  The keywords specified in the outs argument, with their matching
  values are filtered out of the second arguments.

