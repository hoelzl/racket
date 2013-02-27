#lang scribble/doc
@(require (for-label swindle/misc))

@title{Swindle Misc}

@defmodulelang[swindle/misc]

... Convenient syntax definitions

 (define* ...)
  Like `define', except that the defined identifier is automatically
  `provide'd.  Doesn't provide the identifier if outside of a module
  context.

 (make-provide-syntax orig-def-syntax provide-def-syntax)
  Creates `provide-def-syntax' as a syntax that is the same as
  `orig-def-syntax' together with an automatic `provide' form for the
  defined symbol, which should be either the first argument or the first
  identifier in a list (it does not work for recursive nesting).  The
  `provide' form is added only if the form appears at a module
  top-level.  The convention when this is used is to use a "*" suffix
  for the second identifier.

 (define-syntax* ...)
  Defined as the auto-provide form of `define-syntax'.

 (defsyntax ...)
 (defsyntax* ...)
 (letsyntax (local-syntaxes ...) ...)
  These are just shorthands for `define-syntax', `define-syntax*', and
  `let-syntax'.  This naming scheme is consistent with other definitions
  in this module (and the rest of Swindle).

 (defsubst name body)
 (defsubst* name body)
 (letsubst ([name body] ...) letbody ...)
  These are convenient ways of defining simple pattern transformer
  syntaxes (simple meaning they're much like inlined functions).  In
  each of these forms, the `name' can be either a `(name arg ...)' which
  will define a simple macro or an identifier which will define a
  symbol-macro.  For example:
    => (defsubst (my-if cond then else)
         (if (and cond (not (eq? 0 cond))) then else))
    => (my-if 1 (echo 2) (echo 3))
    2
    => (my-if 0 (echo 2) (echo 3))
    3
    => (define x (list 1 2 3))
    => (defsubst car-x (car x))
    => car-x
    1
    => (set! car-x 11)
    => x
    (11 2 3)
  Actually, if a `(name arg ...)' is used, then the body can have more
  pattern/expansions following -- but since this form translates to a
  usage of `syntax-rules', the `name' identifier should normally be `_'
  in subsequent patterns.  For example:
    => (defsubst (my-if cond then else)
                   (if (and cond (not (eq? 0 cond))) then else)
                 (_ cond then)
                   (and cond (not (eq? 0 cond)) then))
    => (my-if 0 1)
    #f
  Finally, note that since these are just patterns that get handled by
  syntax-rules, all the usual pattern stuff applies, like using `...'.

 (defmacro name body)
 (defmacro* name body)
 (letmacro ([name body] ...) letbody ...)
  These are just like Racket's define-macro (from mzlib/defmacro) with
  two major extensions:
  * If `name' is a simple identifier then a symbol-macro is defined (as
    with `defsubst' above).
  * A `letmacro' form for local macros is provided.

... Controlling syntax

 (define-syntax-parameter name default)
 (define-syntax-parameter* name default)
  Creates a `syntax parameter'.  Syntax parameters are things that you
  can use just like normal parameters, but they are syntax transformers,
  and the information they store can be used by other syntax
  transformers.  The purpose of having them around is to parameterize
  the way syntax transformation is used -- so they should be used as
  global option changes, not for frequent side effect: they change their
  value at syntax expansion time.  Note that using it stores the literal
  syntax that is passed to them -- there is no way to evaluate the given
  argument, for example, if some parameter expects a boolean -- then
  `(not #t)' will not work!  The syntax parameter itself is invoked
  wither with no arguments to retrieve its value, or with an argument to
  set it.  Retrieving or setting the value in this way is meaningful
  only in an interactive context since using it in a function just
  expands to the current value:
    => (define-syntax-parameter -foo- 1)
    => (-foo-)
    1
    => (define (foo) (-foo-))
    => (-foo- 2)
    => (-foo-)
    2
    => (foo)
    1

... Setters and more list accessors

 (set-caar! place x)
 (set-cadr! place x)
 (set-cdar! place x)
 (set-cddr! place x)
 (set-caaar! place x)
 (set-caadr! place x)
 (set-cadar! place x)
 (set-caddr! place x)
 (set-cdaar! place x)
 (set-cdadr! place x)
 (set-cddar! place x)
 (set-cdddr! place x)
 (set-caaaar! place x)
 (set-caaadr! place x)
 (set-caadar! place x)
 (set-caaddr! place x)
 (set-cadaar! place x)
 (set-cadadr! place x)
 (set-caddar! place x)
 (set-cadddr! place x)
 (set-cdaaar! place x)
 (set-cdaadr! place x)
 (set-cdadar! place x)
 (set-cdaddr! place x)
 (set-cddaar! place x)
 (set-cddadr! place x)
 (set-cdddar! place x)
 (set-cddddr! place x)
  These are all defined so it is possible to use `setf!' from "setf.rkt"
  with these standard and library-provided functions.

 (1st list)
 (2nd list)
 (3rd list)
 (4th list)
 (5th list)
 (6th list)
 (7th list)
 (8th list)
  Quick list accessors -- no checking is done, which makes these
  slightly faster than the bindings provided by mzlib/list.

 (set-1st! list x)
 (set-2nd! list x)
 (set-3rd! list x)
 (set-4th! list x)
 (set-5th! list x)
 (set-6th! list x)
 (set-7th! list x)
 (set-8th! list x)
  Setter functions for the above.

 (head pair)
 (tail pair)
 (set-head! pair x)
 (set-tail! pair x)
  Synonyms for `first', `rest', `set-first!', `set-rest!'.

 (set-second! list x)
 (set-third! list x)
 (set-fourth! list x)
 (set-fifth! list x)
 (set-sixth! list x)
 (set-seventh! list x)
 (set-eighth! list x)
  Defined to allow `setf!' with these mzlib/list functions.  Note that
  there is no error checking (unlike the accessor functions which are
  provided by mzlib/list).

 (nth list n)
 (nthcdr list n)
  Functions for pulling out the nth element and the nth tail of a list.
  Note the argument order which is unlike the one in CL.

 (list-set! list n x)
 (set-nth! list n x)
  A function to set the nth element of a list, also provided as
  `set-nth!' to allow using `setf!' with `nth'.

 (set-list-ref! list n x)
 (set-vector-ref! vector n x)
 (set-string-ref! string n x)
  These are defined as `list-set!', `vector-set!', and `string-set!', so
  the accessors can be used with `setf!'.

 (last list)
 (set-last! list x)
  Accessing a list's last element, and modifying it.

 (set-unbox! box x)
  Allow using `setf!' with `unbox'.  Note: this is an alias for
  `set-box!' which is an inconsistent name with other Scheme `set-foo!'
  functions -- the result is that you can also do `(setf! (box foo) x)'
  and bogusly get the same effect.

 (set-hash-table-get! table key [default] value)
  This is defined to be able to `setf!' into a `hash-table-get'
  accessor.  The form that `setf!' assembles always puts the new value
  last, but it is still useful to have a default thunk which results in
  an optional argument in an unusual place (and this argument is ignored
  by this, which is why it is defined as a macro).  For example:
    => (define t (make-hash-table))
    => (inc! (hash-table-get t 'foo))
    hash-table-get: no value found for key: foo
    => (inc! (hash-table-get t 'foo (thunk 0)))
    => (hash-table-get t 'foo)
    1

... Utilities

 (eprintf fmt-string args ...)
  Same as `printf' but it uses `current-error-port'.

 concat
  A shorter alias for `string-append'.

 (symbol-append sym ...)
  Self explanatory.

 (maptree func tree)
  Applies given function to a tree made of cons cells, and return the
  results tree with the same shape.

 (map! func list ...)
  Same as `map' -- but destructively modifies the first list to hold the
  results of applying the function.  Assumes all lists have the same
  length.

 (maptree! func tree)
  Same as `maptree' -- but destructively modifies the list to hold the
  results of applying the function.

 (mappend func list ...)
 (mappend! func list ...)
  Common idiom for doing a `(map func list ...)' and appending the
  results.  `mappend!' uses `append!'.

 (mapply func list-of-lists)
  Apply the given `func' on every list in `list-of-lists' and return the
  results list.

 (negate predicate?)
  Returns a negated predicate function.

 (position-of x list)
  Finds `x' in `list' and returns its index.

 (find-if predicate? list)
  Find and return an element of `list' which satisfies `predicate?', or
  #f if none found.

 (some predicate? list ...)
 (every predicate? list ...)
  Similar to Racket's `ormap' and `andmap', except that when multiple
  lists are given, the check stops as soon as the shortest list ends.

 (with-output-to-string thunk)
  Run `thunk' collecting generated output into a string.

 (1+ x)
 (1- x)
  Synonyms for `add1' and `sub1'.

... Multi-dimensional hash-tables
sing lists of `eq?' keys, based on Racket's hash tables (MzScheme doesn't
ave custom hashes).  Use weak hash-tables so no space is redundantly
asted.

 (make-l-hash-table)
 (l-hash-table-get table keys [failure-thunk])
 (l-hash-table-put! table keys value)
 (set-l-hash-table-get! table key [default] value)
  These functions are similar to Racket's hash-table functions, except
  that they work with a list of keys (compared with `eq?').  If it was
  possible to use a custom equality hash-table, then then would use
  something like
    (lambda (x y) (and (= (length x) (length y)) (andmap eq? x y))).
  The implementation uses a hash-table of hash-tables, all of them weak,
  since it is supposed to be used for memoization.

  `set-l-hash-table-get!' is defined to work with `setf!'.

 (memoize func)
  Return a memoized version of `func'.  Note that if `func' is
  recursive, it should be arranged for it to call the memoized version
  rather then call itself directly.

 (memoize! func-name)
  Changes the given function binding to a memoized version.

... Generic iteration and list comprehension
dea originated in a post on c.l.s by Based on Phil Bewig (July 2002), but
ent light years beyond that.

 (collect [dir] (var base expr) clause ...)
  Sophisticated iteration syntax.  The iteration is specified by the
  given clauses, where `var' serves as an accumulator variable that
  collects a value beginning with `base' and continuing with `expr' --
  similar to a single binding in a `do' form with a variable, an initial
  value and an update expression.  But there are much more iteration
  options than a `do' form: this form supports a generic
  list-comprehension and related constructs.  Forms that use this
  construct are:


 (loop-for clause ...)
  Use when no value collection is needed, and the default for
  expressions is to do them instead of using them as a filter.
  Implemented as:
    (collect => (acc (void) acc) do clause ...)

 (list-of expr clause ...)
  Implemented as:
    (reverse! (collect (acc '() (cons expr acc)) clause ...))

 (sum-of expr clause ...)
  Implemented as:
    (collect (acc 0 (+ expr acc)) clause ...)

 (product-of expr clause ...)
  Implemented as:
    (collect (acc 1 (* expr acc)) clause ...)

 (count-of clause ...)
  Only count matching cases, implemented as:
    (sum-of 1 clause ...)

  Each clause is either:
  * (v <- ...):     a binding generator clause;
  * (v <- ... and v <- ...): parallel generator clauses;
  * (v is is-expr): bind `v' to the result of `is-expr';
  * while expr:     a `while' keyword followed by an expression will
                    abort the whole loop if that expression evaluates to
                    #f;
  * until expr:     an `until' keyword followed by an expression will
                    abort the whole loop if that expression evaluates to
                    a non-#f value;
  * when ...:       filter by the following expressions -- if an
                    expression evaluates to #f, stop processing this
                    iteration (default for all macros except for
                    `loop-for');
  * unless ...:     filter by the negation of the following expressions;
  * do ...:         execute the following expressions, used for side
                    effects (default for the `loop-for' macro);
  * expr:           expression is used according to the current mode set
                    by a `when', `unless', or `do', keyword that
                    precedes it.
  The effect of this form is to iterate each generator variable
  according to generating `<-' clauses (see below for these) and
  parallel clauses, and evaluate the `expr' with each combination, which
  composes a result out of iteration-bound values and an accumulated
  result.  Generation is done in a nested fashion, where the rightmost
  generator spin fastest.  Parallel generators (specified with an infix
  `and') make all iterations happen simultaneously, ending as soon as
  the first one ends.  An `is' clause is used for binding arbitrary
  variables, a `do' clause is used to execute code for general
  side-effects, and other clauses are used to filter results before
  continuing down the clause list.  Each clause can use variables bound
  by previous clauses, and the `expr' can use all bound variables as
  well as the given accumulator variable.

  An optional first token can be used to specify the direction which is
  used to accumulate the result.  It can be one of these two tokens:
  `<=': A "backward" collection, the default (similar to `foldl');
  `=>': A "forward" collection (similar to `foldr').
  The default "backward" direction works by generating an accumulator
  carrying loop, as in this code (this code is for demonstration, not
  what `collect' creates):
    (let loop ([x foo] [acc '()])
      (if (done? x) acc (loop (next x) (cons (value x) acc))))
  which is a common Scheme idiom for such operations.  The problem is
  that this accumulation happens in reverse -- requiring reversing the
  final result (which is done by the `list-of' macro).  A "forward"
  direction does a naive recursive loop:
    (let loop ([x foo])
      (if (done? x) '() (cons (value x) (loop (next x)))))
  collecting values in the correct order, but the problem is that it
  keeps a computation context which makes memory consumption
  inefficient.  The default style is usually preferred, since reversing
  a list is a cheap operation, but it is not possible when infinite
  lists (streams) are used since it is impossible to reverse them.  In
  these cases, the "forward" style should be used, but the `expr' must
  take care not to evaluate the iteration "variable" immediately, using
  `delay' or a similar mechanism (this "variable" is not bound to a
  value but substituted with an expression (a symbol macro)).  For
  example, here's a quick lazy list usage:
    => (defsubst (lcons x y) (delay (cons x y)))
    => (define (lcar s) (car (force s)))
    => (define (lcdr s) (cdr (force s)))
    => (define x (collect (_ '() (lcons x _)) (x <- 0 ..)))
    ; loops indefinitely
    => (define x (collect => (_ '() (lcons x _)) (x <- 0 ..)))
    => (lcar (lcdr (lcdr x)))
    2
  Note that the `loop-for' macro uses a "forward" direction, but this is
  only because it is slightly faster since it doesn't require an extra
  binding.
  [The direction can be changed for a single part by using a "<-!"
  keyword instead of "<-", but this is an experimental feature since I
  don't know if it's actually useful for anything.  Do not try to mix
  this with the `while' and `until' keywords which are implemented
  differently based on the direction.]


  Generator forms are one of the following ("..", "then", "until",
  "while" are literal tokens), see below for what values are generated:
  * (v <- sequence):
    iterate `v' on values from `sequence';

  * (v <- 1st [2nd] .. [last]):
    iterate on an enumerated range, including last element of range;

  * (v <- 1st [2nd] ..< last):
    iterate on an enumerated range, excluding last element of range;

  * (v <- 1st [2nd] .. while last):
    iterate on an enumerated range, excluding last element of range;

  * (v <- 1st [2nd] .. until last):
    iterate on an enumerated range, excluding last element of range;

  * (v <- x then next-e [{while|until} cond-e]):
    start with the `x' expression, continue with the `next-e' expression
    (which can use `v'), do this while/until `cond-e' is true if a
    condition is given;

  * (v <- x {while|until} cond-e):
    repeat using the `x' expression while/until `cond-e' is true;

  * (v <- func arg ...):
    applies `func' to `arg ...', the result is expected to be some
    "iterator value" which is used to do the iteration -- iteration
    values are created by `collect-iterator' and `collect-numerator',
    see below for their description and return values.
  * (v <- gen1 <- gen2 <- ...):
    generator clauses can have multiple parts specified by more `<-'s,
    all of them will run sequentially;

  * (v1 <- gen1 ... and v2 <- gen2 ...):
    finally, an infix `and' specifies parallel generators, binding
    several variables.

  Iteration is possible on one of the following sequence values:

  * list: iterate over the list's element;
  * vector: iterate over the vector's elements;
  * string: iterate over characters in the string;
  * integer n: iterate on values from 0 to n-1;
  * procedure f:
    - if f accepts zero arguments, begin with (f) and iterate by
      re-applying (f) over and over, so the only way to end this
      iteration is by returning `collect-final' (see below);
    - otherwise, if f accepts one argument, it is taken as a generator
      function: it is passed a one-argument procedure `yield' which can
      be used to suspend its execution returning the given value, and it
      will be continued when more values are required (see
      `function-iterator' below);
  * hash-table: iterate over key-value pairs -- this is done with a
    generator function:
      (lambda (yield)
        (hash-table-for-each seq (lambda (k v) (yield (cons k v)))))
  * other values: repeated infinitely.
  Note that iteration over non-lists is done efficiently, iterating over
  a vector `v' is better than iterating over `(vector->list v)'.


  Enumeration is used whenever a ".." token is used to specify a range.
  There are different enumeration types based on different input types,
  and all are modified by the token used:
  * "..": a normal inclusive range;
  * "..<": a range that does not include the last element;
  * ".. while": a range that continues while a predicate is true;
  * ".. until": a range that continues until a predicate is true.
  The "..<" token extends to predicates in the expected way: the element
  that satisfies the predicate is the last one and it is not included in
  the enumeration -- unlike "..".
  These are the possible types that can be used with an enumeration:

  * num1 [num2] .. [num3]: go from num1 to num3 in num3 in num2-num1
    steps, if num2 is not given then use +1/-1 steps, if num3 is not
    given don't stop;
  * num1 [num2] .. pred: go from num1 by num2-num1 steps (defaults to
    1), up to the number that satisfies the given predicate;
  * char1 [char2] .. [char3/pred]: the same as with numbers, but on
    character ranges;
  * func .. [pred/x]: use `func' the same way as in an iterator above,
    use `pred' to identify the last element, if `pred' is omitted repeat
    indefinitely;
  * fst [next] .. [pred]: start with `fst', continue by repeated
    applications of the `next' function on it, and use `pred' to
    identify the last element, if `pred' is omitted repeat indefinitely,
    if `next' is omitted repeat `fst', and if both `fst' and `next' are
    numbers or characters then use their difference for stepping.  (Note
    that to repeat a function value you should use `identity' as for
    `next' or the function will be used as described above.)

  Here is a long list of examples for clarification, all using
  `list-of', but the generalization should be obvious:
    => (list-of x [x <- '(1 2 3)])
    (1 2 3)
    => (list-of (list x y) [x <- '(1 2 3)] [y <- 1 .. 2])
    ((1 1) (1 2) (2 1) (2 2) (3 1) (3 2))
    => (list-of (format "~a~a~a" x y z)
                [x <- '(1 2)] [y <- #(a b)] [z <- "xy"])
    ("1ax" "1ay" "1bx" "1by" "2ax" "2ay" "2bx" "2by")
    => (list-of (+ x y) [x <- '(1 2 3)] [y <- 20 40 .. 100])
    (21 41 61 81 101 22 42 62 82 102 23 43 63 83 103)
    => (list-of (+ x y) [x <- '(1 2 3) and y <- 20 40 .. 100])
    (21 42 63)
    => (list-of y [x <- 0 .. and y <- '(a b c d e f g h i)] (even? x))
    (a c e g i)
    => (list-of y [x <- 0 .. and y <- '(a b c d e f g h i)]
         when (even? x) do (echo y))
    a
    c
    e
    g
    i
    (a c e g i)
    => (list-of (list x y) [x <- 3 and y <- 'x])
    ((0 x) (1 x) (2 x))
    => (list-of (list x y) [x <- 3 and y <- 'x ..])
    ((0 x) (1 x) (2 x))
    => (list-of (list x y) [x <- #\0 .. and y <- '(a b c d)])
    ((#\0 a) (#\1 b) (#\2 c) (#\3 d))
    => (list-of x [x <- '(1 2 3) then (cdr x) until (null? x)])
    ((1 2 3) (2 3) (3))
    => (list-of (list x y)
         [x <- '(1 2 3) then (cdr y) until (null? x) and
          y <- '(10 20 30) then (cdr x) until (null? y)])
    (((1 2 3) (10 20 30)) ((20 30) (2 3)) ((3) (30)))
    => (list-of x [x <- (lambda (yield) 42)])
    ()
    => (list-of x [x <- (lambda (yield) (yield 42))])
    (42)
    => (list-of x [x <- (lambda (yield) (yield (yield 42)))])
    (42 42)
    => (list-of x [x <- (lambda (yield)
                          (for-each (lambda (x) (echo x) (yield x))
                                    '(3 2 1 0)))])
    3
    2
    1
    0
    (3 2 1 0)
    => (list-of x [x <- (lambda (yield)
                          (for-each (lambda (x) (echo x) (yield (/ x)))
                                    '(3 2 1 0)))])
    3
    2
    1
    0
    /: division by zero
    => (list-of x
         [c <- 3 and
          x <- (lambda (yield)
                 (for-each (lambda (x) (echo x) (yield (/ x)))
                           '(3 2 1 0)))])
    3
    2
    1
    (1/3 1/2 1)
    => (define h (make-hash-table))
    => (set! (hash-table-get h 'x) 1
             (hash-table-get h 'y) 2
             (hash-table-get h 'z) 3)
    => (list-of x [x <- h])
    ((y . 2) (z . 3) (x . 1))
    => (list-of x [x <- 4 <- 4 .. 0 <- '(1 2 3)])
    (0 1 2 3 4 3 2 1 0 1 2 3)
    => (list-of (list x y)
         [x <- 1 .. 3 <- '(a b c) and
          y <- (lambda (y) (y 'x) (y 'y)) <- "abcd"])
    ((1 x) (2 y) (3 #\a) (a #\b) (b #\c) (c #\d))

  Note that parallel iteration is useful both for enumerating results,
  and for walking over a finite prefix of an infinite iteration.

  The following is an extensive list of various ranges:
    => (list-of x [x <- 0 .. 6])
    (0 1 2 3 4 5 6)
    => (list-of x [x <- 0 ..< 6])
    (0 1 2 3 4 5)
    => (list-of x [x <- 0 .. -6])
    (0 -1 -2 -3 -4 -5 -6)
    => (list-of x [x <- 0 ..< -6])
    (0 -1 -2 -3 -4 -5)
    => (list-of x [x <- 0 2 .. 6])
    (0 2 4 6)
    => (list-of x [x <- 0 2 ..< 6])
    (0 2 4)
    => (list-of x [x <- 0 -2 ..< -6])
    (0 -2 -4)
    => (list-of x [x <- #\a .. #\g])
    (#\a #\b #\c #\d #\e #\f #\g)
    => (list-of x [x <- #\a ..< #\g])
    (#\a #\b #\c #\d #\e #\f)
    => (list-of x [x <- #\a #\c .. #\g])
    (#\a #\c #\e #\g)
    => (list-of x [x <- #\a #\c ..< #\g])
    (#\a #\c #\e)
    => (list-of x [x <- #\g #\e ..< #\a])
    (#\g #\e #\c)
    => (list-of x [x <- 6 5 .. zero?])
    (6 5 4 3 2 1 0)
    => (list-of x [x <- 6 5 ..< zero?])
    (6 5 4 3 2 1)
    => (list-of x [x <- 6 5 .. until zero?])
    (6 5 4 3 2 1)
    => (list-of x [x <- 6 5 .. while positive?])
    (6 5 4 3 2 1)
    => (list-of x [x <- '(1 2 3) cdr .. null?])
    ((1 2 3) (2 3) (3) ())
    => (list-of x [x <- '(1 2 3) cdr ..< null?])
    ((1 2 3) (2 3) (3))
    => (list-of x [x <- '(1 2 3) cdr .. until null?])
    ((1 2 3) (2 3) (3))
    => (list-of x [x <- '(1 2 3) cdr .. while pair?])
    ((1 2 3) (2 3) (3))
    => (list-of x [x <- #\a #\d .. while char-alphabetic?])
    (#\a #\d #\g #\j #\m #\p #\s #\v #\y)
    => (list-of x [x <- #\a #\d .. char-alphabetic?])
    (#\a)
    => (list-of x [x <- #\a #\d ..< char-alphabetic?])
    ()
    => (list-of x [x <- 0 1 .. positive?])
    (0 1)
    => (list-of x [x <- 1 2 .. positive?])
    (1)
    => (list-of x [x <- 1 2 ..< positive?])
    ()
    => (list-of x [x <- '(a b c) ..< pair?])
    ()
    => (list-of x [x <- '(a b c) .. pair?])
    ((a b c))
    => (list-of x [x <- '(a b c) cdr .. pair?])
    ((a b c))
    => (list-of x [x <- read-line .. eof-object?])
    ...list of remaining input lines, including #<eof>...
    => (list-of x [x <- read-line ..< eof-object?])
    ...list of remaining input lines, excluding #<eof>...
    => (list-of x [x <- read-line ..< eof])
    ...the same...


 collect-final
  This value can be used to terminate iterations: when it is returned as
  the iteration value (not the state), the iteration will terminate
  without using it.

 (function-iterator f [final-value])
  `f' is expected to be a function that can accept a single input value.
  It is applied on a `yield' function that can be used to return a value
  at any point.  The return value is a function of no argument, which
  returns on every application values that were passed to `yield'.  When
  `f' terminates, the final result of the iterated return value depends
  on the optional argument -- if none was supplied, the actual return
  value is returned, if a thunk was supplied it is applied for a return
  value, and if any other value was given it is returned.  After
  termination, calling the iterated function again results in an error.
  (The supplied `yield' function returns its supplied value to the
  calling context when resumed.)
    => (define (foo yield) (yield 1) (yield 2) (yield 3))
    => (define bar (function-iterator foo))
    => (list (bar) (bar) (bar))
    (1 2 3)
    => (bar)
    3
    => (bar)
    function-iterator: iterated function #<procedure:foo> exhausted.
    => (define bar (function-iterator foo 'done))
    => (list (bar) (bar) (bar) (bar))
    (1 2 3 done)
    => (bar)
    function-iterator: iterated function #<procedure:foo> exhausted.
    => (define bar (function-iterator foo (thunk (error 'foo "done"))))
    => (list (bar) (bar) (bar))
    (1 2 3)
    => (bar)
    foo: done

 (collect-iterator sequence)
 (collect-numerator from second to [flag])
  These functions are used to construct iterations.  `collect-iterator'
  is the function used to create iteration over a sequence object and it
  is used by `(x <- sequence)' forms of `collect'.  `collect-numerator'
  create range iterations specified with `(x <- from second to)' forms,
  where unspecified values are passed as `#f', and the flag argument is
  a `<', `while', or `until' symbol for ranges specified with "..<",
  ".. while" and ".. until".  These functions are available for
  implementing new iteration constructs, for example:
    => (define (in-values producer)
         (collect-iterator (call-with-values producer list)))
    => (list-of x [x <- in-values (thunk (values 1 2 3))])
    (1 2 3)
  The return value that specifies an iteration is a list of four items:
  1. the initial state value;
  2. a `step' function that gets a state and returns the next one;
  3. a predicate for the end state (#f for none);
  4. a function that computes a value from the state variable.
  But usually the functions are more convenient.

  Finally, remember that you can return `collect-final' as the value to
  terminate any iteration.

... Convenient printing

 *echo-display-handler* [h]
 *echo-write-handler*   [h]
  Currently, Racket's I/O can be customized only on a per port basis.
  This means that installing the object printing generic later will
  change only the standard ports, and for new ports a handleres should
  always be installed.  This means that `echos' will not work with
  objects since it uses a new port -- so use these parameters to allow
  to change them later to the Swindle printer.

 (echo arg ...)
  This is a handy printout utility that offers an alternative approach
  to `printf'-like output (it's a syntax, but it can be used as a
  regular function too, see below).  When applied, it simply prints its
  arguments one by one, using certain keywords to control its behavior:
  * :>e     - output on the current-error-port;
  * :>o     - output on the current-output-port (default);
  * :>s     - accumulate output in a string which is the return value
              (string output sets `:n-' as default (unless
              pre-specified));
  * :> p    - output on the given port `p', or a string if `#f';
  * :>> o   - use `o', a procedure that gets a value and a port, as the
              output handler (the procedure can take one value and
              display it on the current output port);
  * :d      - use `display' output (default);
  * :w      - use `write' output;
  * :d1 :w1 - change to a `display' or `write' output just for the next
              argument;
  * :s-     - no spaces between arguments;
  * :s+     - add spaces between arguments (default);
  * :n-     - do not print a final newline;
  * :n+     - terminate the output with a newline (default);
  * :n      - output a newline now;
  * : or :: - avoid a space at this point;
  * :\{     - begin a list construct (see below).
  Keywords that require additional argument are ignored if no argument
  is given.

  Recursive processing of a list begins with a `:\{' and ends with a
  `:\}' (which can be simpler if `read-curly-brace-as-paren' is off).
  Inside a list context, values are inspected and any lists cause
  iteration for all elements.  In each iteration, all non-list arguments
  are treated normally, but lists are dissected and a single element is
  printed in each step, terminating when the shortest list ends (and
  repeating a last `dotted' element of a list):
    => (define abc '(a b c))
    => (echo :\{ "X" abc :\})
    X a X b X c
    => (echo :\{ "X" abc '(1 2 3 4) :\})
    X a 1 X b 2 X c 3
    => (echo :\{ "X" abc '(1 . 2) :\})
    X a 1 X b 2 X c 2
  Inside a list context, the `:^' keyword can be used to stop this
  iteration if it is the last:
    => (echo :s- :\{ abc :^ ", " :\})
    a, b, c
  Nesting of lists is also simple, following these simple rules, by
  nesting the `:\{' ... `:\}' construct:
    => (echo :s- :\{ "<" :\{ '((1 2) (3 4 5) 6 ()) :^ "," :\} ">"
                     :^ "-" :\})
    <1,2>-<3,4,5>-<6>-<>
  Note that this example is similar to the CL `format':
    (format t "~{<~{~a~^,~}>~^-~}" '((1 2) (3 4 5) 6 ()))
  except that `echo' treats a dotted element (a non-list in this case)
  as repeating as needed.

  There are two additional special keywords that are needed only in
  uncommon situations:
  * :k-  - turn off keyword processing
  * :k+  - turn keyword processing on
  Usually, when `echo' is used, it is processed by a macro that detects
  all keywords, even if there is a locally bound variable with a keyword
  name.  This means that keywords are only ones that are syntactically
  so, not expressions that evaluate to keywords.  The two cases where
  this matters are -- when `echo' is used for its value (using it as a
  value, not in a head position) no processing is done so all keywords
  will just get printed; and when `echo' is used in a context where a
  variable has a keyword name and you want to use its value (which not a
  great idea anyway, so there is no way around it).  The first case is
  probably more common, so the variable `echo:' is bound to a special
  value that will force treating the next value as a keyword (if it
  evaluates to one) -- it can also be used to turn keyword processing on
  (which means that all keyword values will have an effect).  Here is a
  likely examples where `echo:' should be used:
    => (define (echo-values vals)
         (apply echo "The given values are:" echo: :w vals))
    => (echo-values '("a" "b" "c"))
    The given values are: "a" "b" "c"
    => (echo-values '(:a :b :c))
    The given values are: :a :b :c
  And here are some tricky examples:
    => (echo :>s 2)
    "2"
    => (define e echo)                 ; `e' is the real `echo' function
    => (e :>s 2)                       ; no processing done here
    :>s 2
    => (e echo: :>s 2)                 ; explicit key
    "2"
    => (e echo: :k+ :>s 2)             ; turn on keywords
    "2"
    => (let ([:>s 1]) (echo :>s 2))    ; `:>s' was processed by `echo'
    "2"
    => (let ([:>s 1]) (e :>s 2))       ; `:>s' was not processed
    1 2
    => (let ([:>s 1]) (e echo: :>s 2)) ; `:>s' is not a keyword here!
    1 2
    => (let ([:>s 1]) (echo echo: :>s 2)) ; `echo:' not needed
    "2"

  Finally, it is possible to introduce new keywords to `echo'.  This is
  done by calling it with the `:set-user' keyword, which expects a
  keyword to attach a handler to, and the handler itself.  The handler
  can be a simple value or a keyword that will be used instead:
    => (echo :set-user :foo "foo")
    => (echo 1 :foo 2)
    1 foo 2
    => (echo :set-user :foo :n)
    => (echo 1 :foo 2)
    1
    2
  The `:set-user' keyword can appear with other arguments, it has a
  global effect in any case:
    => (echo 1 :foo :set-user :foo "FOO" 2 :foo 3
             :set-user :foo "bar" :foo 4)
    1
    2 FOO 3 bar 4
    => (echo 1 :foo 2)
    1 bar 2
  If the handler is a function, then when this keyword is used, the
  function is applied on arguments pulled from the remaining `echo'
  arguments that follow (if the function can get any number of
  arguments, then all remaining arguments are taken).  The function can
  work in two ways: (1) when it is called, the `current-output-port'
  will be the one that `echo' currently prints to, so it can just print
  stuff; (2) if the function returns a list (or a single value which is
  not `#f' or `void'), then these values will be used instead of the
  taken arguments.  Some examples:
    => (echo :set-user :foo (thunk "FOO") 1 :foo 2)
    1 FOO 2
    => (echo :set-user :add1 add1 1 :add1 2)
    1 3
    => (echo :set-user :+1 (lambda (n) (list n '+1= (add1 n))) :+1 2)
    2 +1= 3
    => (echo :set-user :<> (lambda args (append '("<") args '(">")))
             :<> 1 2 3)
    < 1 2 3 >
  Care should be taken when user keywords are supposed to handle other
  keywords -- the `echo:' tag will usually be among the arguments except
  when `:k+' was used and an argument value was received.  This exposes
  the keyword treatment hack and might change in the future.

  To allow user handlers to change settings temporarily, there are
  `:push' and `:pop' keywords that will save and restore the current
  state (space and newline flags, output type and port etc).  For
  example:
    => (echo :set-user :@
             (lambda (l)
               (echo-quote
                list :push :s- :\{ "\"" l "\"" :^ ", " :\} :pop)))
    => (echo 1 :@ '(2 3 4) 5)
    1 "2", "3", "4" 5
  The above example shows another helper tool -- the `echo-quote'
  syntax: `(echo-quote head arg ...)' will transform into `(head ...)',
  where keyword arguments are prefix with the `echo:' tag.  Without it,
  things would look much worse.

  In addition to `:set-user' there is an `:unset-user' keyword which
  cancels a keyword handler.  Note that built-in keywords cannot be
  overridden or unset.

 (echo-quote head arg ...) [h]
  This macro will result in `(head arg ...)', where all keywords in the
  argument list are preceded with the `echo:' tag.  It is a convenient
  form to use for defining new echo keyword handlers.

 (echos arg ...)
  Just uses `echo' with `:>s'.

 echo:
  See the `echo' description for usage of this value.

 (named-lambda name args body ...)
  Like `lambda', but the name is bound to itself in the body.

 (thunk body ...)
  Returns a procedure of no arguments that will have the given body.

 (while condition body ...)
 (until condition body ...)
  Simple looping constructs.

 (dotimes (i n) body ...)
  Loop `n' times, evaluating the body when `i' is bound to 0,1,...,n-1.

 (dolist (x list) body ...)
  Loop with `x' bound to elements of `list'.

 (no-errors body ...)
  Execute body, catching all errors and returning `#f' if one occurred.

 (no-errors* body ...)
  Execute body, catching all errors and returnsthe exception if one
  occured.

 (regexp-case string clause ...)
  Try to match the given `string' against several regexps.  Each clause
  has one of the following forms:
  * (re => function): if `string' matches `re', apply `function' on the
    resulting list.
  * ((re args ...) body ...): if `string' matches `re', bind the tail of
    results (i.e, excluding the whole match result) to the given
    arguments and evaluate the body.  The whole match result (the first
    element of `regexp-match') is bound to `match'.
  * (re body ...): if `string' matches `re', evaluate the body -- no
    match results are available.
  * (else body ...): should be the last clause which is evaluated if all
    previous cases failed.

