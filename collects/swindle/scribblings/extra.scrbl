#lang scribble/doc
@(require (for-label swindle/extra))

@title{Swindle Extra}

@defmodulelang[swindle/extra]

This module defines some additional useful functionality which requires
Swindle.

 (defstruct <struct-name> ([super]) slot ...)
  This is just a Swindle-style syntax for one of
    (define-struct struct-name (slot ...) (make-inspector))
    (define-struct (struct-name super) (slot ...) (make-inspector))
  with an additional binding of <struct-name> to the Swindle class that
  is computed by `struct-type->class'.  The `(make-inspector)' is needed
  to make this a struct that we can access information on.  Note that in
  method specifiers, the `struct:foo' which is defined by
  `define-struct' can be used just like `<foo>'.  What all this means is
  that you can use Racket structs if you just want Swindle's generic
  functions, but use built in structs that are more efficient since they
  are part of the implementation.  For example:

    => (defstruct <foo> () x y)
    => <foo>
    #<primitive-class:foo>
    => (defmethod (bar [x <foo>]) (foo-x x))
    => (bar (make-foo 1 2))
    1
    => (defmethod (bar [x struct:foo]) (foo-x x))
    => (bar (make-foo 3 4))
    3
    => (generic-methods bar)
    (#<method:bar:foo>)
    => (defstruct <foo2> (foo) z)
    => (bar (make-foo2 10 11 12))
    10

  To make things even easier, the super-struct can be written using a
  "<...>" syntax which will be stripped, and appropriate methods are
  added to `allocate-instance' and `initialize' so structs can be built
  using keywords:

    => (defstruct <foo3> (<foo>) z)
    => (foo-x (make <foo3> :z 3 :y 2 :x 1))
    1
    => (foo3-z (make <foo3> :z 3 :y 2 :x 2))
    3

  The `<struct-name>' identifier *must* be of this form -- enclosed in
  "<>"s.  This restriction is due to the fact that defining a Racket
  struct `foo', makes `foo' bound as a syntax object to something that
  cannot be used in any other way.

 (with-slots obj (slot ...) body ...)
  Evaluate the body in an environment where each `slot' is defined as a
  symbol-macro that accesses the corresponding slot value of `obj'.
  Each `slot' is either an identifier `id' which makes it stand for
  `(slot-ref obj 'id)', or `(id slot)' which makes `id' stand for
  `(slot-ref obj slot)'.

 (with-accessors obj (accessor ...) body ...)
  Evaluate the body in an environment where each `accessor' is defined
  as a symbol-macro that accesses `obj'.  Each `accessor' is either an
  identifier `id' which makes it stand for `(id obj)', or
  `(id accessor)' which makes `id' stand for `(accessor obj);.

 (as class obj)
  Converts `obj' to an instance of `class'.  This is a convenient
  generic wrapper around Scheme conversion functions (functions that
  look like `foo->bar'), but can be used for other classes too.

 (add-as-method from-class to-class op ...)
  Adds a method to `as' that will use the function `op' to convert
  instances of `from-class' to instances of `to-class'.  More operators
  can be used which will make this use their composition.  This is used
  to initialize `as' with the standard Scheme conversion functions.

 (equals? x y)
  A generic that compares `x' and `y'.  It has an around method that
  will stop and return `#t' if the two arguments are `equal?'.  It is
  intended for user-defined comparison between any instances.

 (add-equals?-method class pred?)
  Adds a method to `equals?' that will use the given `pred?' predicate
  to compare instances of `class'.

 (class+slots-equals? x y)
  This is a predicate function (not a generic function) that will
  succeed if `x' and `y' are instances of the same class, and all of
  their corresponding slots are `equals?'.  This is useful as a quick
  default for comparing simple classes (but be careful and avoid
  circularity problems).

 (make-equals?-compare-class+slots class)
  Make `class' use `class+slots-equals?' for comparison with `equals?'.

 (add x ...)
  A generic addition operation, initialized for some Scheme types
  (numbers (+), lists (append), strings (string-append), symbols
  (symbol-append), procedures (compose), and vectors).  It dispatches
  only on the first argument.

 (add-add-method class op)
  Add a method to `add' that will use `op' to add objects of class
  `class'.

 (len x)
  A generic length operation, initialized for some Scheme types (lists
  (length), strings (string-length), vectors (vector-length)).

 (add-len-method class op)
  Add a method to `len' that will use `op' to measure objects length for
  instances of `class'.

 (ref x indexes...)
  A generic reference operation, initialized for some Scheme types and
  instances.  Methods are predefined for lists, vectors, strings,
  objects, hash-tables, boxes, promises, parameters, and namespaces.

 (add-ref-method class op)
  Add a method to `ref' that will use `op' to reference objects of class
  `class'.

 (put! x v indexes)
  A generic setter operation, initialized for some Scheme types and
  instances.  The new value comes first so it is possible to add methods
  to specialize on it.  Methods are predefined for lists, vectors,
  strings, objects, hash-tables, boxes, parameters, and namespaces.

 (add-put!-method class op)
  Add a method to `put!' that will use `op' to change objects of class
  `class'.

 (set-ref! x indexes... v)
  This syntax will just translate to `(put! x v indexes...)'.  It makes
  it possible to make `(set! (ref ...) ...)' work with `put!'.

... Generic-based printing mechanism

 *print-level*
 *print-length*
  These parameters control how many levels deep a nested data object
  will print, and how many elements are printed at each level.  `#f'
  means no limit.  The effect is similar to the corresponding globals in
  Lisp.  Only affects printing of container objects (like lists, vectors
  and structures).

 (print-object obj esc? port)
  Prints `obj' on `port' using the above parameters -- the effect of
  `esc?' being true is to use a `write'-like printout rather than a
  `display'-like printout when it is false.  Primitive Scheme values are
  printed normally, Swindle objects are printed using the un-`read'-able
  "#<...>" sequence unless a method that handles them is defined.  For
  this printout, objects with a `name' slot are printed using that name
  (and their class's name).

  Warning: this is the method used for user-interaction output, errors
  etc.  Make sure you only define reliable methods for it.

 (name-sans-<> name)
  Given a string or symbol for name, return a string where the outermost
  set of angle brackets have been stripped if they are present.  This is
  handy if you are writing your own print-object methods.

 (print-object-with-slots obj esc? port)
  This is a printer function that can be used for classes where the
  desired output shows slot values.  Note that it is a simple function,
  which should be embedded in a method that is to be added to
  `print-object'.

 (display-object obj [port])
 (write-object obj [port])
  Used to display and write an object using `print-object'.  Used as the
  corresponding output handler functions.

 (object->string obj [esc? = #t])
  Convert the given `obj' to a string using its printed form.

 (install-swindle-printer)
  In Racket, output is configurable on a per-port basis.  Use this
  function to install Swindle's `display-object' and `write-object' on
  the current output and error ports whenever they are changed
  (`swindle' does that on startup).  This makes it possible to see
  Swindle values in errors, when using `printf' etc.

... Simple matching

 match-failure
  The result for a matcher function application that failed.  You can
  return this value from a matcher function in a <matcher> so the next
  matching one will get invoked.

 (matching? matcher value)
  The `matcher' argument is a value of any type, which is matched
  against the given `value'.  For most values matching means being equal
  (using `equals?')  to, but there are some exceptions: class objects
  are tested with `instance-of?', functions are used as predicates,
  literals are used with equals?, pairs are compared recursively and
  regexps are used with regexp-match.

 (let/match pattern value body ...)
  Match the `value' against the given `pattern', and evaluate the body
  on a success.  It is an error for the match to fail.  Variables that
  get bound in the matching process can be used in the body.

  The pattern specification has a complex syntax as follows:
  - simple values (not symbols) are compared with `matching?' above;
  - :x                 keywords are also used as literal values;
  - *                  is a wildcard that always succeeds;
  - ???                matches the `???' value;
  - (lambda ...)       use the resulting closure value (for predicates);
  - (quote ...)        use the contents as a simple value;
  - (quasiquote ...)   same;
  - (V := P)           assign the variable V to the value matched by P;
  - V                  for a variable name V that was not part of the
                       pattern so far, this matches anything and binds V
                       to the value -- the same as (V := *);
  - (! E)              evaluate E, use the result as a literal value;
  - (!! E)             evaluate E, continue matching only if it is true;
  - (V when E)         same as (and V (!! E));
  - (and P ...)        combine the matchers with and, can bind any
                       variables in all parts;
  - (or P ...)         combine the matchers with or, bound variables are
                       only from the successful form;
  - (if A B C)         same as (or (and A B) C);
  - (F => P)           continue matching P with (F x) (where is x is the
                       current matched object);
  - (V :: P ...)       same as (and (! V) P...), useful for class forms
                       like (<class> :: (foo => f) ...);
  - (make <class> ...) if the value is an instance of <class>, then
                       continue by the `...' part which is a list of
                       slot names and patterns -- a slot name is either
                       :foo or 'foo, and the pattern will be matched
                       against the contents of that slot in the original
                       <class> instance;
  - ???                matches the unspecified value (`???' in tiny-clos)
  - (regexp R)         convert R to a regexp and use that to match
                       strings;
  - (regexp R P ...)   like the above, but continue matching the result
                       with `(P ...)' so it can bind variables to the
                       result (something like `(regexp "a(x?)b" x y)'
                       will bind `x' to the `regexp-match' result, and
                       `y' to a match of the sub-regexp part);
  - (...)              other lists - match the elements of a list
                       recursively (can use a dot suffix for a "rest"
                       arguments).

Note that variable names match anything and bind the name to the result,
except when the name was already seen -- where the previously bound
value is used, allowing patterns where some parts should match the same
value.  (A name was `seen' if it was previously used in the pattern
except on different branches of an `or' pattern.)

 (matcher pattern body ...)
  This creates a matcher function, using the given `pattern' which will
  be matched with the list of given arguments on usage.  If the given
  arguments fail to match on an application, an error will be raised.

atching similar to `cond'
 (match x (pattern expr ...) ...)
  This is similar to a `cond' statement but each clause starts with a
  pattern, possibly binding variables for its body.  It also handles
  `else' as a last clause.

 <matcher>
  A class similar to a generic function, that holds matcher functions
  such as the ones created by the `matcher' macro.  It has three slots:
  `name', `default' (either a default value or a function that is
  applied to the arguments to produce the default value), and `matchers'
  (a list of matcher functions).

 (defmatcher (name pattern) body ...)
 (defmatcher0 (name pattern) body ...)
  These macros define a matcher (if not defined yet), create a matcher
  function and add it to the matcher (either at the end (defmatcher) or
  at the beginning (defmatcher0)).

... An amb macro
This is added just because it is too much fun to miss.  To learn about
`amb', look for it in the Help Desk, in the "Teach Yourself Scheme in
Fixnum Days" on-line manual.

 (amb expr ...)
  Execute forms in a nondeterministic way: each form is tried in
  sequence, and if one fails then evaluation continues with the next.
  `(amb)' fails immediately.

 (amb-assert cond)
  Asserts that `cond' is true, fails otherwise.

 (amb-collect expr)
  Evaluate expr, using amb-fail repeatedly until all options are
  exhausted and returns the list of all results.

... Very basic UI - works also in console mode
The following defines some hacked UI functions that works using GRacket
GUI if it is available, or the standard error and input ports otherwise.
The check is done by looking for a GUI global binding.

 *dialog-title*
  This parameter defines the title used for the hacked UI interface.

 (message fmt-string arg ...)
  Like `printf' with a prefix title, or using a message dialog box.

 (ok/cancel? fmt-string arg ...)
 (yes/no? fmt-string arg ...)
  These functions are similar to `message', but they are used to ask an
  "ok/cancel" or a "yes/no" question.  They return a boolean.


