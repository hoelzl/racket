#lang scribble/doc
@(require (for-label swindle/clos))

@title{Swindle Clos}

@defmodulelang[swindle/clos]

This module contains only syntax definitions, which makes Swindle closer
to CLOS -- making the object system much more convenient to use.

... Generic macros

 (generic)
| (generic name initargs ...)
| (generic name (arg ...) initargs ...)
  Create a generic function object (an instance of the
  `*default-generic-class*' parameter).  The first form uses the default
  name given by the syntactical context, the second one gets an explicit
  name and the third also gets a list of arguments which is used to
  count the required number of arguments.  If there is no argument list
  to count, the first method that gets added will set this number.  The
  two last forms allow initargs to be passed to the <generic> instance
  creation, for example, to specify a `:combination' argument.  (The
  first form does not allow keywords, since a keyword would be taken as
  the name.)

 (defgeneric name (arg ...) initargs ...)
| (defgeneric (name arg ...) initargs ...)
| (defgeneric name initargs ...)
  This form defines a generic function using the `generic' syntax given
  above.  The last form doesn't specify a number of arguments.  Some
  extra `initargs' can be specified too but they are needed mainly for a
  `:combination' argument.

... Method macros

 (call-next-method [args ...]) [*local*]
 (next-method?) [*local*]
  These are bindings which are available only in method bodies.
  `call-next-method' will invoke the next method in a generic invocation
  sequence if any.  If arguments are given to `call-next-method', it
  will change the arguments for the next method -- but this is done when
  the methods are already filtered and sorted, so the new arguments
  should always be consistent with the old types.  If there are no
  methods left, or when calling a method directly, or when a before or
  after method is used, the `no-next-method' generic will be used --
  normally resulting in an error.  `next-method?' returns `#t' if there
  is another method ready to be called.

 (method (arg ...) body ...)
 (named-method name (arg ...) body ...)
 (qualified-method qualifier (arg ...) body ...)
  These forms are all similar variants to create a method object (and
  instance of the `*default-method-class*' parameter).  A method looks
  very similar to a lambda expression, except that the an argument can
  be a of the form `[arg spec]' where `spec' is a specializer -- either
  a class or a singleton specifier (the square brackets are equivalent
  to round parens, just make the code more readable).  Also, an argument
  can have the form of `[arg = val]' which is shorthand for specifying
  `[arg (singleton val)]'.  In case of a simple argument, <top> is
  always used as a specializer, but this processing stops as soon as a
  &-keyword is encountered.  The `named-method' form is used to provide
  an explicit name (which can be used to call itself recursively) , and
  `qualified-method' is used to provide an explicit qualifier (which
  should be one of the standard qualifiers (:primary, :around, :before,
  or :after) when using the standard <method> and <generic> classes).

  The resulting method can be added to a generic and these specializers
  will be used when filtering applicable methods, or it can be used by
  itself and the specializers will be used to check the arguments.  This
  makes it easy to use `method' instead of `lambda' to get some type
  information, but note that the result is going to run slower since the
  type check only takes time but cannot be used by Racket to optimize
  the code.

  Note that the specializer argument are evaluated normally, which means
  that anything can be used, even something like:
    (let ([x (list <string> <integer>)])
      (method ([x (2nd x)] [y = (+ 2 3)]) (+ x y)))

 (-defmethod-create-generics- [#t/#f])
  This is a syntax parameter (see above) holding a boolean.  When this
  is set to `#t' (the default), then the `defmethod' form below will try
  to detect when the first definition happens and automatic add a
  `defgeneric' form to define the object as a generic.  A safer but less
  convenient approach would be to set this to `#f' and always do an
  explicit `defgeneric'.

 (defmethod name [qualifier] (arg ...) body ...)
| (defmethod [qualifier] (name arg ...) body ...)
  This form is used to define a method object using `method' and its
  variants above.  A qualifier (a :keyword) can be specified anywhere
  before the argument list, and the name can be either specified before
  the arguments (Lisp style) or with the arguments (Scheme style).
  Depending on `-defmethod-create-generics-' (see above), this form
  might add a `defgeneric' form to define the given `name' as a generic
  object, and then add the created method.  The created method is
  attached to the generic in any case, which makes the name of this form
  a little misleading since it is not always defining a variable value.
  In a local definition context, this should do the right thing as long
  as `defmethod' or `defgeneric' is used to define the method (but note
  that using a local generic function, is very inefficient) -- for
  example, both of these work (defining a local generic):
    (define (f)
      (defgeneric foo)
      (defmethod (foo [x <c1>]) 1)
      (defmethod (foo [x <c2>]) 2)
      3)
    (define (f)
      (defmethod (foo [x <c1>]) 1)
      (defmethod (foo [x <c2>]) 2)
      3)
  but this fails because the first `defmethod' doesn't know that it is
  already defined:
    (define (f)
      (define foo (generic foo))
      (defmethod (foo [x c1]) 1)
      (defmethod (foo [x c1]) 2)
      3)
  second "but" -- this:
    (define (f)
      (define foo (generic foo))
      blah
      (defmethod (foo [x <c1>]) 1)
      (defmethod (foo [x <c2>]) 2)
      3)
  works because a `defmethod' in an expression context is always the
  same as `add-method'.

 (beforemethod ...)
 (aftermethod ...)
 (aroundmethod ...)
 (defbeforemethod ...)
 (defaftermethod ...)
 (defaroundmethod ...)
  These forms are shorthands that will generate a qualified method using
  one of the standard qualifiers.

... Class macros

 (class [name] (super ...) slot ... class-initarg ...)
  Create a class object (an instance of the `*default-class-class*'
  parameter).  An explicit name can optionally be specified explicitly.
  The list of superclasses are evaluated normally, so they can be any
  expression (as with the `method' forms).  Each slot can be either a
  symbol, which will be used as the slot name, or a list that begins
  with a symbol and continues with a keyword-argument option list.
  Finally, more initargs for the class generation can be provided.  See
  the `defclass' forms below for an explanation on the available slot
  option and class initargs.  If a name is given, then `rec-make' is
  used, see that for a description.

 (entityclass [name] (super) slot ... class-initarg ...)
  Same as the `class' form, but creates an entity class object (an
  instance of the `*default-entityclass-class*' parameter).

 (-defclass-auto-initargs- [#f/initargs])
  This is a syntax parameter (see above) holding either `#f' or an
  initargs list .  If it is not `#f', `defclass' below will add its
  contents to the end of the given initargs (so user supplied arguments
  can override them).  The default is `#f'.

 (-defclass-autoaccessors-naming- [naming-keyword])
  This syntax parameter holds a keyword symbol that is used in the
  `defclass' for the `:autoaccessors' if it is specified as `#t' or if
  it used due to `:auto'.  See the description of the `:autoaccessors'
  option below for possible values.  The default is `:class-slot'.

 (-defclass-accessor-mode- [mode-keyword])
  This syntax parameter holds a keyword symbol that is used in the
  `defclass' for the way accessors, readers, and writers are generated.
  It can be `:defmethod' for using `defmethod', `:defgeneric' for using
  `defgeneric' and then `add-method', `:add-method' for using
  `add-method', `:method' for defining an independent method, or
  `:procedure' for defining a simple Scheme procedure.  The default is
  `:defmethod.  This default is usually fine, but a situation where this
  is important is if the syntax parameter `-defmethod-create-generics-'
  is set to `#f' so a `defmethod' requires a prior `defgeneric' so a
  defclass will not work unless the generic functions are defined in
  advance.

 (defclass name (super ...) slot ... class-initarg ...)
  This form uses the `class' form above to define a new class.  See the
  `class' form for the syntax.  Note that slot-options that are not
  compile-time ones (method names) are accumulated according to the
  class precedence list.

  Available slot options are:
  * :initarg keyword
    Use `keyword' in `make' to provide a value for this slot.
  * :initializer func
    Use the given function to initialize the slot -- either a thunk or a
    function that will be applied on the initargs given to `make'.
  * :initvalue value
    Use `value' as the default for this slot.
  * :reader name
    Define `name' (an unquoted symbol) as a reader method for this slot.
  * :writer name
    Define `name' (an unquoted symbol) as a writer method for this slot.
  * :accessor name
    Define `name' (an unquoted symbol) as an accessor method for this
    slot -- this means that two methods are defined: `name' and
    `set-name!'.
  * :type type
    Restrict this slot value to objects of the given `type'.
  * :lock { #t | #f | value }
    If specified and non-`#f', then this slot is locked.  `#t' locks it
    permanently, but a different value works as a key: they allow setting
    the slot by using cons of the key and the value to set.
  * :allocation { :class | :instance }
    Specify that this slot is a normal one (`:instance', the default),
    or allocated per class (`:class').
  The specific way of creating helper methods (for readers, writers, and
  accessors) is determined by `-defclass-accessor-mode-' (see above).

  Available class options (in addition to normal ones that initialize
  the class slots like `:name', `:direct-slots', `:direct-supers') are:
  * :metaclass class
    create a class object which is an instance of the `class'
    meta-class (this means that an instance of the given meta-class
    should be used for creating the new class).
  * :autoinitargs { #t | #f }
    if set to `#t', make the class definition automatically generate
    initarg keywords from the slot names.  (The keywords have the same
    name as the slots, eg `:foo'.)
  * :autoaccessors { #f | #t | :class-slot | :slot }
    if set to non-`#f', generate accessor methods automatically --
    either using the classname "-" slotname convention (`:class-slot')
    or just the slotname (`:slot').  If it is `#t' (or turned on by
    `:auto') then the default naming style is taken from the
    `-defclass-autoaccessors-naming-' syntax parameter.  Note that for
    this, and other external object definitions (`:automaker' and
    `:autopred'), the class name is stripped of a surrounding "<>"s if
    any.
  * :automaker { #f | #t }
    automatically creates a `maker' function using the "make-" classname
    naming convention.  The maker function is applied on arguments and
    keyword-values -- if there are n slots, then arguments after the
    first n are passed to `make' to create the instance, then the first
    n are `slot-set!'ed into the n slots.  This means that it can get
    any number of arguments, and usually there is no point in additional
    keyword values (since if they initialize slots, their values will
    get overridden anyway).  It also means that the order of the
    arguments depend on the *complete* list of the class's slots (as
    given by `class-slots'), so use caution when doing multiple
    inheritance (actually, in that case it is probably better to avoid
    these makers anyway).
  * :autopred { #f | #t }
    automatically create a predicate function using the `classname "?"'
    naming convention.
  * :default-slot-options { #f | '(keyword ...) }
    if specified as a quoted list, then slot descriptions are modified
    so the first arguments are taken as values to the specified
    keywords.  For example, if it is `'(:type :initvalue)' then a slot
    description can have a single argument for `:type' after the slot
    name, a second argument for `:initvalue', and the rest can be more
    standard keyword-values.  This is best set with
    `-defclass-auto-initargs-'
  * :auto { #f | #t }
    if specified as `#t', then all automatic behavior available above is
    turned on.
he following option is added in extra.rkt
  * :printer { #f | #t | procedure }
    if given, install a printer function.  `#t' means install the
    `print-object-with-slots' function from "clos.rkt", otherwise, it is
    expected to be a function that gets an object, an escape boolean
    flag an an optional port (i.e, 2 or more arguments), and prints the
    object on the class using the escape flag to select `display'-style
    (`#f') or `write'-style (#t).

  Note that the class object is made by `class' with a name, so it is
  possible to use the class itself as the value of `:type' properties
  for a recursive class.

  Whenever the classname is used, it is taken from the defined name,
  without a surrounding "<>"s if any.  Note that some of these options
  are processed at compile time (all method names and auto-generation of
  methods).

 (defentityclass name (super ...) slot ... class-initarg ...)
  The same as `defclass', but for entity classes.

...
*** Auto provide forms

 (defgeneric* ...)
 (defclass* ...)
 (defentityclass* ...)
  These forms are defined as the original version, except that the
  defined variable is automatically provided (made using
  `make-provide-syntax' above).  Note that there is no version for
  `defmethod' since it should not be used where a single definition
  place is needed -- and it wouldn't make sense to have multiple
  `provide' forms for every `defmethod*' occurrence.  Note that
  `defclass*' provides only the class identifier and not any
  automatically generated ones (accessors etc).

