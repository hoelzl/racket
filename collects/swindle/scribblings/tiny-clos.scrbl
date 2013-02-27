#lang scribble/doc
@(require (for-label swindle/tiny-clos))

@title{Swindle Tiny-Clos}

@defmodulelang[swindle/tiny-clos]

This module is the core object system.  It is a heavily hacked version
of the original Tiny-CLOS code from Xerox, but it has been fitted to
Racket, optimized and extended.  See the source file for a lot of
details about how the CLOS magic is created.

[There is one difference between Swindle and Tiny-CLOS: the meta object
hierarchy is assumed to be using only single inheritance, or if there is
multiple inheritance then the built in meta objects should come first to
make the slots allocated in the same place.  This should not be a
problem in realistic situations.]

 ???
  This is Racket's `unspecified' value which is used as the default
  value for unbound slots.  It is provided so you can check if a slot is
  unbound.

...
*** Low level functionality
(These functions should be used with caution, since they make shooting
legs in exotic ways extremely easy.)

 (change-class! object new-class initargs ...)
  This operation changes the class of the given `object' to the given
  `new-class'.  The way this is done is by creating a fresh instance of
  `new-class', then copying all slot values from `object' to the new
  instance for all shared slot names.  Finally, the new instance's set
  of slots is used for the original object with the new class, so it
  preserves its identity.

 (set-instance-proc! object proc)
  This function sets the procedure of an entity object.  It is useful
  only for making new entity classes.

...
*** Basic functionality

 (instance? x)
 (object? x)
  These two are synonyms: a predicate that returns #t for objects that
  are allocated and managed by Swindle.

 (class-of x)
  Return the class object of `x'.  This will either be a Swindle class
  for objects, or a built-in class for other Scheme values.
%allocate-instance, %allocate-entity, %instance-ref, %instance-set! and
class-of are the normal interface, from the rest of the code, to the
low-level memory system.  One thing to take note of is that the protocol
does not allow the user to add low-level instance representations.  I have
never seen a way to make that work.
Note that this implementation of class-of assumes the name of a the
primitive classes that are set up later.

 (slot-ref obj slot)
  Pull out the contents of the slot named `slot' in the given `obj'.
  Note that slot names are usually symbols, but can be other values as
  well.

 (slot-set! obj slot new)
  Change the contents of the `slot' slot of `obj' to the given `new'
  value.

 (set-slot-ref! obj slot new)
  An alias for `slot-set!', to enable using `setf!' on it.

 (slot-bound? object slot)
  Checks if the given `slot' is bound in `object'.  See also `???'
  above.

... Singleton and Struct Specifiers

 (singleton x)
  Returns a singleton specification.  Singletons can be used as type
  specifications that have only one element in them so you can
  specialize methods on unique objects.

  This is actually just a list with the symbol `singleton' in its head
  and the value, but this function uses a hash table to always return
  the same object for the same value.  For example:
    => (singleton 1)
    (singleton 1)
    => (eq? (singleton 1) (singleton 1))
    #t
  but if the input objects are not `eq?', the result isn't either:
    => (eq? (singleton "1") (singleton "1"))
    #f
  Only `eq?' is used to compare objects.

 (singleton? x)
  Determines if something is a singleton specification (which is any
  list with a head containing the symbol `singleton').

 (singleton-value x)
  Pulls out the value of a singleton specification.

...
Also note that Racket struct types are converted to appropriate
Swindle classes.  This way, it is possible to have Swindle generic
functions that work with struct type specializers.

 (struct-type->class struct-type)
  This function is used to convert a struct-type to a corresponding
  Swindle subclass of `<struct>'.  See the Racket manual for details
  on struct types.

...
*** Common accessors

Given that the early version of MAKE is allowed to call accessors on class
metaobjects, the definitions for them come here, before the actual class
definitions, which are coming up right afterwards.
 (class-direct-slots class)
 (class-direct-supers class)
 (class-slots class)
 (class-cpl class)
 (class-name class)
 (class-initializers class)
  Accessors for class objects (look better than using `slot-ref').

 (generic-methods generic)
 (generic-arity generic)
 (generic-name generic)
 (generic-combination generic)
  Accessors for generic function objects.

 (method-specializers method)
 (method-procedure method)
 (method-qualifier method)
 (method-name method)
 (method-arity method)
  Accessors for method objects.  `method-arity' is not really an
  accessor, it is deduced from the arity of the procedure (minus one for
  the `call-next-method' argument).

...
*** Basic classes

 <class>
  This is the "mother of all classes": every Swindle class is an
  instance of `<class>'.
  Slots:
  * direct-supers:  direct superclasses
  * direct-slots:   direct slots, each a list of a name and options
  * cpl:            class precedence list (classes list this to <top>)
  * slots:          all slots (like direct slots)
  * nfields:        number of fields
  * field-initializers: a list of functions to initialize slots
  * getters-n-setters:  an alist of slot-names, getters, and setters
  * name:           class name (usually the defined identifier)
  * initializers:   procedure list that perform additional initializing
  See the `clos' documentation for available class and slot keyword
  arguments and their effect.

 <top>
  This is the "mother of all values": every value is an instance of
  `<top>' (including standard Scheme values).

 <object>
  This is the "mother of all objects": every Swindle object is an
  instance of `<object>'.

 <procedure-class>
  The class of all procedures classes, both standard Scheme procedures
  classes and entity (Swindle procedure objects) classes.  (Note that
  this is a class of *classes*).

 <entity-class>
  The class of entity classes -- generic functions and methods.  An
  entity is a procedural Swindle object, something that you can apply as
  a function but it is still a Swindle object.  Note that this is the
  class of entity *classes* not of entities themselves.

 <function>
  The class of all applicable values: methods, generic functions, and
  standard closures.

 <generic>
  The class of generic functions: objects that contain method objects
  and calls the appropriate ones when applied.
  Slots:
  * methods:     a list of <method> objects
  * arity:       the generic arity (same for all of its methods)
  * name:        generic name
  * combination: a method combination function or #f, see
                 `make-generic-combination' below for details

 <method>
  The class of methods: objects that are similar to Scheme closures,
  except that they have type specifiers attached.  Note that in contrast
  to Tiny CLOS, methods are applicable objects in Swindle -- they check
  supplied argument types when applied.
  Slots:
  * specializers: a list of class (and singleton) specializers
  * procedure:    the function (never call directly!)
  * qualifier:    some qualifier tag, used when applying a generic
  * name:         method name

...
*** Convenience functions

These are some convenience functions -- no new syntax, just function
wrappers for `make' with some class and some slot values.  See `clos'
for a more sophisticated (and convenient) approach.

These are the convenient syntax we expose to the base-level user.
 (make-class direct-supers direct slots)
  Creates a class object -- an instance of <class>.

 (make-generic-function [name/arity])
  Creates a generic function object -- an instance of <generic>.  The
  argument can specify name and/or arguments number.

 (make-method specializers procedure)
  Creates a method object -- an instance of <method>, using the given
  specializer list and procedure.  The procedure should have a first
  argument which is being used to access a `call-next-method' call.

 (no-next-method generic method [args ...])
 (no-applicable-method generic [args ...])
  These two generic functions are equivalents to the ones in CL.  The
  first one is applied on a generic and a method in case there was no
  next method and `call-next-method' was used.  The second is used when
  a generic was called but no matching primary methods were found.  The
  only difference is that in Swindle methods can be applied directly,
  and if `call-next-method' is used, then `no-next-method' gets `#f' for
  the generic argument.

... Generics in the instance initialization protocol
The following generic functions are used as part of the protocol of
instantiating an instance, and some are used specifically to instantiate
class objects.

The instance structure protocol.
 (allocate-instance class initargs)
  This generic function is called to allocate an instance of a class.
  It is applied on the class object, and is expected to return the new
  instance object of that class.

 (initialize instance initargs)
  This generic is called to initialize an instance.  It is applied on
  the newly allocated object and the given initargs, and is not expected
  to return any meaningful value -- only do some side effects on the
  instance to initialize it.  When overriding this for a some class, it
  is not a good idea to skip `call-next-method' since it is responsible
  for initializing slot values.

 (compute-getter-and-setter class slot allocator)
  This generic is used to get a getter and setter functions for a given
  slot.  It is passed the class object, the slot information (a list of
  a slot name and options), and an allocator function.  The allocator is
  a function that gets an initializer function and returns an index
  position for the new slot.  The return value should be a list of two
  elements -- a getter and a setter functions.

The class initialization protocol.
 (compute-cpl class)
  This generic is used to get the class-precedence-list for a class
  object.  The standard <class> object uses the `compute-std-cpl' (see
  in the code) which flattens the class ancestors using a topological
  sort that resolve ambiguities left-to-right.

 (compute-slots class)
  This generic is used to compute all slot information for a given
  class, after its precedence list has been computed.  The standard
  <class> collects information from all preceding classes.

 (compute-apply-method method)
  This generic is used to compute the procedure that will get executed
  when a method is applied directly.

... Generics in the generic invocation protocol
These generics are used for invocation of generic functions.  See the
code to see how this circularity is achieved.

 ((compute-apply-generic generic) args ...)
  This generic is used to compute the object (a closure) that is
  actually applied to execute the generic call.  The standard version
  uses `compute-method' and `compute-apply-methods' below, and caches
  the result.

 (compute-methods generic args)
  Computes the methods that should be applied for this generic
  invocation with args.  The standard code filters applicable methods
  and sorts them according to their specificness.  The return value is
  expected to depend only on the types of the arguments (and values if
  there are singleton specializers).

 ((compute-method-more-specific? generic) mthd1 mthd2 args)
  Get a generic and return a function that gets two methods and a list
  of arguments and decide which of the two methods is more specific.
  This decision should only be based on the argument types, or values
  only in case of singletons.

 ((compute-apply-methods generic methods) args ...)
  Gets a generic and returns a function that gets the given arguments
  for this call.  This function which it returns is the combination of
  all given methods.  The standard one arranges them by default using
  the `call-next-method' argument that methods have.  Swindle extends
  this with qualified methods and applies `before', `after', and
  `around' methods in a similar way to CLOS: first the `around' methods
  are applied (and they usually call their `call-next-method' to
  continue but can return a different value), then all the `before'
  methods are applied (with no `call-next-method'), then all `primary'
  methods as usual (remembering the return value), and finally the
  `after' methods (similar to the `before', but in reverse specificness
  order).  If the generic has a `combination' slot value, then it is a
  procedure that is used to combine the primary methods, but the
  auxiliary ones are still applied in the same way.  This is unlike CLOS
  where the standard combinations run only `around' methods, and there
  is generally more control with method combinations, but in Swindle
  `compute-apply-methods' should be overridden for this.  See
  `make-generic-combination' for details about method combinations.

 (add-method generic method)
  This generic function is called to add a method to a generic function
  object.  This is an other change from the original Tiny CLOS where it
  was a normal function.

 (((make-generic-combination keys...) generic) tail args)
  This function can be used to construct simple method combinations that
  can be used with the `combination' slot of generic functions.  The
  combination itself is a function that gets a generic and returns a
  function that gets a list of method/procedure pairs (for optimization
  the method-procedures are pre taken) and the arguments and performs
  the call -- but this is only interesting if there's any need to
  implement a method combination directly, otherwise, the
  `make-generic-combination' interface should allow enough freedom.
  Note that when a method combination is used, `around', `before', and
  `after' are called around the primary call as usual, but the primaries
  are never called with a valid `call-next-method' argument.

  The keyword arguments that can be taken determine the behavior of this
  combination.  Overall, it is roughly like a customizable version of a
  fold operation on the method calls.
  * :init
    - The initial value for this computation.  Defaults to null.
  * :combine
    - A function to be called on a method call result and the old value,
      and produces a new value.  The default is `cons', which with an
      initial null value will collect the results into a reversed list.
  * :process-methods
    - A function that can be called on the initial list of
      method/procedure pairs to change it -- for example, it can be
      reversed to apply the methods from the least specific to the most
      specific.  No default.
  * :process-result
    - A function that can be called on the final resulting value to
      produce the actual return value.  For example, it can reverse back
      a list of accumulated values.  No default.
  * :control
    - If this parameter is specified, then the `:combine' argument is
      ignored.  The value given to `:control' should be a function of
      four arguments:
      1. a `loop' function that should be called on some new value and
         some new tail;
      2. a `val' argument that gets the current accumulated value;
      3. a `this' thunk that can be called to apply the current method
         and return its result;
      4. a `tail' value that holds the rest of the method/procedure list
         which can be sent to `loop'.
      It should be clear now, that a `:control' argument can have a lot
      of control on the computation, it can abort, change arbitrary
      values and skip calling methods.  Note that if it won't call
      `loop' with an empty list, then a `:process-result' function will
      not be used as well.  See the pre-defined combinations in the
      source code to see examples of using this function.

 generic-+-combination
 generic-list-combination
 generic-min-combination
 generic-max-combination
 generic-append-combination
 generic-append!-combination
 generic-begin-combination
 generic-and-combination
 generic-or-combination
  These are all functions that can be used as a `combination' value for
  a generic function.  They work in the same way as the standard method
  combinations of CL.  Most of them do the obvious thing based on some
  function to combine the result.  The `begin' combination simply
  executes all methods one by one and returns the last value, the `and'
  and `or' combinations will call them one by one until a false or true
  result is returned.  The source of these can be used as templates for
  defining more combinations.

...
*** More class functionality
(In the following, a `class' can be a class, a singleton specifier, or a
struct type.)

 (subclass? class1 class2)
  Is `class1' a subclass of `class2'?

 (instance-of? x class)
  Checks if `x' is an instance of `class' (or one of its subclasses).

 (specializer? x)
  Determines whether `x' is a class, a singleton, or a struct-type.

 (more-specific? class1 class2 x)
  Is `class1' more specific than `class2' for the given value?

... Swindle Customization Parameters

 *default-method-class*
 *default-generic-class*
 *default-class-class*
 *default-entityclass-class*
  These parameters specify default classes for the many constructor
  macros in `clos'.

n automatic superclass for all classes -- turned off for the builtins below
 *default-object-class*
  This parameter contains a value which is automatically made a
  superclass for all classes.  Defaults to `<object>'.

 *make-safely*
  Setting this parameter to #t will make Swindle perform sanity checks
  on given initargs for creating an object.  This will make things
  easier for debugging, but also slower.  Defaults to `#f'.  Note that
  the sanity checks are done in `initialize'.
his could be in `make', but `defclass' will call that with no slots to make
he object and then call `initialize' with all arguments to actually create
he class.

... Creating Instances
 (make class initargs ...)
  Create an instance of `class', which can be any Swindle class (except
  for some special top-level classes and built-in classes).

  See the `Object Initialization Protocol' below for a description of
  generic functions that are involved in creating a Swindle object.

 (rec-make (name class arg ...) ...)
  This is similar to:

    (letrec ([name (make class arg ...)] ...)
      (values name ...))

  except that the names are first bound to allocated instances with no
  initargs, and then they are initialized with all these bindings.  This
  is useful for situations where creating some instances needs other
  instances as values.  One sample usage is the way `defclass' makes the
  class binding available for slot specifications like `:type'.  Note
  that this is a special form, which invokes `allocate-instance' and
  `initialize' directly, so specializing `make' on some input will not
  change the way `rec-make' works.

... Built-in Classes

 <primitive-class>
  The class of all built-on classes.

 <builtin>
  The superclass of all built-in classes.

 <sequence>
 <mutable>
 <immutable>
 <pair>
 <mutable-pair>
 <mpair>
 <immutable-pair>
 <list>
 <nonempty-list>
 <null>
 <vector>
 <char>
 <string-like>
 <mutable-string-like>
 <immutable-string-like>
 <string>
 <mutable-string>
 <immutable-string>
 <bytes>
 <mutable-bytes>
 <immutable-bytes>
 <path>
 <symbol>
 <keyword>
 <real-keyword>
 <boolean>
 <number>
 <exact>
 <inexact>
 <complex>
 <real>
 <rational>
 <integer>
 <exact-complex>
 <inexact-complex>
 <exact-real>
 <inexact-real>
 <exact-rational>
 <inexact-rational>
 <exact-integer>
 <inexact-integer>
 <end-of-file>
 <port>
 <input-port>
 <output-port>
 <stream-port>
 <input-stream-port>
 <output-stream-port>
 <void>
 <box>
 <weak-box>
 <regexp>
 <byte-regexp>
 <parameter>
 <promise>
 <exn>
 <exn:fail>
 <exn:break>
 <semaphore>
 <hash-table>
 <subprocess>
 <thread>
 <syntax>
 <identifier-syntax>
 <namespace>
 <custodian>
 <tcp-listener>
 <security-guard>
 <will-executor>
 <struct-type>
 <inspector>
 <pseudo-random-generator>
 <compiled-expression>
 <unknown-primitive>
  These classes represent built-in objects.  See the class hierarchy
  below for a complete description of the relations between these
  classes.
 <struct>
 <opaque-struct>
  These are also classes for built-in objects, but they are classes for
  Racket structs -- which can be used like Swindle classes since they
  will get converted to appropriate Swindle subclasses of `<struct>'.
  `<opaque-struct>' is a class of structs that are hidden -- see the
  documentation for `struct-info' and the `skipped?' result.  Note that
  structs can be used as long as they can be inspected -- otherwise, we
  can't even know that they are structs with `struct?' (this means that
  <opaque-struct> can only appear in the cpl of a struct class that
  inherits from a struct which is not under the current inspector).

 <procedure>
  The class of all Scheme procedures.

 <primitive-procedure>
  The class of all primitive Racket procedures.

 (builtin? x)
 (function? x)
 (generic? x)
 (method? x)
  Predicates for instances of <builtin>, <function>, <generic>, and
  <method>.

... Class Hierarchy

In the following, every class's class is specified after a colon.  Also,
some classes appear in more than once place due to multiple-inheritance.

  <top> : <class>
    <object> : <class>
      <class> : <class>
        <procedure-class> : <class>
          <entity-class> : <class>
        <primitive-class> : <class>
      <generic> : <entity-class>
      <method> : <entity-class>
    <function> : <class>
      <generic> : <entity-class>
      <method> : <entity-class>
      <procedure> : <procedure-class>
        <primitive-procedure> : <procedure-class>
    <builtin> : <class>
      <sequence> : <primitive-class>
        <pair> : <primitive-class>
          <mutable-pair> : <primitive-class>
          <mpair> : <primitive-class>  ; alias for <mutable-pair>
          <immutable-pair> : <primitive-class>
          <nonempty-list> : <primitive-class>
        <list> : <primitive-class>
          <nonempty-list> : <primitive-class>
          <null> : <primitive-class>
        <vector> : <primitive-class>
        <string-like> : <primitive-class>
          <string> : <primitive-class>
            <mutable-string> : <primitive-class>
            <immutable-string> : <primitive-class>
          <bytes> : <primitive-class>
            <mutable-bytes> : <primitive-class>
            <immutable-bytes> : <primitive-class>
          <path> : <primitive-class>
      <mutable> : <primitive-class>
        <mutable-pair> : <primitive-class>
        <mpair> : <primitive-class>  ; alias for <mutable-pair>
        <mutable-string-like> : <primitive-class>
          <mutable-string> : <primitive-class>
          <mutable-bytes> : <primitive-class>
        <vector>
        <box>
      <immutable> : <primitive-class>
        <list> : <primitive-class>
        <pair> : <primitive-class>
        <immutable-string-like> : <primitive-class>
          <immutable-string> : <primitive-class>
          <immutable-bytes> : <primitive-class>
          <path> : <primitive-class>
      <char> : <primitive-class>
      <symbol> : <primitive-class>
        <keyword> : <primitive-class>
      <real-keyword> : <primitive-class>
      <boolean> : <primitive-class>
      <number> : <primitive-class>
        <complex> : <primitive-class>
          <exact-complex> : <primitive-class>
          <inexact-complex> : <primitive-class>
          <real> : <primitive-class>
            <exact-real> : <primitive-class>
            <inexact-real> : <primitive-class>
            <rational> : <primitive-class>
              <integer> : <primitive-class>
              <exact-rational> : <primitive-class>
              <inexact-rational> : <primitive-class>
                <exact-integer> : <primitive-class>
                <inexact-integer> : <primitive-class>
        <exact> : <primitive-class>
          <exact-complex> : <primitive-class>
            <exact-real> : <primitive-class>
              <exact-rational> : <primitive-class>
                <exact-integer> : <primitive-class>
        <inexact> : <primitive-class>
          <inexact-complex> : <primitive-class>
            <inexact-real> : <primitive-class>
              <inexact-rational> : <primitive-class>
                <inexact-integer> : <primitive-class>
      <end-of-file> : <primitive-class>
      <port> : <primitive-class>
        <input-port> : <primitive-class>
          <input-stream-port> : <primitive-class>
        <output-port> : <primitive-class>
          <output-stream-port> : <primitive-class>
        <stream-port> : <primitive-class>
          <input-stream-port> : <primitive-class>
          <output-stream-port> : <primitive-class>
      <void> : <primitive-class>
      <box> : <primitive-class>
        <weak-box> : <primitive-class>
      <regexp> : <primitive-class>
      <byte-regexp> : <primitive-class>
      <parameter> : <primitive-class>
      <promise> : <primitive-class>
      <exn> : <primitive-class>
        <exn:fail> : <primitive-class>
        <exn:break> : <primitive-class>
      <semaphore> : <primitive-class>
      <hash-table> : <primitive-class>
      <subprocess> : <primitive-class>
      <thread> : <primitive-class>
      <syntax> : <primitive-class>
        <identifier-syntax> : <primitive-class>
      <namespace> : <primitive-class>
      <custodian> : <primitive-class>
      <tcp-listener> : <primitive-class>
      <security-guard> : <primitive-class>
      <will-executor> : <primitive-class>
      <inspector> : <primitive-class>
      <pseudo-random-generator> : <primitive-class>
      <compiled-expression> : <primitive-class>
      <unknown-primitive> : <primitive-class>
      <procedure> : <procedure-class>
        <primitive-procedure> : <procedure-class>
      <struct> : <primitive-class>
        <opaque-struct> : <primitive-class>
        ... struct type classes ...

... Object Initialization Protocol
This is the initialization protocol.  All of these are generic
functions (unlike the original Tiny CLOS).  See the individual
descriptions above for more details.

  make
    allocate-instance
    initialize
  class initialization only:
    compute-cpl
    compute-slots
    compute-getter-and-setter
  method initialization only:
    compute-apply-method
  add-method
    compute-apply-generic
      compute-methods
        compute-method-more-specific?
      compute-apply-methods
