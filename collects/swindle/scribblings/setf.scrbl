#lang scribble/doc
@(require (for-label swindle/setf))

@title{Swindle Setf}

@defmodulelang[swindle/setf]

This module provides the forms `setf!', `psetf!', and `setf!-values' for
generic setters, much like CL's `setf', and `psetf', and a form similar
to Racket's `set!-values'.  Note that when these are later re-exported
(by `turbo'), they are renamed as `set!', `pset!', and `set!-values'
(overriding the built-in `set!' and `set!-values').  Also, note that
this just defines the basic functionality, the `misc' module defines
many common setters.

 (setf! place value ...)
  Expand `(setf! (foo ...) v)' to `(set-foo! ... v)'.  The generated
  `set-foo!' identifier has the same syntax context as `foo', which
  means that to use this for some `foo' you need to define `set-foo!'
  either as a function or a syntax in the same definition context of
  `foo'.  The nice feature that comes out of this and the syntax system
  is that examples like the following work as expected:
    (let ([foo mcar] [set-foo! set-mcar!]) (setf! (foo a) 11))

  `place' gets expanded before this processing is done so macros work
  properly.  If the place is not a form, then this will just use the
  standard `set!'.

  Another extension of the original `set!' is that it allows changing
  several places in sequence -- `(setf! x a y b)' will set `x' to `a'
  and then set `y' to `b'.

 (psetf! place value ...)
  This is very similar to `setf!' above, except that the change to the
  places is done *simultaneously*.  For example, `(setf! x y y x)'
  switches the values of the two variables.

 (setf!-values (place ...) expr)
  This is a version of `setf!', that works with multiple values.  `expr'
  is expected to evaluate to the correct number of values, and these are
  then put into the specified places which can be an place suited to
  `setf!'.  Note that no duplication of identifiers is checked, if an
  identifier appears more than once then it will have the last assigned
  value.

 (set-values! places ... values-expr)
 (set-list! places ... list-expr)
 (set-vector! places ... vector-expr)
  These are defined as special forms that use `setf!-values' to set the
  given places to the appropriate components of the third form.  This
  allows foing the following:
    => (define (values a b c) (values 1 2 3))
    => (setf! (values a b c) (values 11 22 33))
    => (list a b c)
    (11 22 33)
    => (setf! (list a b c) (list 111 222 333))
    => (list a b c)
    (111 222 333)
    => (setf! (list a b c) (list 1111 2222 3333))
    => (list a b c)
    (1111 2222 3333)
  Furthermore, since the individual setting of each place is eventually
  done with `setf!', then this can be used recursively:
    => (set! (list a (vector b) (vector c c)) '(2 #(3) #(4 5)))
    => (list a b c)
    (2 3 5)

 (shift! place ... newvalue)
  This is similar to CL's `shiftf' -- it is roughly equivalent to
    (begin0 place1
            (psetf! place1 place2
                    place2 place3
                    ...
                    placen newvalue))
  except that it avoids evaluating index subforms twice, for example:
    => (let ([foo (lambda (x) (printf ">>> ~s\n" x) x)]
             [a '(1)] [b '(2)])
         (list (shift! (car (foo a)) (car (foo b)) 3) a b))
    >>> (1)
    >>> (2)
    (1 (2) (3))

 (rotate! place ...)
  This is similar to CL's `rotatef' -- it is roughly equivalent to
    (psetf! place1 place2
            place2 place3
            ...
            placen place1)
  except that it avoids evaluating index subforms twice.

 (inc! place [delta])
 (dec! place [delta])
 (push! x place)
 (pop! place)
  These are some simple usages of `setf!'.  Note that they also avoid
  evaluating any indexes twice.

