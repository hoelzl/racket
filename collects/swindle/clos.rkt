;;; Written by Eli Barzilay: Maze is Life!  (eli@barzilay.org)

#lang s-exp swindle/turbo

(require swindle/tiny-clos)
(provide (all-from swindle/tiny-clos))

;;; ---------------------------------------------------------------------------
;;; General helpers

(defsyntax (args-arity stx)
  (syntax-case stx ()
    [(_ args)
     (let loop ([args #'args] [n 0])
       (syntax-case args ()
         [(a . more)
          (or (not (identifier? #'a))
              ;; stop at &-keyword
              (let ([sym (syntax-e #'a)])
                (or (eq? sym '||)
                    (not (eq? #\& (string-ref (symbol->string sym) 0))))))
          (loop #'more (add1 n))]
         [() (datum->syntax-object stx n stx)]
         [_  (quasisyntax/loc stx (make-arity-at-least #,n))]))]))

;;; ---------------------------------------------------------------------------
;;; Generic macros

(defsyntax* (generic stx)
  (syntax-case stx ()
    [(_)
     #`(make (*default-generic-class*) :name '#,(syntax-local-name))]
    [(_ name) (identifier? #'name)
     #'(make (*default-generic-class*) :name 'name)]
    [(_ name initarg initargs ...)
     (and (identifier? #'name) (syntax-keyword? #'initarg))
     #'(make (*default-generic-class*) initarg initargs ... :name 'name)]
    [(_ name args) (identifier? #'name)
     #`(make (*default-generic-class*)
             :name 'name :arity (args-arity args))]
    [(_ name args initarg initargs ...)
     (and (identifier? #'name) (syntax-keyword? #'initarg))
     #`(make (*default-generic-class*)
             initarg initargs ... :name 'name :arity (args-arity args))]))

(defsyntax* (defgeneric stx)
  (let* ([ctx (syntax-local-context)]
         [ctx (cond [(pair? ctx) (car ctx)]
                    [(eq? ctx 'top-level) ctx]
                    [else #f])]
         [mark (lambda (name)
                 ((syntax-local-value #'generic-contexts-defined?) name ctx))])
    (syntax-case stx ()
      [(_ name args initargs ...) (identifier? #'name)
       (begin (mark #'name) #'(define name (generic name args initargs ...)))]
      [(_ (name . args) initargs ...) (identifier? #'name)
       (begin (mark #'name) #'(define name (generic name args initargs ...)))]
      [(_ name initargs ...) (identifier? #'name)
       (begin (mark #'name) #'(define name (generic name initargs ...)))])))

;; returns #t if an identifier id in context ctx is already defined as a genric
;; (used by defmethod to detect when it should expand to an add-method)
(define-syntax generic-contexts-defined?
  (let ([table (make-hash-table 'weak)])
    (lambda (id ctx)
      ;; ctx is either the first element of (syntax-local-context) or
      ;; 'top-level.  Note that top-level identifiers in different modules
      ;; should not be `module-identifier=?' (eg, `eval' takes care of this).
      (let ([cs (hash-table-get table ctx (lambda () '()))])
        (or (ormap (lambda (c) (module-identifier=? id c)) cs) ; defined
            (begin (hash-table-put! table ctx (cons id cs)) ; undefined
                   #f))))))

;;; ---------------------------------------------------------------------------
;;; Method macros

(defsyntax (make-method-specs/initargs stx)
  (syntax-case stx ()
    [(_ name args0 body . more)
     (let loop ([args #'args0] [specializers '()] [arguments '()])
       (syntax-case args (=)
         [([arg = val] . rest)
          (loop #'rest
                (cons #'(singleton val) specializers) (cons #'arg arguments))]
         [([arg type] . rest)
          (loop #'rest (cons #'type specializers) (cons #'arg arguments))]
         [([arg] . rest)
          (loop #'rest (cons #'<top> specializers) (cons #'arg arguments))]
         [(arg . rest)
          (and (identifier? #'arg)
               ;; stop at &-keyword
               (let ([sym (syntax-e #'arg)])
                 (or (eq? sym '||)
                     (not (eq? #\& (string-ref (symbol->string sym) 0))))))
          (loop #'rest (cons #'<top> specializers) (cons #'arg arguments))]
         [_ ; both null and rest argument
          (let* ([specializers (reverse specializers)]
                 [arguments    (reverse arguments)]
                 [name-e       (syntax-e #'name)]
                 [cnm (datum->syntax-object
                       #'args0 'call-next-method #'args0)])
            (unless (null? (syntax-e args))
              (set! arguments
                    (if (null? arguments) args (append arguments args))))
            (let ([makeit
                   (quasisyntax/loc stx
                     (make (*default-method-class*)
                           :specializers (list #,@specializers)
                           :name '#,(if name-e #'name (syntax-local-name))
                           :procedure
                           (lambda (#,cnm . #,arguments)
                             ;; See "Trick" in tiny-clos.rkt
                             ;; -- use a syntax to not do this unless needed
                             (letsyntax
                                 ([#,(datum->syntax-object
                                      #'args0 'next-method? #'args0)
                                   (lambda (stx)
                                     (syntax-case stx ()
                                       [(__) #'(not (eq? '*no-next-method*
                                                         (object-name #,cnm)))]
                                       [(__ . xs)
                                        #'((named-lambda next-method? () 1)
                                           . xs)]
                                       [__
                                        #'(named-lambda next-method? ()
                                            (not
                                             (eq? '*no-next-method*
                                                  (object-name #,cnm))))]))])
                               . body))
                           . more))])
              (if name-e
                (quasisyntax/loc stx (letrec ([name #,makeit]) name))
                makeit)))]))]))

(defsubst* (method args body0 body ...)
  (make-method-specs/initargs #f args (body0 body ...)))
(defsubst* (named-method name args body0 body ...)
  (make-method-specs/initargs name args (body0 body ...)))
(defsubst* (qualified-method qualifier args body0 body ...)
  (make-method-specs/initargs #f args (body0 body ...) :qualifier qualifier))

(define-syntax-parameter* -defmethod-create-generics- #t)

(defsyntax (method-def-adder stx)
  (syntax-case stx ()
    [(_ qualifier name args body ...) (identifier? #'name)
     ;; always make it with no name so add-method will add it
     (with-syntax ([method-make (syntax/loc stx
                                  (qualified-method qualifier args body ...))])
       (let ([ctx (syntax-local-context)])
         (cond
          [(or ; if:
            ;; not enabled
            (not (syntax-e ((syntax-local-value
                             #'-defmethod-create-generics-))))
            ;; expression position -- same as using add-method
            (eq? 'expression ctx)
            ;; defined symbol or second module binding
            (identifier-binding #'name)
            ;; already defined in this local context or top-level
            (let ([ctx (cond [(pair? ctx) (car ctx)]
                             [(eq? ctx 'top-level) ctx]
                             [else #f])])
              (and ctx ((syntax-local-value #'generic-contexts-defined?)
                        #'name ctx))))
           ;; then use add-method
           ;; (printf ">>> ~s: add\n" (syntax-e #'name))
           (syntax/loc stx (add-method name method-make))]
          ;; this might still be useful sometimes...
          ;; [(eq? 'top-level ctx)
          ;;  ;; if top-level then use a trick: try to use an
          ;;  (syntax/loc stx
          ;;    (define name ; trick: try using exising generic
          ;;      (let ([g (or (no-errors name) (generic name))])
          ;;        (add-method g method-make)
          ;;        g)))]
          [else
           ;; first module or function binding
           ;; (printf ">>> ~s: def\n" (syntax-e #'name))
           (syntax/loc stx (define name
                             (let ([g (generic name)])
                               (add-method g method-make)
                               g)))])))]))

(defsyntax* (defmethod stx)
  (define (n+a? stx)
    (let ([na (syntax-e stx)]) (and (pair? na) (identifier? (car na)))))
  (syntax-case stx ()
    [(_ name qualifier args body0 body ...)
     (and (identifier? #'name) (syntax-keyword? #'qualifier))
     (syntax/loc stx
       (method-def-adder qualifier name args body0 body ...))]
    [(_ qualifier name args body0 body ...)
     (and (identifier? #'name) (syntax-keyword? #'qualifier))
     (syntax/loc stx
       (method-def-adder qualifier name args body0 body ...))]
    [(_ qualifier name+args body0 body ...)
     (and (n+a? #'name+args) (syntax-keyword? #'qualifier))
     ;; simple pattern matching with (name . args) and using args won't work
     ;; since the destructing loses the arguments context and call-next-method
     ;; won't be accessible in the body.
     (with-syntax ([name (car (syntax-e #'name+args))]
                   [args (datum->syntax-object ; hack binding context!
                          #'name+args
                          (cdr (syntax-e #'name+args))
                          #'name+args)])
       (syntax/loc stx
         (method-def-adder qualifier name args body0 body ...)))]
    [(_ name+args body0 body ...) (n+a? #'name+args)
     ;; same as above
     (with-syntax ([name (car (syntax-e #'name+args))]
                   [args (datum->syntax-object ; hack binding context!
                          #'name+args
                          (cdr (syntax-e #'name+args))
                          #'name+args)])
       (syntax/loc stx
         (method-def-adder #f name args body0 body ...)))]
    [(_ name args body0 body ...) (identifier? #'name)
     (syntax/loc stx (method-def-adder #f name args body0 body ...))]))

(defsubst* (beforemethod . more) (qualified-method :before . more))
(defsubst* (aftermethod  . more) (qualified-method :after  . more))
(defsubst* (aroundmethod . more) (qualified-method :around . more))
(defsubst* (defbeforemethod . more) (defmethod :before . more))
(defsubst* (defaftermethod  . more) (defmethod :after  . more))
(defsubst* (defaroundmethod . more) (defmethod :around . more))

;;; ---------------------------------------------------------------------------
;;; Class macros

(defsyntax (make-class-form stx)
  (define (slots/initargs s/a)
    (let loop ([xs s/a] [r '()])
      (syntax-case xs ()
        [() (values (datum->syntax-object #'s/a (reverse r) #'s/a)
                    #'())]
        [((name . args) . more) (identifier? #'name)
         (loop #'more (cons #'(list 'name . args) r))]
        [(key val . more) (syntax-keyword? #'key)
         (values (datum->syntax-object #'s/a (reverse r) #'s/a)
                 #'(key val . more))]
        [(name . more) (identifier? #'name)
         (loop #'more (cons #'(list 'name) r))])))
  (syntax-case stx ()
    [(_ metaclass cname supers . s/a)
     (let*-values ([(slots initargs) (slots/initargs #'s/a)]
                   [(meta) (syntax-getarg initargs :metaclass #'metaclass)])
       (with-syntax ([(arg ...) #`(#,@initargs
                                   :direct-supers (list . supers)
                                   :direct-slots (list #,@slots)
                                   :name '#,(if (syntax-e #'cname)
                                              #'cname (syntax-local-name)))])
         (if (identifier? #'cname)
           #`(rec-make (cname #,meta arg ...))
           #`(make #,meta arg ...))))]))

(defsyntax* (class stx)
  (syntax-case stx ()
    [(_ name supers slot ...) (identifier? #'name)
     #'(make-class-form (*default-class-class*) name supers slot ...)]
    [(_ supers slot ...)
     #'(make-class-form (*default-class-class*) #f supers slot ...)]))

(defsyntax* (entityclass stx)
  (syntax-case stx ()
    [(_ name supers slot ...) (identifier? #'name)
     #'(make-class-form (*default-entityclass-class*) name supers slot ...)]
    [(_ supers slot ...)
     #'(make-class-form (*default-entityclass-class*) #f supers slot ...)]))

(define-syntax-parameter* -defclass-auto-initargs- #f)

(define-syntax-parameter* -defclass-autoaccessors-naming- :class-slot)

(define-syntax-parameter* -defclass-accessor-mode- :defmethod)

(defsyntax (make-defclass-form stx)
  (syntax-case stx ()
    [(_ class-maker name supers . slots0)
     (identifier? #'name)
     (let loop ([slots1 #'slots0] [slots2 '()])
       (syntax-case slots1 ()
         [(slot more ...) (not (syntax-keyword? #'slot))
          (loop #'(more ...) (cons #'slot slots2))]
         [(initarg ...) ; if slots1 is not null then it contains class keywords
          (let* ([autoargs (let ([as ((syntax-local-value
                                       #'-defclass-auto-initargs-))])
                             (and (syntax? as) (syntax-e as) as))]
                 [initargs (if autoargs
                             #`(initarg ... #,@autoargs) #'(initarg ...))]
                 [defmethods '()]
                 [sgetarg (lambda (arg . def)
                            (let ([a (apply syntax-getarg initargs arg def)])
                              (if (syntax? a) (syntax-object->datum a) a)))]
                 [all-auto (sgetarg :auto)]
                 [autoaccessors (sgetarg :autoaccessors (and all-auto #t))]
                 [automaker (or (sgetarg :automaker) all-auto)]
                 [autopred (or (sgetarg :autopred) all-auto)]
                 [accessor-mode (syntax-e ((syntax-local-value
                                            #'-defclass-accessor-mode-)))]
                 [default-slot-options (sgetarg :default-slot-options)]
                 [string-name
                  (regexp-replace
                   #rx"^<(.*)>$" (symbol->string (syntax-e #'name)) "\\1")])
            (define (get-defaccessor-form a-name typed-args untyped-args body)
              (case accessor-mode
                [(:defmethod)
                 #`(defmethod (#,a-name #,@typed-args) #,body)]
                [(:defgeneric)
                 #`(begin (defgeneric (#,a-name #,@untyped-args))
                          (add-method #,a-name (method #,typed-args #,body)))]
                [(:add-method)
                 #`(add-method #,a-name (method #,typed-args #,body))]
                [(:method) #`(define #,a-name (method #,typed-args #,body))]
                [(:procedure) #`(define (#,a-name #,@untyped-args) #,body)]
                [else (error
                       'defclass
                       "bad value in -defclass-accessor-mode-: ~e"
                       accessor-mode)]))
            (define (addreader reader sname)
              (push! (get-defaccessor-form
                      reader #'((x name)) #'(x) #`(slot-ref x '#,sname))
                     defmethods))
            (define (addwriter writer sname type)
              (push! (get-defaccessor-form
                      writer #`((x name) #,(if type #`(n #,type) #'n)) #'(x n)
                      #`(slot-set! x '#,sname n))
                     defmethods))
            (define (do-slot slot)
              (define-values (sname args)
                (syntax-case slot ()
                  [(sname args ...)
                   (values
                    #'sname
                    (cond
                     [(not default-slot-options) #'(args ...)]
                     [(and (list? default-slot-options)
                           (= 2 (length default-slot-options))
                           (memq (car default-slot-options)
                                 '(quote quasiquote)))
                      (let loop ([d  (cadr default-slot-options)]
                                 [as #'(args ...)]
                                 [r  '()])
                        (syntax-case as ()
                          [(v rest ...) (pair? d)
                           (loop (cdr d)
                                 #'(rest ...)
                                 (list* #'v (car d) r))]
                          [_ (datum->syntax-object #'(args ...)
                                                   (append (reverse r) as)
                                                   #'(args ...))]))]
                     [else (raise-syntax-error
                            #f "bad form for :default-slot-options"
                            stx initargs)]))]
                  [sname (values #'sname #'())]))
              (let ([reader (syntax-getarg args :reader)]
                    [writer (syntax-getarg args :writer)]
                    [accessor
                     (syntax-getarg
                      args :accessor
                      (and autoaccessors
                           (thunk
                             (if (eq? autoaccessors :slot)
                               sname
                               (datum->syntax-object
                                sname
                                (string->symbol
                                 (concat string-name "-"
                                         (symbol->string (syntax-e sname))))
                                sname)))))]
                    [type (syntax-getarg args :type)])
                (when reader (addreader reader sname))
                (when writer (addwriter writer sname type))
                (when accessor
                  (addreader accessor sname)
                  (addwriter
                   (datum->syntax-object
                    accessor
                    (string->symbol
                     (concat "set-" (symbol->string (syntax-e accessor)) "!"))
                    accessor)
                   sname type))
                (let loop ([as args] [res (list sname)])
                  (syntax-case as ()
                    [(keyword value more ...)
                     (loop #'(more ...)
                           (list* (if (memq (syntax-e #'keyword)
                                            '(:reader :writer :accessor))
                                    #''value #'value)
                                  #'keyword res))]
                    [() (datum->syntax-object as (reverse res) as)]))))
            (when (eq? autoaccessors #t)
              (set! autoaccessors
                    (syntax-e ((syntax-local-value
                                #'-defclass-autoaccessors-naming-)))))
            (unless (memq autoaccessors '(#t #f :slot :class-slot))
              (raise-syntax-error
               #f (concat "`:autoaccessors' expecting either a "
                          "`:slot' or `:class-slot' as value.")
               stx initargs))
            (let ([slots (map do-slot (reverse slots2))])
              #`(begin
                  (define name
                    (class-maker name supers
                                 . #,(datum->syntax-object
                                      #'slots0
                                      ;; note: append with a non-list 2nd arg
                                      (append
                                       slots (if all-auto
                                               #`(:autoinitargs #t #,@initargs)
                                               initargs))
                                      #'slots0)))
                  #,@(datum->syntax-object
                      #'stx (reverse defmethods) #'stx)
                  #,@(if automaker
                       (with-syntax
                           ([maker (datum->syntax-object
                                    #'name
                                    (string->symbol
                                     (concat "make-" string-name))
                                    #'name)])
                         #'((define maker
                              (let ([slots (class-slots name)])
                                (lambda args
                                  (let loop ([as args] [ss slots] [r '()])
                                    (if (or (null? as) (null? ss))
                                      (let ([new (make name . as)])
                                        (for-each (lambda (x)
                                                    (slot-set! new . x))
                                                  r)
                                        new)
                                      (loop (cdr as) (cdr ss)
                                            (cons (list (caar ss) (car as))
                                                  r)))))))))
                       '())
                  #,@(if autopred
                       (with-syntax
                           ([pred? (datum->syntax-object
                                    #'name
                                    (string->symbol (concat string-name "?"))
                                    #'name)])
                         #'((define (pred? x) (instance-of? x name))))
                       '()))))]))]))

(defsubst* (defclass name supers slot ...)
  (make-defclass-form class name supers slot ...))

(defsubst* (defentityclass name supers slot ...)
  (make-defclass-form entityclass name supers slot ...))

;;; ---------------------------------------------------------------------------
;;; Forms with a provide version

(provide defgeneric*)     (make-provide-syntax defgeneric     defgeneric*)
(provide defclass*)       (make-provide-syntax defclass       defclass*)
(provide defentityclass*) (make-provide-syntax defentityclass defentityclass*)
