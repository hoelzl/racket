#lang s-exp swindle/turbo

(require swindle/clos)

;;; ---------------------------------------------------------------------------
;;; A convenient `defstruct'

;; This makes it possible to create Racket structs using Swindle's `make' and
;; keyword arguments.

(define struct-to-slot-names (make-hash-table))

(hash-table-put! struct-to-slot-names <struct> '())

(add-method initialize (method ([s <struct>] initargs) ???))

(define (struct-type->class* stype maker slots)
  (let* ([this (struct-type->class stype)]
         [superslots (let ([s (class-direct-supers this)])
                       (and (pair? s) (null? (cdr s))
                            (hash-table-get
                             struct-to-slot-names (car s) (thunk #f))))])
    (when superslots
      (when (some (lambda (x) (memq x superslots)) slots)
        (error 'defstruct "cannot redefine slot names"))
      (let ([allslots (append superslots slots)])
        (hash-table-put! struct-to-slot-names this slots)
        (add-method allocate-instance
          (let ([???s (build-list (length allslots) (lambda _ ???))])
            (method ([class = this] initargs) (maker . ???s))))
        (add-method initialize
          (let ([none "-"]
                [keys (build-list
                       (length slots)
                       (lambda (n) (list (symbol-append ': (nth slots n)) n)))]
                [setter! (5th (call-with-values
                                  (thunk (struct-type-info stype))
                                  list))])
            (method ([obj this] initargs)
              (for-each (lambda (k)
                          (let ([v (getarg initargs (1st k) none)])
                            (unless (eq? none v)
                              (setter! obj (2nd k) v))))
                        keys)
              (call-next-method))))))
    this))

(defsyntax* (defstruct stx)
  (define <>-re #rx"^<(.*)>$")
  (define (<>-id? id)
    (and (identifier? id)
         (regexp-match? <>-re (symbol->string (syntax-e id)))))
  (define (doit name super slots)
    (let* ([str (regexp-replace <>-re (symbol->string (syntax-e name)) "\\1")]
           [name-sans-<> (datum->syntax-object name (string->symbol str) name)]
           [struct:name (datum->syntax-object
                         name (string->symbol (concat "struct:" str)) name)]
           [make-struct (datum->syntax-object
                         name (string->symbol (concat "make-" str)) name)]
           [super (and super (datum->syntax-object
                              super (string->symbol
                                     (regexp-replace
                                      <>-re (symbol->string (syntax-e super))
                                      "\\1"))
                              super))])
      (quasisyntax/loc stx
        (begin
          (define-struct #,(if super #`(#,name-sans-<> #,super) name-sans-<>)
            #,slots (make-inspector))
          (define #,name
            (struct-type->class* #,struct:name #,make-struct '#,slots))))))
  (syntax-case stx ()
    [(_ name (s) slot ...) (<>-id? #'name) (doit #'name #'s #'(slot ...))]
    [(_ name ( ) slot ...) (<>-id? #'name) (doit #'name #f  #'(slot ...))]
    [(_ name more ...) (not (<>-id? #'name))
     (raise-syntax-error #f "requires a name that looks like \"<...>\""
                         stx #'name)]))

;;; ---------------------------------------------------------------------------
;;; Convenient macros

(defsyntax process-with-slots
  (syntax-rules ()
    [(_ obj () (bind ...) body ...)
     (letsubst (bind ...) body ...)]
    [(_ obj ((id slot) slots ...) (bind ...) body ...)
     (process-with-slots
      obj (slots ...) (bind ... (id (slot-ref obj slot))) body ...)]
    [(_ obj (id slots ...) (bind ...) body ...)
     (process-with-slots
      obj (slots ...) (bind ... (id (slot-ref obj 'id))) body ...)]))

(defsubst* (with-slots obj (slot ...) body0 body ...)
  (process-with-slots obj (slot ...) () body0 body ...))

(defsyntax process-with-accessors
  (syntax-rules ()
    [(_ obj () (bind ...) body ...)
     (letsubst (bind ...) body ...)]
    [(_ obj ((id acc) accs ...) (bind ...) body ...)
     (process-with-accessors
      obj (accs ...) (bind ... (id (acc obj))) body ...)]
    [(_ obj (id accs ...) (bind ...) body ...)
     (process-with-accessors
      obj (accs ...) (bind ... (id (id obj))) body ...)]))

(defsubst* (with-accessors obj (acc ...) body0 body ...)
  (process-with-accessors obj (acc ...) () body0 body ...))

;;; ---------------------------------------------------------------------------
;;; An "as" conversion operator.

(defgeneric* as (class object))

(defmethod (as [c <class>] [x <top>])
  (if (instance-of? x c)
    x
    (error 'as "can't convert ~e -> ~e; given: ~e." (class-of x) c x)))

(define* (add-as-method from to . op)
  (let ([op (apply compose op)])
    (add-method as (method ([c = to] [x from]) (op x)))))

;; Add Scheme primitives.
(for-each
 (lambda (args)
   (apply (lambda (from to . ops)
            (add-as-method from to . ops)
            (let ([from* (cond [(eq? from <string>) <immutable-string>]
                               [(eq? from <bytes>) <immutable-bytes>]
                               [else #f])])
              (when from* (add-as-method from* to . ops))))
          args))
 `((,<immutable-string> ,<string> ,string-copy)
   (,<string> ,<immutable-string> ,string->immutable-string)
   (,<string> ,<symbol> ,string->symbol)
   (,<symbol> ,<string> ,symbol->string)
   (,<string> ,<keyword> ,string->keyword)
   (,<keyword> ,<string> ,keyword->string)
   (,<exact> ,<inexact> ,exact->inexact)
   (,<inexact> ,<exact> ,inexact->exact)
   (,<number> ,<string> ,number->string)
   (,<string> ,<number> ,string->number)
   (,<char> ,<string> ,string)
   (,<char> ,<integer> ,char->integer)
   (,<integer> ,<char> ,integer->char)
   (,<string> ,<list> ,string->list)
   (,<list> ,<string> ,list->string)
   (,<vector> ,<list> ,vector->list)
   (,<list> ,<vector> ,list->vector)
   (,<number> ,<integer> ,inexact->exact ,round)
   (,<rational> ,<integer> ,inexact->exact ,round)
   (,<struct> ,<vector> ,struct->vector)
   (,<string> ,<regexp> ,regexp)
   (,<regexp> ,<string> ,object-name)
   (,<immutable-bytes> ,<bytes> ,bytes-copy)
   (,<bytes> ,<immutable-bytes> ,bytes->immutable-bytes)
   (,<bytes> ,<list> ,bytes->list)
   (,<list> ,<bytes> ,list->bytes)
   (,<bytes> ,<byte-regexp> ,byte-regexp)
   (,<byte-regexp> ,<bytes> ,object-name)
   (,<string> ,<bytes> ,string->bytes/utf-8)
   (,<bytes> ,<string> ,bytes->string/utf-8)
   (,<string> ,<path> ,string->path)
   (,<path> ,<string> ,path->string)
   (,<bytes> ,<path> ,bytes->path)
   (,<path> ,<bytes> ,path->bytes)
   ;; Some weird combinations
   (,<symbol> ,<number> ,string->number ,symbol->string)
   (,<number> ,<symbol> ,string->symbol ,number->string)
   (,<struct> ,<list> ,vector->list ,struct->vector)
   (,<bytes> ,<number> ,string->number ,bytes->string/utf-8)
   (,<number> ,<bytes> ,string->bytes/utf-8 ,number->string)
   ))

;;; ---------------------------------------------------------------------------
;;; Recursive equality.

(defgeneric* equals? (x y))

(defaroundmethod (equals? [x <top>] [y <top>])
  ;; check this first in all cases
  (or (equal? x y) (call-next-method)))

(defmethod (equals? [x <top>] [y <top>])
  ;; the default is false - the around method returns #t if they're equal?
  #f)

(define* (add-equals?-method class pred?)
  (add-method equals? (method ([x class] [y class]) (pred? x y))))

(define* (class+slots-equals? x y)
  (let ([xc (class-of x)] [yc (class-of y)])
    (and (eq? xc yc)
         (every (lambda (s)
                  (equals? (slot-ref x (car s)) (slot-ref y (car s))))
                (class-slots xc)))))

(define* (make-equals?-compare-class+slots class)
  (add-equals?-method class class+slots-equals?))

;;; ---------------------------------------------------------------------------
;;; Generic addition for multiple types.

(defgeneric* add (x . more))

(define* (add-add-method c op)
  ;; dispatch on first argument
  (add-method add (method ([x c] . more) (apply op x more))))

(add-add-method <number>    +)
(add-add-method <list>      append)
(add-add-method <string>    string-append)
(add-add-method <symbol>    symbol-append)
(add-add-method <procedure> compose)

(defmethod (add [v <vector>] . more)
  ;; long but better than vectors->lists->append->vectors
  (let* ([len (apply + (map vector-length (cons v more)))]
         [vec (make-vector len)])
    (let loop ([i 0] [v v] [vs more])
      (dotimes [j (vector-length v)]
        (set! (vector-ref vec (+ i j)) (vector-ref v j)))
      (unless (null? vs) (loop (+ i (vector-length v)) (car vs) (cdr vs))))
    vec))

;;; ---------------------------------------------------------------------------
;;; Generic len for multiple types.

(defgeneric* len (x))

(define* (add-len-method c op)
  (add-method len (method ([x c]) (op x))))

(add-len-method <list>   length)
(add-len-method <string> string-length)
(add-len-method <vector> vector-length)

;;; ---------------------------------------------------------------------------
;;; Generic ref for multiple types.

(defgeneric* ref (x . indexes))

(define* (add-ref-method c op)
  (add-method ref (method ([x c] . indexes) (op x . indexes))))

(add-ref-method <list>       list-ref)
(add-ref-method <vector>     vector-ref)
(add-ref-method <string>     string-ref)
(add-ref-method <object>     slot-ref)
(add-ref-method <hash-table> hash-table-get)
(add-ref-method <box>        unbox)
(add-ref-method <promise>    force)
(defmethod (ref [p <parameter>] . _) (p))
(defmethod (ref [n <namespace>] . args)
  (parameterize ([current-namespace n])
    (apply namespace-variable-value args)))

;;; ---------------------------------------------------------------------------
;;; Generic set-ref! for multiple types.

(defgeneric* put! (x v . indexes))

(define* (add-put!-method c op)
  (add-method put! (method ([x c] v . indexes) (op x v . indexes))))

(defsyntax* (set-ref! stx)
  (syntax-case stx ()
    [(_ x i ...)
     (let* ([ris  (reverse (syntax->list #'(i ...)))]
            [idxs (reverse (cdr ris))]
            [val  (car ris)])
       (quasisyntax/loc stx
         (put! x #,val #,@(datum->syntax-object #'(i ...) idxs #'(i ...)))))]))

(define (put!-arg typename args)
  (if (or (null? args) (pair? (cdr args)))
   (if (null? args)
     (error 'put! "got no index for a ~a argument" typename)
     (error 'put! "got more than one index for a ~a argument ~e"
            typename args))
   (car args)))

#|
(defmethod (put! [l <list>] x . i_)
  (list-set! l (put!-arg '<list> i_) x))
|#
(defmethod (put! [v <vector>] x . i_)
  (vector-set! v (put!-arg '<vector> i_) x))
(defmethod (put! [s <string>] [c <char>] . i_)
  (string-set! s (put!-arg '<string> i_) c))
(defmethod (put! [o <object>] x . s_)
  (slot-set! o (put!-arg '<object> s_) x))
(defmethod (put! [h <hash-table>] x . k_)
  (if (null? k_)
    (error 'put! "got no index for a <hash-table> argument")
    (hash-table-put! h (car k_) x)))
(add-put!-method <box> set-unbox!)
(defmethod (put! [p <parameter>] x . _)
  (if (null? _)
    (p x)
    (error 'put! "got extraneous indexes for a <parameter> argument")))
(defmethod (put! [n <namespace>] x . v_)
  (if (null? v_)
    (error 'put! "got no index for a <namespace> argument")
    (parameterize ([current-namespace n])
      (apply namespace-set-variable-value! (car v_) x
             (if (null? (cdr v_)) '() (list (cadr v_)))))))

;;; ---------------------------------------------------------------------------
(define* *print-level*  (make-parameter 6))
(define* *print-length* (make-parameter 20))

;; grab the builtin write/display handlers
(define-values (mz:write mz:display)
  (let ([p (open-output-bytes)])
    (values (port-write-handler p) (port-display-handler p))))

(defgeneric* print-object (object esc? port))

(defmethod (print-object o esc? port)
  (mz:display "#" port)
  (mz:display (class-name (class-of o)) port))

(defmethod (print-object [o <builtin>] esc? port)
  ((if esc? mz:write mz:display) o port))

(define printer:too-deep "#?#")
(define printer:too-long "...")

;; use a single implementation for both pairs and mpairs, punctuation
;; shorthands for pairs only
(defmethod (print-object [o <pair>] esc? port)
  (let ([punct (and (pair? (cdr o)) (null? (cddr o))
                    (assq (car o)
                          '([quote "'"] [quasiquote "`"] [unquote ","]
                            [unquote-splicing ",@"]
                            [syntax "#'"] [quasisyntax "#`"] [unsyntax "#,"]
                            [unsyntax-splicing "#,@"])))])
    (if punct
      (begin (mz:display (cadr punct) port) (print-object (cadr o) esc? port))
      (print-pair o esc? port "(" ")" pair? car cdr))))
(defmethod (print-object [o <mutable-pair>] esc? port)
  (print-pair o esc? port "{" "}" mpair? mcar mcdr))
(define (print-pair p esc? port open close pair? car cdr)
  (define level (*print-level*))
  (if (eq? level 0)
    (mz:display printer:too-deep port)
    (begin
      (mz:display open port)
      (if (eq? (*print-length*) 0)
        (mz:display printer:too-long port)
        (parameterize ([*print-level* (and level (sub1 level))])
          (print-object (car p) esc? port)
          (do ([p (cdr p) (if (pair? p) (cdr p) '())]
               [n (sub1 (or (*print-length*) 0)) (sub1 n)])
              [(or (null? p)
                   (and (zero? n)
                        (begin (mz:display " " port)
                               (mz:display printer:too-long port)
                               #t)))]
            (if (pair? p)
              (begin (mz:display " " port) (print-object (car p) esc? port))
              (begin (mz:display " . " port) (print-object p esc? port))))))
      (mz:display close port))))

(defmethod (print-object [o <vector>] esc? port)
  (define level (*print-level*))
  (cond [(eq? level 0) (mz:display printer:too-deep port)]
        [(zero? (vector-length o)) (mz:display "#()" port)]
        [else (mz:display "#(" port)
              (if (eq? (*print-length*) 0)
                (mz:display printer:too-long port)
                (parameterize ([*print-level* (and level (sub1 level))])
                  (print-object (vector-ref o 0) esc? port)
                  (let ([len (if (*print-length*)
                               (min (vector-length o) (*print-length*))
                               (vector-length o))])
                    (do ([i 1 (add1 i)]) [(>= i len)]
                      (mz:display " " port)
                      (print-object (vector-ref o i) esc? port))
                    (when (< len (vector-length o))
                      (mz:display " " port)
                      (mz:display printer:too-long port)))))
              (mz:display ")" port)]))

(define <>-re #rx"^<(.*)>$")
(define* (name-sans-<> name)
  (cond [(string? name) (regexp-replace <>-re name "\\1")]
        [(symbol? name) (regexp-replace <>-re (symbol->string name) "\\1")]
        [(eq? ??? name) "???"]
        [else name]))

;; Take care of all <object>s with a `name' slot
(defmethod (print-object (o <object>) esc? port)
  (let* ([c  (class-of o)]
         [cc (class-of c)]
         [(name x) (name-sans-<> (slot-ref x 'name))])
    (if (and (assq 'name (class-slots c)) (assq 'name (class-slots cc)))
      (begin (mz:display "#<" port)
             (mz:display (name c) port)
             (mz:display ":" port)
             (mz:display (name o) port)
             (mz:display ">" port))
      (call-next-method))))

(define* (print-object-with-slots o esc? port)
  (define level (*print-level*))
  (if (eq? level 0)
    (mz:display printer:too-deep port)
    (let ([class (class-of o)])
      (mz:display "#<" port)
      (mz:display (name-sans-<> (class-name class)) port)
      (mz:display ":" port)
      (parameterize ([*print-level* (and level (sub1 level))])
        (do ([s (class-slots class) (cdr s)]
             [n (or (*print-length*) -1) (sub1 n)])
            [(or (null? s)
                 (and (zero? n)
                      (begin (mz:display " " port)
                             (mz:display printer:too-long port))))]
          (let ([val (slot-ref o (caar s))])
            (if (eq? ??? val)
              (set! n (add1 n))
              (begin (mz:display " " port)
                     (mz:display (caar s) port)
                     (mz:display "=" port)
                     (print-object val esc? port))))))
      (mz:display ">" port))))

;; Add a hook to make <class> so it will initialize a printer if given
(defmethod :after (initialize [c <class>] initargs)
  (let ([printer (or (getarg initargs :printer)
                     (and (getarg initargs :auto) #t))])
    (when printer
      (when (eq? #t printer) (set! printer print-object-with-slots))
      (add-method print-object
                  (method ([x c] esc? port) (printer x esc? port))))))

(define* (display-object obj &optional [port (current-output-port)])
  (print-object obj #f port))
(define* (write-object obj &optional [port (current-output-port)])
  (print-object obj #t port))

(define* (object->string obj &optional [esc? #t])
  (with-output-to-string
    (thunk (print-object obj esc? (current-output-port)))))

;; Hack these to echo
(*echo-display-handler* display-object)
(*echo-write-handler* write-object)

(define* (install-swindle-printer)
  (global-port-print-handler write-object)
  (port-display-handler (current-output-port) display-object)
  (port-display-handler (current-error-port)  display-object)
  (port-write-handler   (current-output-port) write-object)
  (port-write-handler   (current-error-port)  write-object))

;;; ---------------------------------------------------------------------------
(define* match-failure "failure")

(define* (matching? matcher value)
  (cond [(class? matcher)    (instance-of? value matcher)]
        [(function? matcher) (matcher value)]
        [(pair? matcher)     (and (pair? value)
                                  (matching? (car matcher) (car value))
                                  (matching? (cdr matcher) (cdr value)))]
        ;; handle regexps - the code below relies on returning this result
        [(regexp? matcher)   (and (string? value)
                                  (regexp-match matcher value))]
        [else (equals? matcher value)]))

(defsyntax (make-matcher-form stx)
  (define (re r)
    ;; Note: this inserts the _literal_ regexp in the code if it is a string.
    (cond [(regexp? (syntax-e r)) r]
          [(string? (syntax-e r)) (regexp (syntax-e r))]
          [else #`(regexp #,r)]))
  (define (loop x pattern vs body)
    ;; body always a delayed function that expects bindings
    (syntax-case pattern (* ??? := ! !! when and or if => ::
                            make regexp quote quasiquote lambda)
      [* ; wildcard
       (body vs)]
      [??? ; matches ???
       #`(if (matching? ??? #,x) #,(body vs) match-failure)]
      [(v := p) ; assign the variable V to the value matched by P
       #`(let ([v #,x]) #,(loop #'v #'p (cons #'v vs) body))]
      [v ; (V := *) if V is a symbol that was not already used
       (and (identifier? #'v) (not (syntax-keyword? #'v))
            (not (ormap (lambda (u) (bound-identifier=? #'v u)) vs)))
       (loop x #'(v := *) vs body)]
      [(! e) ; evaluate E and use it as a simple value
       #`(if (matching? e x) #,(body vs) match-failure)]
      [(!! e) ; evaluate E and succeed only if it is true
       #`(if e #,(body vs) match-failure)]
      [(p when e) ; => (and P (!! E))
       #`(_ x (and p (!! e)) #,(body vs))]
      ;; and/or
      [(and) (body vs)]
      [(or)  #'match-failure]
      [(and p) (loop x #'p vs body)]
      [(or  p) (loop x #'p vs body)]
      [(and p1 p2 ...) (loop x #'p1 vs
                             (lambda (vs) (loop x #'(and p2 ...) vs body)))]
      [(or  p1 p2 ...) #`(let ([tmp #,(loop x #'p1 vs body)])
                           (if (eq? tmp match-failure)
                             #,(loop x #'(or p2 ...) vs body)
                             tmp))]
      [(if a b c) ; => (or (and A B) C)
       (loop x #'(or (and a b) c) vs body)]
      [(f => p) ; continue matching P with (F x)
       #`(let ([v (f #,x)]) #,(loop #'v #'p vs body))]
      [(v :: . p) ; => (and (! V) P ...), eg (<foo> :: (foo => f) ...)
       (loop x #'(and (! v) . p) vs body)]
      [(make class initarg+vals ...)
       ;; (make <class> :slotname p ...) - match on slots of the given class
       #`(let ([obj #,x])
           (if (instance-of? obj class)
             #,(let loop1 ([av #'(initarg+vals ...)] [vs vs])
                 (syntax-case av (quote)
                   [(key p more ...) (syntax-keyword? #'key)
                    (let* ([s (symbol->string (syntax-e #'key))]
                           [s (datum->syntax-object
                               #'key
                               (string->symbol
                                (substring s 1 (string-length s)))
                               #'key)])
                      (loop #`(slot-ref obj '#,s) #'p vs
                            (lambda (vs) (loop1 #'(more ...) vs))))]
                   [('key p more ...)
                    (loop #'(slot-ref obj 'key) #'p vs
                          (lambda (vs) (loop1 #'(more ...) vs)))]
                   [() (body vs)]))
             match-failure))]
      [(regexp r) ; use R as a regexp (matching? handles it)
       #`(if (matching? #,(re #'r) #,x) #,(body vs) match-failure)]
      [(regexp r . p) ; => like the above, but match P... on result
       #`(let ([m (matching? #,(re #'r) #,x)])
           (if m #,(loop #'m #'p vs body) match-failure))]
      ;; literal lists
      ['v #`(if (matching? 'v #,x) #,(body vs) match-failure)]
      [`v #`(if (matching? `v #,x) #,(body vs) match-failure)]
      [(lambda as b ...)
       #`(if (matching? (lambda as b ...) #,x) #,(body vs) match-failure)]
      [(a . b) ; simple lists
       #`(if (pair? #,x)
           (let ([hd (car #,x)] [tl (cdr #,x)])
             #,(loop #'hd #'a vs (lambda (vs) (loop #'tl #'b vs body))))
           match-failure)]
      ;; other literals (null, keywords, non-symbols)
      [() #`(if (null? #,x) #,(body vs) match-failure)]
      [v  #`(if (matching? v #,x) #,(body vs) match-failure)]))
  (syntax-case stx ()
    [(_ x pattern body) (loop #'x #'pattern '() (lambda (vs) #'body))]))
(defsubst* (let/match pattern value body ...)
  (let* ([v value] [r (make-matcher-form v pattern (begin body ...))])
    (if (eq? r match-failure)
      (error 'let/match "value did not match pattern: ~e" v)
      r)))

(defsubst* (matcher pattern body ...)
  (lambda args
    (let ([r (make-matcher-form args pattern (begin body ...))])
      (if (eq? r match-failure)
        (error 'matcher "application values did not match pattern: ~e" v)
        r))))

(defsyntax match-internal
  (syntax-rules (else)
    [(_ x) (void)]
    [(_ x (else body0 body ...)) (begin body0 body ...)]
    [(_ x (pattern body0 body ...) clause ...)
     (let ([m (make-matcher-form x pattern (begin body0 body ...))])
       (if (eq? m match-failure) (match x clause ...) m))]))
(defsubst* (match x clause ...)
  (let ([v x]) (match-internal v clause ...)))

(defentityclass* <matcher> (<generic>)
  (name     :initarg :name     :initvalue '-anonymous-)
  (default  :initarg :default  :initvalue #f)
  (matchers :initarg :matchers :initvalue '()))

;; Set the entity's proc
(defmethod (initialize [matcher <matcher>] initargs)
  (call-next-method)
  (set-instance-proc!
   matcher
   (lambda args
     (let loop ([matchers (slot-ref matcher 'matchers)])
       (if (null? matchers)
         (let ([default (slot-ref matcher 'default)])
           (if (procedure? default)
             (default . args)
             (or default
                 (error (slot-ref matcher 'name) "no match found."))))
         (let ([r (apply (car matchers) args)])
           (if (eq? r match-failure)
             (loop (cdr matchers))
             r)))))))

;;; Add a matcher - normally at the end, with add-matcher0 at the beginning
(define (add-matcher matcher m)
  (slot-set! matcher 'matchers
             (append (slot-ref matcher 'matchers) (list m))))
(define (add-matcher0 matcher m)
  (slot-set! matcher 'matchers
             (cons m (slot-ref matcher 'matchers))))

(defsyntax (defmatcher-internal stx)
  (syntax-case stx ()
    [(_ adder name args body ...)
     (with-syntax ([matcher-make (syntax/loc stx (matcher args body ...))])
       (if (or
            ;; not enabled
            (not (syntax-e
                  ((syntax-local-value #'-defmethod-create-generics-))))
            ;; defined symbol or second module binding
            (identifier-binding #'name)
            ;; local definition -- don't know which is first => no define
            (eq? 'lexical (syntax-local-context)))
         (syntax/loc stx (adder name matcher-make))
         ;; top-level or first module binding
         (syntax/loc stx
           (define name ; trick: try using exising generic
             (let ([m (or (no-errors name) (make <matcher> :name 'name))])
               (adder m matcher-make)
               m)))))]))

(defsyntax* (defmatcher stx)
  (syntax-case stx ()
    [(_ (name . args) body0 body ...) (identifier? #'name)
     #'(defmatcher-internal add-matcher name args body0 body ...)]
    [(_ name args body0 body ...) (identifier? #'name)
     #'(defmatcher-internal add-matcher name args body0 body ...)]))
(defsyntax* (defmatcher0 stx)
  (syntax-case stx ()
    [(_ (name . args) body0 body ...) (identifier? #'name)
     #'(defmatcher-internal add-matcher0 name args body0 body ...)]
    [(_ name args body0 body ...) (identifier? #'name)
     #'(defmatcher-internal add-matcher0 name args body0 body ...)]))

;;; ---------------------------------------------------------------------------

(define amb-fail (make-parameter #f))
(define (initialize-amb-fail)
  (amb-fail (thunk (error 'amb "tree exhausted"))))
(initialize-amb-fail)

(defsubst* (amb expr ...)
  (let ([prev-amb-fail (amb-fail)])
    (let/ec sk
      (let/cc fk
        (amb-fail (thunk (amb-fail prev-amb-fail) (fk 'fail)))
        (sk expr)) ...
      (prev-amb-fail))))

(define* (amb-assert bool) (unless bool ((amb-fail))))

(defsubst* (amb-collect e)
  (let ([prev-amb-fail (amb-fail)]
        [results '()])
    (when (let/cc k
            (amb-fail (thunk (k #f)))
            (let ([v e]) (push! v results) (k #t)))
      ((amb-fail)))
    (amb-fail prev-amb-fail)
    (reverse results)))

;;; ---------------------------------------------------------------------------
(define* *dialog-title* (make-parameter "Swindle Message"))

(define* (message str . args)
  (let ([msg (format str . args)])
    (if (namespace-defined? 'message-box)
      ((namespace-variable-value 'message-box) (*dialog-title*) msg)
      (echo :>e :s- "<<<" (*dialog-title*) ": " msg ">>>")))
  (void))

(define (first-non-ws-char str idx)
  (and (< idx (string-length str))
       (let ([c (string-ref str idx)])
         (if (memq c '(#\space #\tab #\newline))
           (first-non-ws-char str (add1 idx))
           c))))

(define (ui-question str args prompt positive-result msg-style
                     positive-char negative-char)
  (let ([msg (apply format str args)])
    (if (namespace-defined? 'message-box)
      (eq? ((namespace-variable-value 'message-box)
            (*dialog-title*) msg #f msg-style)
           positive-result)
      (begin (echo :>e :n- :s- (*dialog-title*) ">>> " msg " " prompt " ")
             (let loop ()
               (let ([inp (first-non-ws-char (read-line) 0)])
                 (cond [(char-ci=? inp positive-char) #t]
                       [(char-ci=? inp negative-char) #f]
                       [else (loop)])))))))

(define* (ok/cancel? str . args)
  (ui-question str args "Ok/Cancel" 'ok '(ok-cancel) #\o #\c))
(define* (yes/no? str . args)
  (ui-question str args "Yes/No" 'yes '(yes-no) #\y #\n))
