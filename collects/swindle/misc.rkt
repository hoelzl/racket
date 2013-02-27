;;; Written by Eli Barzilay: Maze is Life!  (eli@barzilay.org)

;;> A lot of miscellaneous functionality that is needed for Swindle, or
;;> useful by itself.

#lang s-exp swindle/base

(require mzlib/list)   (provide (all-from mzlib/list))
(require mzlib/etc)    (provide (all-from mzlib/etc))
(require mzlib/string) (provide (all-from mzlib/string))

;; these are needed to make regexp-case work in scheme/base too
(require (rename scheme/base base-else else) (rename scheme/base base-=> =>))

;; ----------------------------------------------------------------------------
(provide define*)
(define-syntax (define* stx)
  (syntax-case stx ()
    [(_ x . xs)
     (memq (syntax-local-context) '(module module-begin))
     (let ([name (let loop ([x #'x])
                   (syntax-case x () [(x . xs) (loop #'x)] [_ x]))])
       (if name
         #`(begin (provide #,name) (define x . xs))
         #`(define x . xs)))]
    [(_ x . xs) #`(define x . xs)]))

(provide make-provide-syntax)
(define-syntax make-provide-syntax
  (syntax-rules ()
    [(_ form form*)
     (define-syntax (form* stx)
       (syntax-case stx ()
         [(_ (id . as) . r)
          (memq (syntax-local-context) '(module module-begin))
          #'(begin (provide id) (form (id . as) . r))]
         [(_ id . r)
          (memq (syntax-local-context) '(module module-begin))
          #'(begin (provide id) (form id . r))]
         [(_ . r) #'(form . r)]))]))

(provide define-syntax*)
(make-provide-syntax define-syntax define-syntax*)

(define-syntax* defsyntax
  (syntax-rules () [(_ . args) (define-syntax . args)]))
(make-provide-syntax defsyntax defsyntax*) (provide defsyntax*)
(define-syntax* letsyntax
  (syntax-rules () [(_ . args) (let-syntax . args)]))


(defsyntax defsubst-process
  (syntax-rules ()
    [(_ name (acc ...)) (define-syntax name (syntax-rules () acc ...))]
    [(_ name (acc ...) n+a subst . more)
     (defsubst-process name (acc ... (n+a subst)) . more)]))
(defsyntax* defsubst
  (syntax-rules ()
    [(_ (name . args) subst)
     (define-syntax name
       (syntax-rules () [(name . args) subst]))]
    [(_ (name . args) subst . more)
     (defsubst-process name () (name . args) subst . more)]
    [(_ name subst)
     (define-syntax (name stx)
       (syntax-case stx () ; syntax-rules won't handle identifier expansion
         ;; doesn't matter here, but see `letsubst' for an explanation on `___'
         [(___ . args) (syntax/loc stx (subst . args))]
         [___          (syntax/loc stx subst)]))]))
(make-provide-syntax defsubst defsubst*) (provide defsubst*)

;; a let version of the above
(defsyntax* (letsubst stx)
  (syntax-case stx ()
    [(_ ([name body] ...) letbody ...)
     (quasisyntax/loc stx
       (let-syntax
           #,(map
              (lambda (name body)
                ;; use `___' in the following, if we use `name', then it would
                ;; not be possible to make an X subst that expand to something
                ;; with the previous X, so (let ([x 1]) (letsubst ([x x]) x))
                ;; will loop forever instead of returning 1.
                (syntax-case name ()
                  [(name . args)
                   (quasisyntax/loc body
                     (name (syntax-rules () [(___ . args) #,body])))]
                  [name (identifier? #'name)
                   (quasisyntax/loc body
                     (name
                      (lambda (stx)
                        (syntax-case stx ()
                          [(___ . args) (syntax/loc stx (#,body . args))]
                          [___          (syntax/loc stx #,body)]))))]))
              (syntax-e #'(name ...)) (syntax-e #'(body ...)))
         letbody ...))]))


(require (for-syntax (submod compatibility/defmacro dmhelp)))
(provide defmacro letmacro)
(define-syntaxes (defmacro letmacro)
  (let ()
    (define (syntax-null? x)
      (or (null? x) (and (syntax? x) (null? (syntax-e x)))))
    (define (syntax-pair? x)
      (or (pair? x) (and (syntax? x) (pair? (syntax-e x)))))
    (define (syntax-car x)   (if (pair? x) (car x) (car (syntax-e x))))
    (define (syntax-cdr x)   (if (pair? x) (cdr x) (cdr (syntax-e x))))
    (define (check-args stx name args)
      (unless (identifier? name)
        (raise-syntax-error
         #f "expected an identifier for the macro name" stx name))
      (let loop ([args args])
        (cond [(syntax-null? args) 'ok]
              [(identifier? args) 'ok]
              [(syntax-pair? args)
               (unless (identifier? (syntax-car args))
                 (raise-syntax-error
                  #f "expected an identifier for a macro argument"
                  stx (syntax-car args)))
               (loop (syntax-cdr args))]
              [else
               (raise-syntax-error
                #f "not a valid argument sequence after the macro name"
                stx)])))
    (values
     (lambda (stx) ; defmacro
       (syntax-case stx ()
         [(_ (name . args) body0 body ...)
          (begin
            (check-args stx #'name #'args)
            #'(define-syntax name
                (let ([p (lambda args body0 body ...)])
                  (lambda (stx)
                    (let ([l (syntax->list stx)])
                      (unless (and l (procedure-arity-includes?
                                      p (sub1 (length l))))
                        (raise-syntax-error #f "bad form" stx))
                      (let ([ht (make-hash-table)])
                        (datum->syntax-object
                         stx
                         (dm-subst
                          ht (apply p (cdr (dm-syntax->datum stx ht))))
                         stx)))))))]
         [(_ name body) (identifier? #'name)
          #'(define-syntax name
              (lambda (stx)
                (syntax-case stx ()
                  [(_ . xs) (quasisyntax/loc stx
                              (#,(datum->syntax-object stx body stx) . xs))]
                  [_ (datum->syntax-object stx body stx)])))]))
     (lambda (stx) ; letmacro
       (syntax-case stx ()
         [(_ ([name body] ...) letbody ...)
          (quasisyntax/loc stx
            (let-syntax
                #,(map
                   (lambda (name body)
                     (if (identifier? name)
                       (quasisyntax/loc body
                         (#,name
                          (lambda (stx)
                            (syntax-case stx ()
                              [(_1 . xs)
                               (quasisyntax/loc stx
                                 (#,(datum->syntax-object stx body stx)
                                  . xs))]
                              [_1 (datum->syntax-object stx #,body stx)]))))
                       (syntax-case name ()
                         [(name . args)
                          (begin
                            (check-args stx #'name #'args)
                            (quasisyntax/loc body
                              (name
                               (let ([p (lambda args #,body)])
                                 (lambda (stx)
                                   (let ([l (syntax->list stx)])
                                     (unless
                                         (and l (procedure-arity-includes?
                                                 p (sub1 (length l))))
                                       (raise-syntax-error #f "bad form" stx))
                                     (let ([ht (make-hash-table)])
                                       (datum->syntax-object
                                        stx
                                        (dm-subst
                                         ht (apply p (cdr (dm-syntax->datum
                                                           stx ht))))
                                        stx))))))))])))
                   (syntax-e #'(name ...)) (syntax-e #'(body ...)))
              letbody ...))])))))
(make-provide-syntax defmacro defmacro*) (provide defmacro*)

;; ----------------------------------------------------------------------------
(defsyntax* define-syntax-parameter
  (syntax-rules ()
    [(_ name default)
     (define-syntax name
       (let ([p (make-parameter #'default)])
         (lambda stx
           (if (null? stx)
             (p) ; when the value is used in other transformers
             (syntax-case (car stx) ()
               [(_ new) (begin (p #'new) #'(void))]
               [(_)     (p)])))))]))
(make-provide-syntax define-syntax-parameter define-syntax-parameter*)
(provide define-syntax-parameter*)

;; ----------------------------------------------------------------------------
#|
(define* set-caar!   (lambda (p v) (set-car! (car p) v)))
(define* set-cadr!   (lambda (p v) (set-car! (cdr p) v)))
(define* set-cdar!   (lambda (p v) (set-cdr! (car p) v)))
(define* set-cddr!   (lambda (p v) (set-cdr! (cdr p) v)))
(define* set-caaar!  (lambda (p v) (set-car! (caar p) v)))
(define* set-caadr!  (lambda (p v) (set-car! (cadr p) v)))
(define* set-cadar!  (lambda (p v) (set-car! (cdar p) v)))
(define* set-caddr!  (lambda (p v) (set-car! (cddr p) v)))
(define* set-cdaar!  (lambda (p v) (set-cdr! (caar p) v)))
(define* set-cdadr!  (lambda (p v) (set-cdr! (cadr p) v)))
(define* set-cddar!  (lambda (p v) (set-cdr! (cdar p) v)))
(define* set-cdddr!  (lambda (p v) (set-cdr! (cddr p) v)))
(define* set-caaaar! (lambda (p v) (set-car! (caaar p) v)))
(define* set-caaadr! (lambda (p v) (set-car! (caadr p) v)))
(define* set-caadar! (lambda (p v) (set-car! (cadar p) v)))
(define* set-caaddr! (lambda (p v) (set-car! (caddr p) v)))
(define* set-cadaar! (lambda (p v) (set-car! (cdaar p) v)))
(define* set-cadadr! (lambda (p v) (set-car! (cdadr p) v)))
(define* set-caddar! (lambda (p v) (set-car! (cddar p) v)))
(define* set-cadddr! (lambda (p v) (set-car! (cdddr p) v)))
(define* set-cdaaar! (lambda (p v) (set-cdr! (caaar p) v)))
(define* set-cdaadr! (lambda (p v) (set-cdr! (caadr p) v)))
(define* set-cdadar! (lambda (p v) (set-cdr! (cadar p) v)))
(define* set-cdaddr! (lambda (p v) (set-cdr! (caddr p) v)))
(define* set-cddaar! (lambda (p v) (set-cdr! (cdaar p) v)))
(define* set-cddadr! (lambda (p v) (set-cdr! (cdadr p) v)))
(define* set-cdddar! (lambda (p v) (set-cdr! (cddar p) v)))
(define* set-cddddr! (lambda (p v) (set-cdr! (cdddr p) v)))
|#

(define* 1st car)
(define* 2nd cadr)
(define* 3rd caddr)
(define* 4th cadddr)
(define* 5th (lambda (x) (car (cddddr x))))
(define* 6th (lambda (x) (cadr (cddddr x))))
(define* 7th (lambda (x) (caddr (cddddr x))))
(define* 8th (lambda (x) (cadddr (cddddr x))))

#|
(define* set-1st! set-car!)
(define* set-2nd! set-cadr!)
(define* set-3rd! set-caddr!)
(define* set-4th! set-cadddr!)
(define* set-5th! (lambda (p v) (set-car! (cddddr p) v)))
(define* set-6th! (lambda (p v) (set-car! (cdr (cddddr p)) v)))
(define* set-7th! (lambda (p v) (set-car! (cddr (cddddr p)) v)))
(define* set-8th! (lambda (p v) (set-car! (cdddr (cddddr p)) v)))
|#

(define* head first)
(define* tail rest)
;(define* set-head! set-first!)
;(define* set-tail! set-rest!)

#|
(define* set-second!  set-2nd!)
(define* set-third!   set-3rd!)
(define* set-fourth!  set-4th!)
(define* set-fifth!   set-5th!)
(define* set-sixth!   set-6th!)
(define* set-seventh! set-7th!)
(define* set-eighth!  set-8th!)
|#

(define* nth list-ref)
(define* (nthcdr l n)
  (if (zero? n) l (nthcdr (cdr l) (- n 1))))

#|
(define* (list-set! lst index new)
  (set-car! (nthcdr lst index) new))
(define* set-nth! list-set!)
|#

; (define* set-list-ref!   list-set!)
(define* set-vector-ref! vector-set!)
(define* set-string-ref! string-set!)

(define* (last l)
  (car (last-pair l)))
#|
(define* (set-last! l x)
  (set-car! (last-pair l) x))
|#

(define* set-unbox! set-box!)

(defsubst*
  (set-hash-table-get! table key value) (hash-table-put! table key value)
  (_ table key thunk value)             (hash-table-put! table key value))

;; ----------------------------------------------------------------------------
(define* (eprintf . args)
  (apply fprintf (current-error-port) args))

(define* concat string-append)

(define* (symbol-append . symbols)
  (string->symbol (apply string-append (map symbol->string symbols))))

(define* (maptree f x)
  (let loop ([x x])
    (cond [(list? x) (map loop x)]
          [(pair? x) (cons (loop (car x)) (loop (cdr x)))]
          [else (f x)])))

#|
(define* (map! f l . rest)
  (if (null? rest)
    (let loop ([xs l])
      (if (null? xs) l (begin (set-car! xs (f (car xs))) (loop (cdr xs)))))
    (let loop ([xs l] [ls rest])
      (if (null? xs) l (begin (set-car! xs (apply f (car xs) (map car ls)))
                              (loop (cdr xs) (map cdr ls)))))))
|#

#|
(define* (maptree! f x)
  (if (pair? x)
    (begin (let loop ([x x])
             (defsubst (do-part get set)
               (let ([y (get x)])
                 (cond [(pair? y) (loop y)]
                       [(not (null? y)) (set x (f y))])))
             (do-part car set-car!)
             (do-part cdr set-cdr!))
           x)
    (f x))) ; can't be destructive here
|#

(define* (mappend f . ls)
  (apply append (apply map f ls)))
#|
(define* (mappend! f . ls)
  (apply append! (apply map f ls)))
|#

(define* (mapply f ls)
  (map (lambda (args) (apply f args)) ls))

(define* (negate pred?)
  (lambda x (not (pred? . x))))

(define* (position-of x lst)
  (let loop ([i 0] [l lst])
    (cond [(null? l) #f]
          [(eq? x (car l)) i]
          [else (loop (add1 i) (cdr l))])))

(define* (find-if pred? l)
  (let loop ([l l])
    (cond [(null? l) #f]
          [(pred? (car l)) (car l)]
          [else (loop (cdr l))])))


(define* (some pred? l . rest)          ; taken from slib/comlist.scm,
  (cond [(null? rest)                   ; modified to check only up to the
         (let mapf ([l l])              ; length of the shortest list.
           (and (not (null? l))
                (or (pred? (car l)) (mapf (cdr l)))))]
        [else (let mapf ([l l] [rest rest])
                (and (not (or (null? l) (memq '() rest)))
                     (or (apply pred? (car l) (map car rest))
                         (mapf (cdr l) (map cdr rest)))))]))

(define* (every pred? l . rest)         ; taken from slib/comlist.scm
  (cond [(null? rest)                   ; modified to check only up to the
         (let mapf ([l l])              ; length of the shortest list.
           (or (null? l)
               (and (pred? (car l)) (mapf (cdr l)))))]
        [else (let mapf ([l l] [rest rest])
                (or (null? l) (if (memq '() rest) #t #f)
                    (and (apply pred? (car l) (map car rest))
                         (mapf (cdr l) (map cdr rest)))))]))

(define* (with-output-to-string thunk)
  (let ([str (open-output-string)])
    (parameterize ([current-output-port str]) (thunk))
    (get-output-string str)))

(define* 1+ add1)
(define* 1- sub1)

;; ----------------------------------------------------------------------------

;; Internal values, used below.
(define *nothing* (list "*"))
(define (return-nothing) *nothing*)

(defsubst l-hash-vector-length 10)

(define* (make-l-hash-table)
  (make-vector (add1 l-hash-vector-length) *nothing*))

(define* (l-hash-table-get table keys . thunk)
  (let ([len (length keys)])
    (let loop ([obj (vector-ref table (min len l-hash-vector-length))]
               [keys (if (< len l-hash-vector-length) keys (cons len keys))])
      (cond [(eq? obj *nothing*)
             (if (null? thunk)
               (error 'l-hash-table-get "no value found.") ((car thunk)))]
            [(null? keys) obj]
            [(not (hash-table? obj))
             (error 'l-hash-table-get "got to a premature value.")]
            [else (loop (hash-table-get obj (car keys) return-nothing)
                        (cdr keys))]))))

(define* (l-hash-table-put! table keys value)
  (let* ([len (length keys)]
         [obj (vector-ref table (min len l-hash-vector-length))])
    (when (eq? obj *nothing*)
      (set! obj (if (zero? len) value (make-hash-table 'weak)))
      (vector-set! table (min len l-hash-vector-length) obj))
    (unless (zero? len)
      (let loop ([obj obj]
                 [keys (if (< len l-hash-vector-length) keys (cons len keys))])
        (cond [(not (hash-table? obj))
               (error 'l-hash-table-put! "got to a premature value.")]
              [(null? (cdr keys)) (hash-table-put! obj (car keys) value)]
              [else (let ([value (hash-table-get
                                  obj (car keys) return-nothing)])
                      (when (eq? value *nothing*)
                        (set! value (make-hash-table 'weak))
                        (hash-table-put! obj (car keys) value))
                      (loop value (cdr keys)))])))))

(defsubst*
  (set-l-hash-table-get! table key value) (l-hash-table-put! table key value)
  (_ table key thunk value)               (l-hash-table-put! table key value))

;; Simple memoization.

(define* (memoize f)
  (let ([table (make-l-hash-table)])
    (lambda args
      (l-hash-table-get
       table args
       (thunk
         (let ([r (apply f args)]) (l-hash-table-put! table args r) r))))))

(defsubst* (memoize! f) (set! f (memoize f)))

;; ---------------------------------------------------------------------------
(defsubst* (loop-for clause ...)
  (collect => (acc (void) acc) do clause ...))

(defsubst* (list-of expr clause ...)
  (reverse (collect (acc '() (cons expr acc)) clause ...)))

(defsubst* (sum-of expr clause ...)
  (collect (acc 0 (+ expr acc)) clause ...))

(defsubst* (product-of expr clause ...)
  (collect (acc 1 (* expr acc)) clause ...))

(defsubst* (count-of clause ...)
  (sum-of 1 clause ...))


(defsyntax* (collect stx)
  (define (split id stxs)
    (let loop ([stxs '()] [stxss '()]
               [l (if (syntax? stxs) (syntax->list stxs) stxs)])
      (cond [(null? l) (reverse (cons (reverse stxs) stxss))]
            [(and (identifier? (car l)) (module-identifier=? id (car l)))
             (loop '() (cons (reverse stxs) stxss) (cdr l))]
            [else (loop (cons (car l) stxs) stxss (cdr l))])))
  (define (gen-loop generate add-aux! &optional hacked)
    (with-syntax ([generate generate]
                  [(cur step done? value)
                   (generate-temporaries '(cur step done? value))])
      (add-aux! #'((cur step done? value) (apply values generate)))
      (with-syntax ([value #'(if value (value cur) cur)])
        (with-syntax ([value (if hacked
                               #`(let ([r value]) (set! #,hacked r) r)
                               #'value)])
          #'(cur cur (step cur) (and done? (done? cur)) value)))))
  (define (gen var args add-aux! hack-var! &optional seq?)
    (define (hack!) (when (and seq? hack-var!) (hack-var! var)))
    (define (gen1 arg) (if seq? arg (gen-loop arg add-aux!)))
    (with-syntax ([v var])
      (syntax-case args (then until while .. ..<)
        [(arg)            (gen1 #'(collect-iterator arg))]
        [(a b ..  z)      (gen1 #'(collect-numerator a b  z        ))]
        [(a b ..   )      (gen1 #'(collect-numerator a b  #f       ))]
        [(a   ..  z)      (gen1 #'(collect-numerator a #f z        ))]
        [(a   ..   )      (gen1 #'(collect-numerator a #f #f       ))]
        [(a b ..< z)      (gen1 #'(collect-numerator a b  z  '<    ))]
        [(a   ..< z)      (gen1 #'(collect-numerator a #f z  '<    ))]
        [(a b .. while z) (gen1 #'(collect-numerator a b  z  'while))]
        [(a   .. while z) (gen1 #'(collect-numerator a #f z  'while))]
        [(a b .. until z) (gen1 #'(collect-numerator a b  z  'until))]
        [(a   .. until z) (gen1 #'(collect-numerator a #f z  'until))]
        [(arg then next) (hack!)
         (if seq? ; making seq? => convert to composable funcs
           #'(list arg (lambda (v) next) #f #f)
           #'(v arg next #f v))]
        [(arg then next while cond) (hack!)
         (if seq?
           #'(list arg (lambda (v) next) (lambda (v) (not cond)) #f)
           #'(v arg next (not cond) v))]
        [(arg then next until cond) (hack!)
         (if seq?
           #'(list arg (lambda (v) next) (lambda (v) cond) #f)
           #'(v arg next cond v))]
        [(arg while cond) (hack!)
         (if seq?
           #'(list #f #f #f (lambda (_) (if cond arg collect-final)))
           #'(v #f #f #f (begin (set! v arg) (if cond v collect-final))))]
        [(arg until cond) (hack!)
         (if seq?
           #'(list #f #f #f (lambda (_) (if cond collect-final arg)))
           #'(v #f #f #f (begin (set! v arg) (if cond collect-final v))))]
        [(f x ...)
         (let ([argss (split #'<- args)])
           (if (= 1 (length argss))
             (gen1 #'(f x ...))
             (let ([hacked #f])
               (with-syntax
                   ([(gen ...)
                     (map (lambda (as)
                            (gen var as add-aux!
                                 (lambda (v) (set! hacked v) (hack-var! v))
                                 #t))
                          argss)])
                 (gen-loop #'(sequential-generators gen ...)
                           add-aux! hacked)))))])))
  (define-values (acc base0 expr clauses fwd?)
    (syntax-case stx (<= =>)
      [(_ <= (acc base expr) clause ...)
       (values #'acc #'base #'expr #'(clause ...) #f)]
      [(_ => (acc base expr) clause ...)
       (values #'acc #'base #'expr #'(clause ...) #t)]
      [(_ (acc base expr) clause ...)
       (values #'acc #'base #'expr #'(clause ...) #f)]))
  (define need-break? #f)
  (define loop-body
    (let c-loop ([base base0] [clauses clauses] [mode 'when] [rev? #f])
      (syntax-case clauses (<- <-! is do when unless while until)
        [() (if (if rev? (not fwd?) fwd?)
              #`(letsubst ([#,acc #,base]) #,expr)
              expr)]
        [((var <-! arg ...) rest ...)
         (c-loop base #'((var <- arg ...) rest ...) mode 'rev!)]
        [((var <- arg ...) rest ...)
         (let ([rev? (if (eq? 'rev! rev?) #t #f)]
               [gens (split #'and #'(var <- arg ...))]
               [loop-id (car (generate-temporaries '(loop)))]
               [aux '()] [hacked-vars '()])
           (for-each
            (lambda (g)
              (syntax-case g (<-)
                [(var <- arg ...) (identifier? #'var) #f]
                [_ (raise-syntax-error
                    #f "expected a generator clause" stx g)]))
            gens)
           (with-syntax ([((var <- arg ...) ...) gens])
             ;; Hack needed: generator variables are defined later in the loop
             ;; just before their code, after the place where the expression
             ;; appear in setup code.  This is usually not a problem since
             ;; functions are applied the same, but when using expression
             ;; iteration (`then') in a sequential range which is in
             ;; simultaneous iteration where real expressions are turned to
             ;; functions (which are define before variables the might
             ;; reference).  This could be eliminated, restricting expressions
             ;; from referencing variables that are bound in parallel, but this
             ;; is usually the power of using expression (which can be claimed
             ;; redundant).  The hack is doing this:
             ;;  (let ([x #f] ...)
             ;;    ... (let ([x (let ([r value]) (set! x r) r)])))
             ;; The problem is that the extra junk makes it run twice slower,
             ;; so do this only for bindings that has the above scenario
             ;; (parallel of sequential of expression generators).  To test it,
             ;; do this:
             ;;  (list-of (list c x y)
             ;;    (c <- 1 .. 5 and x <- 1 <- 'x then y
             ;;                 and y <- 1 <- 'y then x))
             ;; but this always works:
             ;;  (list-of (list c x y)
             ;;    (c <- 1 .. 5 and x <- 'x then y and y <- 'y then x))
             (with-syntax ([((cur fst next done? value) ...)
                            (map (lambda (v as)
                                   (gen v as
                                        (lambda (a) (set! aux (cons a aux)))
                                        (lambda (v)
                                          (set! hacked-vars
                                                (cons v hacked-vars)))))
                                 (syntax->list #'(var ...))
                                 (syntax->list #'((arg ...) ...)))]
                           [loop loop-id]
                           [(aux ...) (reverse aux)] [acc acc] [base base])
               (with-syntax
                   ([body
                     (let* ([fwd? (if rev? (not fwd?) fwd?)]
                            [return (if fwd? #'base #'acc)]
                            [body (if fwd?
                                    (c-loop #`(#,loop-id next ...)
                                            #'(rest ...) mode rev?)
                                    #`(loop next ...
                                            #,(c-loop #'acc #'(rest ...)
                                                      mode rev?)))])
                       #`(let-values (aux ...)
                           (let loop ([cur fst] ...
                                      #,@(if fwd? #'() #'((acc base))))
                             (if (or done? ...)
                               #,return
                               #,(let vloop ([vars (syntax->list #'(var ...))]
                                             [values (syntax->list
                                                      #'(value ...))])
                                   (if (null? vars)
                                     body
                                     #`(let ([#,(car vars) #,(car values)])
                                         (if (eq? #,(car vars) collect-final)
                                           #,return
                                           #,(vloop (cdr vars)
                                                    (cdr values))))))))))])
                 (if (null? hacked-vars)
                   #'body
                   (with-syntax ([(var ...) (reverse hacked-vars)])
                     #'(let ([var #f] ...) body)))))))]
        [((var is is-expr) rest ...)
         #`(let ([var is-expr]) #,(c-loop base #'(rest ...) mode rev?))]
        [(while cond rest ...)
         #`(if cond
             #,(c-loop base #'(rest ...) mode rev?)
             #,(if (if rev? (not fwd?) fwd?)
                 base0 (begin (set! need-break? #t) #`(break #,base))))]
        [(until cond rest ...)
         #`(if cond
             #,(if (if rev? (not fwd?) fwd?)
                 base0 (begin (set! need-break? #t) #`(break #,base)))
             #,(c-loop base #'(rest ...) mode rev?))]
        [(do     rest ...) (c-loop base #'(rest ...) 'do     rev?)]
        [(when   rest ...) (c-loop base #'(rest ...) 'when   rev?)]
        [(unless rest ...) (c-loop base #'(rest ...) 'unless rev?)]
        [(expr rest ...)
         (with-syntax ([cont (c-loop base #'(rest ...) mode rev?)])
           (case mode
             [(when)   #`(if expr cont #,base)]
             [(unless) #`(if expr #,base cont)]
             [(do)     #`(begin expr cont)]))])))
  (if need-break?
    #`(let/ec break #,loop-body) loop-body))

(define (sequential-generators gen . rest)
  (let-values ([(new) #f] [(fst step done? value) (values . gen)])
    (define (next!)
      (and (pair? rest)
           (begin (set! gen   (car rest)) (set! rest  (cdr rest))
                  (set! fst   (1st gen))  (set! step  (2nd gen))
                  (set! done? (3rd gen))  (set! value (4th gen))
                  #t)))
    (list fst
          (lambda (x)
            (let ([r (step (if new (begin0 new (set! new #f)) x))])
              (if (and done? (done? r)) (if (next!) fst collect-final) r)))
          (lambda (x)
            (and (null? rest)
                 (or (eq? x collect-final) (and done? (done? x)))))
          (lambda (x)
            (let ([r (if value (value x) x)])
              (if (eq? r collect-final)
                (let* ([n? (next!)] [r (and n? (if value (value fst) fst))])
                  (set! new fst)
                  (if (or (not n?) (done? fst)) collect-final r))
                r))))))

(define (function->iterator f &optional done? include-last?)
  (define arity
    (cond [(procedure-arity-includes? f 0) 0]
          [(procedure-arity-includes? f 1) 1]
          [else (error 'function->iterator
                       "don't know how to iterate over function ~e" f)]))
  (when (and done? include-last?)
    (set! done?
          (let ([d? done?])
            (lambda (x) (when (d? x) (set! f (lambda _ collect-final))) #f))))
  (when (eq? 1 arity) (set! f (function-iterator f collect-final)))
  (list (void) void #f
        (if done?
          (lambda (_)
            (let ([x (f)])
              (if (or (eq? x collect-final) (done? x)) collect-final x)))
          (lambda (_) (f)))))

(define* (collect-iterator seq)
  (define (out-of-range r) (lambda (x) (<= r x)))
  (cond
   [(list? seq) (list seq cdr null? car)]
   [(vector? seq) (list 0 add1 (out-of-range (vector-length seq))
                        (lambda (i) (vector-ref seq i)))]
   [(string? seq) (list 0 add1 (out-of-range (string-length seq))
                        (lambda (i) (string-ref seq i)))]
   [(integer? seq) (list 0 add1 (out-of-range seq) #f)]
   [(procedure? seq)
    (function->iterator seq)]
   [(hash-table? seq)
    (collect-iterator (lambda (yield)
                        (hash-table-for-each
                         seq (lambda (k v) (yield (cons k v))))))]
   [else (list seq identity #f #f)]))

(define* (collect-numerator from second to &optional flag)
  (define (check-type pred? &optional not-to)
    (and (pred? from) (or (not second) (pred? second))
         (or not-to (not to) (pred? to))))
  (define (to->pred)
    (and to (let ([to (if (and (procedure? to)
                               (procedure-arity-includes? to 1))
                        to (lambda (x) (equal? x to)))])
              (if (eq? 'while flag) (negate to) to))))
  (when (and (memq flag '(while until))
             (not (and (procedure? to) (procedure-arity-includes? to 1))))
    (set! to (lambda (x) (equal? x to))))
  (cond [(check-type number?)
         (let* ([step
                 (cond [second (- second from)]
                       [(and (number? to) (> from to)) -1]
                       [else 1])]
                [gt?
                 (case flag
                   [(#f) (if (positive? step) > <)]
                   [(<)  (if (positive? step) >= <=)]
                   [else (error 'collect-numerator "internal error")])])
           (list from
                 (lambda (x) (+ x step))
                 (if (number? to) (lambda (x) (gt? x to)) #f)
                 #f))]
        [(check-type char? #t)
         (let ([numerator (collect-numerator
                           (char->integer from)
                           (and second (char->integer second))
                           (cond [(char? to) (char->integer to)]
                                 [(and (procedure? to)
                                       (procedure-arity-includes? to 1))
                                  (compose to integer->char)]
                                 [else to])
                           flag)])
           (list (1st numerator) (2nd numerator) (3rd numerator)
                 integer->char))]
        [(and (procedure? from) (not second))
         (let ([to (to->pred)])
           (function->iterator from to (and (not flag) to)))]
        [else
         (cond [(and (number? from) (number? second))
                (let ([d (- second from)]) (set! second (lambda (x) (+ x d))))]
               [(not second) (set! second identity)]
               [(not (and (procedure? second)
                          (procedure-arity-includes? second 1)))
                (error 'collect-numerator
                       "don't know how to enumerate ~e ~e .. ~e"
                       from second to)])
         (if (not to)
           (list from second #f #f)
           (let ([to (to->pred)])
             (if (or flag (not to))
               (list from second to #f)
               (let ([almost-done? (to from)] [done? #f])
                 (list from (lambda (x)
                              (if almost-done?
                                (set! done? #t)
                                (let ([next (second x)])
                                  (when (to next) (set! almost-done? #t))
                                  next)))
                       (lambda (_) done?) #f)))))]))

(define* collect-final (list "*"))

(define* (function-iterator f . finally)
  (define ret #f)
  (define (done)
    (set! cnt (thunk (error 'function-iterator
                            "iterated function ~e exhausted." f))))
  (define cnt
    (cond [(null? finally) (thunk (let ([r (f yield)]) (done) (ret r)))]
          [(and (procedure? (car finally))
                (procedure-arity-includes? (car finally) 0))
           (thunk (f yield) (done) (ret ((car finally))))]
          [else (thunk (f yield) (done) (ret (car finally)))]))
  (define (yield v) (let/cc k (set! cnt (thunk (k v))) (ret v)))
  (thunk (let/cc ret1 (set! ret ret1) (cnt))))


;; ----------------------------------------------------------------------------
(define* *echo-display-handler* (make-parameter display))
(define* *echo-write-handler* (make-parameter write))

(defsyntax* (echo-quote stx)
  (define (process args)
    (syntax-case args ()
      [() #'()]
      [(x . more) (with-syntax ([more (process #'more)])
                    (if (syntax-keyword? #'x)
                      ;; `datum' protects from using a local binding
                      #'(echo: (#%datum . x) . more) #'(x . more)))]
      [x #'x])) ; only in case of (echo ... . x)
  (syntax-case stx ()
    [(_ head . args) (quasisyntax/loc stx (head . #,(process #'args)))]))

(provide (rename echo-syntax echo))
(defsyntax (echo-syntax stx)
  (syntax-case stx ()
    [(_ . args) (syntax/loc stx (echo-quote echo . args))]
    [_ #'echo]))

;; A table for user-defined keywords
(define echo-user-table (make-hash-table))

;; Make an echo keyword handler for a given procedure.  The handler gets the
;; current list of arguments and returns the new list of arguments.
(define (make-echo-handler keyword proc)
  (let* ([arity (procedure-arity proc)]
         [at-least (and (arity-at-least? arity)
                        (arity-at-least-value arity))]
         [required (or at-least arity)])
    (unless (integer? required)
      (error 'echo "handler function for `~.s' has bad arity" keyword))
    (lambda (args)
      (if (< (length args) required)
        (error 'echo "user-keyword `~.s' didn't get enough arguments" keyword)
        (let*-values ([(proc-args rest-args)
                       (if at-least
                         (values args '())
                         (let loop ([rest args] [args '()] [n required])
                           (if (zero? n)
                             (values (reverse args) rest)
                             (loop (cdr rest) (cons (car rest) args)
                                   (sub1 n)))))]
                      [(result) (apply proc proc-args)])
          (cond [(list? result) (append result rest-args)]
                [(and result (not (void? result)))
                 (if (keyword? result)
                   (list* echo: result rest-args) (cons result rest-args))]
                [else rest-args]))))))

(define (echo . args)
  (define break: "break:")
  (define call:  "call:")
  (let ([printer (*echo-display-handler*)] [out (current-output-port)]
        [spaces? #t] [newline? 'x] [first? #t] [str? #f] [keys? #f]
        [states '()])
    (define (getarg) (begin0 (car args) (set! args (cdr args))))
    (define (push-state!)
      (set! states (cons (list printer out spaces? newline? first? str? keys?)
                         states)))
    (define (pop-state!)
      (if (null? states)
        (error 'echo "tried to restore a state, but none saved")
        (let ([s (car states)])
          (set! states (cdr states))
          (set!-values (printer out spaces? newline? first? str? keys?)
                       (apply values s)))))
    (define (set-out! arg)
      (set! out (or arg (open-output-string)))
      (set! str? (not arg))
      (unless (output-port? out)
        (error 'echo "expected an output-port or #f, given ~e" out)))
    (define (printer1! hparam)
      (unless (or (null? args) (eq? echo: (car args)))
        (let ([p (hparam)])
          (unless (eq? printer p)
            (let ([v (getarg)] [op printer])
              (set! printer p)
              (set! args (list* v echo: :>> op args)))))))
    (define (process-list)
      (define level 1)
      (define ((do-lists args))
        ;; this returns a thunk so the whole thing is not expanded in one shot
        (let loop ([args args] [cars '()] [cdrs '()] [last? '?])
          (if (null? args)
            (reverse
             (if last? cars (list* (do-lists (reverse cdrs)) call: cars)))
            (let* ([1st (car args)] [p? (pair? 1st)])
              (if (and last? (eq? 1st break:))
                (reverse cars)
                (if (null? 1st)
                  '()
                  (loop (cdr args)
                        (if (eq? 1st break:)
                          cars (cons (if p? (car 1st) 1st) cars))
                        (cons (if p? (cdr 1st) 1st) cdrs)
                        (if p?
                          (or (eq? last? #t) (null? (cdr 1st)))
                          last?))))))))
      (let loop ([l-args '()])
        (define (pop-key-tags)
          (when (and (pair? l-args) (eq? echo: (car l-args)))
            (set! l-args (cdr l-args)) (pop-key-tags)))
        (when (null? args)
          (error 'echo "found a `~.s' with no matching `~.s'" :\{ :\}))
        (let ([arg (getarg)])
          (define (next) (loop (cons arg l-args)))
          (cond
           [(eq? arg echo:) (set! keys? (or keys? 'just-one)) (next)]
           [(and keys? (keyword? arg))
            (unless (eq? keys? #t) (set! keys? #f))
            (case arg
              [(:\})
               (set! level (sub1 level))
               (if (zero? level)
                 (begin
                   (pop-key-tags)
                   (set! args (append ((do-lists (reverse l-args))) args)))
                 (next))]
              [(:\{)
               (set! level (add1 level)) (next)]
              [(:^)
               (when (eq? 1 level) (set! arg break:) (pop-key-tags))
               (next)]
              [else (next)])]
           [else (next)]))))
    (let loop ()
      (unless (null? args)
        (let ([arg (getarg)])
          (cond
           [(eq? arg call:) (set! args (append ((getarg)) args))]
           [(eq? arg echo:) (set! keys? (or keys? 'just-one))]
           [(and keys? (keyword? arg))
            (unless (eq? keys? #t) (set! keys? #f))
            (case arg
              [(:>e)    (set-out! (current-error-port))]
              [(:>o)    (set-out! (current-output-port))]
              [(:>s)    (set-out! #f)]
              [(:>)     (unless (or (null? args) (eq? echo: (car args)))
                          (set-out! (getarg)))]
              [(:>>)    (unless (or (null? args) (eq? echo: (car args)))
                          (let ([p (getarg)])
                            (set! printer (if (eq? 1 (procedure-arity p))
                                            (lambda (x _) (p x)) p))))]
              [(:d)     (set! printer (*echo-display-handler*))]
              [(:w)     (set! printer (*echo-write-handler*))]
              [(:d1)    (printer1! *echo-display-handler*)]
              [(:w1)    (printer1! *echo-write-handler*)]
              [(:s-)    (set! spaces? (and spaces? (not first?) 'just-one))]
              [(:s+)    (set! spaces? #t)]
              [(:n-)    (set! newline? #f)]
              [(:n+)    (set! newline? #t)]
              [(:n)     (newline out) (set! first? #t)]
              [(:: :)   (set! first? #t)]
              [(:push)  (push-state!)]
              [(:pop)   (pop-state!)]
              [(:\{)    (process-list)]
              [(:\} :^) (error 'echo "unexpected list keyword `~.s'" arg)]
              [(:k-)    (set! keys? #f)]
              [(:k+)    (set! keys? #t)]
              [(:set-user :unset-user)
               (let loop ([keyword echo:])
                 (if (null? args)
                   (error 'echo "expecting a keyword+handler after `~.s'" arg)
                   (let ([x (getarg)])
                     (cond
                      [(eq? keyword echo:) (loop x)]
                      [(not (keyword? keyword))
                       (error 'echo "got a `~.s' with a non-keyword `~.s'"
                              arg keyword)]
                      [(eq? arg :unset-user)
                       (hash-table-put! echo-user-table keyword #f)]
                      [(eq? x echo:) (loop keyword)]
                      [else (let ([handler (if (procedure? x)
                                             (make-echo-handler keyword x) x)])
                              (hash-table-put! echo-user-table keyword handler)
                              (when (and newline? (not (eq? #t newline))
                                         (null? args))
                                (set! newline? #f)))]))))]
              [else
               (let ([user (hash-table-get echo-user-table arg (thunk #f))])
                 (if user
                   (set! args
                         (cond [(procedure? user) (user args)]
                               [(keyword? user) (list* echo: user args)]
                               [else (cons user args)]))
                   (error 'echo "unknown keyword: `~.s'" arg)))])]
           [first?  (printer arg out) (set! first? #f)]
           [spaces? (display " " out) (printer arg out)
                    (unless (eq? spaces? #t) (set! spaces? #f))]
           [else (printer arg out)])
          (loop))))
    (when (and newline? (or (not str?) (eq? newline? #t))) (newline out))
    (when str? (get-output-string out))))

(provide (rename echos-syntax echos))
(defsyntax (echos-syntax stx)
  (syntax-case stx ()
    [(_ . args) (syntax/loc stx (echo-syntax :>s . args))]
    [_ #'echos]))
(define (echos . args)
  (echo echo: :>s . args))

(define* echo: "echo:")

;; ----------------------------------------------------------------------------
;; Simple macros

(defsubst* (named-lambda name args . body)
  (letrec ([name (lambda args . body)]) name))

(defsubst* (thunk body ...) (lambda () body ...))

(defsubst* (while cond body ...)
  (let loop () (when cond (begin body ... (loop)))))
(defsubst* (until cond body ...)
  (while (not cond) body ...))

(defsubst* (dotimes [i n] body0 body ...)
  (let ([n* n])
    (let loop ([i 0])
      (when (< i n*) body0 body ... (loop (add1 i))))))

(defsubst* (dolist [x lst] body0 body ...)
  (for-each (lambda (x) body0 body ...) lst))

(defsubst* (no-errors body ...)
  (with-handlers ([void (lambda (x) #f)]) body ...))
(defsubst* (no-errors* body ...)
  (with-handlers ([void identity]) body ...))

(defsyntax* (regexp-case stx)
  (define (do-clause c)
    (syntax-case c (else base-else => base-=>)
      [(else body ...) c]
      [(base-else body ...) #'(else body ...)]
      [(re => func) #'((regexp-match re s) => (lambda (r) (apply func r)))]
      [(re base-=> func) #'((regexp-match re s) => (lambda (r) (apply func r)))]
      [((re . args) body ...)
       #`((regexp-match re s) =>
          (lambda (r)
            (apply (lambda (#,(datum->syntax-object c 'match c) . args)
                     body ...)
                   r)))]
      [(re body ...) #'((regexp-match re s) body ...)]))
  (syntax-case stx ()
    [(_ str clause ...)
     #`(let ([s str])
         (cond #,@(map do-clause (syntax->list #'(clause ...)))))]))
