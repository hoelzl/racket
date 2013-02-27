;;; Written by Eli Barzilay: Maze is Life!  (eli@barzilay.org)

#lang mzscheme

;; Original idea thanks to Eric Kidd who stole it from Dylan
(provide setf!)
(define-syntax (setf! stx)
  (define (set!-prefix id)
    (datum->syntax-object
     id
     (string->symbol (string-append "set-" (symbol->string (syntax-e id)) "!"))
     id id))
  (syntax-case stx (setf!)
    ;; if the getter is a set!-transformer, make it do its thing
    [(setf! getter . xs)
     (and (identifier? #'getter)
          (set!-transformer? (syntax-local-value #'getter (lambda () #f))))
     ((set!-transformer-procedure (syntax-local-value #'getter)) stx)]
    [(setf! place val)
     ;; need to expand place first, in case it is itself a macro
     (with-syntax ([place (local-expand
                           #'place 'expression
                           (append (list #'#%app #'#%top #'#%datum)
                                   (map (lambda (s)
                                          (datum->syntax-object #'place s #f))
                                        '(#%app #%top #%datum))))])
       (syntax-case #'place ()
         [(getter args ...)
          (if (identifier? #'getter)
            (with-syntax ([setter (set!-prefix #'getter)])
              (syntax/loc stx (setter args ... val)))
            (raise-syntax-error #f "not an identifier" stx #'getter))]
         [_ (syntax/loc stx (set! place val))]))]
    [(setf! place val . more)
     (let loop ([pvs #'(place val . more)] [r '()])
       (syntax-case pvs ()
         [(p v . more)
          (loop #'more (cons (syntax/loc stx (setf! p v)) r))]
         [() (quasisyntax/loc stx (begin #,@(reverse r)))]
         [_ (raise-syntax-error #f "uneven number of forms" stx)]))]))

;; This could have been expressed using `setf!-values', but that would lead to
;; an unnecessary creation of a values tuple.
(provide psetf!)
(define-syntax (psetf! stx)
  (syntax-case stx ()
    ;; optimize common case
    [(_ place val) (syntax/loc stx (setf! place val))]
    [(_ more ...)
     (let loop ([vars '()] [vals '()] [more (syntax->list #'(more ...))])
       (cond
        [(null? more)
         (let ([vars (reverse vars)]
               [vals (reverse vals)]
               [tmps (generate-temporaries (map (lambda (x) 'x) vars))])
           (quasisyntax/loc stx
             (let #,(map (lambda (t v) #`(#,t #,v)) tmps vals)
               #,@(map (lambda (v t) #`(setf! #,v #,t)) vars tmps))))]
        [(null? (cdr more))
         (raise-syntax-error #f "uneven number of forms" stx)]
        [else (loop (cons (car more) vars) (cons (cadr more) vals)
                    (cddr more))]))]))

(provide setf!-values)
(define-syntax (setf!-values stx)
  (syntax-case stx ()
    ;; optimize common case
    [(_ (place) val) (syntax/loc stx (setf! place val))]
    [(_ (place ...) values)
     (with-syntax ([(temp ...) (datum->syntax-object
                                #'(place ...)
                                (generate-temporaries #'(place ...))
                                #'(place ...))])
       (syntax/loc stx
         (let-values ([(temp ...) values])
           (setf! place temp) ...)))]))

(provide set-values! set-list! set-vector!)
(define-syntaxes (set-values! set-list! set-vector!)
  (let ([make-setter
         (lambda (convert)
           (lambda (stx)
             (syntax-case stx ()
               [(_ x y ...)
                (let loop ([args (syntax->list #'(x y ...))] [as '()])
                  (if (null? (cdr args))
                    (quasisyntax/loc stx
                      (setf!-values #,(datum->syntax-object
                                       #'(x y ...) (reverse as) #'(x y ...))
                                    #,(convert (car args))))
                    (loop (cdr args) (cons (car args) as))))])))])
    (values
     ;; set-values!
     (make-setter (lambda (x) x))
     ;; set-list!
     (make-setter (lambda (x) #`(apply values #,x)))
     ;; set-vector!
     (make-setter (lambda (x) #`(apply values (vector->list #,x)))))))

(provide shift! rotate! inc! dec! push! pop!)
(define-syntaxes (shift! rotate! inc! dec! push! pop!)
  (let* ([protect-indexes
          (lambda (place body)
            (syntax-case place ()
              [(getter . xs)
               (let ([bindings+expr
                      (let loop ([xs #'xs]
                                 [bindings '()]
                                 [expr (list #'getter)]
                                 [all-ids? #t])
                        (syntax-case xs ()
                          [() (and (not all-ids?)
                                   (cons (reverse bindings) (reverse expr)))]
                          [(x . xs)
                           (let ([new (datum->syntax-object
                                       #'x (gensym) #'x)])
                             (loop #'xs
                                   (cons (list new #'x) bindings)
                                   (cons new expr)
                                   (and (identifier? #'x) all-ids?)))]
                          [x (and (not (and all-ids? (identifier? #'x)))
                                  (let ([new (datum->syntax-object
                                              #'x (gensym) #'x)])
                                    (cons (reverse (cons (list new #'x)
                                                          bindings))
                                          (append (reverse expr) new))))]))])
                 (if bindings+expr
                   #`(let #,(car bindings+expr) #,(body (cdr bindings+expr)))
                   (body place)))]
              [_ (body place)]))]
         [protect-indexes-list
          (lambda (places body)
            (let loop ([ps places] [r '()])
              (if (null? ps)
                (body (reverse r))
                (protect-indexes (car ps) (lambda (p)
                                            (loop (cdr ps) (cons p r)))))))])
    (values

     ;; --- shift!
     (lambda (stx)
       (syntax-case stx ()
         [(_ x y more ...)
          (protect-indexes-list (syntax->list #'(x y more ...))
            (lambda (vars)
              (let loop ([vs vars] [r '()])
                (if (null? (cdr vs))
                  (quasisyntax/loc stx
                    (let ([v #,(car vars)])
                      (psetf! #,@(datum->syntax-object
                                  #'(x y more ...)
                                  (reverse r)
                                  #'(x y more ...)))
                      v))
                  (loop (cdr vs) (list* (cadr vs) (car vs) r))))))]))
     ;; --- rotate!
     (lambda (stx)
       (syntax-case stx ()
         [(_ x) #'(void)]
         [(_ x xs ...)
          (protect-indexes-list (syntax->list #'(x xs ...))
            (lambda (vars)
              (let loop ([vs vars] [r '()])
                (if (null? (cdr vs))
                  (quasisyntax/loc stx
                    (psetf! #,@(datum->syntax-object
                                #'(x xs ...)
                                (reverse (list* (car vars) (car vs) r))
                                #'(x xs ...))))
                  (loop (cdr vs) (list* (cadr vs) (car vs) r))))))]))
     ;; --- inc!
     (lambda (stx)
       (syntax-case stx ()
         [(_ p) #'(_ p 1)]
         [(_ p d) (protect-indexes #'p
                    (lambda (p) #`(setf! #,p (+ #,p d))))]))
     ;; --- dec!
     (lambda (stx)
       (syntax-case stx ()
         [(_ p) #'(_ p 1)]
         [(_ p d) (protect-indexes #'p
                    (lambda (p) #`(setf! #,p (- #,p d))))]))
     ;; --- push!
     (lambda (stx)
       (syntax-case stx ()
         [(_ x p) (protect-indexes #'p
                    (lambda (p) #`(setf! #,p (cons x #,p))))]))
     ;; --- pop!
     (lambda (stx)
       (syntax-case stx ()
         [(_ p) (protect-indexes #'p
                  (lambda (p)
                    #`(let ([p1 #,p])
                        (begin0 (car p1) (setf! #,p (cdr p1))))))])))))
