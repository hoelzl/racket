;;; Written by Eli Barzilay: Maze is Life!  (eli@barzilay.org)


#lang s-exp swindle/base

(require swindle/setf swindle/misc)
(provide (all-from-except swindle/base set! set!-values #%module-begin)
         (rename module-begin~ #%module-begin)
         (all-from-except swindle/setf setf! psetf!)
         (rename setf! set!) (rename psetf! pset!)
         (rename setf!-values set!-values)
         (all-from swindle/misc))
(defsyntax (module-begin~ stx)
  (let ([e (if (syntax? stx) (syntax-e stx) stx)])
    (if (pair? e)
      (datum->syntax-object
       (quote-syntax here)
       (list* (quote-syntax #%plain-module-begin)
              (datum->syntax-object stx
                                    (list (quote-syntax require-for-syntax)
                                          'swindle/turbo))
              (cdr e))
       stx)
      (raise-syntax-error #f "bad syntax" stx)))
  ;; This doesn't work anymore (from 203.4)
  ;; (syntax-rules ()
  ;;   [(_ . body)
  ;;    (#%plain-module-begin
  ;;     (require-for-syntax swindle/turbo) . body)])
  )
