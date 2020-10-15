#lang racket/base

(require (prefix-in rosette: rosette/safe)
         (only-in "../store.rkt" get-current-concrete-value))

(provide immediate-concretize)

(define (immediate-concretize v)
  (cond
    [(rosette:union? v)
     (for/first ([guard-value (in-list (rosette:union-contents v))]
                 #:when (get-current-concrete-value (car guard-value)))
       (immediate-concretize (cdr guard-value)))]
    [(list? v) v]
    [(procedure? v) v]
    [else (get-current-concrete-value v)]))
