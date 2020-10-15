#lang racket
(require (for-syntax racket/struct-info))
(provide (for-syntax get-relevant-struct-info))

(define-for-syntax (get-relevant-struct-info who stx id Ts)
  (struct not-bound ())
  (define val (syntax-local-value id (λ () (not-bound))))
  (when (not-bound? val)
    (raise-syntax-error
     who
     "expected a struct-bound identifier as its first argument, but it isn't bound"
     stx
     id))
  (unless (struct-info? val)
    (raise-syntax-error
     who
     (format "expected a struct-bound identifier as its first argument\n  bound to: ~e"
             val)
     stx
     id))
  (define struct-info-list (extract-struct-info val))
  (define selectors (reverse (list-ref struct-info-list 3)))
  (when (and (pair? selectors)
             (equal? (car selectors) #f))
    (raise-syntax-error
     who
     "struct binding does not have full selector information"
     stx
     id))
  (unless (= (length (syntax->list Ts))
             (length selectors))
    (raise-syntax-error
     who
     (format "struct fields and types don't match\n  struct field count: ~a\n  struct/s argument count: ~a"
             (length selectors)
             (length (syntax->list Ts)))
     stx
     id))
  (define constructor (list-ref struct-info-list 1))
  (unless constructor
    (raise-syntax-error
     who
     "cannot find constructor"
     stx
     id))
  (define predicate (list-ref struct-info-list 2))
  (unless constructor
    (raise-syntax-error
     who
     "cannot find predicate"
     stx
     id))
  (values constructor predicate selectors))