#lang racket
(module lib racket
  (define member (λ (✌0 ✌1) (cons (λ (✌2) (error "ASSERT_UNREACHABLE")) null)))
  (provide/contract [member (any/c (listof any/c) . -> . (or/c false? (non-empty-listof any/c)))]))
(module ex-03 racket
  (provide/contract [f (any/c (listof any/c) . -> . false?)])
  (require (submod ".." lib))
  (define (f v l)
    (let ([x (member v l)])
      (if x x #f))))
(require 'ex-03 'lib)
(f (λ (✌0) (error "ASSERT_UNREACHABLE")) null)
