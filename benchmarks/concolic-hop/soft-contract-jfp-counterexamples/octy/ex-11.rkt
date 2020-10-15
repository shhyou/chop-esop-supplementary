#lang racket
(module g racket
  (define g (λ (✌0) (error "ASSERT_UNREACHABLE")))
  (provide/contract [g ((cons/c number? number?) . -> . symbol?)]))

(module f racket
  (provide/contract [f (cons? . -> . symbol?)])
  (require (submod ".." g))
  (define (f p)
    (if (and (number? (car p)) (number? (#|HERE|# car p))) (g p) 'no)))

(require 'f)
(f (cons 0 (λ (✌0) (error "ASSERT_UNREACHABLE"))))
