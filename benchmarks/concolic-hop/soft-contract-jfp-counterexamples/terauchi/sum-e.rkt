#lang racket
(module assert racket
  (define assert (λ (✌0) (error "ASSERT_UNREACHABLE"))) (provide/contract [assert ((not/c false?) . -> . any/c)]))

(module m racket
  (provide/contract [main (-> integer? any/c)])
  (require (submod ".." assert))
  (define (sum x)
    (if (<= x 0) 0 (+ x (sum (- x 1)))))
  (define (main n)
    (assert (<= 100 (sum n)))))

(require 'm)

((λ (✌0) (✌0 0)) main)

