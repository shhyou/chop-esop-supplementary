#lang racket
(module assert racket
  (define assert (λ (✌0) (error "ASSERT_UNREACHABLE"))) (provide/contract [assert ((not/c false?) . -> . any/c)]))

(module m racket
  (provide/contract [main (integer? . -> . any/c)])
  (require (submod ".." assert))
  (define (mult x y)
    (if (or (<= x 0) (<= y 0)) 0 (+ x (mult x (- y 1)))))
  (define (h y) (assert (<= (+ y y) (mult y y))))
  (define (main n) (h n)))

(require 'm)

((λ (✌0) (✌0 1)) main)

