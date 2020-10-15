#lang racket
(module assert racket
  (define assert (λ (✌0) (error "ASSERT_UNREACHABLE"))) (provide/contract [assert ((not/c false?) . -> . any/c)]))

(module m racket
  (provide/contract [main (-> any/c)])
  (require (submod ".." assert))
  (define (sum x y k)
    (if (<= x 0) (k y) (sum (- x 1) (+ x y) k)))
  (define (check x) (assert (<= 100 x)))
  (define (main) (sum 5 0 check)))

(require 'm)

((λ (✌0) (✌0)) main)

