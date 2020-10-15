#lang racket
(module f racket
  (provide/contract [f (any/c any/c . -> . number?)])
  (define (f x y)
    (+ x (string-length y))))

(require 'f)
(f (λ (✌0) (error "ASSERT_UNREACHABLE")) (λ (✌0) (error "ASSERT_UNREACHABLE")))
