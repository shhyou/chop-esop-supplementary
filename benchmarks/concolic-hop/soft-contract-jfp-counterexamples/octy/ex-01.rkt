#lang racket
(module f racket
  (provide/contract [f (any/c . -> . number?)])
  (define (f x)
    (if (number? x) 0 #|HERE|# (add1 x))))

(require 'f)
((λ (✌0) (✌0 (λ (✌1) (error "ASSERT_UNREACHABLE")))) f)
