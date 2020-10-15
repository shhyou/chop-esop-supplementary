#lang racket
(module f racket
  (provide/contract [f (#|HERE|# any/c . -> . number?)])
  (define (f x)
    (if (number? x) (add1 x) (string-length x))))

(require 'f)
(f (λ (✌0) (error "ASSERT_UNREACHABLE")))
