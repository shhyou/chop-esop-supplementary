#lang racket
(module f racket
  (provide/contract [f (cons? . -> . number?)])
  (define (f p)
    (if (number? (#|HERE|# cdr p)) (add1 (car p)) 7)))

(require 'f)
(f (cons (λ (✌0) (error "ASSERT_UNREACHABLE")) 0))
