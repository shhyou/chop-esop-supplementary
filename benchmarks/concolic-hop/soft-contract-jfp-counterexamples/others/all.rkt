#lang racket
(module all racket
  (provide/contract [all ((any/c . -> . any/c) (listof any/c) . -> . #|HERE|#boolean?)])
  (define (all p? xs)
    (cond
      [(empty? xs) #t]
      [(empty? (cdr xs)) (p? (car xs))]
      [else (and (p? (car xs)) (all p? (cdr xs)))])))

(require 'all)
(all (λ (✌0) (λ (✌1) (error "ASSERT_UNREACHABLE"))) (cons (λ (✌0) (error "ASSERT_UNREACHABLE")) null))
