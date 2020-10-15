#lang racket
(module foldr racket
  (provide/contract
   [foldr ((number? boolean? . -> . boolean?) boolean? (listof any/c) . -> . boolean?)])
  (define (foldr f z xs)
    (if (empty? xs) z
        (f #|HERE|# (foldr f z (cdr xs)) (car xs)))))

(require 'foldr)
(foldr (λ (✌0 ✌1) (error "ASSERT_UNREACHABLE")) #f (cons (λ (✌0) (error "ASSERT_UNREACHABLE")) null))
