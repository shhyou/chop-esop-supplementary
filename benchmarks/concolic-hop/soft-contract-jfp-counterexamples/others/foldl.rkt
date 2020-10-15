#lang racket
(module foldl racket
  (provide/contract
   [foldl ((number? boolean? . -> . boolean?) boolean? (listof number?) . -> . boolean?)])
  (define (foldl f z xs)
    (if (empty? xs) z
        (foldl f (f #|HERE|# z (car xs)) (cdr xs)))))

(require 'foldl)
(foldl (λ (✌0 ✌1) (error "ASSERT_UNREACHABLE")) #f (cons 0 null))
