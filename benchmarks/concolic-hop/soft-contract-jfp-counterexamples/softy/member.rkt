#lang racket
(module member racket
  (provide/contract
   [member (any/c (listof any/c) . -> . #|HERE|# boolean?)])
  (define (member x l)
    (cond
     [(empty? l) empty]
     [(equal? x (car l)) l]
     [else (member x (cdr l))])))

(require 'member)
(member (λ (✌0) (error "ASSERT_UNREACHABLE")) null)
