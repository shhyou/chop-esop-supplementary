#lang racket
(module recursive-div2 racket
  (provide/contract
   [recursive-div2 ((listof any/c)
                    . -> . (listof any/c))])
  (define (recursive-div2 l)
    (if (empty? l) empty
        (cons (car l) (recursive-div2 (cdr (cdr l)))))))

(require 'recursive-div2)
(recursive-div2 (cons (λ (✌0) (error "ASSERT_UNREACHABLE")) null))
