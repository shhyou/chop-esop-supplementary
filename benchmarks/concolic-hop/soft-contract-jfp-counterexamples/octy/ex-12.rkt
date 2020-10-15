#lang racket
(module carnum? racket
  (provide/contract [carnum? (->i ([p #|HERE|# any/c])
				  (res (p) (and/c boolean? (λ (a) (equal? a (number? (car p)))))))])
  (define (carnum? p) (number? (car p))))

(require 'carnum?)
(carnum? (λ (✌0) (error "ASSERT_UNREACHABLE")))
