#lang racket
(module taut racket
  (define taut-arg/c
    (or/c boolean? number? [boolean? . -> . (recursive-contract taut-arg/c #:chaperone)]))
  (provide/contract
   [taut (taut-arg/c . -> . boolean?)])
  (define (taut b)
    (cond
      [(procedure? b) (and (taut (b #t)) (taut (b #f)))]
      [else b])))

(require 'taut)
(taut 0)
