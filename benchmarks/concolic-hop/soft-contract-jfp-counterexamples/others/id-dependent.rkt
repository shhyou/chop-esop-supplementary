#lang racket
(module id racket
  (provide/contract
   [f (->i ([x number?]) (res (x) (=/c x)))])
  (define (f x) x))

(require 'id)
(f 0+1i)
