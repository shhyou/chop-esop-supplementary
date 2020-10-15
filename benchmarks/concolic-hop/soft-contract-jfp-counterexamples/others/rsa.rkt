#lang racket
(module prime? racket
  (define prime?
  (λ (✌0)
    (if (integer? ✌0)
      (λ (✌1) (error "ASSERT_UNREACHABLE"))
      (if (boolean? ✌0)
        (λ (✌2) (error "ASSERT_UNREACHABLE"))
        (if (procedure? ✌0)
          (λ (✌3) (error "ASSERT_UNREACHABLE"))
          (λ (✌4) (error "ASSERT_UNREACHABLE")))))))
  (provide/contract [prime? (any/c . -> . any/c)]))

(module keygen racket
  (define keygen (λ (✌0) 0))
  (require (submod ".." prime?))
  (provide/contract [keygen (any/c . -> . (λ (x) (prime? x)))]))

(module rsa racket
  (define rsa (λ (✌0 ✌1) (error "ASSERT_UNREACHABLE")))
  (require (submod ".." prime?))
  (provide/contract [rsa ((λ (x) (prime? x)) number? . -> . number?)]))

(module enc racket
  (provide/contract [enc (any/c . -> . any/c)])
  (require (submod ".." rsa) (submod ".." keygen))
  (define (enc x) (rsa (keygen #t) x)))

(require 'enc)
(enc (λ (✌0) (error "ASSERT_UNREACHABLE")))
