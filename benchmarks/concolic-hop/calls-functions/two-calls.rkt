#lang concolic-hop/lang

(provide (all-defined-out))

(define (equals m)
  (λ (n) (if (= n m) 0 1)))

(define (two-calls F)
  (when (and (= (F (equals 2))  12)
             (= (F (equals 30))  5)
             (= (F (equals 7))  -2))
    (error-bug "REAL")))

(define two-calls:ce
  (list
   (λ (g)
     (define i (g 2))
     (define j (g 30))
     (cond
       [(= i 0) 12]
       [(= j 0)  5]
       [else         -2]))))

(define-concolic-test prop-two-calls
  #:inputs
  [F (->s (->s integer integer) integer)]
  #:prop
  (prop-not-error-bug
   (λ () (two-calls F))))

(module* test racket/base
  (require rackunit
           concolic-hop/strategy-queue
           "../private/test-prop.rkt"
           (submod ".."))

  (check-exn
   #rx"bug: REAL"
   (λ () (apply two-calls two-calls:ce)))

  (test-property "two-calls" prop-two-calls
                 #:all? #f
                 #:strategy (ignore-locals-adapter
                             (simple-prioritize-branch-strategy 1000)))
  )

(module* main racket/base
  (require (submod ".." test)))
