#lang concolic-hop/lang

(provide (all-defined-out))

(define (derived-guarded-first-order-two-calls f)
  (cond
    [(= (+ (f (λ (n) 4))
           (f (λ (y) (* y 2))))
        10)
     (when (< (f (λ (n) 4))
              (f (λ (y) (* y 2))))
       (f (λ (w)
            (when (= w 2) (error-bug "REAL"))
            0)))]
    [else 0]))

(define derived-guarded-first-order-two-calls:ce
  (list
   (λ (g)
     (define n (g 3))
     (cond
       [(= n 4) 4]
       [(= n 6) 6]
       [else
        (g 2)]))))

(define-concolic-test prop-derived-guarded-first-order-two-calls
  #:inputs
  [F (->s (->s integer integer) integer)]
  #:prop
  (prop-not-error-bug
   (λ () (derived-guarded-first-order-two-calls F))))

(module* test racket/base
  (require rackunit
           concolic-hop/strategy-queue
           "../private/test-prop.rkt"
           (submod ".."))

  (check-exn
   #rx"bug: REAL"
   (λ () (apply derived-guarded-first-order-two-calls
                derived-guarded-first-order-two-calls:ce)))

  (test-property "derived-guarded-first-order-two-calls"
                 prop-derived-guarded-first-order-two-calls
                 #:all? #f
                 #:strategy (simple-prioritize-branch-strategy 1000))

  )

(module* main racket/base
  (require (submod ".." test)))
