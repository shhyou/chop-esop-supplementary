#lang concolic-hop/lang

(provide (all-defined-out))

(define (Omega) (Omega))

(define (derived-guarded-first-order-sequential-calls f)
  (cond
    [(= (+ (f (λ (n) 4))
           (f (λ (y) (* y 2))))
        10)
     (f (λ (x)
          (unless (= x 2) (Omega))
          0))
     (f (λ (w)
          (when (= w 2) (error-bug "REAL"))
          0))]
    [else 0]))

(define derived-guarded-first-order-sequential-calls:ce
  (list
   (λ (g)
     (g 2)
     5)))

(define-concolic-test prop-derived-guarded-first-order-sequential-calls
  #:inputs
  [F (->s (->s integer integer) integer)]
  #:prop
  (prop-not-error-bug
   (λ () (derived-guarded-first-order-sequential-calls F))))

(module* test racket/base
  (require rackunit
           concolic-hop/strategy-queue
           "../private/test-prop.rkt"
           (submod ".."))

  (check-exn
   #rx"bug: REAL"
   (λ () (apply derived-guarded-first-order-sequential-calls
                derived-guarded-first-order-sequential-calls:ce)))

  (test-property "derived-guarded-first-order-sequential-calls"
                 prop-derived-guarded-first-order-sequential-calls
                 #:all? #f
                 #:timeout 0.5
                 #:strategy (simple-prioritize-branch-strategy 1000))

  )

(module* main racket/base
  (require (submod ".." test)))
