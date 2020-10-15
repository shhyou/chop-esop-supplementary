#lang concolic-hop/lang

(provide (all-defined-out))

(define (Omega) (Omega))

(define (sequential-calls f)
  (f (λ (n) (if (= n 7) 73 (Omega))))
  (f (λ (n) (if (= n 7) 64
                (if (= n 31)
                    (error-bug "REAL")
                    73)))))

(define sequential-calls:ce
  (list
   (λ (g)
     (cond
       [(= (g 7) 64) (g 31)]
       [else         0]))))

(define-concolic-test prop-sequential-calls
  #:inputs
  [F (->s (->s integer integer) integer)]
  #:prop
  (prop-not-error-bug
   (λ () (sequential-calls F))))

(module* test racket/base
  (require rackunit
           concolic-hop/strategy-queue
           "../private/test-prop.rkt"
           (submod ".."))

  (check-exn
   #rx"bug: REAL"
   (λ () (apply sequential-calls sequential-calls:ce)))

  (test-property "sequential-calls" prop-sequential-calls
                 #:all? #f
                 #:timeout 0.5
                 #:strategy (ignore-locals-adapter
                             (simple-prioritize-branch-strategy 1000)))

  )

(module* main racket/base
  (require (submod ".." test)))
