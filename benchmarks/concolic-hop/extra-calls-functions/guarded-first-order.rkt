#lang concolic-hop/lang

(provide (all-defined-out))

(define (guarded-first-order f)
  (cond
    [(= (+ (f (λ (n) 4))
           (f (λ (y) (* y 2))))
        10)
     (when (= (f (λ (m) 0)) -1)
       (f (λ (w)
            (when (= w 2) (error-bug "REAL"))
            0)))]
    [else 0]))

(define guarded-first-order:ce
  (list
   (λ (g)
     (if (= (g 2) 4)
         5
         -1))))

(define-concolic-test prop-guarded-first-order
  #:inputs
  [F (->s (->s integer integer) integer)]
  #:prop
  (prop-not-error-bug
   (λ () (guarded-first-order F))))

(module* test racket/base
  (require rackunit
           concolic-hop/strategy-queue
           "../private/test-prop.rkt"
           (submod ".."))

  (check-exn
   #rx"bug: REAL"
   (λ () (apply guarded-first-order guarded-first-order:ce)))

  (test-property "guarded-first-order" prop-guarded-first-order
                 #:all? #f
                 #:strategy (simple-prioritize-branch-strategy 1000))

  )

(module* main racket/base
  (require (submod ".." test)))
