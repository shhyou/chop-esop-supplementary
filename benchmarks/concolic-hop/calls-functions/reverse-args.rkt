#lang concolic-hop/lang

(provide (all-defined-out))

(define (Omega) (Omega))

(define (reverse-args f)
  (define n1 ((f (λ (n) (if (= n 0) 10 (Omega)))) 0))
  (define n2 ((f (λ (n) (if (= n 0) 23 (Omega)))) 0))
  (define n3 ((f (λ (m) (if (= m 1) 37 (Omega)))) 1))
  (define n4 ((f (λ (m) (if (= m 1) 41 (Omega)))) 1))
  (when (and (= n1 12)
             (= n2 34)
             (= n3 56)
             (= n4 78))
    (error-bug "REAL")))

(define reverse-args:ce
  (list
   (λ (f)
     (λ (x)
       (define k (f x))
       (cond
         [(= k 10) 12]
         [(= k 23) 34]
         [(= k 37) 56]
         [(= k 41) 78]
         [else 0])))))

(define-concolic-test prop-reverse-args
  #:inputs
  [F (->s (->s integer integer)
          (->s integer integer))]
  #:prop
  (prop-not-error-bug
   (λ () (reverse-args F))))

(module* test racket/base
  (require rackunit
           concolic-hop/strategy-queue
           "../private/test-prop.rkt"
           (submod ".."))

  (check-exn
   #rx"bug: REAL"
   (λ () (apply reverse-args reverse-args:ce)))

  (test-property "reverse-args" prop-reverse-args
                 #:all? #f
                 #:timeout 0.5
                 #:strategy (ignore-locals-adapter
                             (simple-prioritize-branch-strategy 1000)))

  )

(module* main racket/base
  (require (submod ".." test)))
