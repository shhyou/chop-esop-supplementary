#lang concolic-hop/lang

(provide (all-defined-out))

(define (derived-two-calls-in-list f)
  (when (and (= 55 (f (list (λ (n) #f) (λ (n) (= n 5)))))
             (= 1  (f (list (λ (n) #f) (λ (n) (= n 7)))))
             (= 20 (f (list (λ (n) #f) (λ (n) (= n 9))))))
    (error-bug "REAL")))

(define derived-two-calls-in-list:ce
  (list
   (λ (g-lst)
     (define g (list-ref g-lst 1))
     (cond
       [(g 5) 55]
       [(g 7) 1]
       [else  20]))))

(define-concolic-test prop-derived-two-calls-in-list
  #:inputs
  [F (->s (list-of (->s integer boolean)) integer)]
  #:prop
  (prop-not-error-bug
   (λ () (derived-two-calls-in-list F))))

(module* test racket/base
  (require rackunit
           concolic-hop/strategy-queue
           "../private/test-prop.rkt"
           (submod ".."))

  (check-exn
   #rx"bug: REAL"
   (λ () (apply derived-two-calls-in-list derived-two-calls-in-list:ce)))

  (test-property "derived-two-calls-in-list" prop-derived-two-calls-in-list
                 #:all? #f
                 #:strategy (simple-prioritize-branch-strategy 1000))
  )

(module* main racket/base
  (require (submod ".." test)))
