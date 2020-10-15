#lang concolic-hop/lang

(provide prop-diff-by-0
         prop-call-2 call-2
         prop-call-3)

;; diff-by-0 : ((int -> int) -> int) -> bool
(define (const1 _) 1)
(define (_×2 y) (* 2 y))
(define (diff-by-0 F)
  (cond
    [(< (F const1) (F _×2))
     #f]
    [else #t]))

(define-concolic-test prop-diff-by-0
  #:inputs
  [F (->s (->s integer integer) integer)]
  #:prop
  (prop-not-false (diff-by-0 F)))


(define (call-2 F)
  (not (and (= (F (λ (n) (= n 2))) 12)
            (= (F (λ (n) (= n 30))) 5)
            (= (F (λ (n) (= n 7))) -2))))

(define-concolic-test prop-call-2
  #:inputs
  [F (->s (->s integer boolean) integer)]
  #:prop
  (prop-not-false (call-2 F)))


(define (call-3 F X Y)
  (not (and (= (F (λ (n) (if (= n 2) 0 1))) 12)
            (= (F (λ (n) (if (= n 30) 0 1))) 5)
            (= (F (λ (n) (if (= n 7) 0 1))) -2))))

(define-concolic-test prop-call-3
  #:inputs
  [F (->s (->s integer integer) integer)]
  [X integer]
  [Y integer]
  #:prop
  (prop-not-false (call-3 F X Y)))


(module* test racket/base
  (require concolic-hop/strategy-queue
           concolic-hop/data
           concolic-hop/lib
           racket/port
           rackunit
           "../private/test-prop.rkt"
           (submod ".."))

  (test-proposition prop-diff-by-0
                    #:all? #f)

  (test-proposition prop-call-2
                    #:all? #f)

  (test-case
   "prop-call-2 counterexample"

   (define ce
     (parameterize ([current-output-port (open-output-nowhere)])
       (concolic-test prop-call-2
                      #:all? #f
                      #:strategy (simple-prioritize-branch-strategy 1000))))

   (check-pred input? ce)

   (define counterexample
     (parameterize ([current-output-port (open-output-nowhere)])
       (concretize-input prop-call-2 ce)))

   (check-false (call-2
                 (parameterize ([current-namespace (make-base-namespace)])
                   (eval (hash-ref counterexample 'F))))))

  (test-proposition prop-call-3
                    #:all? #f
                    #:strategy (simple-prioritize-branch-strategy 1000))
  )

(module* main racket/base

  (require (submod "../private/utils.rkt" config-output-port)
           (submod "../private/test-prop.rkt" config printing-to-current-output-port))
  (port-count-lines! (current-output-port))

  (require (submod ".." test))

  (sleep 0.1) (reset-output-port!)
  )
