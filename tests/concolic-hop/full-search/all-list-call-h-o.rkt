#lang concolic-hop/lang

(provide (all-defined-out))

(define (extract-content-3.2 f)
  (not (and (= 55 (f (list (λ (n) #f) (λ (n) (= n 5)))))
            (= 1  (f (list (λ (n) #f) (λ (n) (= n 7)))))
            (= 20 (f (list (λ (n) #f) (λ (n) (= n 9))))))))

(define-concolic-test prop-extract-content-3.2
  #:inputs
  [F (->s (list-of (->s integer boolean)) integer)]
  #:prop
  (prop-not-false (extract-content-3.2 F)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(module* test racket/base
  (require concolic-hop/strategy-queue
           "../private/test-prop.rkt"
           (submod ".."))

  (test-proposition prop-extract-content-3.2
                    #:all? #f
                    #:strategy (simple-prioritize-branch-strategy 1000))
  )

(module* main racket/base
  (require (submod "../private/utils.rkt" config-output-port)
           (submod "../private/test-prop.rkt" config printing-to-current-output-port))

  (require (submod ".." test))

  (sleep 0.1)
  (reset-output-port!)
  )
