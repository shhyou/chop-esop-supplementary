#lang concolic-hop/lang

(provide (all-defined-out))

(define (extract-content-0 f)
  (not (and (= 3 (f (list 0)))
            (= 10 (f (list 1))))))

(define-concolic-test prop-extract-content-0
  #:inputs
  [F (->s (list-of integer) integer)]
  #:prop
  (prop-not-false (extract-content-0 F)))

(define (extract-content-0.3 f)
  (not (and (= 7 (f (list -10 0)))
            (= 1 (f (list -10 1))))))

(define-concolic-test prop-extract-content-0.3
  #:inputs
  [F (->s (list-of integer) integer)]
  #:prop
  (prop-not-false (extract-content-0.3 F)))

(define (extract-content-0.5 f)
  (not (and (= 7 (f (list -10)))
            (= 1 (f (list -10 1))))))

(define-concolic-test prop-extract-content-0.5
  #:inputs
  [F (->s (list-of integer) integer)]
  #:prop
  (prop-not-false (extract-content-0.5 F)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define (extract-content-1 f)
  (not (and (= 72 (f (list (λ (n) 0))))
            (= 16 (f (list (λ (n) 1)))))))

(define-concolic-test prop-extract-content-1
  #:inputs
  [F (->s (list-of (->s integer integer)) integer)]
  #:prop
  (prop-not-false (extract-content-1 F)))

(define (extract-content-2 f)
  (not (and (= 11 (f (list (λ (n) -1) (λ (n) 0))))
            (= 87 (f (list (λ (n) -1) (λ (n) 1)))))))

(define-concolic-test prop-extract-content-2
  #:inputs
  [F (->s (list-of (->s integer integer)) integer)]
  #:prop
  (prop-not-false (extract-content-2 F)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (extract-content-3 f)
  (not (and (= 55 (f (list (λ (n) #f) (λ (n) (= n 5)))))
            (= 1  (f (list (λ (n) #f) (λ (n) (= n 7))))))))

(define-concolic-test prop-extract-content-3
  #:inputs
  [F (->s (list-of (->s integer boolean)) integer)]
  #:prop
  (prop-not-false (extract-content-3 F)))

(define (extract-content-3.1 f)
  (not (and (= 55 (f (list (λ (n) -1) (λ (n) (if (= n 5) 0 1)))))
            (= 1  (f (list (λ (n) -1) (λ (n) (if (= n 7) 0 1))))))))

(define-concolic-test prop-extract-content-3.1
  #:inputs
  [F (->s (list-of (->s integer integer)) integer)]
  #:prop
  (prop-not-false (extract-content-3.1 F)))

(module* test racket/base
  (require concolic-hop/strategy-queue
           "../private/test-prop.rkt"
           (submod ".."))


  (test-proposition prop-extract-content-0 #:all? #f)

  (test-proposition prop-extract-content-0.3
                    #:all? #f
                    #:strategy (simple-prioritize-branch-strategy 1000))

  (test-proposition prop-extract-content-0.3
                    #:all? #f
                    #:strategy (simple-destructor-adapter
                                (simple-prioritize-branch-strategy 1000)))

  (test-proposition prop-extract-content-0.5 #:all? #f)

  (test-proposition prop-extract-content-0.5
                    #:all? #f
                    #:strategy (simple-destructor-adapter
                                breadth-first-search-strategy))

  (test-proposition prop-extract-content-1
                    #:all? #f
                    #:strategy (simple-prioritize-branch-strategy 1000))

  (test-proposition prop-extract-content-2
                    #:all? #f
                    #:strategy (simple-destructor-adapter
                                (simple-prioritize-branch-strategy 1000)))

  (test-proposition prop-extract-content-3
                    #:all? #f
                    #:strategy (simple-prioritize-branch-strategy 1000))

  (test-proposition prop-extract-content-3.1
                    #:all? #f
                    #:strategy (simple-destructor-adapter
                                (simple-prioritize-branch-strategy 1000)))
  )

(module* main racket/base
  (require (submod "../private/utils.rkt" config-output-port)
           (submod "../private/test-prop.rkt" config printing-to-current-output-port))

  (require (submod ".." test))

  (sleep 0.1)
  (reset-output-port!)
  )
