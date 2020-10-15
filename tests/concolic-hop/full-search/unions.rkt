#lang concolic-hop/lang

(provide prop-union-0-toplevels
         prop-union-1-bases
         prop-union-2-inputs
         prop-union-3-inputs
         )

(define-concolic-test prop-union-0-toplevels
  #:inputs
  [L (or/s (list/s)
           (list/s integer)
           (list/s integer integer)
           (list/s integer integer integer integer)
           (list/s integer boolean integer))]
  #:prop
  (prop-not-false
   (and (= 3 (length L))
        (not (cadr L)))))


(define (union-1-bases X Y)
  (not (and (integer? (X 0)) (> (X 0) 7)
            (boolean? (Y 0)) (Y 0))))

(define-concolic-test prop-union-1-bases
  #:inputs
  [X (->s integer (or/s integer boolean))]
  [Y (->s integer (or/s integer boolean))]
  #:prop
  (prop-not-false (union-1-bases X Y)))


(define (union-2-inputs F X)
  (not (and (= (F add1) 5)
            (= (F (λ (n) (* n 2))) 11)
            (= (F X) 6)
            (= (F (* X 2)) 9))))

(define-concolic-test prop-union-2-inputs
  #:inputs
  [F (->s (or/s integer (->s integer integer))
          integer)]
  [X integer]
  #:prop
  (prop-not-false (union-2-inputs F X)))


(define (union-3-inputs F X)
  (not (and (= (F X) 6)
            (= (F add1) 5)
            (= (F (* X 2)) 9)
            (= (F (λ (n) (* n 2))) 11))))

(define-concolic-test prop-union-3-inputs
  #:inputs
  [F (->s (or/s integer (->s integer integer))
          integer)]
  [X integer]
  #:prop
  (prop-not-false (union-3-inputs F X)))

(module* test racket/base
  (require concolic-hop/strategy-queue
           concolic-hop/data
           concolic-hop/lib
           racket/port
           rackunit
           "../private/test-prop.rkt"
           (submod ".."))

  (test-proposition prop-union-0-toplevels)

  (test-proposition prop-union-1-bases
                    #:all? #f)

  (test-proposition prop-union-2-inputs
                    #:all? #f
                    #:strategy (simple-prioritize-branch-strategy 1000))

  (test-proposition prop-union-3-inputs
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
