#lang concolic-hop/lang

(provide prop-one-branch
         prop-two-branches
         prop-h h
         prop-cubic-expr
         prop-contradict-cond
         prop-simp-map1
         prop-simp-map2
         prop-simp-map3
         prop-simp-map-twice
         )

(define-concolic-test prop-one-branch
  #:inputs
  [X integer]
  #:prop
  (prop-not-false
   (if (= (* X 3) (+ X 68))
       #f
       #t)))


(define-concolic-test prop-two-branches
  #:inputs
  [X integer]
  [Y integer]
  #:prop
  (prop-not-false
   (if (> Y 24)
       (if (= (* X 2) (+ X 15))
           #f
           #t)
       #t)))


(define (f x)
  (* 2 x))

;; h : int -> int -> any
(define (h x y)
  (if (= x y)
      (if (= (f x) (+ x 2147483))
          #f
          #t)
      #t))

(define-concolic-test prop-h
  #:inputs
  [X integer]
  [Y integer]
  #:prop
  (prop-not-false (h X Y)))


(define (cubic-expr x y)
  (if (> (* x x x) 0)
      (if (and (> x 0) (= y 10))
          #f
          #t)
      (if (and (> x 0) (= y 20))
          (not (= y 20))
          #t)))

(define-concolic-test prop-cubic-expr
  #:inputs
  [X integer]
  [Y integer]
  #:prop
  (prop-not-false (cubic-expr X Y)))


;; this function has no bug
(define (contradict-cond x y)
  (define z y)
  (if (= x z)
      (if (= y (+ x 10))
          #f
          #t)
      #t))

(define-concolic-test prop-contradict-cond
  #:inputs
  [X integer]
  [Y integer]
  #:prop
  (prop-not-false (contradict-cond X Y)))


(define (simp-map1 f)
  (not (and (= (f 3) 8)
            (= (f 7) 1)
            (= (f 44) -1))))

(define-concolic-test prop-simp-map1
  #:inputs
  [F (->s integer integer)]
  #:prop
  (prop-not-false (simp-map1 F)))


(define (simp-map2 f x)
  (not (and (= (f (* 2 x)) 456)
            (= (f (+ x 123)) 456)
            (= (* 2 x) (+ x 123)))))

(define-concolic-test prop-simp-map2
  #:inputs
  [F (->s integer integer)]
  [X integer]
  #:prop
  (prop-not-false (simp-map2 F X)))


(define (simp-map3 f x)
  (not (and (= (f (* 2 x)) 456)
            (= (f (+ x 123)) 456)
            (not (= (* 2 x) (+ x 123)))
            (> x 50))))

(define-concolic-test prop-simp-map3
  #:inputs
  [F (->s integer integer)]
  [X integer]
  #:prop
  (prop-not-false (simp-map3 F X)))


(define-concolic-test prop-simp-map-twice
  #:inputs
  [F (->s integer integer)]
  [X integer]
  [Y integer]
  #:prop
  (prop-not-false
   (if (= (F (F X)) 123)
       (if (= (F (F Y)) 33)
           #f
           #t)
       #t)))

(module* test racket/base
  (require concolic-hop/strategy-queue
           concolic-hop/data
           concolic-hop/lib
           racket/port
           rackunit
           "../private/test-prop.rkt"
           (submod ".."))

  (test-proposition prop-one-branch)

  (test-proposition prop-two-branches)

  (test-proposition prop-h)

  (test-case
   "prop-h counterexample"

   (define ce
     (parameterize ([current-output-port (open-output-nowhere)])
       (concolic-test prop-h)))

   (check-pred input? ce)

   (define counterexample
     (concretize-input prop-h ce))

   (check-false (h (hash-ref counterexample 'X)
                   (hash-ref counterexample 'Y))))

  (test-proposition prop-cubic-expr)

  ;; this function has no bug
  ;; (test-proposition prop-contradict-cond)

  (test-proposition prop-simp-map1)

  (test-proposition prop-simp-map2)

  (test-proposition prop-simp-map3)

  (test-proposition prop-simp-map-twice)
  )

(module* main racket/base

  (require (submod "../private/utils.rkt" config-output-port)
           (submod "../private/test-prop.rkt" config printing-to-current-output-port))
  (port-count-lines! (current-output-port))

  (require (submod ".." test))

  (sleep 0.1) (reset-output-port!)
  )
