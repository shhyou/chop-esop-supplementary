#lang concolic-hop/lang

(provide (all-defined-out))

;; testing basic list operations
(define (length-4 zs)
  (not (= 4 (length zs))))

(define-concolic-test prop-length-4
  #:inputs
  [ZS (list-of integer)]
  #:prop (prop-not-false (length-4 ZS)))


(define (length-append-0 xs ys)
  (not (and (>= (length ys) 2)
            (= (length (append xs ys)) 5))))

(define-concolic-test prop-length-append-0
  #:inputs
  [XS (list-of integer)]
  [YS (list-of integer)]
  #:prop
  (prop-not-false (length-append-0 XS YS)))

(define (length-append-1 xs ys zs)
  (not (and (>= (length ys) 2)
            (= (length zs) 5)
            (= 17 (cadr ys))
            (equal? (append xs ys) zs)
            (pair? xs)
            (= 5 (car xs)))))

(define-concolic-test prop-length-append-1
  #:inputs
  [XS (list-of integer)]
  [YS (list-of integer)]
  [ZS (list-of integer)]
  #:prop
  (prop-not-false (length-append-1 XS YS ZS)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Testing foldl, foldr with empty list and non-empty lists

(define (foldl-0-empty f xs)
  (define n
    (foldl (λ (x y)
             (define v ((f x) y))
             (+ 10 (* v v)))
           -5
           xs))
  (not (and (n . < . 0))))

(define-concolic-test prop-foldl-0-empty
  #:inputs
  [F (->s integer (->s integer integer))]
  [XS (list-of integer)]
  #:prop
  (prop-not-false (foldl-0-empty F XS)))

(define (foldl-1-cons f xs)
  (define n
    (foldl (λ (x y)
             (define v ((f x) y))
             (+ y (* v v (- x))))
           -5
           xs))
  (not (and (n . > . 10))))

(define-concolic-test prop-foldl-1-cons
  #:inputs
  [F (->s integer (->s integer integer))]
  [XS (list-of integer)]
  #:prop
  (prop-not-false (foldl-1-cons F XS)))

(define (foldr-0-empty f xs)
  (define n
    (foldr (λ (x y)
             (define v ((f x) y))
             (+ 10 (* v v)))
           -5
           xs))
  (not (and (n . < . 0))))

(define-concolic-test prop-foldr-0-empty
  #:inputs
  [F (->s integer (->s integer integer))]
  [XS (list-of integer)]
  #:prop
  (prop-not-false (foldr-0-empty F XS)))

(define (foldr-1-cons f xs)
  (define n
    (foldr (λ (x y)
             (define v ((f x) y))
             (+ y (* v v (- x))))
           -5
           xs))
  (not (and (n . > . 10))))

(define-concolic-test prop-foldr-1-cons
  #:inputs
  [F (->s integer (->s integer integer))]
  [XS (list-of integer)]
  #:prop
  (prop-not-false (foldr-1-cons F XS)))

;; Testing filter

(define (filter-0 pred? xs)
  (define ys (filter pred? xs))
  (not (and (pair? xs) (pair? (cdr xs))
            (null? ys))))

(define-concolic-test prop-filter-0
  #:inputs
  [F (->s integer boolean)]
  [XS (list-of integer)]
  #:prop
  (prop-not-false (filter-0 F XS)))

(define (filter-1 pred? xs)
  (define ys (filter pred? xs))
  (not (and (pair? xs) (pair? (cdr xs))
            (pair? ys) (null? (cdr ys))
            (equal? (car ys) (cadr xs)))))

(define-concolic-test prop-filter-1
  #:inputs
  [F (->s integer boolean)]
  [XS (list-of integer)]
  #:prop
  (prop-not-false (filter-1 F XS)))

(define (filter-2 pred? xs)
  (define ys (filter pred? xs))
  (not (and (pair? xs) (pair? (cdr xs))
            (pair? ys) (null? (cdr ys))
            (equal? (car ys) (car xs)))))

(define-concolic-test prop-filter-2
  #:inputs
  [F (->s integer boolean)]
  [XS (list-of integer)]
  #:prop
  (prop-not-false (filter-2 F XS)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(module* test racket/base
  (require concolic-hop/strategy-queue
           "../private/test-prop.rkt"
           (submod ".."))

  (test-proposition prop-length-4
                    #:all? #f)

  (test-proposition prop-length-append-0
                    #:all? #f)

  (test-proposition prop-length-append-1
                    #:all? #f)

  (test-proposition prop-foldl-0-empty
                    #:all? #f)

  (test-proposition prop-foldl-1-cons
                    #:all? #f)

  (test-proposition prop-foldr-0-empty
                    #:all? #f)

  (test-proposition prop-foldr-1-cons
                    #:all? #f)

  (test-proposition prop-filter-0
                    #:all? #f)

  (test-proposition prop-filter-1
                    #:all? #f)

  (test-proposition prop-filter-2
                    #:all? #f)
  )

(module* main racket/base
  (require (submod "../private/utils.rkt" config-output-port)
           (submod "../private/test-prop.rkt" config printing-to-current-output-port))

  (require (submod ".." test))

  (sleep 0.1)
  (reset-output-port!)
  )
