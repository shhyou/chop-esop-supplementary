#lang concolic-hop/lang

(provide (all-defined-out))

(define (my-length-3 xs acc)
  (cond
    [(>= acc 3) #f]
    [(null? xs) #t]
    [else
     (my-length-3 (cdr xs) (+ 1 acc))]))

(define (len>=3? xs)
  (my-length-3 xs 0))

(define-concolic-test prop-len>=3?
  #:inputs
  [XS (list-of integer)]
  #:prop
  (prop-not-false (len>=3? XS)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (my-length-content full-xs xs acc)
  (cond
    [(and (>= acc 1) (< acc (cadr full-xs)))
     #f]
    [(null? xs) #t]
    [else
     (my-length-content full-xs (cdr xs) (+ 1 acc))]))

(define (len-content? xs x)
  (or (>= x -1) (my-length-content xs xs x)))

(define-concolic-test prop-len-content
  #:inputs
  [XS (list-of integer)]
  [X integer]
  #:prop
  (prop-not-false (len-content? XS X)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (basic-tuple t)
  (or (not (equal? (length t) 3))
      (let ()
        (define x (car t))
        (define b (cadr t))
        (define n (caddr t))
        (and (not (= x 0))
             (or (not (= (* 2 x) (+ x 15)))
                 (not b)
                 (> (* n n) 9))))))

(define-concolic-test prop-basic-tuple
  #:inputs
  [T (list/s integer boolean (integer-range -5 -3))]
  #:prop
  (prop-not-false (basic-tuple T)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (simple-singleton-list F)
  (define n (F '(1234)))
  ;; will create an infinitely expanding path constraint here
  ;; so at some point F will examine the singleton list with
  ;; pair? on the result of (cdr _).
  (define copy-n
    (let loop ([n n])
      (cond
        [(<= n 0) 0]
        [else (add1 (loop (sub1 n)))])))
  (when (= copy-n 20)
    (error-bug)))

(define-concolic-test prop-simple-singleton-list
  #:inputs
  [F (->s (list/s integer)
          integer)]
  #:prop
  (prop-not-error-bug
   (λ () (simple-singleton-list F))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (tell-null-from-pair? f)
  (not (and (= (f '()) 5)
            (= (f '(1 2 3)) 133))))

(define-concolic-test prop-tell-null-from-pair?
  #:inputs
  [F (->s (list-of integer) integer)]
  #:prop
  (prop-not-false (tell-null-from-pair? F)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(module* test racket/base
  (require concolic-hop/strategy-queue
           "../private/test-prop.rkt"
           (submod ".."))

  (test-proposition prop-len>=3?)

  (test-proposition prop-len-content #:all? #f)

  (test-proposition prop-basic-tuple #:all? #t)

  (test-proposition prop-simple-singleton-list #:all? #f)

  (test-proposition prop-tell-null-from-pair? #:all? #f)
  )

(module* main racket/base
  (require (submod "../private/utils.rkt" config-output-port)
           (submod "../private/test-prop.rkt" config printing-to-current-output-port))

  (require (submod ".." test))

  (sleep 0.1)
  (reset-output-port!)
  )
