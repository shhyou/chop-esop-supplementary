#lang concolic-hop/lang

(provide (all-defined-out))

(define (basic-generate-content-0 f)
  (not (and (>= (length (f 3)) 3)
            (> (length (f 1)) 1)
            (< (length (f 1)) 3))))

(define-concolic-test prop-basic-generate-content-0
  #:inputs
  [F (->s integer (list-of integer))]
  #:prop
  (prop-not-false (basic-generate-content-0 F)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (my-length-content full-xs xs acc)
  (cond
    [(and (>= acc 1) (< acc (cadr full-xs)))
     #f]
    [(null? xs) #t]
    [else
     (my-length-content full-xs (cdr xs) (+ 1 acc))]))

(define (basic-generate-content-1 f x)
  (not (and (let ([f-x (f x)])
              (and (pair? f-x)
                   (pair? (cdr f-x))
                   (my-length-content f-x f-x 0)))
            (not (let ([f-2x (f (+ x x))])
                   (my-length-content f-2x f-2x -2))))))

(define-concolic-test prop-basic-generate-content-1
  #:inputs
  [F (->s integer (list-of integer))]
  [X integer]
  #:prop
  (prop-not-false (basic-generate-content-1 F X)))

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

(define (basic-generate-content-2 f x)
  (not (and (basic-tuple (f x))
            (not (basic-tuple (f (* x 2)))))))

(define-concolic-test prop-basic-generate-content-2
  #:inputs
  [F (->s integer (list/s integer boolean (integer-range -20 -3)))]
  [X integer]
  #:prop
  (prop-not-false (basic-generate-content-2 F X)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(module* test racket/base
  (require concolic-hop/strategy-queue
           "../private/test-prop.rkt"
           (submod ".."))

  (test-proposition prop-basic-generate-content-0 #:all? #f)

  (test-proposition prop-basic-generate-content-1 #:all? #f)

  (test-proposition prop-basic-generate-content-2 #:all? #f)
  )

(module* main racket/base
  (require (submod "../private/utils.rkt" config-output-port)
           (submod "../private/test-prop.rkt" config printing-to-current-output-port))

  (require (submod ".." test))

  (sleep 0.1)
  (reset-output-port!)
  )
