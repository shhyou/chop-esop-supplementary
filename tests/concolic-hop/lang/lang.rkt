#lang concolic-hop/lang

(provide (all-defined-out))

(define-concolic-test test-procedure-arity-includes?
  #:inputs
  [X integer]
  [B boolean]
  [L (list-of (->s integer integer))]
  [K (list-of integer)]
  [F (->s integer integer)]
  #:prop
  (prop-not-exn
   (λ ()
     (when (<= -3 X 5)
       (unless (procedure-arity-includes? values (+ X 3))
         (error-bug)))
     (unless (procedure-arity-includes? F 1)
       (error-bug))
     (unless (procedure-arity-includes? (λ (x y z) (+ x (* y z))) 3)
       (error-bug))
     (when (and (pair? L) (pair? K) (>= (list-ref K 0) 0))
       (unless (equal? (procedure-arity-includes? (if B (list-ref L 0) F)
                                                  (list-ref K 0))
                       (= (list-ref K 0) 1))
         (error-bug))))))

(define-concolic-test test-string?
  #:inputs
  [X integer]
  [B boolean]
  [L (list-of (->s integer integer))]
  #:prop
  (prop-not-exn
   (λ ()
     (when (string? (if B X (+ X 1)))
       (error-bug))
     (when (and (pair? L) (string? (list-ref L 0)))
       (error-bug))
     (unless (string? (if (not B) "abc" "def"))
       (error-bug)))))

(define-concolic-test test-string-length
  #:inputs
  [B boolean]
  #:prop
  (prop-not-false
   (if (equal? (string-length (if B "123" "123456789"))
               (if B 3 9))
       #t
       #f)))

(define-concolic-test test-string-length-exception
  #:inputs
  [B boolean]
  [L (list-of integer)]
  #:prop
  (prop-not-exn
   (λ ()
     (when (pair? L)
       (string-length (if B "123" L))))))

(define (i-am-a-function)
  'a-happy-function)

(define (i-am-another-function)
  'a-wonderful-function)

(define-concolic-test test-object-name
  #:inputs
  [B boolean]
  #:prop
  (prop-not-false
   (let ()
     (define answer
       (if (not B) 'i-am-another-function 'i-am-a-function))
     (if (equal? (object-name (if B i-am-a-function i-am-another-function))
                 answer)
         #t
         #f))))

(define-concolic-test test-object-name-sym
  #:inputs
  [X integer]
  [L (list-of (->s integer integer))]
  #:prop
  (prop-not-exn
   (λ ()
     (object-name #t)
     (object-name X)
     (object-name (+ X 3))
     (if (pair? L)
         (unless (object-name (car L))
           (error-bug))
         (object-name L)))))

(define-concolic-test test-div-error
  #:inputs
  [X integer]
  #:prop
  (prop-not-exn
   (λ ()
     (if (= X 0) (/ 1 X) 'ok))))

(define-concolic-test test-div-affects-control-flow
  #:inputs
  [X integer]
  #:prop
  (prop-not-exn
   (λ ()
     (/ 1 (+ X 2147483648)))))

(define-concolic-test test-div-multiple-divisors
  #:inputs
  [X integer]
  #:prop
  (prop-not-exn
   (λ ()
     (/ 12 2 (- X 3) 4))))

(define-concolic-test test-car-exception
  #:inputs
  [X integer]
  #:prop
  (prop-not-exn
   (λ ()
     (car (cdr (list X))))))

(define-concolic-test test-car-list-of-magic-exception
  #:inputs
  [L (list-of integer)]
  #:prop
  (prop-not-exn
   (λ ()
     (if (null? L) (car L) 'ok))))

(define-concolic-test test-cdr-exception
  #:inputs
  [X integer]
  #:prop
  (prop-not-exn
   (λ ()
     (cdr (cdr (list X))))))

(define-concolic-test test-cdaddr-exception
  #:inputs
  [X integer]
  #:prop
  (prop-not-exn
   (λ ()
     (cdaddr (list X)))))

(define-concolic-test test-when
  #:inputs
  [X integer]
  #:prop
  (prop-not-error-bug
   (λ ()
     (when (= X 31415926)
       (error-bug "a correct bug")))))

(define-concolic-test test-unless
  #:inputs
  [X integer]
  #:prop
  (prop-not-error-bug
   (λ ()
     (unless (not (= X 271828))
       (error-bug "a correct bug")))))

(define-concolic-test test-abort-okay
  #:inputs
  [F (->s boolean (or/s integer boolean))]
  #:prop
  (prop-not-false
   (let ()
     (define val (F #f))
     (cond
       [(integer? val)
        (abort-concolic-execution "abort int: ~a" val)
        #f]
       [else
        #t]))))

(define-concolic-test test-abort-continue
  #:inputs
  [F (->s boolean (or/s integer (list-of (->s integer integer)) boolean))]
  #:prop
  (prop-not-error-bug
   (λ ()
     (define val (F #f))
     (cond
       [(integer? val)
        (abort-concolic-execution "abort int: ~a" val)
        #f]
       [(boolean? val)
        (abort-concolic-execution "abort bool")
        #f]
       [(and (list? val) (not (null? val)) (= 1 ((car val) 13)))
        (error-bug "a correct bug")]
       [else
        #t]))))

(define-concolic-test test-timeout
  #:inputs
  [X integer]
  #:prop
  (prop-not-false
   (let ()
     (unless (= (* X 3) (+ X 24))
       (let loop ()
         (loop)))
     #f)))

(define-concolic-test test-memory
  #:inputs
  [X integer]
  #:prop
  (prop-not-false
   (let ()
     (unless (= (* X 4) (+ X 75))
       (let loop ()
         (list 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20
               (loop))))
     #f)))

(define (copy-nat n)
  (cond
    [(<= n 0) 0]
    [else (+ 1 (copy-nat (- n 1)))]))

(define-concolic-test test-path-limit
  #:inputs
  [X integer]
  #:prop
  (prop-not-false
   (if (= 10 (copy-nat X))
       #f
       #t)))

(module* test racket/base
  (require "../private/test-prop.rkt"
           (submod "../private/test-prop.rkt" config)
           "../private/utils.rkt"
           racket/port
           rackunit
           concolic-hop/data
           concolic-hop/store
           concolic-hop/lib
           (prefix-in cl: concolic-hop/lang)
           (submod ".."))

  (test-case
   "lifted Racket functions"

   (check-false (concolic-test test-procedure-arity-includes?))
   (check-false (concolic-test test-string?))
   (check-false (concolic-test test-string-length))
   (test-proposition test-string-length-exception)
   (check-false (concolic-test test-object-name))
   (check-false (concolic-test test-object-name-sym))
   )

  (test-case
   "results of division"
   (define-input empty-inputs)
   (call-with-model
    (input-model empty-inputs)
    (λ ()
      (check-equal? (cl:/ 3) 1/3)
      (check-equal? (cl:/ 2 3) 2/3)
      (check-equal? (cl:/ 2 3 4) 1/6))))

  (test-case
   "test-div-error concrete values"
   (define-input empty-inputs)
   (call-with-model
    (input-model empty-inputs)
    (λ ()
       (check-exn exn:fail? (λ () (cl:/ 0)))
       (check-exn exn:fail? (λ () (cl:/ 3 0)))
       (check-exn exn:fail? (λ () (cl:/ 3 2 1 0)))
       (check-exn exn:fail? (λ () (cl:/ 3 0 -1 2)))
       (check-exn exn:fail? (λ () (cl:/ 3 1 0 4))))))

  (test-proposition test-div-error)
  (test-proposition test-div-affects-control-flow)
  (test-proposition test-div-multiple-divisors)

  (test-proposition test-car-exception)
  (test-proposition test-car-list-of-magic-exception)
  (test-proposition test-cdr-exception)
  (test-proposition test-cdaddr-exception)

  (test-case
   "test car and cdr concrete value"

   (define-input inputs
     [L (list-of (or/s (list-of integer)
                       integer))
        (make-list [X 5]
                   (make-list [Z 133] [W 53])
                   [Y 1])])

   (define L-value
     (call-with-model
      (input-model inputs)
      (λ ()
        (interpret inputs
                   (hash-ref (input-type inputs) 'L)
                   L))))

   (check-equal?
    (call-with-model
     (input-model inputs)
     (λ () (get-current-concrete-value (cl:car L-value))))
    5)

   (check-equal?
    (call-with-model
     (input-model inputs)
     (λ () (get-current-concrete-value (cl:cdr L-value))))
    '((133 53) 1))

   (check-equal?
    (call-with-model
     (input-model inputs)
     (λ () (get-current-concrete-value (cl:cddr L-value))))
    '(1))

   (check-equal?
    (call-with-model
     (input-model inputs)
     (λ () (get-current-concrete-value (cl:caadr L-value))))
    '133)

   (check-equal?
    (call-with-model
     (input-model inputs)
     (λ () (get-current-concrete-value (cl:cdadr L-value))))
    '(53)))

  (test-proposition test-when)
  (test-proposition test-unless)

  (test-case
   "check abort-concolic-execution"
   (check-false (concolic-test test-abort-okay))
   (test-proposition test-abort-continue))

  (test-case
   "evaluation limits"

   (check-not-false (concolic-test-timeout))
   (test-proposition test-timeout
                     #:memory #f)

   (check-not-false (concolic-test-memory))
   (test-proposition test-memory
                     #:timeout #f)

   (check-not-false (concolic-test-path-limit))
   (check-false
    (concolic-test test-path-limit
                   #:path-limit 5
                   #:timeout #f
                   #:memory #f))
   (test-proposition test-path-limit
                     #:all? #f
                     #:path-limit 100
                     #:timeout #f
                     #:memory #f)
   )
  )

(module* main racket/base
  (require (submod "../private/test-prop.rkt" config printing-to-current-output-port)
           (submod ".." test))
  )
