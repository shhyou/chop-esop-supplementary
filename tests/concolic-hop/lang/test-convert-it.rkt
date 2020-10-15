
#lang racket
(require racket/stxparam
         concolic-hop/convert-it
         (submod concolic-hop/convert-it test)
         rackunit
         (only-in concolic-hop/lib exn:fail:error-bug? abort-data?)
         (only-in concolic-hop/lang ->s or/s list-of list/s integer boolean))

(check-equal? (let ([n 4]) (in/out n integer in)) 4)
(check-equal? (let ([n 5]) (in/out n integer out)) 5)

(let ()
  (define F (λ (x) (λ (y) (+ x y))))
  (define f (in/out F (->s integer integer integer) out))
  (check-equal? (f 1 2) 3))

(let ()
  (define f (λ (x y) (+ x y)))
  (define F (in/out f (->s integer integer integer) in))
  (check-equal? ((F 1) 2) 3))

(let ()
  (define f (λ () 11))
  (define F (in/out f (->s integer) in))
  (check-equal? (F 0) 11))

(let ()
  (define F (λ (x) 11))
  (define f (in/out F (->s integer) out))
  (check-equal? (f) 11))

(let ()
  (define (f arg) (arg 1))
  (define called-main? #f)
  (define (main n)
    (set! called-main? #t)
    123)
  ((convert-it f (->s
                  (->s integer
                       (->s integer
                            integer))
                  integer))
   main)
  (check-true called-main?))

(let ()
  (define fs (list (λ (x y) (+ x y))
                   (λ (x y z) (+ x y z))
                   (λ (x) x)))
  (define Fs (in/out fs
                     (list/s (->s integer integer integer)
                             (->s integer integer integer integer)
                             (->s integer integer))
                     in))
  (check-equal? (((list-ref Fs 0) 1) 2) 3)
  (check-equal? ((((list-ref Fs 1) 1) 2) 3) 6)
  (check-equal? ((list-ref Fs 2) 2) 2))

(let ()
  (define fs (list (λ (x) (λ (y) (+ x y)))
                   (λ (x) (λ (y) (λ (z) (+ x y z))))
                   (λ (x) x)))
  (define Fs (in/out fs
                     (list/s (->s integer integer integer)
                             (->s integer integer integer integer)
                             (->s integer integer))
                     out))
  (check-equal? ((list-ref Fs 0) 1 2) 3)
  (check-equal? ((list-ref Fs 1) 1 2 3) 6)
  (check-equal? ((list-ref Fs 2) 2) 2))

(define-for-syntax inside 'inside)
(define-for-syntax both 'both)

(check-equal? (syntax-parameterize ([arithmetic-mode inside])
                (define l (list 0 1 2 1))
                (in/out l
                        (list/s integer integer integer integer)
                        out))
              (* 2 (sqrt -1)))
(check-equal? (syntax-parameterize ([arithmetic-mode inside])
                (define n (sqrt -1))
                (in/out n
                        (list/s integer integer integer integer)
                        in))
              (list 0 1 1 1))
(check-equal? (syntax-parameterize ([arithmetic-mode inside])
                (define L (list 0 1 1 1))
                (in/out L
                        (list/s integer integer integer integer)
                        out))
              0+1i)
(check-equal? (syntax-parameterize ([arithmetic-mode both])
                (define L (list 0 1 1 1))
                (in/out L
                        (list/s integer integer integer integer)
                        out))
              (list 0 1 1 1))

(let ()
  (define-lump L)
  (define l (list 0 1 1 1))
  (check-equal? (convert-it l
                            (list/s integer integer integer integer)
                            L
                            #:arithmetic-coercion-inside)
                (sqrt -1)))

(check-equal? (let ([l (list 0 1 1 1)])
                (convert-it l
                            (list/s integer integer integer integer)
                            #:arithmetic-coercion-inside))
              (sqrt -1))

(check-equal? (let ([l (list 3 0 22 0)])
                (convert-it l
                            (list/s integer integer integer integer)
                            #:arithmetic-coercion-inside))
              3+22i)
(check-equal? (let ([l (list 3 1 22 1)])
                (convert-it l
                            (list/s integer integer integer integer)
                            #:arithmetic-coercion-inside))
              3+22i)


(check-equal? (let ([L (let ([l (list (λ (x y) (+ x y))
                                      (λ (x y) (* x y)))])
                         (in/out l
                                 (list-of (->s integer integer integer))
                                 in))])
                (vector (((list-ref L 0) 1) 2)
                        (((list-ref L 1) 3) 4)))
              (vector 3 12))

(check-equal? (let ([l (let ([L (list (λ (x) (λ (y) (+ x y)))
                                      (λ (x) (λ (y) (* x y))))])
                         (in/out L
                                 (list-of (->s integer integer integer))
                                 out))])
                (vector ((list-ref l 0) 1 2)
                        ((list-ref l 1) 3 4)))
              (vector 3 12))

(check-equal? (let ([l (list 1 2 3)])
                (in/out l
                        (or/s (->s integer integer integer)
                              (list-of integer))
                        in))
              (list 1 2 3))
(check-equal? (let ([n 11])
                (in/out n
                        (or/s (->s integer integer integer)
                              (list-of integer)
                              integer)
                        in))
              11)

(let ()
  (define f (λ (x y) (+ x y)))
  (define F (in/out f (or/s (->s integer integer integer) integer) in))
  (check-equal? (f 1 2) 3))

(let ()
  (define-lump L (0 'x) (1 'y))
  (define f (λ (x) (- 1 x)))
  (define F (convert-it f (->s lump/s lump/s) L))
  (check-equal? (F 'x) 'y)
  (check-equal? (F 'y) 'x))

(let ()
  (define-lump L (0 'x) (1 'y) (2 'z))
  (define f (λ (x) (λ (y) (modulo (+ x y) 3))))
  (define F (convert-it f (->s lump/s lump/s lump/s) L))
  (check-equal? (F 'x 'y) 'y)
  (check-equal? (F 'y 'z) 'x))

(let ()
  (define-lump L (0 'x) (1 'y) (2 'z))
  (define f (λ (g) (list ((g 0) 1) ((g 1) 2) ((g 2) 0))))
  (define F (convert-it f (->s (->s lump/s lump/s lump/s) (list-of integer)) L))
  (check-equal? (F (λ (a b)
                     (case a
                       [(x) 'y]
                       [(y) 'z]
                       [(z) 'x])))
                '(1 2 0))
  (check-equal? (F (λ (a b)
                     (case b
                       [(x) 'y]
                       [(y) 'z]
                       [(z) 'x])))
                '(2 0 1)))

(let ()
  (define-lump L (0 'x) (1 'y) (2 'z))
  (check-exn
   abort-data?
   (λ ()
     (convert-it 3 lump/s L))))

(let ()
  (define-lump L (0 'x) (1 'y) (2 'z))
  (check-exn
   exn:fail?
   (λ ()
     ((convert-it (λ (x) x) (->s lump/s integer) L) 'q))))

(let ()
  (define F (list (λ (a) (+ a 1)) (λ (a) (λ (b) (+ 2 (* a b))))))
  (define f (in/out F
                    (->si ([msg (one-of/c 'x 'y)])
                          (res (msg)
                               (cond
                                 [(equal? msg 'x) (->s integer integer)]
                                 [(equal? msg 'y) (->s integer integer integer)]
                                 [else "error"])))
                    out))
  (check-equal? ((f 'x) 3) 4)
  (check-equal? ((f 'y) 7 11) 79))

(let ()
  (define f (λ (msg)
              (case msg
                [(x) (λ (a) (+ a 1))]
                [(y) (λ (a b) (+ 2 (* a b)))])))
  (define F (in/out f
                    (->si ([msg (one-of/c 'x 'y)])
                          (res (msg)
                               (cond
                                 [(equal? msg 'x) (->s integer integer)]
                                 [(equal? msg 'y) (->s integer integer integer)]
                                 [else "error"])))
                    in))
  (check-equal? ((list-ref F 0) 3) 4)
  (check-equal? (((list-ref F 1) 7) 11) 79))

(let ()
  (define F (list (λ (a) (+ a 1)) (λ (a) (λ (b) (+ 2 (* a b))))))
  (define f (in/out F
                    (->si ([msg (one-of/c "x" "y")])
                          (res (msg)
                               (cond
                                 [(equal? msg "x") (->s integer integer)]
                                 [else (->s integer integer integer)])))
                    out))
  (check-equal? ((f "x") 3) 4)
  (check-equal? ((f "y") 7 11) 79))


(let ()
  (define f (λ (msg)
              (case msg
                [("x") (λ (a) (+ a 1))]
                [("y") (λ (a b) (+ 2 (* a b)))])))
  (define F (in/out f
                    (->si ([msg (one-of/c "x" "y")])
                          (res (msg)
                               (cond
                                 [(equal? msg "x") (->s integer integer)]
                                 [else (->s integer integer integer)])))
                    in))
  (check-equal? ((list-ref F 0) 3) 4)
  (check-equal? (((list-ref F 1) 7) 11) 79))

(let ()
  (define l (list 2 (list 3 4)))
  (define L (in/out l (cons/s integer (cons/s integer integer)) out))
  (check-equal? L (cons 2 (cons 3 4))))

(let ()
  (define L (cons (cons 1 2) 3))
  (define l (in/out L (cons/s (cons/s integer integer) integer) in))
  (check-equal? l (list (list 1 2) 3)))

;; these next few tests (for string/s and string-or-integer/s)
;; depend on the precise ordiner that data/enumerate uses
(let ()
  (define l "racket")
  (define L (in/out l string/s in))
  (check-equal? L 34015667898221561123161278314514))

(let ()
  (define L 34015667898221561123161278314514)
  (define l (in/out L string/s out))
  (check-equal? l "racket"))

(let ()
  (define L (* 2 34015667898221561123161278314514))
  (define l (in/out L string-or-integer/s out))
  (check-equal? l "racket"))

(let ()
  (define l 11)
  (define L (in/out l string-or-integer/s out))
  (check-equal? L 3))

(let ()
  (define L 3)
  (define l (in/out L string-or-integer/s in))
  (check-equal? l 11))

(let ()
  (define l "racket")
  (define L (in/out l string-or-integer/s in))
  (check-equal? L (* 2 34015667898221561123161278314514)))


(let ()
  (struct s (a b) #:transparent)
  (define l (s 11 12))
  (define L (in/out l (struct/s s integer integer) in))
  (check-equal? L (list 99900000000115 11 12)))

(let ()
  (struct s (a b) #:transparent)
  (define L (list 's 11 12))
  (define l (in/out L (struct/s s integer integer) out))
  (check-equal? l (s 11 12)))

(let ()
  (struct s (a b) #:transparent)
  (define l (s (s 1 2) 3))
  (define L (in/out l (struct/s s (struct/s s integer integer) integer) in))
  (check-equal? L (list 99900000000115 (list 99900000000115 1 2) 3)))

(let ()
  (struct s (a b) #:transparent)
  (define L (list 99900000000115 (list 99900000000115 1 2) 3))
  (define l (in/out L (struct/s s (struct/s s integer integer) integer) out))
  (check-equal? l (s (s 1 2) 3)))


(let ()
  (struct s (a b) #:transparent)
  (struct t (a b c) #:transparent)
  (define l (s 11 12))
  (define L (in/out l (or/s (struct/s s integer integer)
                            (struct/s t integer integer boolean))
                    in))
  (check-equal? L (list 99900000000115 11 12)))

(let ()
  (struct s (a b) #:transparent)
  (struct t (a b c) #:transparent)
  (define l (t 9 47 #f))
  (define L (in/out l (or/s (struct/s s integer integer)
                            (struct/s t integer integer boolean))
                    in))
  (check-equal? L (list 99900000000116 9 47 #f)))

(let ()
  (struct s (a b) #:transparent)
  (struct t (a b c) #:transparent)
  (define L (list 99900000000115 11 12))
  (define l (in/out L (or/s (struct/s s integer integer)
                            (struct/s t integer integer boolean))
                    out))
  (check-equal? l (s 11 12)))

(let ()
  (struct s (a b) #:transparent)
  (struct t (a b c) #:transparent)
  (define L (list 99900000000116 9 47 #f))
  (define l (in/out L (or/s (struct/s s integer integer)
                            (struct/s t integer integer boolean))
                    out))
  (check-equal? l (t 9 47 #f)))

(let ()
  (define L (list #true (list 1 2 3)))
  (define l (in/out L any/s out))
  (check-equal? l (cons 1 (cons 2 3))))

(let ()
  (define L (list #false (list 1 2 3)))
  (define l (in/out L any/s out))
  (check-equal? l (list 1 2 3)))

(let ()
  (define l (cons 1 (cons 2 3)))
  (define L (in/out l any/s in))
  (check-equal? L (list #true (list 1 2 3))))

(let ()
  (define l (cons 1 (cons 2 (cons 3 '()))))
  (define L (in/out l any/s in))
  (check-equal? L (list #false (list 1 2 3))))

;; tests to make sure that when values go across
;; at any/c, they come out a the types that the
;; concolic tester has been told to expect
(let ()
  ;; any/c, normal mode: top-level value is wrong
  (define l (vector "not something the concolic tester expects"))
  (define L (in/out l any/s in))
  (check-equal? L 0))

(let ()
  ;; any/c, normal mode: top-level value is a wrong-arity procedure
  (define l (λ (x y) (+ x y)))
  (define L (in/out l any/s in))
  (check-equal? L 0))

(let ()
  ;; any/c, normal mode: function result isn't an integer
  (define l-vector-returning-function (λ (x) (vector "not something the concolic tester expects")))
  (define L (in/out l-vector-returning-function any/s in))
  (check-equal? (L 123) 0))

(let ()
  ;; any/c, normal mode: function coming out is called with a non-integer
  (define answer #f)
  (define L (λ (x) (set! answer x) 5))
  (define l (in/out L any/s out))
  (l (vector "not something the concolic tester expects"))
  (check-equal? answer 0))

(let ()
  ;; any/c, normal mode: proper list contains non-integer
  (define l (list (vector "not something the concolic tester expects")))
  (define L (in/out l any/s in))
  (check-equal? L (list #f (list 0))))

(let ()
  ;; any/c, normal mode: improper list contains non-integer
  (define l (cons (vector "not something the concolic tester expects")
                  (vector "not something the concolic tester expects")))
  (define L (in/out l any/s in))
  (check-equal? L (list #t (list 0 0))))

(let ()
  ;; any/c, arithmetic mode: top-level value is wrong
  (define l (vector "not something the concolic tester expects"))
  (define L (syntax-parameterize ([arithmetic-mode both])
              (in/out l any/s in)))
  (check-equal? L '(0 1 0 1)))

(let ()
  ;; any/c, arithmetic mode: function returns a bad result
  (define l (λ (_) (vector "not something the concolic tester expects")))
  (define L (syntax-parameterize ([arithmetic-mode both])
              (in/out l any/s in)))
  (check-equal? (L '(4 1 2 1)) '(0 1 0 1)))

(let ()
  ;; any/c, arithmetic mode: function called with a bad input
  (define answer #f)
  (define L (λ (x) (set! answer x) '(5 0 0 1)))
  (define l (syntax-parameterize ([arithmetic-mode both])
              (in/out L any/s out)))
  (l (vector "not something the concolic tester expects"))
  (check-equal? answer '(0 1 0 1)))

(let ()
  ;; any/c, arithmetic mode: top-level value is wrong
  (define l (vector "not something the concolic tester expects"))
  (define L (syntax-parameterize ([arithmetic-mode inside])
              (in/out l any/s in)))
  (check-equal? L '(0 1 0 1)))

(let ()
  ;; any/c, arithmetic mode: top-level value is a number
  (define l 3+2i)
  (define L (syntax-parameterize ([arithmetic-mode inside])
              (in/out l any/s in)))
  (check-equal? L '(3 1 2 1)))

(let ()
  ;; any/c, arithmetic mode: top-level value is a number
  (define L '(3 1 2 1))
  (define l (syntax-parameterize ([arithmetic-mode inside])
              (in/out L any/s out)))
  (check-equal? l 3+2i))

(let ()
  ;; any/c, arithmetic mode: function returns a bad result
  (define l (λ (_) (vector "not something the concolic tester expects")))
  (define L (syntax-parameterize ([arithmetic-mode inside])
              (in/out l any/s in)))
  (check-equal? (L '(4 1 2 1)) '(0 1 0 1)))

(let ()
  ;; any/c, arithmetic mode: function called with a bad input
  (define answer #f)
  (define L (λ (x) (set! answer x) '(5 0 0 1)))
  (define l (syntax-parameterize ([arithmetic-mode inside])
              (in/out L any/s out)))
  (l (vector "not something the concolic tester expects"))
  (check-equal? answer '(0 1 0 1)))

(let ()
  (define l (list 1 2 (list 1 2 (list 1 2))))
  (check-equal? (in/out l (list-of any/s) in)
                (list 1 2 (list #f (list 1 2 0)))))

(define (il->pl->il l) (proper-list->improper-list (improper-list->proper-list l)))
(check-equal? (il->pl->il 1) 1)
(check-equal? (il->pl->il (cons 1 2)) (cons 1 2))
(check-equal? (il->pl->il (cons 1 (cons 2 3))) (cons 1 (cons 2 3)))
