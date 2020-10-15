#lang racket

(require concolic-hop/ctc
         (only-in concolic-hop/lib exn:fail:error-bug? abort-data?)
         rackunit)

(check-equal?
 (apply-ctc integer? 1 bug bad-input TEST)
 1)

(check-exn
 exn:fail:error-bug?
 (λ ()
   (apply-ctc integer? #f bug bad-input TEST)))

(check-equal? (apply-ctc integer? #f no-blame bad-input TEST)
              #f)

(check-equal?
 (apply-ctc boolean? #f bug bad-input TEST)
 #f)

(check-exn
 exn:fail:error-bug?
 (λ ()
   (apply-ctc boolean? 1 bug bad-input TEST)))

(check-equal?
 (apply-ctc (λ (x) (and (integer? x) (<= 11 x 13)))
            12
            bug bad-input TEST)
 12)

(check-exn
 exn:fail:error-bug?
 (λ ()
   (apply-ctc (λ (x) (and (integer? x) (<= 11 x 13)))
              1
              bug bad-input TEST)))

(check-true ((ctc->pred integer?) 1))
(check-false ((ctc->pred integer?) #f))

(check-exn
 exn:fail:error-bug?
 (λ ()
   ((apply-ctc (-> integer? integer?)
               (λ (x) #f)
               bug bad-input TEST)
    1)))

(check-exn
 abort-data?
 (λ ()
   ((apply-ctc (-> integer? integer?)
               (λ (x) 1)
               bug bad-input TEST)
    #f)))

(check-exn
 exn:fail:error-bug?
 (λ ()
   ((apply-ctc (-> integer? boolean? integer?)
               (λ (x b) #f)
               bug bad-input TEST)
    1 #f)))

(check-exn
 abort-data?
 (λ ()
   ((apply-ctc (-> integer? boolean? integer?)
               (λ (x b) 1)
               bug bad-input TEST)
    #f #f)))

(check-exn
 abort-data?
 (λ ()
   ((apply-ctc (-> integer? boolean? integer?)
               (λ (x b) 1)
               bug bad-input TEST)
    1 1)))

(check-exn
 exn:fail:error-bug?
 (λ ()
   (((apply-ctc (-> boolean? (-> integer? integer?))
                (λ (b) (λ (x) #f))
                bug bad-input TEST)
     #f)
    1)))

(check-exn
 abort-data?
 (λ ()
   (((apply-ctc (-> boolean? (-> integer? integer?))
                (λ (b) (λ (x) 1))
                bug bad-input TEST)
     #f)
    #f)))

(check-exn
 exn:fail:error-bug?
 (λ ()
   ((apply-ctc (-> (-> integer? integer?) boolean?)
               (λ (f) (f #f))
               bug bad-input TEST)
    (λ (x) x))))

(check-exn
 abort-data?
 (λ ()
   ((apply-ctc (-> (-> integer? integer?) boolean?)
               (λ (f) (f 1))
               bug bad-input TEST)
    (λ (x) #f))))

(check-exn
 exn:fail:error-bug?
 (λ ()
   (apply-ctc (and/c integer? boolean?) #f
              bug bad-input TEST)))

(check-exn
 exn:fail:error-bug?
 (λ ()
   (apply-ctc (and/c integer? boolean?) 1
              bug bad-input TEST)))

(check-exn
 abort-data?
 (λ ()
   ((apply-ctc (-> (and/c integer? boolean?) integer?)
               (λ (x) 0)
               bug bad-input TEST)
    1)))

(check-exn
 abort-data?
 (λ ()
   ((apply-ctc (-> (and/c integer? boolean?) integer?)
               (λ (x) 0)
               bug bad-input TEST)
    #f)))

(check-false (ctc->pred (and/c integer? (-> integer? integer?) boolean?)))
(check-false ((ctc->pred (and/c integer? boolean?)) 1))
(check-false ((ctc->pred (and/c integer? boolean?)) #t))
(check-false ((ctc->pred (and/c integer? positive?)) -1))
(check-true ((ctc->pred (and/c integer? positive?)) 1))

(check-exn
 abort-data?
 (λ ()
   ((apply-ctc (->i ([x (listof boolean?)]) [res (x) integer?])
               (λ (x) 0)
               bug bad-input TEST)
    #f)))

(check-exn
 abort-data?
 (λ ()
   ((apply-ctc (->i ([x (listof boolean?)]) [res (x) integer?])
               (λ (x) 0)
               bug bad-input TEST)
    '(1))))

(check-exn
 exn:fail:error-bug?
 (λ ()
   (apply-ctc (listof boolean?) 1
              bug bad-input TEST)))

(check-exn
 exn:fail:error-bug?
 (λ ()
   (apply-ctc (listof boolean?) '("x")
              bug bad-input TEST)))

(check-false ((ctc->pred (listof boolean?)) #f))
(check-false ((ctc->pred (listof boolean?)) '(1)))
(check-true  ((ctc->pred (listof boolean?)) '(#t)))
(check-true  ((ctc->pred (listof boolean?)) '()))

(check-exn
 abort-data?
 (λ ()
   ((apply-ctc (->i ([x (non-empty-listof boolean?)]) [res (x) integer?])
               (λ (x) 0)
               bug bad-input TEST)
    #f)))

(check-exn
 abort-data?
 (λ ()
   ((apply-ctc (->i ([x (non-empty-listof boolean?)]) [res (x) integer?])
               (λ (x) 0)
               bug bad-input TEST)
    '(1))))

(check-exn
 exn:fail:error-bug?
 (λ ()
   (apply-ctc (non-empty-listof boolean?) 1
              bug bad-input TEST)))

(check-exn
 exn:fail:error-bug?
 (λ ()
   (apply-ctc (non-empty-listof boolean?) '("x")
              bug bad-input TEST)))

(check-exn
 exn:fail:error-bug?
 (λ ()
   (apply-ctc (non-empty-listof boolean?) '()
              bug bad-input TEST)))

(check-false ((ctc->pred (non-empty-listof boolean?)) #f))
(check-false ((ctc->pred (non-empty-listof boolean?)) '(1)))
(check-true  ((ctc->pred (non-empty-listof boolean?)) '(#t)))
(check-false ((ctc->pred (non-empty-listof boolean?)) '()))


(check-exn
 exn:fail:error-bug?
 (λ ()
   ((apply-ctc (->i ([x integer?]) [res (x) integer?])
               (λ (x) #f)
               bug bad-input TEST)
    1)))

(check-exn
 abort-data?
 (λ ()
   ((apply-ctc (->i ([y integer?]) [res (y) integer?])
               (λ (x) 1)
               bug bad-input TEST)
    #f)))

(check-exn
 exn:fail:error-bug?
 (λ ()
   ((apply-ctc (->i ([w integer?] [z boolean?]) [res (w z) integer?])
               (λ (x b) #f)
               bug bad-input TEST)
    1 #f)))

(check-exn
 abort-data?
 (λ ()
   ((apply-ctc (->i ([w integer?] [q boolean?]) [ret (w q) integer?])
               (λ (x b) 1)
               bug bad-input TEST)
    #f #f)))

(check-exn
 abort-data?
 (λ ()
   ((apply-ctc (->i ([a integer?] [b boolean?]) [ret (a b) integer?])
               (λ (x b) 1)
               bug bad-input TEST)
    1 1)))

(check-exn
 exn:fail:error-bug?
 (λ ()
   (((apply-ctc (-> boolean? (->i ([x integer?]) [ret (x) integer?]))
                (λ (b) (λ (x) #f))
                bug bad-input TEST)
     #f)
    1)))

(check-exn
 abort-data?
 (λ ()
   (((apply-ctc (-> boolean? (->i ([x integer?]) [res (x) integer?]))
                (λ (b) (λ (x) 1))
                bug bad-input TEST)
     #f)
    #f)))

(check-exn
 exn:fail:error-bug?
 (λ ()
   ((apply-ctc (-> (->i ([x integer?]) [res (x) integer?]) boolean?)
               (λ (f) (f #f))
               bug bad-input TEST)
    (λ (x) x))))

(check-exn
 abort-data?
 (λ ()
   ((apply-ctc (-> (->i ([f integer?]) [g (f) integer?]) boolean?)
               (λ (f) (f 1))
               bug bad-input TEST)
    (λ (x) #f))))

(check-equal?
 ((apply-ctc (->i ([x integer?])
                  [res (x)
                       (cond
                         [(= x 0) boolean?]
                         [(= x 1) integer?]
                         [else any/c])])
             (λ (x) #f)
             bug bad-input TEST)
  0)
 #f)

(check-exn
 exn:fail:error-bug?
 (λ ()
   ((apply-ctc (->i ([x integer?])
                    [res (x)
                         (cond
                           [(= x 0) boolean?]
                           [(= x 1) integer?]
                           [else any/c])])
               (λ (x) #f)
               bug bad-input TEST)
    1)))

(check-exn
 exn:fail:error-bug?
 (λ ()
   ((apply-ctc (->i ([x integer?])
                    [res (x)
                         (cond
                           [(= x 0) boolean?]
                           [(= x 1) integer?]
                           [else (listof integer?)])])
               (λ (x) #f)
               bug bad-input TEST)
    2)))

(check-equal? (apply-ctc (-> integer? integer? integer?)
                         5
                         no-blame no-blame TEST)
              5)

(check-equal? ((apply-ctc (-> integer? integer? integer?)
                          (λ (x) x)
                          no-blame no-blame TEST)
               5)
              5)

(check-equal? ((apply-ctc (-> integer? integer? integer?)
                          (λ (x y) x)
                          no-blame no-blame TEST)
               #f #t)
              #f)
(check-false (ctc->pred (-> integer? integer?)))

(check-equal?
 (apply-ctc any/c '(1 2 3)
            bug bad-input TEST)
 '(1 2 3))

(check-equal?
 (apply-ctc any/c '(1 2 3)
            no-blame no-blame TEST)
 '(1 2 3))

(check-true ((ctc->pred any/c) 5))
(check-true ((ctc->pred any/c) '(1 2 3)))


(check-exn
 abort-data?
 (λ ()
   ;; none/c always tells us to give up on this run
   (apply-ctc none/c 4 no-blame no-blame TEST)))

(check-equal?
 (apply-ctc (listof integer?) '(1 2 3) bug bad-input TEST)
 '(1 2 3))

(check-exn
 exn:fail:error-bug?
 (λ ()
   (apply-ctc (listof integer?) #f bug bad-input TEST)))

(check-equal?
 (apply-ctc (listof integer?) #f no-blame no-blame TEST)
 #f)

(check-equal?
 (apply-ctc (listof integer?) '(#f) no-blame no-blame TEST)
 '(#f))

(check-equal?
 (apply-ctc (>=/c 0) 0 bug bad-input TEST)
 0)

(check-equal?
 (apply-ctc (>=/c 0) 1 bug bad-input TEST)
 1)

(check-exn
 exn:fail:error-bug?
 (λ ()
   (apply-ctc (>=/c 0) '() bug bad-input TEST)))

(check-exn
 exn:fail:error-bug?
 (λ ()
   (apply-ctc (>=/c 0) -1 bug bad-input TEST)))

(check-equal?
 (apply-ctc (>/c 0) 1 bug bad-input TEST)
 1)

(check-exn
 exn:fail:error-bug?
 (λ ()
   (apply-ctc (>/c 0) 0 bug bad-input TEST)))

(check-exn
 exn:fail:error-bug?
 (λ ()
   (apply-ctc (>/c 0) '() bug bad-input TEST)))

(check-exn
 exn:fail:error-bug?
 (λ ()
   (apply-ctc (>/c 0) -1 bug bad-input TEST)))

(check-equal?
 (apply-ctc (=/c 0) 0 bug bad-input TEST)
 0)

(check-exn
 (λ (x)
   (and (exn:fail? x)
        (regexp-match? (regexp (~a "^" (regexp-quote "=/c: expected a real number")))
                       (exn-message x))))
 (λ () (apply-ctc (=/c "not a number") (list 1 1) bug bad-input TEST)))

(check-exn
 (λ (x)
   (and (exn:fail? x)
        (regexp-match? #rx"^=/c: expected a real number"
                       (exn-message x))))
 (λ () (apply-ctc (=/c (sqrt -1)) (list 1 1) bug bad-input TEST)))

(check-equal?
 (apply-ctc (c:=/c (list 1 0 0 1)) (list 1 0 0 1) bug bad-input TEST)
 (list 1 0 0 1))

(check-exn
 (λ (x)
   (and (exn:fail? x)
        (regexp-match? #rx"^c:=/c: expected a real number"
                       (exn-message x))))
 (λ () (apply-ctc (c:=/c (list 1 1)) (list 1 1) bug bad-input TEST)))

(check-exn
 (λ (x)
   (and (exn:fail? x)
        (regexp-match? #rx"^c:=/c: expected a real number"
                       (exn-message x))))
 (λ () (apply-ctc (c:=/c "not a number") (list 1 1) bug bad-input TEST)))
   
(check-exn
 exn:fail:error-bug?
 (λ ()
   (apply-ctc (=/c 0) 1 bug bad-input TEST)))

(check-exn
 exn:fail:error-bug?
 (λ ()
   (apply-ctc (=/c 0) (list 0) bug bad-input TEST)))

(check-exn
 abort-data?
 (λ ()
   ((apply-ctc (-> (-> integer? integer? integer?) integer?)
               (λ (f) (f 1)) ;; wrong arity, thus bad input
               bad-input
               bug
               X)
    (λ (x y) (+ x y)))))

(check-equal?
 (apply-ctc (one-of/c 'x 'y 'z) 'x bug bad-input TEST)
 'x)

(check-equal?
 (apply-ctc (one-of/c 'x 'y 'z) 'y bug bad-input TEST)
 'y)

(check-equal?
 (apply-ctc (one-of/c 'x 'y 'z) 'z bug bad-input TEST)
 'z)

(check-equal?
 (apply-ctc (one-of/c 'x 0 'z) 0 bug bad-input TEST)
 0)

(check-equal?
 (apply-ctc (one-of/c "x" 0 "z") "z" bug bad-input TEST)
 "z")

(check-exn
 exn:fail:error-bug?
 (λ ()
   (apply-ctc (one-of/c 'x 'y 'z) 'w bug bad-input TEST)))

(check-exn
 exn:fail:error-bug?
 (λ ()
   (apply-ctc (one-of/c 'x 'y 'z 0) #f bug bad-input TEST)))

(check-exn
 exn:fail:error-bug?
 (λ ()
   (apply-ctc (one-of/c "x" "y" "z") "w" bug bad-input TEST)))

(check-exn
 exn:fail:error-bug?
 (λ ()
   (apply-ctc (one-of/c "x" "y" "z") #f bug bad-input TEST)))

(check-equal?
 (apply-ctc (not/c (one-of/c 'x 0 'z)) 12 bug bad-input TEST)
 12)

(check-exn
 exn:fail:error-bug?
 (λ ()
   (apply-ctc (not/c (one-of/c 'x 'y 'z)) 'y bug bad-input TEST)))

(check-equal?
 (apply-ctc (not/c boolean?) 12 bug bad-input TEST)
 12)

(check-exn
 exn:fail:error-bug?
 (λ ()
   (apply-ctc (not/c boolean?) #t bug bad-input TEST)))


(check-equal?
 (apply-ctc false? #f bug bad-input TEST)
 #f)

(check-exn
 exn:fail:error-bug?
 (λ ()
   (apply-ctc false? #t bug bad-input TEST)))

(check-exn
 exn:fail:error-bug?
 (λ ()
   (apply-ctc false? 11 bug bad-input TEST)))

(check-equal? (apply-ctc "x" "x" bug bad-input TEST)
              "x")

(check-exn
 exn:fail:error-bug?
 (λ ()
   (apply-ctc "x" "y" bug bad-input TEST)))

(define-ctc a-number-that-has-all-zeros-after-the-decimal integer?)

(check-equal? (apply-ctc a-number-that-has-all-zeros-after-the-decimal 11 bug bad-input TEST)
              11)

(check-exn
 exn:fail:error-bug?
 (λ ()
   (apply-ctc a-number-that-has-all-zeros-after-the-decimal "y" bug bad-input TEST)))




(check-equal? (apply-ctc (or/c (listof integer?) boolean?) #f bug bad-input TEST)
              #f)

(check-equal? (apply-ctc (or/c (listof integer?) boolean?) '(1 2 3) bug bad-input TEST)
              '(1 2 3))

(check-exn
 exn:fail:error-bug?
 (λ ()
   (apply-ctc (or/c (listof integer?) boolean?) "y" bug bad-input TEST)))

(check-equal? (apply-ctc (or/c (listof integer?) boolean? (-> integer? integer?))
                         #f bug bad-input TEST)
              #f)
(check-equal? (apply-ctc (or/c (listof integer?) boolean? (-> integer? integer?))
                         '(1 2 3) bug bad-input TEST)
              '(1 2 3))
(check-equal? ((apply-ctc (or/c (listof integer?) boolean? (-> integer? integer?))
                          (λ (x) x) bug bad-input TEST) 5)
              5)

(check-exn
 exn:fail:error-bug?
 (λ ()
   (apply-ctc (or/c (listof integer?) boolean? (-> integer? integer?)) "y" bug bad-input TEST)))
(check-exn
 exn:fail:error-bug?
 (λ ()
   ((apply-ctc (or/c (listof integer?) boolean? (-> integer? integer?))
               (λ (x) "one") bug bad-input TEST)
    1)))

(check-equal? (apply-ctc (list/c integer? boolean? string?)
                         (list 1 #f "x")
                         bug bad-input TEST)
              (list 1 #f "x"))

(check-exn
 exn:fail:error-bug?
 (λ ()
   (apply-ctc (list/c integer? boolean? string?)
              (list 1 #f '())
              bug bad-input TEST)))

(check-exn
 exn:fail:error-bug?
 (λ ()
   (apply-ctc (list/c integer? boolean? string?)
              (list 1 4 "x")
              bug bad-input TEST)))

(check-exn
 exn:fail:error-bug?
 (λ ()
   (apply-ctc (list/c integer? boolean? string?)
              (list "z" #f "x")
              bug bad-input TEST)))

(check-true ((ctc->pred (list/c integer? integer? integer?)) '(1 2 3)))
(check-false ((ctc->pred (list/c integer? integer? integer?)) '(1 "two" 3)))
(check-false ((ctc->pred (list/c integer? integer? integer?)) 123))

(check-equal? (apply-ctc (cons/c integer? boolean?)
                         (cons 1 #f)
                         bug bad-input TEST)
              (cons 1 #f))

(check-exn
 exn:fail:error-bug?
 (λ ()
   (apply-ctc (cons/c integer? boolean?)
              (cons 1 4)
              bug bad-input TEST)))

(check-exn
 exn:fail:error-bug?
 (λ ()
   (apply-ctc (cons/c integer? boolean?)
              (list "z" #f)
              bug bad-input TEST)))

(check-false ((ctc->pred (cons/c integer? string?)) (cons 1 2)))
(check-false ((ctc->pred (cons/c integer? string?)) (cons "one" "two")))
(check-true ((ctc->pred (cons/c integer? string?)) (cons 1 "two")))
(check-false ((ctc->pred (cons/c integer? integer?)) 123))

(check-equal?
 (object-name
  (apply-ctc (-> integer? integer?)
             (let ([f (λ (x) x)]) f)
             bug bug TEST))
 'f)

(check-exn
 (λ (x) (regexp-match #rx"^bug:" (exn-message x)))
 (λ () (apply-ctc integer? "one" bug bad-input TEST)))

(check-exn
 (λ (x) (regexp-match #rx"^bad-input:" (exn-message x)))
 (λ () (apply-ctc integer? "one" bad-input bug TEST)))

(let ()
  (struct s (a b))
  (check-exn
   exn:fail:error-bug?
   (λ ()
     (define an-s (s 1 #f))
     (apply-ctc (struct/c s integer? integer?) an-s bug bad-input TEST))))

(let ()
  (struct s (a b))
  (check-exn
   exn:fail:error-bug?
   (λ ()
     (define an-s (s #f 1))
     (apply-ctc (struct/c s integer? integer?) an-s bug bad-input TEST))))

(let ()
  (struct s (a b))
  (check-exn
   exn:fail:error-bug?
   (λ ()
     (define an-s (s 1 #f))
     (apply-ctc (struct/c s integer? (-> integer? integer?)) an-s bug bad-input TEST))))

(let ()
  (struct s (a b))
  (check-exn
   exn:fail:error-bug?
   (λ ()
     (define an-s (s #f 1))
     (apply-ctc (struct/c s (-> integer? integer?) integer?) an-s bug bad-input TEST))))

(let ()
  (struct s (a b))
  (define an-s (s 5 6))
  (check-true (eq? an-s
                   (apply-ctc (struct/c s integer? integer?) an-s bug bad-input TEST))))

(let ()
  (struct s (a b))
  (define an-s (s (λ (x) #f) 1))
  (define s2
    (apply-ctc (struct/c s (-> integer? integer?) integer?) an-s bug bad-input TEST))
  (define f (s-a s2))
  (check-exn
   exn:fail:error-bug?
   (λ ()
     (f 1))))


(let ()
  (struct leaf () #:transparent)
  (struct node (val left right) #:transparent)
  (define-ctc bt
    (or/c (struct/c leaf)
          (struct/c node
                    integer?
                    (recursive-contract bt #:chaperone)
                    (recursive-contract bt #:chaperone))))
  (define a-bt.1 (node 1 (node 2 (leaf) (leaf)) (node 3 (leaf) (leaf))))
  (define a-bt.2 (apply-ctc bt a-bt.1 bug bad-input TEST))
  (check-equal? a-bt.1 a-bt.2)

  (check-exn
   exn:fail:error-bug?
   (λ ()
     (apply-ctc bt 5 bug bad-input TEST)))

  (check-exn
   exn:fail:error-bug?
   (λ ()
     (apply-ctc bt (node 1 (node (node "string" (leaf) (leaf)) 2 (leaf)) (leaf))
                bug bad-input TEST)))

  (check-exn
   exn:fail:error-bug?
   (λ ()
     (apply-ctc bt (node 1 (node (node 11 "string" (leaf)) 2 (leaf)) (leaf))
                bug bad-input TEST))))



(let ()
  (struct s (a b))
  (define-id-with-ctc (-> integer? integer? any/c) s _s bug bad-input)
  (check-equal? (match (s 1 2)
                  [(s x y) (+ x y)])
                3)
  (check-equal? (match (_s 1 2)
                  [(_s x y) (+ x y)])
                3)
  (check-equal? (match (_s 1 2)
                  [(s x y) (+ x y)])
                3)
  (check-equal? (match (s 1 2)
                  [(_s x y) (+ x y)])
                3))
