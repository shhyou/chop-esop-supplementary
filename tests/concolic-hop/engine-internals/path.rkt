#lang racket/base

(require racket/match
         racket/set
         racket/vector
         rackunit

         (only-in rosette/safe
                  define-symbolic*
                  sat
                  expression
                  constant)

         concolic-hop/rosette

         concolic-hop/data
         concolic-hop/conds
         concolic-hop/path
         concolic-hop/lib

         "../private/utils.rkt")

;
;
;
;
;
;                              ;;;;
;                                ;;
;                         ;;     ;;
;                         ;;     ;;
;                         ;;     ;;
;   ;;; ;;;;     ;;;     ;;;;;;  ;; ;;;;      ;;;;
;    ;;;   ;;   ;  ;;     ;;     ;;;   ;;   ;;   ;;
;    ;;    ;;  ;;   ;;    ;;     ;;    ;;   ;;   ;
;    ;;     ;;      ;;    ;;     ;;    ;;   ;;;
;    ;;     ;;    ;;;;    ;;     ;;    ;;    ;;;;
;    ;;     ;;  ;;  ;;    ;;     ;;    ;;      ;;;
;    ;;     ;; ;;   ;;    ;;     ;;    ;;   ;    ;;
;    ;;     ;  ;;   ;;    ;;     ;;    ;;   ;    ;;
;    ;;    ;   ;;  ;;;    ;;  ;  ;;    ;;   ;;  ;;
;    ;;;;;;     ;;; ;;;;   ;;; ;;;;;  ;;;;; ;;;;;
;    ;;
;    ;;
;    ;;
;    ;;
;  ;;;;;;
;

(module* test #f
  (require (only-in concolic-hop/lib integer boolean ->s))

  (test-case
   "path-constraint->key for branches"
   (check-equal?
    (path-constraint->key
     (input (hash)
            (hash)
            (sat))
     (extend-path-constraint
      (extend-path-constraint
       (empty-path-constraint)
       (branch 'then #t))
      (branch 'else #f)))
    #(#t #f)))

  (test-case
   "path-constraint->key for first-order functions, keys and concolic variables"
   (define-input an-input
     [X integer 5]
     [F (->s integer integer)
        (λ (_)
          (cond @ lbl0
                [5 : integer 0] @ lbl1
                [(* 2 X.var) : integer [Y 13]] @ lbl2
                [(+ Y.var 3) : integer [Z 0]] @ lbl3))])

   (define path-1
     (with-rosette ()
       (extend-path-constraint
        (extend-path-constraint
         (extend-path-constraint
          (extend-path-constraint
           (empty-path-constraint)
           (dispatch lbl0 #f 'integer -1))
          (dispatch lbl0 lbl1 'integer X.var))
         (dispatch lbl0 lbl2 'integer (+ X.var X.var)))
        (dispatch lbl0 lbl3 'integer (+ 3 Y.var)))))

   (define path≡-1
     (vector
      (dispatch-else≡ lbl0)
      (dispatch≡ lbl0 5 (a$x≡ 0))
      (dispatch≡ lbl0
                 (match (with-rosette () (* 2 X.var))
                   [(expression op 2 (== X.var)) (list op 2 (a$X≡ 'X integer))]
                   [(expression op (== X.var) 2) (list op (a$X≡ 'X integer) 2)])
                 (a$X≡ 0 integer))
      (dispatch≡ lbl0
                 (match (with-rosette () (+ Y.var 3))
                   [(expression op 3 (== Y.var)) (list op 3 (a$X≡ 0 integer))]
                   [(expression op (== Y.var) 3) (list op (a$X≡ 0 integer) 3)])
                 (a$X≡ 1 integer))))

   (check-equal?
    (path-constraint->key an-input path-1)
    path≡-1)

   (define path-2
     (with-rosette ()
       (extend-path-constraint
        path-1
        (dispatch lbl0 lbl2 'integer 10))))

   (define path≡-2
     (vector-append
      path≡-1
      (vector
       (dispatch≡ lbl0
                  (match (with-rosette () (* 2 X.var))
                    [(expression op 2 (== X.var)) (list op 2 (a$X≡ 'X integer))]
                    [(expression op (== X.var) 2) (list op (a$X≡ 'X integer) 2)])
                  (a$X≡ 0 integer)))))

   (check-equal?
    (path-constraint->key
     an-input
     path-2)
    path≡-2)
   )

  (test-case
   "path-constraint->key for highr-order functions and local variables"
   (define-input an-input
     [F (->s (->s integer integer)
             (->s integer integer))
        (λ (_)
          (cond @ lbl0
                [a$proc : (->s integer integer)
                        0] @ lbl1))])
   (check-equal?
    (path-constraint->key
     an-input
     (with-rosette ()
       (extend-path-constraint
        (empty-path-constraint)
        (dispatch lbl0 lbl1 'arrow (λ n (+ n 1))))))
    (vector
     (dispatch≡ lbl0 a$proc (a$x≡ 0)))))

  (test-case
   "path-constraint->key for higher-order curried functions"
   (define-input an-input
     [F (->s integer (->s integer integer))
        (λ (_)
          (cond @ lbl0
                [12 : integer
                    (λ (_)
                      (cond @ lbl2
                            [34 : integer 1] @ lbl3))] @ lbl1))])
   (check-equal?
    (path-constraint->key
     an-input
     (extend-path-constraint
      (extend-path-constraint
       (empty-path-constraint)
       (dispatch lbl0 lbl1 'integer 12))
      (dispatch lbl2 lbl3 'integer 34)))
    (vector
     (dispatch≡ lbl0 12 (a$λ≡))
     (dispatch≡ lbl2 34 (a$x≡ 1)))))

  (test-case
   "path-constraint->key for lists"

   (define-input inputs
     [L (list-of (list-of integer))
        (make-list (make-list [X 0] [Y 1])
                   (make-list [Z 2] #:unless [B #f] [W 3]))]
     [F (->s (or/s integer boolean) integer)
        (λ (_)
          (cond @ lbl0
                [X.var : integer 0] @ lbl1
                [Y.var : integer 0] @ lbl2
                [Z.var : integer 0] @ lbl3
                [B.var : boolean 0] @ lbl4
                [W.var : integer 0] @ lbl5))])

   (check-match
    (path-constraint->key
     inputs
     (extend-path-constraint
      (empty-path-constraint)
      (dispatch lbl0 lbl1 'integer 0)))
    (vector
     (dispatch≡ (== lbl0)
                (a$X≡ (a$X-name-list 'L 2) integer)
                (a$x≡ 0))))

   (check-match
    (path-constraint->key
     inputs
     (extend-path-constraint
      (empty-path-constraint)
      (dispatch lbl0 lbl2 'integer 1)))
    (vector
     (dispatch≡ (== lbl0)
                (a$X≡ (a$X-name-list 'L 4) integer)
                (a$x≡ 0))))

   (check-match
    (path-constraint->key
     inputs
     (extend-path-constraint
      (empty-path-constraint)
      (dispatch lbl0 lbl3 'integer 2)))
    (vector
     (dispatch≡ (== lbl0)
                (a$X≡ (a$X-name-list 'L 8) integer)
                (a$x≡ 0))))

   (check-match
    (path-constraint->key
     inputs
     (extend-path-constraint
      (empty-path-constraint)
      (dispatch lbl0 lbl4 'boolean #f)))
    (vector
     (dispatch≡ (== lbl0)
                (a$X≡ (a$X-name-list 'L 9) integer)
                (a$x≡ 0))))

   (check-match
    (path-constraint->key
     inputs
     (extend-path-constraint
      (empty-path-constraint)
      (dispatch lbl0 lbl5 'integer 3)))
    (vector
     (dispatch≡ (== lbl0)
                (a$X≡ (a$X-name-list 'L 10) integer)
                (a$x≡ 0)))))

  (test-case
   "path-constraint->key for lists in functions"

   (define-input inputs
     [F (->s integer (list/s boolean integer (list-of integer)))
        (λ (_)
          (cond @ lbl0
                [0 : integer (make-list [B #f] [X 11]
                                        (make-list [Y 12]))]
                @ lbl1
                [X.var : integer (make-list [B2 #t] [Z 21] (make-list))]
                @ lbl2))])

   (define X≡ (a$X≡ 3 integer))

   (check-equal?
    (path-constraint->key
     inputs
     (extend-path-constraint
      (extend-path-constraint
       (empty-path-constraint)
       (dispatch lbl0 lbl1 'integer 0))
      (dispatch lbl0 lbl2 'integer X.var)))
    (vector
     (dispatch≡ lbl0 0
                (a$cons≡ (a$X≡ 0 boolean)
                         (a$X≡ 1 boolean)
                         (a$cons≡ (a$X≡ 2 boolean)
                                  X≡
                                  (a$cons≡ (a$X≡ 4 boolean)
                                           (a$cons≡ (a$X≡ 5 boolean)
                                                    (a$X≡ 6 integer)
                                                    (a$empty≡ (a$X≡ 7 boolean)))
                                           (a$empty≡ (a$X≡ 8 boolean))))))
     (dispatch≡ lbl0 X≡
                (a$cons≡ (a$X≡ 9 boolean)
                         (a$X≡ 10 boolean)
                         (a$cons≡ (a$X≡ 11 boolean)
                                  (a$X≡ 12 integer)
                                  (a$cons≡ (a$X≡ 13 boolean)
                                           (a$empty≡ (a$X≡ 14 boolean))
                                           (a$empty≡ (a$X≡ 15 boolean))))))))
   )

  (test-case
   "path-constraint->key for eliminators a$%app, a$car and a$cdr"

   (define-input inputs
     [F (->s (->s integer boolean) (->s boolean integer))
        (λ (_)
          (cond
            @ lbl0
            [a$proc : (->s (list-of integer) boolean)
                    (λ (_)
                      (cond
                        @ lbl2
                        [#f : boolean
                            (let ([_ (1 (make-list [X1 3] [X2 0]))])
                              (cond
                                @ lbl4
                                [(> X2.var 10) : boolean [X3 2]]
                                @ lbl5))]
                        @ lbl3))]
            @ lbl1))]

     [Y1 integer 456]
     [G (->s (list-of integer) boolean)
        (λ (_)
          (cond
            @ lbl6
            [a$null : (list-of integer) [Y2 #f]] @ lbl7
            [a$pair : (list-of integer)
                    (let ([_ (car 0)])
                      (cond
                        @ lbl9
                        [Y1.var : integer [Y3 #t]] @ lbl10))] @ lbl8))]
     [H (->s (list-of integer) boolean)
        (λ (_)
          (cond
            @ lbl11
            [a$pair : (list-of integer)
                    (let ([_ (cdr 0)])
                      (cond
                        @ lbl13
                        [a$pair : (list-of integer) [Y4 #f]] @ lbl14))] @ lbl12))])

   (define X2>10
     (with-rosette () (> X2.var 10)))

   (check-equal?
    (path-constraint->key
     inputs
     (extend-path-constraint
      (extend-path-constraint
       (extend-path-constraint
        (empty-path-constraint)
        (dispatch lbl0 lbl1 'arrow
                  (λ (xs)
                    (with-rosette ()
                      (> (cadr xs) 10)))))
       (dispatch lbl2 lbl3 'boolean #f))
      (dispatch lbl4 lbl5 'boolean X2>10)))
    (vector
     (dispatch≡ lbl0 a$proc (a$λ≡))
     (dispatch≡ lbl2 #f
                (a$let≡
                 (a$%app≡ (a$x≡ 1)
                          (a$cons≡ (a$X≡ 0 boolean)
                                   (a$X≡ 1 integer)
                                   (a$cons≡ (a$X≡ 2 boolean)
                                            (a$X≡ 3 integer)
                                            (a$empty≡ (a$X≡ 4 boolean)))))))
     (dispatch≡ lbl4
                (match X2>10
                  [(expression op 10 (== X2.var)) (list op 10 (a$X≡ 3 integer))]
                  [(expression op (== X2.var) 10) (list op (a$X≡ 3 integer) 10)])
                (a$X≡ 5 integer))))

   (check-equal?
    (path-constraint->key
     inputs
     (extend-path-constraint
      (extend-path-constraint
       (extend-path-constraint
        (empty-path-constraint)
        (dispatch lbl6 lbl7 'list '()))
       (dispatch lbl6 lbl8 'list (list Y1.var)))
      (dispatch lbl9 lbl10 'integer Y1.var)))
    (vector
     (dispatch≡ lbl6 a$null (a$X≡ 0 boolean))
     (dispatch≡ lbl6 a$pair (a$let≡ (a$car≡ (a$x≡ 0))))
     (dispatch≡ lbl9 (a$X≡ 'Y1 integer) (a$X≡ 1 boolean))))

   (check-equal?
    (path-constraint->key
     inputs
     (extend-path-constraint
      (extend-path-constraint
       (empty-path-constraint)
       (dispatch lbl11 lbl12 'list (list 123 Y1.var)))
      (dispatch lbl13 lbl14 'list (list Y1.var))))
    (vector
     (dispatch≡ lbl11 a$pair (a$let≡ (a$cdr≡ (a$x≡ 0))))
     (dispatch≡ lbl13 a$pair (a$X≡ 0 boolean))))
   )

  )
