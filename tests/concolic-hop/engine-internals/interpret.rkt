#lang racket/base

(require racket/match
         concolic-hop/data
         concolic-hop/store
         (submod concolic-hop/lib internals)
         (only-in rosette/safe
                  sat sat?))


(module* test:λx.conds #f
  (require rackunit
           racket/match
           racket/set
           (only-in rosette/safe
                    define-symbolic*
                    sat
                    [equal? rosette:equal?]
                    [boolean? rosette:boolean?]
                    [integer? rosette:integer?]
                    [= rosette:=]
                    [+ rosette:+]
                    [* rosette:*]
                    [print rosette:print])

           (prefix-in cl: concolic-hop/lang)
           "../private/utils.rkt"
           )

  (define-input empty-inputs)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;
  ;;                          default values
  ;;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (check-pred boolean? (default-value-of (empty-env) boolean))

  (check-pred integer? (default-value-of (empty-env) integer))

  (test-begin
   (define f (default-value-of (empty-env)
                               (->s boolean integer)))

   (check-pred procedure? f)
   (check-pred integer? (f #t)))

  (test-begin
   (define g (default-value-of (empty-env)
                               (->s (->s integer boolean) integer)))

   (check-pred procedure? g)
   (define called? #f)
   (define called-integer #f)
   (check-pred integer? (g (λ (m)
                             (set! called? #t)
                             (set! called-integer m)
                             #t)))
   (when called?
     (check-pred integer? called-integer)))

  (test-begin
   (define h (default-value-of (empty-env)
                               (->s boolean (->s integer boolean))))

   (check-pred procedure? h)
   (check-pred procedure? (h #f))
   (check-pred boolean? ((h #f) 123)))

  (test-begin
   (define f
     (interpret empty-inputs
                (->s integer integer)
                (empty-canonical-function)))
   (check-pred procedure? f)
   (check-regexp-match
    #rx"else"
    (with-handlers ([abort-data? (λ (e) (format "~s" e))])
      (f 123))))

  (test-begin
   (define f
     (interpret empty-inputs
                (->s (->s integer integer) (->s integer integer))
                (empty-canonical-function)))
   (check-pred procedure? f)
   (check-regexp-match
    #rx"else"
    (with-handlers ([abort-data? (λ (e) (format "~s" e))])
      (f (λ (n) n))))
   (check-regexp-match
    #rx"else"
    (with-handlers ([abort-data? (λ (e) (format "~s" e))])
      ((f (λ (n) n)) 456))))

  (test-begin
   (define h (default-value-of (empty-env)
               (->s integer (list-of integer))))
   (check-pred procedure? h)
   (check-pred list? (h 123)))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;
  ;;                    contract (type) failures
  ;;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define regexp-type-error
    #rx"type mismatch")

  (test-begin
   (define f
     (interpret empty-inputs
                (->s integer integer)
                (empty-canonical-function)))

   (check-exn
    regexp-type-error
    (λ () (f #t)))

   (check-exn
    regexp-type-error
    (λ () (f (λ (n) (with-rosette () (+ n 1)))))))

  (test-begin
   (define f
     (interpret empty-inputs
                (->s boolean integer)
                (empty-canonical-function)))

   (check-exn
    regexp-type-error
    (λ () (f 0)))

   (check-exn
    regexp-type-error
    (λ () (f (λ (n) (with-rosette () (+ n 1)))))))

  (test-case
   "interpret checks base values' types"

   (define-input (and inputs (struct* input ([type input-types]
                                             [map the-input-map]
                                             [model model])))
     [F (->s (->s integer boolean) integer)
        (λ (_)
          (cond
            [a$proc : (->s integer boolean)
                    (let ([_ (0 [M 123])])
                      (cond
                        [#f : boolean 1]
                        [#t : boolean 1]))]))])
   (define f
     (interpret inputs
                (hash-ref input-types 'F)
                F))

   (call-with-model
    model
    (λ ()
      (check-exn
       regexp-type-error
       (λ () (f 0)))

      (check-exn
       regexp-type-error
       (λ () (f #f)))

      (check-exn
       regexp-type-error
       (λ () (f (λ (n) (with-rosette () (+ n 1))))))
      ))
   )

  (test-case
   "interpret checks type for local and global variables"
   (define-input (and inputs (struct* input ([type input-types]
                                             [model model]
                                             [map the-input-map])))
     [F (->s boolean integer)
        (λ (_)
          (cond
            [#f : boolean 0]
            [#t : boolean (: [X #f] ;; use a different, bad type
                             boolean)]))])

   (define f
     (interpret inputs
                (hash-ref input-types 'F)
                F))

   (check-exn
    regexp-type-error
    (λ ()
      (call-with-model
       model
       (λ () (f #f)))))

   (check-exn
    regexp-type-error
    (λ ()
      (call-with-model
       model
       (λ () (f #t))))))

  (test-case
   "interpret does not eagerly check tags"

   (define-input (and inputs (struct* input ([type input-types]
                                             [map the-input-map]
                                             [model model])))
     [X integer 123]
     [Y integer 456]
     [B boolean #f]
     [F (->s (list-of integer) integer)
        (λ (_)
          (cond
            [a$null : (list-of integer) [W 0]]
            [a$pair : (list-of integer) [Z 0]]))])

   (define f
     (interpret inputs
                (hash-ref input-types 'F)
                F))

   (call-with-model
    model
    (λ ()
      (check-not-exn
       (λ () (f '())))

      (check-not-exn
       (λ () (f '(1 2))))

      (check-not-exn
       (λ () (f (list X.var 3 Y.var))))

      (check-exn
       regexp-type-error
       (λ () (f 0)))

      (check-exn
       regexp-type-error
       (λ () (f B.var)))

      (check-not-exn
       (λ () (f (list '()))))

      (check-not-exn
       (λ () (f (list X.var Y.var B.var 0))))
      ))
   )

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;
  ;;                          interpreter
  ;;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (test-case
   "interpret: local variables"

   (define-input (and inputs (struct* input ([type input-types]
                                             [map the-input-map])))
     [F (->s integer integer)
        (λ (_)
          (cond
            [456 : integer 0]
            [789 : integer 0]))])
   (define f
     (interpret inputs
                (hash-ref input-types 'F)
                F))
   (check-pred procedure? f)
   (check-equal? (f 456) 456)
   (check-equal? (f 789) 789)
   (check-regexp-match
    #rx"else"
    (with-handlers ([abort-data? (λ (e) (format "~s" e))])
      (f 123))))

  (test-begin
   (define (g n)
     (with-rosette ()
       (* n 13)))

   (define-input (and inputs (struct* input ([type input-types]
                                             [map the-input-map])))
     [F (->s (->s integer integer)
             (->s integer integer))
        (λ (_)
          (cond
            [a$proc : (->s integer integer) 0]))])

   (define f
     (interpret inputs
                (hash-ref input-types 'F)
                F))
   (check-pred procedure? f)
   (check-pred procedure? (f g))
   (check-equal? ((f g) 0) 0)
   (check-equal? ((f g) 1) 13)
   (check-equal? ((f g) 3) 39))

  (test-case
   "interpret: cond and curried functions"

   (define-input (and inputs (struct* input ([type input-types]
                                             [map the-input-map])))
     [F (->s integer (->s integer integer))
        (λ (_)
          (cond
            [5 : integer
               (λ (_)
                 (cond
                   [8 : integer 0]
                   [11 : integer 1]))]
            [33 : integer
                (λ (_)
                  (cond
                    [8 : integer 0]
                    [11 : integer 1]))]))])

   (define f
     (interpret inputs
                (hash-ref input-types 'F)
                F))
   (check-pred procedure? f)
   (check-pred procedure? (f 5))
   (check-pred procedure? (f 33))

   (check-equal? ((f 5) 8) 8)
   (check-equal? ((f 5) 11) 5)

   (check-equal? ((f 33) 8) 8)
   (check-equal? ((f 33) 11) 33))

  (test-case
   "interpret: global variable"

   (define-input (and inputs (struct* input ([type input-types]
                                             [map the-input-map]
                                             [model model])))
     [F (->s integer integer)
        (λ (_)
          (cond
            [5 : integer [X -999]]))])

   (define f
     (interpret inputs
                (hash-ref input-types 'F)
                F))

   (check-equal?
    (call-with-model
     (model-set model X.var 133)
     (λ () (get-current-concrete-value (f 5))))
    133)

   (check-equal?
    (call-with-model
     (model-set model X.var 21)
     (λ () (get-current-concrete-value (f 5))))
    21))

  (test-case
   "->s with symbolic expressions at test positions"
   (define-input (and inputs (struct* input ([type input-types]
                                             [map the-input-map]
                                             [model model])))
     [X integer 5]
     [F (->s integer integer)
        (λ (_)
          (cond
            [X.var : integer [Y 67]]
            [(* 2 X.var) : integer [Z 1]]))])

   (check-equal?
    (call-with-model
     model
     (λ ()
       (interpret inputs
                  (hash-ref input-types 'X)
                  X)))
    X.var)

   (define f
     (interpret inputs
                (hash-ref input-types 'F)
                F))

   (check-equal?
    (model (call-with-model
            model
            (λ () (f X.var))))
    67)

   (check-equal?
    (model (call-with-model
            model
            (λ () (f 5))))
    67)

   (check-equal?
    (model (call-with-model
            model
            (λ () (f (with-rosette ()
                       (* 2 X.var))))))
    1)

   (check-equal?
    (model (call-with-model
            model
            (λ () (f 10))))
    1)

   (check-equal?
    (model (call-with-model
            model
            (λ () (f (with-rosette ()
                       (+ 5 X.var))))))
    1))

  (test-case
   "->s with (let _ = f v in conds)"
   (define-input (and inputs (struct* input ([type input-types]
                                             [map the-input-map]
                                             [model model])))
     [F (->s (->s integer integer)
             integer)
        (λ (_)
          (cond
            [a$proc : (->s integer integer)
                    (let ([_ (0 [X 5])])
                      (cond
                        [5 : integer [Y 67]]
                        [6 : integer 0]
                        [30 : integer [Z 1]]))]))])

   (define f
     (interpret inputs
                (hash-ref input-types 'F)
                F))

   (check-equal?
    (model (call-with-model
            model
            (λ () (f (λ (n) n)))))
    67)

   (check-equal?
    (model (call-with-model
            model
            (λ () (f (λ (n) (with-rosette () (* n 6)))))))
    1)

   (check-equal?
    (evaluate (call-with-model
               model
               (λ () (f (λ (n) (with-rosette () (+ n 1))))))
              model)
    6))

  (test-case
   "list-of pair? and null?"
   (define-input (and inputs (struct* input ([type input-types]
                                             [map the-input-map]
                                             [model model])))
     [X integer 123]
     [F (->s (list-of integer) integer)
        (λ (_)
          (cond
            [a$null : (list-of integer) [N -13]]
            [a$pair : (list-of integer) [M 37]]))])

   (define f
     (interpret inputs
                (hash-ref input-types 'F)
                F))

   (call-with-model
    model
    (λ ()
      (check-equal?
       (f '())
       N.var)

      (check-equal?
       (f '(1 2))
       M.var)

      (check-equal?
       (f (list 1 X 3))
       M.var)

      (check-equal?
       (f (list X))
       M.var)
      ))
   )

  (test-case
   "list-of car and cdr"
   (define-input (and inputs (struct* input ([type input-types]
                                             [map the-input-map]
                                             [model model])))
     [X integer 123]
     [F (->s (list-of integer)
             (or/s integer (list-of integer)))
        (λ (_)
          (cond
            [a$null : (list-of integer) [N -13]]
            [a$pair : (list-of integer)
                    (let ([_ (car 0)])
                      (cond
                        [5 : integer [M 37]]
                        [(+ N.var 2) : integer [K 11]]
                        [0 : integer
                           (let ([_ (cdr 1)])
                             (cond
                               [a$pair : (list-of integer) 0]))]))]))])

   (define f
     (interpret inputs
                (hash-ref input-types 'F)
                F))

   (call-with-model
    model
    (λ ()
      (check-equal?
       (f '())
       N.var)

      (check-equal?
       (f '(5 -1))
       M.var)

      (check-equal?
       (f (list (+ (get-current-concrete-value N.var)
                   2)))
       K.var)

      (check-equal?
       (f (list 0 -55 22 X.var 123))
       (list -55 22 X.var 123))
      ))
   )

  (test-case
   "list-of in top-level and function outputs"
   (define-input (and inputs (struct* input ([type input-types]
                                             [map the-input-map]
                                             [model model])))
     [L1 (list-of integer) (make-list)]
     [L2 (list-of integer) (make-list #:unless [B #f])]
     [L3 (list-of integer) (make-list #:unless [B1 #f]
                                      [X1 123]
                                      #:unless [B2 #f]
                                      [X2 456]
                                      [X3 789])]
     [F (->s integer (list-of integer))
        (λ (_)
          (cond
            [0 : integer (make-list)]
            [1 : integer (make-list #:unless [B3 #f])]
            [9 : integer (make-list [X4 123]
                                    [X5 456]
                                    [X6 789])]
            [-1 : integer (: [Z -1] integer)]
            [-3 : integer (: (make-list [W1 #f])
                             (list-of boolean))]))])

   (define f
     (interpret inputs
                (hash-ref input-types 'F)
                F))

   (define (concrete-symbolic-equal? v1 v2)
     (get-current-concrete-value
      (rosette:equal? v1 v2)))

   (define L1-value
     (call-with-model
      model
      (λ ()
        (interpret inputs
                   (hash-ref input-types 'L1)
                   L1))))

   (call-with-model
    model
    (λ ()
      (check-pred (not/c list?) L1-value)
      (check-pred rosette:list? L1-value)
      (check-equal? (get-current-concrete-value L1-value)
                    '())))

   (define L2-value
     (call-with-model
      model
      (λ ()
        (interpret inputs
                   (hash-ref input-types 'L2)
                   L2))))
   (call-with-model
    model
    (λ ()
      (check-equal? (get-current-concrete-value L2-value)
                    (list list-of-magic-ending-value))))

   (define L3-value
     (call-with-model
      model
      (λ ()
        (interpret inputs
                   (hash-ref input-types 'L3)
                   L3))))
   (call-with-model
    model
    (λ ()
      (check-equal? (get-current-concrete-value L3-value)
                    '(123 456 789))
      (check concrete-symbolic-equal? (f 0) L1-value)
      (check concrete-symbolic-equal? (f 1) L2-value)
      (check concrete-symbolic-equal? (f 9) L3-value)))

   (call-with-model
    model
    (λ ()
      (check-exn
       regexp-type-error
       (λ () (f -1)))

      (check-exn
       regexp-type-error
       (λ () (f -3)))))

   (call-with-model
    (model-set model B.var #t)
    (λ () (check-equal? (get-current-concrete-value L2-value) '())))

   (call-with-model ;; can't truncate (no effect)
    (model-set model B1.var #t)
    (λ () (check-equal? (get-current-concrete-value L3-value) '(123 456 789))))

   (call-with-model ;; can't truncate (no effect)
    (model-set model B2.var #t)
    (λ () (check-equal? (get-current-concrete-value L3-value) '(123 456 789)))))

  (test-case
   "list-c car"
   (define-input (and inputs (struct* input ([type input-types]
                                             [map the-input-map]
                                             [model model])))
     [X integer 123]
     [Y integer 456]
     [Z integer 789]
     [F (->s (list/s integer integer)
             integer)
        (λ (_)
          (cond
            [a$pair : (list/s integer integer)
                    (let ([_ (car 0)])
                      (cond
                        [X.var : integer [M -13]]
                        [Y.var : integer [N 37]]))]))]

     [L1 (list/s integer integer)
         (make-list [I 123] [J 456])]
     [L2 (list/s integer integer)
         (make-list [K 456] [L 123])])

   (define f
     (interpret inputs
                (hash-ref input-types 'F)
                F))

   (define L1-value
     (call-with-model
      model
      (λ ()
        (interpret inputs
                   (hash-ref input-types 'L1)
                   L1))))

   (define L2-value
     (call-with-model
      model
      (λ ()
        (interpret inputs
                   (hash-ref input-types 'L2)
                   L2))))

   (call-with-model
    model
    (λ ()
      (check-exn
       regexp-type-error
       (λ () (f 0)))

      (check-exn
       regexp-type-error
       (λ () (f '())))

      (check-exn
       regexp-type-error
       (λ () (f (list 123))))

      (check-exn
       regexp-type-error
       (λ () (f (list 123 456 789))))

      (check-exn
       regexp-type-error
       (λ () (f (list 0 #t))))

      (check-exn
       regexp-type-error
       (λ () (f (list #t 0))))

      (check-exn
       regexp-type-error
       (λ () (f (list X.var Y.var Z.var))))

      (check-equal?
       (f L1-value)
       M.var)

      (check-equal?
       (f L2-value)
       N.var)
      ))
   )

  (test-case
   "list-c cadr"
   (define-input (and inputs (struct* input ([type input-types]
                                             [map the-input-map]
                                             [model model])))
     [X integer 123]
     [Y integer 456]
     [Z integer 789]
     [F (->s (list/s integer integer)
             integer)
        (λ (_)
          (cond
            [a$pair : (list/s integer integer)
                    (let ([_ (cdr 0)])
                      (cond
                        [a$pair : (list/s integer)
                                (let ([_ (car 0)])
                                  (cond
                                    [X.var : integer [M 37]]
                                    [Y.var : integer [N -13]]))]))]))]

     [L1 (list/s integer integer)
         (make-list [I 123] [J 456])]
     [L2 (list/s integer integer)
         (make-list [K 456] [L 123])])

   (define f
     (interpret inputs
                (hash-ref input-types 'F)
                F))

   (define L1-value
     (call-with-model
      model
      (λ ()
        (interpret inputs
                   (hash-ref input-types 'L1)
                   L1))))

   (define L2-value
     (call-with-model
      model
      (λ ()
        (interpret inputs
                   (hash-ref input-types 'L2)
                   L2))))

   (call-with-model
    model
    (λ ()
      (check-exn
       regexp-type-error
       (λ () (f 0)))

      (check-exn
       regexp-type-error
       (λ () (f '())))

      (check-exn
       regexp-type-error
       (λ () (f (list 123))))

      (check-exn
       regexp-type-error
       (λ () (f (list 123 456 789))))

      (check-exn
       regexp-type-error
       (λ () (f (list 0 #t))))

      (check-exn
       regexp-type-error
       (λ () (f (list #t 0))))

      (check-exn
       regexp-type-error
       (λ () (f (list X.var Y.var Z.var))))

      (check-equal? (f L1-value) N.var)

      (check-equal? (f L2-value) M.var)
      ))
   )

  ;; interpreter test for lists
  (test-begin
   (define-input (and inputs (struct* input ([type input-types]
                                             [map the-input-map]
                                             [model model])))
     [L1 (list-of integer)
         (make-list [E1 11]
                    #:unless [b2 #f]
                    [E2 22]
                    [E3 33])]
     [L2 (list-of integer)
         (make-list #:unless [b4 #t]
                    [E4 44])]
     [L3 (list-of integer)
         (make-list [E5 55]
                    [E6 66]
                    #:unless [bnull #f])])

   (define-values (L1-value L2-value L3-value)
     (call-with-model
      model
      (λ ()
        (values (interpret inputs (hash-ref input-types 'L1) L1)
                (interpret inputs (hash-ref input-types 'L2) L2)
                (interpret inputs (hash-ref input-types 'L3) L3)))))

   ;; this is an interpreter test
   (call-with-model ;; can't truncate (no effect)
    (model-set model b2.var #t)
    (λ () (check-equal? (get-current-concrete-value L1-value) '(11 22 33))))

   (call-with-model
    (model-set model b4.var #f)
    (λ () (check-equal? (get-current-concrete-value L2-value) '(44))))

   (call-with-model
    (model-set model E3.var 99)
    (λ () (check-equal? (get-current-concrete-value L1-value) '(11 22 99))))

   (call-with-model
    model
    (λ ()
      (check-equal? (get-current-concrete-value L1-value) '(11 22 33))
      (check-equal? (get-current-concrete-value L2-value) '(44)) ;; can't truncate
      (check-equal? (get-current-concrete-value L3-value)
                    (list 55 66 list-of-magic-ending-value))))
   )

  ;; concretization
  (test-case
   "concretization"

   (define-input input
     [X integer 123]
     [L (list-of boolean) (make-list [B1 #f] [B2 #t])]
     [F (->s integer integer)
        (λ (_)
          (cond
            [(* X.var 2) : integer
                         0]))])

   (define dead-end
     '(error "ASSERT_UNREACHABLE"))
   (check-match
    (concretize-input (list 'X 'L 'F) input)
    (hash-table
     ('X 123)
     ('L '(cons #f (cons #t null)))
     ('F `(λ (,(? symbol? x))
            (cond
              [(procedure? ,x) ,(== dead-end)]
              [(null? ,x) ,(== dead-end)]
              [(pair? ,x) ,(== dead-end)]
              [(equal? ,x ,(== (* 123 2))) ,x]
              [else ,(== dead-end)]))))))
  )

(module+ test
  (require (submod "../private/utils.rkt" config-output-port))

  (require (submod ".." test:λx.conds))

  (reset-output-port!)
  )
