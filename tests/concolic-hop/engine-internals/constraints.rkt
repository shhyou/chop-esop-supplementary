#lang racket/base

(module* test:compile-smt racket/base
  (require rackunit
           racket/set
           racket/match
           racket/contract/base
           (only-in rosette/safe sat? unsat? assert)
           concolic-hop/rosette
           concolic-hop/data
           concolic-hop/store
           concolic-hop/path
           concolic-hop/lib
           "../private/utils.rkt")

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;
  ;;                       constraint compilation
  ;;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (test-case
   "top-level function cond expression invariant"

   (define-input inputs
     [N integer -999]
     [F (->s integer integer)
        (λ (_)
          (cond
            [N.var : integer [X 0]]
            [(+ N.var 10) : integer [Y 0]]
            [(* N.var 2) : integer [Z 0]]))])

   (check-pred unsat?
               (solve/allow-exception
                (λ ()
                  (compile-smt inputs (hash-ref (input-type inputs) 'F) F (set))
                  (assert (with-rosette ()
                            (= (+ N.var 10) (* N.var 2)))))))

   (check-pred unsat?
               (solve/allow-exception
                (λ ()
                  (compile-smt inputs (hash-ref (input-type inputs) 'F) F (set))
                  (assert (with-rosette ()
                            (= N.var (* N.var 2)))))))

   (define model
     (solve/allow-exception
      (λ ()
        (compile-smt inputs (hash-ref (input-type inputs) 'F) F (set)))))

   (check-pred sat? model)

   (define N-value (model N.var))
   (check-pred integer? N-value)
   (check-false (or (= N-value (* N-value 2))
                    (= (+ N-value 10) (* N-value 2)))))

  (test-case
   "listof function cond expression invariant"

   (define-input inputs
     [N integer -999]
     [M integer -999]
     [K integer -999]
     [L (list-of (->s integer (list-of (->s integer integer))))
        (make-list
         (λ (_)
           (cond
             [N.var : integer (make-list)]
             [(+ N.var 10) : integer
                           (make-list
                            (λ (_)
                              (cond
                                [M.var : integer [X 0]]
                                [(* M.var 2) : integer [Y 0]])))]
             [(* N.var 2) : integer (make-list)]))
         (λ (_)
           (cond
             [K.var : integer (make-list)]
             [(* K.var 2) : integer (make-list)])))])

   (check-pred unsat?
               (solve/allow-exception
                (λ ()
                  (compile-smt inputs (hash-ref (input-type inputs) 'L) L (set))
                  (assert (with-rosette ()
                            (= (+ N.var 10) (* N.var 2)))))))

   (check-pred unsat?
               (solve/allow-exception
                (λ ()
                  (compile-smt inputs (hash-ref (input-type inputs) 'L) L (set))
                  (assert (with-rosette ()
                            (= N.var (* N.var 2)))))))

   (check-pred unsat?
               (solve/allow-exception
                (λ ()
                  (compile-smt inputs (hash-ref (input-type inputs) 'L) L (set))
                  (assert (with-rosette ()
                            (= M.var (* M.var 2)))))))

   (check-pred unsat?
               (solve/allow-exception
                (λ ()
                  (compile-smt inputs (hash-ref (input-type inputs) 'L) L (set))
                  (assert (with-rosette ()
                            (= K.var (* K.var 2)))))))

   (define model
     (solve/allow-exception
      (λ ()
        (compile-smt inputs (hash-ref (input-type inputs) 'L) L (set)))))

   (check-pred sat? model)

   (define N-value (model N.var))
   (define M-value (model M.var))
   (define K-value (model K.var))

   (check-pred integer? N-value)
   (check-pred integer? M-value)
   (check-pred integer? K-value)

   (check-false (or (= N-value (* N-value 2))
                    (= (+ N-value 10) (* N-value 2))))
   (check-false (= M-value (* M-value 2)))
   (check-false (= K-value (* K-value 2))))

  )

(module* test:one-iteration racket/base
  (require rackunit
           racket/match
           racket/contract/base
           racket/set
           (only-in rosette/safe term?)
           concolic-hop/rosette
           concolic-hop/data
           concolic-hop/store
           concolic-hop/path
           concolic-hop/lib
           "../private/utils.rkt")

  (define input-info-list
    (list (input-info 'X integer)
          (input-info 'Y integer)))
  (define inputs
    (car (all-initial-inputs input-info-list)))

  (test-case
   "solve and run a test with base values"

   (check-equal?
    (list->set (hash-keys (input-map inputs)))
    (set 'X 'Y))

   (check-pred a$X? (hash-ref (input-map inputs) 'X))
   (check-pred a$X? (hash-ref (input-map inputs) 'Y))

   (define new-pending-input
     (pending
      inputs
      (extend-path-constraint
       (empty-path-constraint)
       (branch 'then (with-rosette ()
                       (= (a$X-variable (hash-ref (input-map inputs) 'X))
                          4194967295))))
      (empty-provenance)))

   (define new-inputss
     (solve-for-inputs new-pending-input))

   (check-pred (list/c input?) new-inputss)
   (define new-Y (hash-ref (input-map (car new-inputss)) 'Y))
   (check-pred a$X? new-Y)
   (check-pred
    (and/c (not/c term?) integer?)
    (call-with-model
     (input-model (car new-inputss))
     (λ () (get-current-concrete-value (a$X-variable new-Y)))))

   (check-match
    (run-with-concolic-inputs
     (test-info
      input-info-list
      (match-lambda
        [(list X Y)
         (prop-not-false
          (integer?
           (get-current-concrete-value Y)))]))
     (car new-inputss))
    (struct* test-record ([result 'pass]))))
  )

(module* test:solve racket/base
  (require rackunit
           racket/set
           racket/match
           racket/contract/base
           (only-in rosette/safe unsat? sat?)
           concolic-hop/rosette
           concolic-hop/data
           concolic-hop/store
           concolic-hop/path
           concolic-hop/lib
           concolic-hop/strategy-queue
           (prefix-in cl: concolic-hop/lang)
           "../private/utils.rkt")

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;
  ;;                       constraint solving
  ;;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (test-case
   "statistics of solving"
   (define-input inputs
     [X integer -1])

   (define-concolic-test prop-cubic
     #:inputs
     [Z integer]
     #:prop
     (prop-not-false (if (= (* Z Z Z) 18052977643210691) #t #f)))

   (define instance
     (empty-concolic-instance breadth-first-search-strategy prop-cubic))

   (define-values (inputsss cpu real gc)
     (time-apply
      (λ ()
        (solve-for-inputs (pending
                           inputs
                           (extend-path-constraint
                            (empty-path-constraint)
                            (branch 'then (with-rosette ()
                                            (= (* X.var X.var X.var)
                                               18052977643210691))))
                           (empty-provenance))
                          instance))
      '()))

   (check-pred (list/c (list/c input?)) inputsss)

   (define stats
     (concolic-state-statistics instance))
   (check-equal? (concolic-statistics-solve-count stats) 1)
   (check-pred positive? (concolic-statistics-solve-real-nongc-time stats))
   ;; not super stable test
   (check-pred (<=/c 50) (abs (- (- real gc)
                                 (concolic-statistics-solve-real-nongc-time stats))))
   (log-message (current-logger) 'info 'concolic:test
                (format "solve-for-inputs: ~a ~a ~a" cpu real gc))
   (log-message (current-logger) 'info 'concolic:test
                (format "solve reported: ~a" stats))
   )

  (test-case
   "solving with top-level function cond expression"

   (define-input inputs
     [N integer -999]
     [F (->s integer integer)
        (λ (_)
          (cond
            [N.var : integer [X 0]]
            [(+ N.var 10) : integer [Y 0]]
            [(* N.var 2) : integer [Z 0]]))])

   (check-pred unsat?
               (solve-for-inputs
                (pending inputs
                         (extend-path-constraint
                          (empty-path-constraint)
                          (branch 'then
                                  (with-rosette ()
                                    (= (+ N.var 10) (* N.var 2)))))
                         (empty-provenance))))

   (check-pred unsat?
               (solve-for-inputs
                (pending inputs
                         (extend-path-constraint
                          (empty-path-constraint)
                          (branch 'then (with-rosette ()
                                          (= N.var (* N.var 2)))))
                         (empty-provenance))))

   (define new-inputss
     (solve-for-inputs (pending inputs
                                (extend-path-constraint
                                 (empty-path-constraint)
                                 (branch 'else (with-rosette ()
                                                 (= N.var 123456))))
                                (empty-provenance))))

   (check-pred (list/c input?) new-inputss)

   (define N-value ((input-model (car new-inputss)) N.var))
   (check-pred integer? N-value)
   (check-false (or (= N-value (* N-value 2))
                    (= (+ N-value 10) (* N-value 2)))))

  (test-case
   "solving with cond expression with #f dispatch"

   (define-input inputs
     [N integer 0]
     [F (->s integer integer)
        (λ (_)
          (cond
            @ lbl0
            [(+ N.var 10) : integer [Y 0]]
            [(* N.var 2) : integer [Z 0]] @ lbl-N*2))])

   (define new-inputss
     (solve-for-inputs (pending inputs
                                (extend-path-constraint
                                 (empty-path-constraint)
                                 (dispatch lbl0
                                           #f
                                           'integer
                                           N.var))
                                (empty-provenance))))

   (check-pred (list/c input?) new-inputss)

   (define N-value ((input-model (car new-inputss)) N.var))
   (check-pred integer? N-value)
   (check-false (or (= N-value (* N-value 2))
                    (= (+ N-value 10) (* N-value 2)))))

  (test-case
   "solving with cond expression with non-#f dispatch"

   (define-input inputs
     [N integer 0]
     [F (->s integer integer)
        (λ (_)
          (cond
            @ lbl0
            [N.var : integer [X 0]]
            [(+ N.var 10) : integer [Y 0]] @ lbl-N+10))])

   (define new-inputss
     (solve-for-inputs (pending inputs
                                (extend-path-constraint
                                 (empty-path-constraint)
                                 (dispatch lbl0
                                           lbl-N+10
                                           'integer
                                           (with-rosette () (* N.var 2))))
                                (empty-provenance))))

   (check-pred (list/c input?) new-inputss)

   (define N-value ((input-model (car new-inputss)) N.var))
   (check-pred integer? N-value)
   (check-false (= N-value (* N-value 2)))
   (check-equal? (+ N-value 10) (* N-value 2)))

  (test-case
   "solving with listof functions"

   (define-input inputs
     [N integer -999]
     [M integer -999]
     [K integer -999]
     [L (list-of (->s integer (list-of (->s integer integer))))
        (make-list
         (λ (_)
           (cond
             [N.var : integer (make-list)]
             [(+ N.var 10) : integer
                           (make-list
                            (λ (_)
                              (cond
                                [M.var : integer [X 0]]
                                [(* M.var 2) : integer [Y 0]])))]
             [(* N.var 2) : integer (make-list)]))
         (λ (_)
           (cond
             [K.var : integer (make-list)]
             [(* K.var 2) : integer (make-list)])))])

   (check-pred unsat?
               (solve-for-inputs
                (pending inputs
                         (extend-path-constraint
                          (empty-path-constraint)
                          (branch 'then (with-rosette ()
                                          (= (+ N.var 10) (* N.var 2)))))
                         (empty-provenance))))

   (check-pred unsat?
               (solve-for-inputs
                (pending inputs
                         (extend-path-constraint
                          (empty-path-constraint)
                          (branch 'then (with-rosette ()
                                          (= N.var (* N.var 2)))))
                         (empty-provenance))))

   (check-pred unsat?
               (solve-for-inputs
                (pending inputs
                         (extend-path-constraint
                          (empty-path-constraint)
                          (branch 'then (with-rosette ()
                                          (= M.var (* M.var 2)))))
                         (empty-provenance))))

   (check-pred unsat?
               (solve-for-inputs
                (pending inputs
                         (extend-path-constraint
                          (empty-path-constraint)
                          (branch 'then (with-rosette ()
                                          (= K.var (* K.var 2)))))
                         (empty-provenance))))

   (define new-inputss
     (solve-for-inputs (pending inputs
                                (extend-path-constraint
                                 (empty-path-constraint)
                                 (branch 'else (with-rosette ()
                                                 (= N.var 456))))
                                (empty-provenance))))

   (check-pred (list/c input?) new-inputss)

   (define N-value ((input-model (car new-inputss)) N.var))
   (define M-value ((input-model (car new-inputss)) M.var))
   (define K-value ((input-model (car new-inputss)) K.var))

   (check-pred integer? N-value)
   (check-pred integer? M-value)
   (check-pred integer? K-value)

   (check-false (or (= N-value (* N-value 2))
                    (= (+ N-value 10) (* N-value 2))))
   (check-false (= M-value (* M-value 2)))
   (check-false (= K-value (* K-value 2))))

  (test-case
   "a$%app type test for compile-smt%"

   (define-input inputs
     [F (->s (->s (or/s integer
                        (list/s)
                        (list/s boolean integer (list-of (->s integer integer)))
                        (list/s integer boolean))
                  boolean)
             integer)
        (λ (_)
          (cond
            [a$proc : (->s (or/s integer
                                 (list/s)
                                 (list/s boolean integer (list-of (->s integer integer)))
                                 (list/s integer boolean))
                           boolean)
                    (let ([_ (0 (: (make-list [B #t] [N 123] (make-list))
                                   (list/s boolean integer
                                           (list-of (->s integer integer)))))])
                      (cond
                        [(! B.var) : boolean
                                   [X -1]]))]))])

   (check-pred
    sat?
    (solve/allow-exception
     (λ () (compile-smt inputs (hash-ref (input-type inputs) 'F) F (set))))))

  (test-case
   "list-c type test: no extension or truncation possible"

   (define-input inputs
     [L (list/s integer integer)
        (make-list #:unless [B1 #f]
                   [X1 1]
                   #:unless [B2 #f]
                   [X2 5]
                   #:unless [B3 #t])])

   (check-pred
    unsat?
    (solve-for-inputs (pending inputs
                               (extend-path-constraint
                                (extend-path-constraint
                                 (empty-path-constraint)
                                 (branch 'then (with-rosette (! &&)
                                                 (! B1.var))))
                                (branch 'else (with-rosette (! &&)
                                                (&& (! B1.var) (! B2.var)))))
                               (empty-provenance))))

   (check-pred
    unsat?
    (solve-for-inputs (pending inputs
                               (extend-path-constraint
                                (extend-path-constraint
                                 (extend-path-constraint
                                  (empty-path-constraint)
                                  (branch 'then (with-rosette (! &&)
                                                  (! B1.var))))
                                 (branch 'then (with-rosette (! &&)
                                                 (&& (! B1.var) (! B2.var)))))
                                (branch 'then  (with-rosette (! &&)
                                                 (&& (! B1.var) (! B2.var)
                                                     (! B3.var)))))
                               (empty-provenance))))

   (check-pred
    (list/c input?)
    (solve-for-inputs (pending inputs
                               (extend-path-constraint
                                (extend-path-constraint
                                 (extend-path-constraint
                                  (empty-path-constraint)
                                  (branch 'then (with-rosette (! &&)
                                                  (! B1.var))))
                                 (branch 'then (with-rosette (! &&)
                                                 (&& (! B1.var) (! B2.var)))))
                                (branch 'else  (with-rosette (! &&)
                                                 (&& (! B1.var) (! B2.var)
                                                     (! B3.var)))))
                               (empty-provenance)))))

  (test-case
   "list truncation is not allowed"

   (define-input inputs
     [L (list-of integer)
        (make-list #:unless [B1 #f]
                   [X1 1]
                   #:unless [B2 #f]
                   [X2 2]
                   #:unless [B3 #f]
                   [X3 3]
                   #:unless [B4 #t])])

   (define no-sol
     (solve-for-inputs (pending inputs
                                (extend-path-constraint
                                 (extend-path-constraint
                                  (empty-path-constraint)
                                  (branch 'else
                                          (with-rosette ()
                                            B1.var)))
                                 (branch 'then
                                         (with-rosette (&& !)
                                           (&& (! B1.var) B2.var))))
                                (empty-provenance))))

   (check-pred unsat? no-sol))

  (test-case
   "list extension with a single expansion value"

   (define-input inputs
     [L (list-of integer)
        (make-list #:unless [B1 #f]
                   [X1 1]
                   #:unless [B2 #f]
                   [X2 2]
                   #:unless [B3 #f]
                   [X3 3]
                   #:unless [B4 #t])])

   (check-equal?
    (call-with-model
     (input-model inputs)
     (λ ()
       (get-current-concrete-value
        (cl:length
         (interpret inputs
                    (hash-ref (input-type inputs) 'L)
                    L)))))
    3)

   (define new-inputss
     (solve-for-inputs (pending inputs
                                (extend-path-constraint
                                 (extend-path-constraint
                                  (empty-path-constraint)
                                  (branch 'then
                                          (with-rosette (&& !)
                                            (&& (! B1.var)
                                                (! B2.var)
                                                (! B3.var)
                                                (! B4.var)))))
                                 (list-access #f B4.var))
                                (empty-provenance))))

   (check-pred (list/c input?) new-inputss)

   (define new-L
     (hash-ref (input-map (car new-inputss)) 'L))

   (check-match
    new-L
    (a$cons (== B1) (== X1)
            (a$cons (== B2) (== X2)
                    (a$cons (== B3) (== X3)
                            (a$cons (== B4)
                                    (a$X _ (== integer))
                                    (a$empty (a$X _ (== boolean))))))))

   (check-pred
    (list/c integer? integer? integer? integer?)
    (call-with-model
     (input-model (car new-inputss))
     (λ ()
       (get-current-concrete-value
        (interpret (car new-inputss)
                   (hash-ref (input-type (car new-inputss)) 'L)
                   new-L)))))
   )

  (test-case
   "list extension with multiple expansion values"

   (define-input inputs
     [L (list-of (or/s integer boolean (->s integer integer)))
        (make-list #:unless [B1 #f]
                   [X1 1]
                   #:unless [B2 #f]
                   [X2 #t]
                   #:unless [B3 #f])])

   (define new-inputss
     (solve-for-inputs (pending inputs
                                (extend-path-constraint
                                 (extend-path-constraint
                                  (empty-path-constraint)
                                  (branch 'then
                                          (with-rosette (&& !)
                                            (&& (! B1.var)
                                                (! B2.var)
                                                (! B3.var)))))
                                 (list-access #f B3.var))
                                (empty-provenance))))

   (check-pred (list/c input? input? input?) new-inputss)

   (define vals-at-2
     (for/list ([new-inputs (in-list new-inputss)])
       (define new-L
         (hash-ref (input-map new-inputs) 'L))

       (check-match
        new-L
        (a$cons (== B1) (== X1)
                (a$cons (== B2) (== X2)
                        (a$cons (== B3)
                                _
                                (a$empty (a$X _ (== boolean)))))))

       (list-ref
        (call-with-model
         (input-model new-inputs)
         (λ ()
           (get-current-concrete-value
            (interpret new-inputs
                       (hash-ref (input-type new-inputs) 'L)
                       new-L))))
        2)))

   (check-match
    vals-at-2
    (list-no-order (? integer?) (? boolean?) (? procedure?)))
   )

  (test-case
   "list extension handles nesting"

   (define-input inputs
     [L (list-of (or/s integer
                       (->s integer (list-of (or/s boolean
                                                   (->s integer integer))))))
        (make-list
         #:unless [B1 #f]
         (λ (_)
           (cond
             [0 : integer (make-list #:unless [B #t])]))
         #:unless [B2 #t])])

   (define new-inputss
     (solve-for-inputs (pending inputs
                                (extend-path-constraint
                                 (extend-path-constraint
                                  (extend-path-constraint
                                   (empty-path-constraint)
                                   (list-access #f B1.var))
                                  (branch 'then
                                          (with-rosette (&& !)
                                            (&& (! B1.var) B2.var))))
                                 (list-access #f B.var))
                                (empty-provenance))))

   (check-pred (list/c input? input?) new-inputss)
   (check-match
    (map (λ (inputs)
           (hash-ref (input-map inputs) 'L))
         new-inputss)
    (list-no-order
     (a$cons (== B1)
             (a$λ
              (struct* a$conds
                       ([table
                         (list
                          (struct* a$clause
                                   ([key 0]
                                    [body
                                     (a$cons (== B)
                                             (a$X _ (== boolean))
                                             (a$empty (a$X _ (== boolean))))])))])))
             (a$empty (== B2)))
     (a$cons (== B1)
             (a$λ
              (struct* a$conds
                       ([table
                         (list
                          (struct* a$clause
                                   ([key 0]
                                    [body
                                     (a$cons (== B)
                                             (struct a$λ _)
                                             (a$empty (a$X _ (== boolean))))])))])))
             (a$empty (== B2))))))

  (test-case
   "list extension incorporates local binding: local variable with base types"

   (define-input inputs
     [F (->s integer (list-of integer))
        (λ (_)
          (cond
            [0 : integer
               (make-list #:unless [B #t])]))])

   (define new-inputss
     (solve-for-inputs (pending inputs
                                (extend-path-constraint
                                 (empty-path-constraint)
                                 (list-access #f B.var))
                                (empty-provenance))))

   (check-pred (list/c input? input?) new-inputss)
   (check-match
    (map (λ (inputs)
           (hash-ref (input-map inputs) 'F))
         new-inputss)
    (list-no-order
     (a$λ
      (struct* a$conds
               ([table
                 (list
                  (struct* a$clause
                           ([key 0]
                            [body
                             (a$cons (== B)
                                     (a$X _ (== integer))
                                     (a$empty _))])))])))
     (a$λ
      (struct* a$conds
               ([table
                 (list
                  (struct* a$clause
                           ([key 0]
                            [body
                             (a$cons (== B)
                                     (a$x 0)
                                     (a$empty _))])))]))))))

  (test-case
   "list extension incorporates local binding: local variable with function types"

   (define-input inputs
     [F (->s (->s integer integer)
             (list-of (->s integer integer)))
        (λ (_)
          (cond
            [a$proc : (->s integer integer)
                    (make-list #:unless [B #t])]))])

   (define new-inputss
     (solve-for-inputs (pending inputs
                                (extend-path-constraint
                                 (empty-path-constraint)
                                 (list-access #f B.var))
                                (empty-provenance))))

   (check-pred (list/c input? input?) new-inputss)
   (check-match
    (map (λ (inputs)
           (hash-ref (input-map inputs) 'F))
         new-inputss)
    (list-no-order
     (a$λ
      (struct* a$conds
               ([table
                 (list
                  (struct* a$clause
                           ([key (? a$proc?)]
                            [body
                             (a$cons (== B)
                                     (struct a$λ _)
                                     (a$empty _))])))])))
     (a$λ
      (struct* a$conds
               ([table
                 (list
                  (struct* a$clause
                           ([key (? a$proc?)]
                            [body
                             (a$cons (== B)
                                     (a$x 0)
                                     (a$empty _))])))]))))))
  )

(module+ test
  (require (submod "../private/utils.rkt" config-output-port))

  (require (submod ".." test:compile-smt)
           (submod ".." test:one-iteration)
           (submod ".." test:solve))

  (reset-output-port!)
  )
