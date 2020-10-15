#lang racket/base

(require (submod concolic-hop/lib internals))

(define ((input-map-ref name) inputs)
  (hash-ref (input-map inputs) name))

(define (call-with-progress-server action)
  (match-define (list result)
    (call-with-server
     0
     action))
  result)

(module* test:adjacent #f
  (require rackunit
           racket/match
           racket/pretty
           racket/set
           concolic-hop/data
           concolic-hop/lib
           concolic-hop/path
           concolic-hop/state-passing
           concolic-hop/rosette
           "../private/utils.rkt"
           )

  (concolic-test-enable-provenance? #f)

  (test-case
   "adjacent branches"

   (define-input inputs
     [X integer 1])

   (check-equal?
    (call-with-server
     #f
     (λ (server)
       (adjacent-branches
        server
        0
        (pending inputs (empty-path-constraint) (empty-provenance))
        (branch 'else (with-rosette () (> X.var 5)))
        (extend-path-constraint
         (empty-path-constraint)
         (branch 'then (with-rosette () (not (= (* X.var 2) 6))))))))
    (list
     (pending inputs
              (extend-path-constraint
               (extend-path-constraint
                (empty-path-constraint)
                (branch 'then (with-rosette () (not (= (* X.var 2) 6)))))
               (branch 'then (with-rosette () (> X.var 5))))
              (empty-provenance))))

   (check-equal?
    (call-with-server
     #f
     (λ (server)
       (adjacent-branches
        server
        0
        (pending inputs (empty-path-constraint) (empty-provenance))
        (branch 'then (with-rosette () (> X.var 5)))
        (extend-path-constraint
         (empty-path-constraint)
         (branch 'else (with-rosette () (not (= (* X.var 2) 6))))))))
    (list
     (pending inputs
              (extend-path-constraint
               (extend-path-constraint
                (empty-path-constraint)
                (branch 'else (with-rosette () (not (= (* X.var 2) 6)))))
               (branch 'else (with-rosette () (> X.var 5))))
              (empty-provenance))))
   )

  (test-case
   "adjacent dispatches with base values: existing clause"
   (define-input inputs
     [X integer 1]
     [F (->s integer boolean)
        (λ (_)
          (cond
            @ lbl0
            [X.var : integer       [B1 #t]] @ lbl1
            [(+ 1 X.var) : integer [B2 #f]] @ lbl2))])
   (define pending-input
     (pending inputs (empty-path-constraint) (empty-provenance)))

   (define remaining-path-constraint-0
     (extend-path-constraint
      (empty-path-constraint)
      (branch 'else (with-rosette () (= X.var 123456)))))

   (define 1+X
     (with-rosette ()
       (+ 1 X.var)))

   (define 2X
     (with-rosette ()
       (* 2 X.var)))

   ;; The [M-Change] rule is not applicable because
   ;; (dispatch lbl0 lbl2 'integer 1+X) must be the very
   ;; path condition that caused the lbl2 clause to be
   ;; inserted in the conditional expression lbl0.
   ;;
   ;; Only [M-New] fires.
   (check-match
    (call-with-progress-server
     (λ (progress-count-server)
       (call-with-server
        #f
        (λ (server)
          (adjacent-dispatch-targets server progress-count-server 0
                                     pending-input
                                     (dispatch lbl0 lbl2 'integer 1+X)
                                     remaining-path-constraint-0)))))
    (list-no-order
     (struct*
      pending
      ([prediction (extend-path-constraint
                    (== remaining-path-constraint-0)
                    (dispatch (== lbl0)
                              (and (? label?) (not (== lbl1)) (not (== lbl2)))
                              'integer
                              (== 1+X)))]
       [partial-inputs
        (app
         (input-map-ref 'F)
         (a$λ
          (struct*
           a$conds
           ([label (== lbl0)]
            [table
             (list
              (struct* a$clause ([label (== lbl1)]))
              (struct* a$clause ([label (== lbl2)]))
              (struct* a$clause
                       ([label (? label?)]
                        [type (== integer)]
                        [key (== 1+X)]
                        [body (a$X _ (== boolean))])))]))))]))))

   (define remaining-path-constraint-1
     (extend-path-constraint
      remaining-path-constraint-0
      (dispatch lbl0 lbl2 'integer 1+X)))

   (define adjacent-dispatches
     (call-with-progress-server
      (λ (progress-count-server)
        (call-with-server
         #f
         (λ (server)
           (adjacent-dispatch-targets server progress-count-server 0
                                      pending-input
                                      (dispatch lbl0 lbl2 'integer 2X)
                                      remaining-path-constraint-1))))))

   (check-match
    adjacent-dispatches
    (list-no-order
     (struct* pending ([partial-inputs (== inputs)]
                       [prediction
                        (extend-path-constraint
                         (== remaining-path-constraint-1)
                         (dispatch (== lbl0) (== lbl1) 'integer (== 2X)))]))
     (struct*
      pending
      ([prediction (extend-path-constraint
                    (== remaining-path-constraint-1)
                    (dispatch (== lbl0)
                              (and (? label?) (not (== lbl1)) (not (== lbl2)))
                              'integer
                              (== 2X)))]
       [partial-inputs
        (app
         (input-map-ref 'F)
         (a$λ
          (struct*
           a$conds
           ([label (== lbl0)]
            [table
             (list
              (struct* a$clause ([label (== lbl1)]))
              (struct* a$clause ([label (== lbl2)]))
              (struct* a$clause
                       ([label (? label?)]
                        [type (== integer)]
                        [key (== 2X)]
                        [body (a$X _ (== boolean))])))]))))])))))

  (test-case
   "adjacent dispatches with base values: else"

   (define-input inputs
     [X integer 1]
     [F (->s integer integer)
        (λ (_)
          (cond
            @ lbl0
            [X.var : integer       [Z1 3]] @ lbl1
            [(+ 1 X.var) : integer [Z2 7]] @ lbl2))])
   (define pending-inputs
     (pending inputs (empty-path-constraint) (empty-provenance)))

   (define remaining-path-constraints
     (extend-path-constraint
      (empty-path-constraint)
      (branch 'else (with-rosette () (= X.var 123456)))))

   (define X*3
     (with-rosette ()
       (* X.var 3)))

   (define adjacent-dispatches
     (call-with-progress-server
      (λ (progress-count-server)
        (call-with-server
         #f
         (λ (server)
           (adjacent-dispatch-targets server progress-count-server 0
                                      pending-inputs
                                      (dispatch lbl0 #f 'integer X*3)
                                      remaining-path-constraints))))))

   (check-match
    adjacent-dispatches
    (list-no-order
     ;; picking an existing clause
     (struct* pending
              ([prediction
                (extend-path-constraint
                 (== remaining-path-constraints)
                 (dispatch (== lbl0) (== lbl1) 'integer (== X*3)))]
               [partial-inputs (== inputs)]))
     ;; picking an existing clause
     (struct* pending
              ([prediction
                (extend-path-constraint
                 (== remaining-path-constraints)
                 (dispatch (== lbl0) (== lbl2) 'integer (== X*3)))]
               [partial-inputs (== inputs)]))
     ;; insert new clause: a$exprs = local variable (a$x 0)
     (struct* pending
              ([prediction
                (extend-path-constraint
                 (== remaining-path-constraints)
                 (dispatch (== lbl0)
                           (and (? label?)
                                (not (== lbl1))
                                (not (== lbl2)))
                           'integer (== X*3)))]
               [partial-inputs
                (app
                 (input-map-ref 'F)
                 (a$λ
                  (struct* a$conds
                           ([table
                             (list
                              (struct* a$clause ([key
                                                  (== X.var)]))
                              (struct* a$clause ([key
                                                  (== (with-rosette ()
                                                        (+ 1 X.var)))]))
                              (struct* a$clause ([key (== X*3)]
                                                 [body
                                                  (a$x 0)])))]))))]))
     ;; insert new clause: a$exprs = new global variable (a$X _ integer)
     (struct* pending
              ([prediction
                (extend-path-constraint
                 (== remaining-path-constraints)
                 (dispatch (== lbl0)
                           (and (? label?)
                                (not (== lbl1))
                                (not (== lbl2)))
                           'integer
                           (== X*3)))]
               [partial-inputs
                (app
                 (input-map-ref 'F)
                 (a$λ
                  (struct* a$conds
                           ([table
                             (list
                              (struct* a$clause
                                       ([key (== X.var)]))
                              (struct* a$clause
                                       ([key (== (with-rosette ()
                                                   (+ 1 X.var)))]))
                              (struct* a$clause
                                       ([key (== X*3)]
                                        [body
                                         (a$X _ (== integer))])))]))))])))))

  (test-case
   "adjacent dispatches with functions"

   (define-input inputs
     [F (->s (->s integer boolean) integer)
        (λ (_) (cond @ lbl0))]
     [G (->s (->s integer boolean) integer)
        (λ (_) (cond
                 @ lbl1
                 [a$proc : (->s integer boolean) [X -1]] @ lbl2))])
   (define pending-inputs
     (pending inputs (empty-path-constraint) (empty-provenance)))

   (define (_>3 n)
     (with-rosette ()
       (> n 3)))

   (check-equal?
    (call-with-progress-server
     (λ (progress-count-server)
       (call-with-server
        #f
        (λ (server)
          (adjacent-dispatch-targets server progress-count-server 0
                                     pending-inputs
                                     (dispatch lbl1 lbl2 'arrow _>3)
                                     (empty-path-constraint))))))
    '())

   (define adjacent-dispatches
     (call-with-progress-server
      (λ (progress-count-server)
        (call-with-server
         #f
         (λ (server)
           (adjacent-dispatch-targets server progress-count-server 0
                                      pending-inputs
                                      (dispatch lbl0 #f 'arrow _>3)
                                      (empty-path-constraint)))))))

   (check-match
    adjacent-dispatches
    (list-no-order
     (struct*
      pending
      ([prediction
        (extend-path-constraint
         (empty-path-constraint)
         (dispatch (== lbl0) (? label?) 'arrow (== _>3)))]
       [partial-inputs
        (app
         (input-map-ref 'F)
         (a$λ
          (struct* a$conds
                   ([table
                     (list
                      (struct* a$clause
                               ([key (== a$proc)]
                                [body (a$X _ (== integer))])))]))))]))
     (struct*
      pending
      ([prediction
        (extend-path-constraint
         (empty-path-constraint)
         (dispatch (== lbl0) (? label?) 'arrow (== _>3)))]
       [partial-inputs
        (app
         (input-map-ref 'F)
         (a$λ
          (struct* a$conds
                   ([table
                     (list
                      (struct* a$clause
                               ([key (== a$proc)]
                                [body
                                 (a$let
                                  (a$%app (a$x 0) (a$X _ (== integer)))
                                  (struct* a$conds ([table '()])))])))]))))])))))

  (test-case
   "adjacent dispatches with lists"

   (define-input inputs
     [L1 (list-of integer) (make-list)]
     [L2 (list-of integer) (make-list [N 123] [M 456])]
     [F (->s (list-of integer) boolean)
        (λ (_) (cond @ lbl0))]
     [G (->s (list-of integer) boolean)
        (λ (_)
          (cond
            @ lbl1
            [a$pair : (list-of integer) [X #f]] @ lbl2))]
     [H (->s (list-of integer) boolean)
        (λ (_)
          (cond
            @ lbl3
            [a$null : (list-of integer) [Y #f]] @ lbl4))]
     [J (->s (list-of integer) boolean)
        (λ (_)
          (cond
            @ lbl5
            [a$pair : (list-of integer) [Z #f]] @ lbl6
            [a$null : (list-of integer) [W #f]] @ lbl7))])
   (define pending-inputs
     (pending inputs (empty-path-constraint) (empty-provenance)))

   (define-values (concolic-list:null concolic-list:pair)
     (call-with-model
      (input-model inputs)
      (λ ()
        (values
         (interpret inputs
                    (hash-ref (input-type inputs) 'L1)
                    L1)
         (interpret inputs
                    (hash-ref (input-type inputs) 'L2)
                    L2)))))

   (define remaining-path-constraint-0
     (extend-path-constraint
      (empty-path-constraint)
      (dispatch lbl5 lbl7 'list '())))

   ;; Only [M-Change]
   (check-match
    (call-with-progress-server
     (λ (progress-count-server)
       (call-with-server
        #f
        (λ (server)
          (adjacent-dispatch-targets server progress-count-server 0
                                     pending-inputs
                                     (dispatch lbl5 lbl7 'list concolic-list:null)
                                     remaining-path-constraint-0)))))
    (list
     (struct*
      pending
      ([partial-inputs (== inputs)]
       [prediction
        (extend-path-constraint
         (== remaining-path-constraint-0)
         (dispatch (== lbl5) (== lbl6) 'list (== concolic-list:null)))]))))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (define remaining-path-constraint-1
     (extend-path-constraint
      (empty-path-constraint)
      (dispatch lbl1 lbl2 'list (list 0))))

   ;; Only [M-New] with a$null key
   (check-match
    (call-with-progress-server
     (λ (progress-count-server)
       (call-with-server
        #f
        (λ (server)
          (adjacent-dispatch-targets server progress-count-server 0
                                     pending-inputs
                                     (dispatch lbl1 lbl2 'list concolic-list:pair)
                                     remaining-path-constraint-1)))))
    (list
     (struct*
      pending
      ([prediction
        (extend-path-constraint
         (== remaining-path-constraint-1)
         (dispatch (== lbl1) (not (== lbl2)) 'list (== concolic-list:pair)))]
       [partial-inputs
        (app
         (input-map-ref 'G)
         (a$λ
          (struct* a$conds
                   ([table
                     (list
                      (struct* a$clause ([label (== lbl2)]))
                      (struct* a$clause ([label (not (== lbl2))]
                                         [type (== (list-of integer))]
                                         [key (== a$null)]
                                         [body (a$X _ (== boolean))])))]))))]))))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (define remaining-path-constraint-2
     (extend-path-constraint
      (empty-path-constraint)
      (dispatch lbl3 lbl4 'list '())))

   ;; Only [M-New] with a$proc key
   ;; there are three new pending nodes because once we assert
   ;; that the input list is a pair?, we enabled the use
   ;; of let _ = (car the-new-var) etc.
   (check-match
    (call-with-progress-server
     (λ (progress-count-server)
       (call-with-server
        #f
        (λ (server)
          (adjacent-dispatch-targets server progress-count-server 0
                                     pending-inputs
                                     (dispatch lbl3 lbl4 'list concolic-list:null)
                                     remaining-path-constraint-2)))))
    (list-no-order
     (struct*
      pending
      ([prediction
        (extend-path-constraint
         (== remaining-path-constraint-2)
         (dispatch (== lbl3) (not (== lbl4)) 'list (== concolic-list:null)))]
       [partial-inputs
        (app
         (input-map-ref 'H)
         (a$λ
          (struct* a$conds
                   ([table
                     (list
                      (struct* a$clause ([label (== lbl4)]))
                      (struct* a$clause ([label (not (== lbl4))]
                                         [type (== (list-of integer))]
                                         [key (== a$pair)]
                                         [body (a$X _ (== boolean))])))]))))]))
     (struct*
      pending
      ([prediction
        (extend-path-constraint
         (== remaining-path-constraint-2)
         (dispatch (== lbl3) (not (== lbl4)) 'list (== concolic-list:null)))]
       [partial-inputs
        (app
         (input-map-ref 'H)
         (a$λ
          (struct* a$conds
                   ([table
                     (list
                      (struct* a$clause ([label (== lbl4)]))
                      (struct* a$clause
                               ([label (not (== lbl4))]
                                [type (== (list-of integer))]
                                [key (== a$pair)]
                                [body
                                 (a$let
                                  (a$car (a$x 0))
                                  (struct* a$conds ([table '()])))])))]))))]))
     (struct*
      pending
      ([prediction
        (extend-path-constraint
         (== remaining-path-constraint-2)
         (dispatch (== lbl3) (not (== lbl4)) 'list (== concolic-list:null)))]
       [partial-inputs
        (app
         (input-map-ref 'H)
         (a$λ
          (struct* a$conds
                   ([table
                     (list
                      (struct* a$clause ([label (== lbl4)]))
                      (struct* a$clause
                               ([label (not (== lbl4))]
                                [type (== (list-of integer))]
                                [key (== a$pair)]
                                [body
                                 (a$let
                                  (a$cdr (a$x 0))
                                  (struct* a$conds ([table '()])))])))]))))]))))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (define remaining-path-constraint-3
     (extend-path-constraint
      (empty-path-constraint)
      (dispatch lbl3 lbl4 'list concolic-list:null)))

   ;; In addition to the [M-New] rule, [M-Change] is
   ;; also applicable because it was not already taken.
   (check-match
    (call-with-progress-server
     (λ (progress-count-server)
       (call-with-server
        #f
        (λ (server)
          (adjacent-dispatch-targets server progress-count-server 0
                                     pending-inputs
                                     (dispatch lbl3 #f 'list concolic-list:pair)
                                     remaining-path-constraint-3)))))
    ;; new! -- via [M-Change]
    (list-no-order
     (struct* pending
              ([partial-inputs (== inputs)]
               [prediction
                (extend-path-constraint
                 (== remaining-path-constraint-3)
                 (dispatch (== lbl3) (== lbl4) 'list (== concolic-list:pair)))]))
     ;; same as the previous test
     (struct*
      pending
      ([prediction
        (extend-path-constraint
         (== remaining-path-constraint-3)
         (dispatch (== lbl3) (not (== lbl4)) 'list (== concolic-list:pair)))]
       [partial-inputs
        (app
         (input-map-ref 'H)
         (a$λ
          (struct* a$conds
                   ([table
                     (list
                      (struct* a$clause ([label (== lbl4)]))
                      (struct* a$clause ([label (not (== lbl4))]
                                         [type (== (list-of integer))]
                                         [key (== a$pair)]
                                         [body (a$X _ (== boolean))])))]))))]))
     (struct*
      pending
      ([prediction
        (extend-path-constraint
         (== remaining-path-constraint-3)
         (dispatch (== lbl3) (not (== lbl4)) 'list (== concolic-list:pair)))]
       [partial-inputs
        (app
         (input-map-ref 'H)
         (a$λ
          (struct* a$conds
                   ([table
                     (list
                      (struct* a$clause ([label (== lbl4)]))
                      (struct* a$clause
                               ([label (not (== lbl4))]
                                [type (== (list-of integer))]
                                [key (== a$pair)]
                                [body
                                 (a$let
                                  (a$car (a$x 0))
                                  (struct* a$conds ([table '()])))])))]))))]))
     (struct*
      pending
      ([prediction
        (extend-path-constraint
         (== remaining-path-constraint-3)
         (dispatch (== lbl3) (not (== lbl4)) 'list (== concolic-list:pair)))]
       [partial-inputs
        (app
         (input-map-ref 'H)
         (a$λ
          (struct* a$conds
                   ([table
                     (list
                      (struct* a$clause ([label (== lbl4)]))
                      (struct* a$clause
                               ([label (not (== lbl4))]
                                [type (== (list-of integer))]
                                [key (== a$pair)]
                                [body
                                 (a$let
                                  (a$cdr (a$x 0))
                                  (struct* a$conds ([table '()])))])))]))))]))))

   (check-match
    (call-with-progress-server
     (λ (progress-count-server)
       (call-with-server
        #f
        (λ (server)
          (adjacent-dispatch-targets server progress-count-server 0
                                     pending-inputs
                                     (dispatch lbl0 #f 'list concolic-list:null)
                                     (empty-path-constraint))))))
    (list
     (struct*
      pending
      ([prediction (extend-path-constraint
                    (empty-path-constraint)
                    (dispatch lbl0 (? label?) 'list (== concolic-list:null)))]
       [partial-inputs
        (app
         (input-map-ref 'F)
         (a$λ
          (struct* a$conds
                   ([table
                     (list
                      (struct* a$clause
                               ([key (== a$null)]
                                [type (== (list-of integer))]
                                [body (a$X _ (== boolean))])))]))))]))))

   (check-match
    (call-with-progress-server
     (λ (progress-count-server)
       (call-with-server
        #f
        (λ (server)
          (adjacent-dispatch-targets server progress-count-server 0
                                     pending-inputs
                                     (dispatch lbl0 #f 'list concolic-list:pair)
                                     (empty-path-constraint))))))
    (list-no-order
     (struct*
      pending
      ([prediction
        (extend-path-constraint
         (empty-path-constraint)
         (dispatch (== lbl0) (? label?) 'list (== concolic-list:pair)))]
       [partial-inputs
        (app
         (input-map-ref 'F)
         (a$λ
          (struct* a$conds
                   ([table
                     (list
                      (struct* a$clause ([label (? label?)]
                                         [type (== (list-of integer))]
                                         [key (== a$pair)]
                                         [body (a$X _ (== boolean))])))]))))]))
     (struct*
      pending
      ([prediction
        (extend-path-constraint
         (empty-path-constraint)
         (dispatch (== lbl0) (? label?) 'list (== concolic-list:pair)))]
       [partial-inputs
        (app
         (input-map-ref 'F)
         (a$λ
          (struct* a$conds
                   ([table
                     (list
                      (struct* a$clause
                               ([label (? label?)]
                                [type (== (list-of integer))]
                                [key (== a$pair)]
                                [body
                                 (a$let
                                  (a$car (a$x 0))
                                  (struct* a$conds ([table '()])))])))]))))]))
     (struct*
      pending
      ([prediction
        (extend-path-constraint
         (empty-path-constraint)
         (dispatch (== lbl0) (? label?) 'list (== concolic-list:pair)))]
       [partial-inputs
        (app
         (input-map-ref 'F)
         (a$λ
          (struct* a$conds
                   ([table
                     (list
                      (struct* a$clause
                               ([label (? label?)]
                                [type (== (list-of integer))]
                                [key (== a$pair)]
                                [body
                                 (a$let
                                  (a$cdr (a$x 0))
                                  (struct* a$conds ([table '()])))])))]))))]))))
   )

  (test-case
   "adjacent dispatches: local variables"

   (define-input inputs
     [F (->s (->s integer (list-of boolean))
             (->s (->s (list-of boolean) integer)
                  boolean))
        (λ (_)
          (cond
            @ lbl0
            [a$proc
             : (->s integer (list-of boolean))
             (let ([_ (0 [X 3])])
               (cond
                 @ lbl1
                 [a$pair
                  : (list-of boolean)
                  (λ (_)
                    (cond
                      @ lbl2
                      [a$proc : (->s (list-of boolean) integer)
                              (let ([_ (car 1)])
                                (cond @ lbl3))] @ lbl2-0))] @ lbl1-0))] @ lbl0-0))])
   (define pending-inputs
     (pending inputs (empty-path-constraint) (empty-provenance)))

   ;; try matching the original input to check for any typos in the pattern
   (check-match
    inputs
    (app
     (input-map-ref 'F)
     (a$λ
      (struct*
       a$conds
       ([table
         (list
          (struct*
           a$clause
           ([key (== a$proc)]
            [body
             (a$let
              (a$%app (a$x 0) (a$X _ (== integer)))
              (struct*
               a$conds
               ([table
                 (list
                  (struct*
                   a$clause
                   ([key (== a$pair)]
                    [body
                     (a$λ
                      (struct*
                       a$conds
                       ([table
                         (list
                          (struct*
                           a$clause
                           ([key (== a$proc)]
                            [body
                             (a$let
                              (a$car (a$x 1))
                              (struct*
                               a$conds
                               ([table
                                 '()])))])))])))])))])))])))])))))

   (define adjacent-dispatches
     (call-with-progress-server
      (λ (progress-count-server)
        (call-with-server
         #f
         (λ (server)
           (adjacent-dispatch-targets server progress-count-server 0
                                      pending-inputs
                                      (dispatch lbl3 #f 'boolean #t)
                                      (empty-path-constraint)))))))

   ;; the output should insert exactly one clause in cond @ lbl3
   (check-match
    adjacent-dispatches
    (list
     (struct*
      pending
      ([partial-inputs
        (app
         (input-map-ref 'F)
         (a$λ
          (struct*
           a$conds
           ([table
             (list
              (struct*
               a$clause
               ([key (== a$proc)]
                [body
                 (a$let
                  (a$%app (a$x 0) (a$X _ (== integer)))
                  (struct*
                   a$conds
                   ([table
                     (list
                      (struct*
                       a$clause
                       ([key (== a$pair)]
                        [body
                         (a$λ
                          (struct*
                           a$conds
                           ([table
                             (list
                              (struct*
                               a$clause
                               ([key (== a$proc)]
                                [body
                                 (a$let
                                  (a$car (a$x 1))
                                  (struct*
                                   a$conds
                                   ([table
                                     (list
                                      (struct* a$clause
                                               ([label (? label?)]
                                                [type (== boolean)]
                                                [key #t])))])))])))])))])))])))])))]))))]))
     ...))

   (define/match (let-first-clause let-ast)
     [((a$let _ (struct* a$conds ([table (cons clause _)]))))
      clause])

   (define/match (λ-first-clause let-ast)
     [((a$λ (struct* a$conds ([table (cons clause _)]))))
      clause])

   (define inserted-clauses-body
     (for/list ([inputs (in-list adjacent-dispatches)])
       (define full-ast (hash-ref (input-map (pending-partial-inputs inputs)) 'F))
       (a$clause-body (let-first-clause
                       (a$clause-body (λ-first-clause
                                       (a$clause-body (let-first-clause
                                                       (a$clause-body (λ-first-clause
                                                                       full-ast))))))))))

   (check-match
    inserted-clauses-body
    (list-no-order
     (a$x 0)
     (a$X _ (== boolean))
     (a$let (a$%app (a$x 1) (a$empty _))
            (struct* a$conds ([table '()])))
     (a$let (a$%app (a$x 1) (a$x 2))
            (struct* a$conds ([table '()])))
     (a$let (a$car (a$x 2))
            (struct* a$conds ([table '()])))
     (a$let (a$cdr (a$x 2))
            (struct* a$conds ([table '()])))
     (a$let (a$%app (a$x 3) (a$X _ (== integer)))
            (struct* a$conds ([table '()]))))))

  (test-case
   "pending nodes with only branches"

   (concolic-test-enable-provenance? #f)

   (define-input inputs
     [X integer 1])

   (check-equal?
    (list->set
     (adjacent-pending
      (pending inputs (empty-path-constraint) (empty-provenance))
      (extend-path-constraint
       (extend-path-constraint
        (empty-path-constraint)
        (branch 'then (with-rosette () (not (= (* X.var 2) 6)))))
       (branch 'else (with-rosette () (> X.var 5))))))
    (set
     (pending
      inputs
      (extend-path-constraint
       (empty-path-constraint)
       (branch 'else (with-rosette () (not (= (* X.var 2) 6)))))
      (empty-provenance))
     (pending
      inputs
      (extend-path-constraint
       (extend-path-constraint
        (empty-path-constraint)
        (branch 'then (with-rosette () (not (= (* X.var 2) 6)))))
       (branch 'then (with-rosette () (> X.var 5))))
      (empty-provenance))))
   )
  )

(module+ test
  (require (submod "../private/utils.rkt" config-output-port))

  (require (submod ".." test:adjacent))

  (reset-output-port!)
  )
