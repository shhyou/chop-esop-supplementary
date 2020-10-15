#lang racket/base

(require syntax/parse/define
         rackunit)

(provide define-check-app-matches)

(define-simple-macro (define-check-app-matches result:id 
                       #:for [f:id content:expr]
                       #:do body:expr ...+
                       #:check-match match-pattern)
  (define result
    (car (append (for/list ([f content])
                   (define body-result
                     (let () body ...))
                   (check-match
                    (cons (object-name f) body-result)
                    (cons _ match-pattern))
                   body-result)
                 '(#f)))))

(module* test:funast racket/base

(require racket/set
         racket/match
         racket/class
         racket/contract/base
         rackunit

         (only-in rosette/safe sat)

         concolic-hop/state-passing

         concolic-hop/data
         concolic-hop/funast
         concolic-hop/lib

         (submod "..")
         "../private/utils.rkt")

(test-case
 "a$->datum"

 (define-input inputs
   [X integer 5]
   [L (list-of boolean)
      (make-list [B1 #t] [B2 #f])]
   [F1 (->s integer integer)
       (λ (_)
         (cond
           [(+ X.var 3) : integer [Y 123]]
           [(* X.var 2) : integer 0]))]
   [F1.1 (->s integer (->s integer integer))
         (λ (_)
           (cond
             [123 : integer
                  (λ (_)
                    (cond
                      [456 : integer
                           0]))]))]
   [F1.2 (->s integer (->s integer integer))
         (λ (_)
           (cond
             [123 : integer
                  (λ (_)
                    (cond
                      [456 : integer
                           1]))]))]
   [F2 (->s (or/s integer (->s integer integer))
            integer)
       (λ (_)
         (cond
           [9 : integer [Z -1]]))]
   [F3 (->s (or/s integer (->s integer integer))
            integer)
       (λ (_)
         (cond
           [10 : integer [W -2]]
           [a$proc : (->s integer integer)
                   [I 5]]))]
   [F4 (->s (or/s integer (->s (list-of integer) integer))
            integer)
       (λ (_)
         (cond
           [11 : integer [J -3]]
           [a$proc : (->s (list-of integer) integer)
                   (let ([_ (0 (make-list [m 3] [n 4]))])
                     (cond [(+ 7 X.var) : integer
                                        [k -4]]))]))]
   [G (->s (list-of (list-of integer)) boolean)
      (λ (_)
        (cond
          [a$null : (list-of (list-of integer)) [XX #f]]
          [a$pair : (list-of (list-of integer))
                  (let ([_ (car 0)])
                    (cond
                      [a$pair : (list-of integer)
                              (let ([_ (cdr 0)])
                                (cond
                                  [a$null : (list-of integer)
                                          [YY #t]]))]))]))])

 (define dead-end
   '(error "ASSERT_UNREACHABLE"))

 (check-equal?
  (a$->datum inputs X)
  5)

 (check-equal?
  (a$->datum inputs L)
  '(cons #t (cons #f null)))

 (check-match
  (a$->datum inputs F1)
  `(λ (,(? symbol? x))
     (cond
       [(procedure? ,x) ,(== dead-end)]
       [(null? ,x) ,(== dead-end)]
       [(pair? ,x) ,(== dead-end)]
       [(equal? ,x 8) 123]
       [(equal? ,x 10) ,x]
       [else ,(== dead-end)])))

 (check-match
  (a$->datum inputs F1.1)
  `(λ (,(? symbol? x))
     (cond
       [(procedure? ,x) ,(== dead-end)]
       [(null? ,x) ,(== dead-end)]
       [(pair? ,x) ,(== dead-end)]
       [(equal? ,x 123)
        (λ (,(? symbol? y))
          (cond
            [(procedure? ,y) ,(== dead-end)]
            [(null? ,y) ,(== dead-end)]
            [(pair? ,y) ,(== dead-end)]
            [(equal? ,y 456)
             ,y]
            [else ,(== dead-end)]))]
       [else ,(== dead-end)])))

 (check-match
  (a$->datum inputs F1.2)
  `(λ (,(? symbol? x))
     (cond
       [(procedure? ,x) ,(== dead-end)]
       [(null? ,x) ,(== dead-end)]
       [(pair? ,x) ,(== dead-end)]
       [(equal? ,x 123)
        (λ (,(? symbol? y))
          (cond
            [(procedure? ,y) ,(== dead-end)]
            [(null? ,y) ,(== dead-end)]
            [(pair? ,y) ,(== dead-end)]
            [(equal? ,y 456)
             ,x]
            [else ,(== dead-end)]))]
       [else ,(== dead-end)])))

 (check-match
  (a$->datum inputs F2)
  `(λ (,(? symbol? x))
     (cond
       [(procedure? ,x) ,(== dead-end)]
       [(null? ,x) ,(== dead-end)]
       [(pair? ,x) ,(== dead-end)]
       [(equal? ,x 9) -1]
       [else ,(== dead-end)])))

 (check-match
  (a$->datum inputs F3)
  `(λ (,(? symbol? x))
     (cond
       [(procedure? ,x) 5]
       [(null? ,x) ,(== dead-end)]
       [(pair? ,x) ,(== dead-end)]
       [(equal? ,x 10) -2]
       [else ,(== dead-end)])))

 (check-match
  (a$->datum inputs F4)
  `(λ (,(? symbol? x))
     (cond
       [(procedure? ,x)
        (let ([,(? symbol? y) (,x (cons 3 (cons 4 null)))])
          (cond
            [(procedure? ,y) ,(== dead-end)]
            [(null? ,y) ,(== dead-end)]
            [(pair? ,y) ,(== dead-end)]
            [(equal? ,y 12) -4]
            [else ,(== dead-end)]))]
       [(null? ,x) ,(== dead-end)]
       [(pair? ,x) ,(== dead-end)]
       [(equal? ,x 11) -3]
       [else ,(== dead-end)])))

 (check-match
  (a$->datum inputs G)
  `(λ (,(? symbol? xss))
     (cond
       [(procedure? ,xss) ,(== dead-end)]
       [(null? ,xss) #f]
       [(pair? ,xss)
        (let ([,(? symbol? xs) (car ,xss)])
          (cond
            [(procedure? ,xs) ,(== dead-end)]
            [(null? ,xs) ,(== dead-end)]
            [(pair? ,xs)
             (let ([,(? symbol? rest-xs) (cdr ,xs)])
               (cond
                 [(procedure? ,rest-xs) ,(== dead-end)]
                 [(null? ,rest-xs) #t]
                 [(pair? ,rest-xs) ,(== dead-end)]
                 [else ,(== dead-end)]))]
            [else ,(== dead-end)]))]
       [else ,(== dead-end)])))
 )

(test-case
 "all-new-a$values base values"

 (let ()
   (define-check-app-matches val-inputs-1
     #:for [f (in-list (list all-new-a$values all-new-a$exprs))]
     #:do (call-with-server
           (sat)
           (λ (server)
             (cons (f server integer (empty-env) (hash))
                   (get-local-state server))))
     #:check-match (list (cons (? a$X?) _)))

   (match-define (list (cons X model-1))
     val-inputs-1)
   (check-equal? integer (a$X-type X))
   (check-pred integer? (model-1 (a$X-variable X))))

 (let ()
   (define-check-app-matches val-inputs-2
     #:for [f (in-list (list all-new-a$values all-new-a$exprs))]
     #:do (call-with-server
           (sat)
           (λ (server)
             (cons (f server boolean (empty-env) (hash))
                   (get-local-state server))))
     #:check-match (list (cons (? a$X?) _)))

   (match-define (list (cons B model-2))
     val-inputs-2)
   (check-equal? boolean (a$X-type B))
   (check-pred boolean? (model-2 (a$X-variable B))))

 (let ()
   (define-check-app-matches val-inputs-3
     #:for [f (in-list (list all-new-a$values all-new-a$exprs))]
     #:do (call-with-server
           (sat)
           (λ (server)
             (cons (f server (integer-range -1 2) (empty-env) (hash))
                   (get-local-state server))))
     #:check-match (list (cons (? a$X?) _)))

   (match-define (list (cons I model-3))
     val-inputs-3)
   (check-equal? (integer-range -1 2) (a$X-type I))
   (check-pred (λ (n) (and (integer? n)
                           (<= -1 n 2)))
               (model-3 (a$X-variable I)))))

(test-case
 "all-new-a$values functions"

 (define type
   (->s integer (->s boolean (list-of integer))))

 (define-check-app-matches val-inputs
   #:for [f (in-list (list all-new-a$values all-new-a$exprs))]
   #:do (call-with-server
         (sat)
         (λ (server)
           (cons (f server type (empty-env) (hash))
                 (get-local-state server))))
   #:check-match (list (cons (a$λ
                              (struct* a$conds ([table '()])))
                             _)))

 (void))

(test-case
 "all-new-a$values lists"

 (let ()
   (define-input inputs)

   (define type
     (list-of integer))

   (define-check-app-matches val-inputs
     #:for [f (in-list (list all-new-a$values all-new-a$exprs))]
     #:do (call-with-server
           (sat)
           (λ (server)
             (cons (f server type (empty-env) (hash))
                   (get-local-state server))))
     #:check-match (list (cons (a$empty (? a$X?))
                               _)))

   (match-define (list (cons (a$empty B) the-model))
     val-inputs)
   (check-equal? (a$X-type B) boolean)
   (check-equal? (the-model (a$X-variable B)) #t))

 (let ()
   (define type
     (list/s integer
             (->s boolean integer)
             boolean
             (list/s (integer-range 5 7))))

   (define-check-app-matches val-inputs
     #:for [f (in-list (list all-new-a$values all-new-a$exprs))]
     #:do (call-with-server
           (sat)
           (λ (server)
             (cons (f server type (empty-env) (hash))
                   (get-local-state server))))
     #:check-match (list
                    (cons
                     (a$cons (? a$X?)
                             (? a$X?)
                             (a$cons (? a$X?)
                                     (? a$λ?)
                                     (a$cons (? a$X?)
                                             (? a$X?)
                                             (a$cons (? a$X?)
                                                     (a$cons (? a$X?)
                                                             (? a$X?)
                                                             (a$empty (? a$X?)))
                                                     (a$empty (? a$X?))))))
                     _)))

   (match-define (list
                  (cons
                   (a$cons B1
                           X
                           (a$cons B2
                                   _
                                   (a$cons B3
                                           Z
                                           (a$cons B4
                                                   (a$cons _ I (a$empty _))
                                                   (a$empty B5)))))
                   the-model))
     val-inputs)
   (check-equal? (a$X-type B1) boolean)
   (check-equal? (a$X-type B2) boolean)
   (check-equal? (a$X-type B3) boolean)
   (check-equal? (a$X-type B4) boolean)
   (check-equal? (a$X-type B5) boolean)

   (check-equal? (the-model (a$X-variable B1)) #f)
   (check-equal? (the-model (a$X-variable B2)) #f)
   (check-equal? (the-model (a$X-variable B3)) #f)
   (check-equal? (the-model (a$X-variable B4)) #f)
   (check-equal? (the-model (a$X-variable B5)) #t)

   (check-equal? (a$X-type X) integer)
   (check-equal? (a$X-type Z) boolean)
   (check-equal? (a$X-type I) (integer-range 5 7))

   (check-pred integer? (the-model (a$X-variable X)))
   (check-pred boolean? (the-model (a$X-variable Z)))
   (check-pred (λ (n) (and (integer? n)
                           (<= 5 n 7)))
               (the-model (a$X-variable I))))
 )

(test-case
 "all-new-a$values unions"

 (define type
   (or/s integer
         (list-of (->s integer integer))
         (->s boolean (list-of boolean))))

 (define-check-app-matches val-inputs
   #:for [f (in-list (list all-new-a$values all-new-a$exprs))]
   #:do (call-with-server
         (sat)
         (λ (server)
           (cons (f server type (empty-env) (hash))
                 (get-local-state server))))
   #:check-match (list-no-order
                  (cons (? a$X?) _)
                  (cons (a$empty (? a$X?)) _)
                  (cons (a$λ
                         (struct* a$conds ([table '()])))
                        _)))

 (void))

(test-case
 "all-new-a$exprs functions"

 (define new-exprs
   (call-with-server
    (sat)
    (λ (server)
      (all-new-a$exprs server
                       (->s boolean integer)
                       (extend-env
                        (extend-env
                         (empty-env)
                         (->s boolean integer) (a$x 1))
                        integer                (a$x 0))
                       (hash
                        a$proc
                        (extend-env
                         (empty-env)
                         (->s boolean integer) (cons +inf.0 (a$x 1))))))))

 (check-pred (listof a$expr?) new-exprs)

 (check-match
  new-exprs
  (list-no-order
   (struct a$λ _)
   (a$x 1)
   (a$let (a$%app (a$x 1) (a$X _ (== boolean))) (struct a$conds _))))
 )

(test-case
 "all-new-a$exprs let a$app"

 (define new-exprs
   (call-with-server
    (sat)
    (λ (server)
      (all-new-a$exprs server
                       integer
                       (extend-env
                        (extend-env
                         (extend-env
                          (empty-env)
                          boolean              (a$x 2))
                         (->s boolean integer) (a$x 1))
                        integer                (a$x 0))
                       (hash
                        a$proc
                        (extend-env
                         (empty-env)
                         (->s boolean integer) (cons +inf.0 (a$x 1))))))))

 (check-pred (listof a$expr?) new-exprs)

 (check-match
  new-exprs
  (list-no-order
   (a$X _ (== integer))
   (a$x 0)
   (a$let (a$%app (a$x 1) (a$X _ (== boolean))) (struct a$conds _))
   (a$let (a$%app (a$x 1) (a$x 2))              (struct a$conds _))))
 )

(test-case
 "all-new-a$exprs let a$car, a$cdr basic"

 (define new-exprs
   (call-with-server
    (sat)
    (λ (server)
      (all-new-a$exprs server
                       integer
                       (extend-env
                        (extend-env
                         (extend-env
                          (extend-env
                           (extend-env
                            (empty-env)
                            (list-of boolean) (a$x 4))
                           (list-of integer)  (a$x 3))
                          (list-of integer)   (a$x 2))
                         boolean              (a$x 1))
                        integer               (a$x 0))
                       (hash
                        a$pair
                        (extend-env
                         (extend-env
                          (extend-env
                           (empty-env)
                           (list-of boolean) (cons 1 (a$x 4)))
                          (list-of integer)  (cons 2 (a$x 3)))
                         (list-of integer)   (cons 0 (a$x 2))))))))

 (check-pred (listof a$expr?) new-exprs)

 (check-match
  new-exprs
  (list-no-order
   (a$X _ (== integer))
   (a$x 0)
   (a$let (a$car (a$x 3)) (struct a$conds _))
   (a$let (a$cdr (a$x 3)) (struct a$conds _))
   (a$let (a$car (a$x 4)) (struct a$conds _))
   (a$let (a$cdr (a$x 4)) (struct a$conds _))))
 )

(test-case
 "search-expr λ"

 (define-input inputs
   [F (->s integer integer)
      (λ (_) (cond @ lbl0))])

 (check-equal?
  (let ()
    (define labels '())
    (search-expr F
                 (λ (conds-ast)
                   (set! labels (cons (a$conds-label conds-ast) labels))))
    labels)
  (list lbl0)))

(test-case
 "search-expr conds"

 (define-input inputs
   [F (->s integer (->s integer integer))
      (λ (_)
        (cond @ lbl0
              [0 : integer
                 (λ (_) (cond @ lbl4))] @ lbl1
              [1 : integer
                 (λ (_) (cond @ lbl5))] @ lbl2
              [2 : integer
                 (λ (_) (cond @ lbl6))] @ lbl3))])

 (check-equal?
  (let ()
    (define labels '())
    (search-expr F
                 (λ (conds-ast)
                   (set! labels (cons (a$conds-label conds-ast) labels))))
    labels)
  (list lbl6 lbl5 lbl4 lbl0)))

(test-case
 "search-expr list"

 (define-input inputs
   [F (list-of (->s integer integer))
      (make-list
       (λ (_) (cond @ lbl0))
       (λ (_) (cond @ lbl1))
       (λ (_) (cond @ lbl2))
       (λ (_) (cond @ lbl3)))])

 (check-equal?
  (let ()
    (define labels '())
    (search-expr F
                 (λ (conds-ast)
                   (set! labels (cons (a$conds-label conds-ast) labels))))
    labels)
  (list lbl3 lbl2 lbl1 lbl0)))

(test-case
 "search-expr let"

 (define-input inputs
   [F (->s (or/s (->s (->s integer integer) integer)
                 (list-of integer))
           integer)
      (λ (_) (cond @ lbl0
                   [a$proc : (->s (->s integer integer) integer)
                           (let ([_ (0 (λ (_) (cond @ lbl1)))])
                             (cond @ lbl2))]
                   [a$pair : (list-of integer)
                           (let ([_ (car 0)])
                             (cond @ lbl3
                                   [0 : integer
                                      (let ([_ (car 1)])
                                        (cond @ lbl4))]))]))])

 (check-equal?
  (let ()
    (define labels '())
    (search-expr F
                 (λ (conds-ast)
                   (set! labels (cons (a$conds-label conds-ast) labels))))
    labels)
  (list lbl4 lbl3 lbl2 lbl1 lbl0)))

(test-case
 "traverse-ast% ignores dead branches caused by tuple + null?/pair?"

 (define-input inputs
   [F (->s (list/s integer) integer)
      (λ (_)
        (cond
          [a$pair : (list/s integer)
                  (let ([_ (cdr 0)])
                    (cond
                      @ lbl3
                      [a$null : (list/s) [X 123]]
                      [a$pair : (list/s) [Y 456]]))]
          [a$null : (list/s integer) [Z 789]]))])

 (define visit-ast%
   (class traverse-ast%
     (inherit traverse)

     (define visited-vars '())

     (define/augment (visit-expr ast type)
       (match ast
         [(and var-ast (struct a$X _))
          (set! visited-vars (cons var-ast visited-vars))]
         [_ (void)]))

     (define/public (visit)
       (traverse)
       visited-vars)
     (super-new)))

 (check-equal?
  (call-with-server
   (input-model inputs)
   (λ (server)
     (send (new visit-ast%
                [server server]
                [type (hash-ref (input-type inputs) 'F)]
                [ast F])
           visit)))
  ;; the extra layer of (list _) is from call-with-server
  (list (list X))))
)

(module* test racket/base
  (require (submod "../private/utils.rkt" config-output-port))
  (require (submod ".." test:funast))
  (sleep 0.1) (reset-output-port!)
  )
