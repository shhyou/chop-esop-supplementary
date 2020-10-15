#lang racket/base

(require racket/match

         (for-syntax racket/base
                     racket/list
                     racket/syntax
                     racket/match
                     syntax/parse
                     concolic-hop/data
                     concolic-hop/state-passing)

         (prefix-in rosette:
                    (only-in rosette/safe
                             define-symbolic
                             integer? boolean?
                             sat
                             if cons))

         concolic-hop/data
         concolic-hop/conds
         concolic-hop/rosette
         (prefix-in c- concolic-hop/lib))

(module config-output-port racket/base
  (require racket/port)
  (provide reset-output-port!)

  (define output-port (current-output-port))
  (define-values (read-end write-end) (make-pipe))
  (void
   (thread
    (λ () (copy-port read-end output-port))))
  (port-count-lines! write-end)
  (current-output-port write-end)

  (define (reset-output-port!)
    (current-output-port output-port))
  )

(provide (all-defined-out))

(define (underlying-base-type-of base-type)
  (match base-type
    [(struct primitive-solvable (t))
     t]
    [(struct integer-range _)
     rosette:integer?]))

(define (make-a$X-internal base-type)
  (define var-value (fresh-symbolic-variable (underlying-base-type-of base-type)))
  (define X (a$X var-value base-type))
  (values X (a$X-variable X) (a$X-type X)))

(define (make-a$X-model . args)
  (rosette:sat
   (apply hash
          (for/list ([i (in-naturals)]
                     [arg (in-list args)])
            (cond
              [(even? i) (a$X-variable arg)]
              [else      arg])))))

(define-syntax (make-list stx)
  (raise-syntax-error 'make-list
                      "referred outside of define-inputs"
                      stx))

(define-syntax (: stx)
  (raise-syntax-error ':
                      "referred outside of define-inputs"
                      stx))

(begin-for-syntax
  (define (fresh-var-stx stx)
    (syntax-property
     (datum->syntax #f
                    (syntax-e (car (generate-temporaries (list stx))))
                    stx)
     'original-for-check-syntax #t))

  (struct input-env (defns models)
    #:transparent)

  (define (tell-defn server defn-stx)
    (update-local-state!
     server
     (match-lambda
       [(struct* input-env ([defns defns]
                            [models models]))
        (input-env (cons defn-stx defns)
                   models)])))

  (define (tell-model server model-stx)
    (update-local-state!
     server
     (match-lambda
       [(struct* input-env ([defns defns]
                            [models models]))
        (input-env defns
                   (cons model-stx models))])))

  (define (refine-type stx type-stx)
    (syntax-parse #`(#,stx . #,type-stx)
      #:literals (c-integer c-boolean c-integer-range c-list-of c-list/s c-->s
                            c-or/s
                            make-list λ)
      [(_ . (c-or/s type ...+))
       (for/or ([subtype-stx (in-list (syntax->list #'(type ...)))])
         (refine-type stx subtype-stx))]
      [(n:exact-integer . c-integer)
       type-stx]
      [(n:exact-integer . (c-integer-range low:exact-integer high:exact-integer))
       #:when (<= (syntax-e #'low) (syntax-e #'n) (syntax-e #'high))
       type-stx]
      [(b:boolean . c-boolean)
       type-stx]
      [((make-list . _) . (~or* (c-list-of _) (c-list/s . _)))
       type-stx]
      [((λ . _) . (c-->s _ _))
       type-stx]
      [_
       #f]))

  (define (refine-type/non-#f stx type-stx)
    (or (refine-type stx type-stx)
        (raise-syntax-error
         'refine-type
         (format
          "type error: expression ~s does not match type ~s"
          (syntax->datum stx)
          (syntax->datum type-stx))
         stx)))

  (define (embed-as-a$conds server var-stx env stx type-stx)
    (syntax-parse stx
      #:literals (cond :)
      #:datum-literals (@)
      [(cond
         (~optional (~seq @ label@cond:id))
         (~seq [key:expr : type:expr body] (~optional (~seq @ label@key:id)))
         ...)
       (with-syntax* ([(label-fresh-cond) (generate-temporaries
                                           #'((~? label@cond label-at-cond)))]
                      [label-cond #'(~? label@cond label-fresh-cond)]
                      [(label-fresh-key ...) (generate-temporaries
                                              #'((~? label@key label-at-key) ...))]
                      [(label-key ...) #'((~? label@key label-fresh-key) ...)])
         (define body-exprs
           (for/list ([body (in-list (syntax->list #'(body ...)))]
                      [clause-type-stx (in-list (syntax->list #'(type ...)))])
             (embed-as-a$ server (extend-env env clause-type-stx var-stx)
                                 body type-stx)))
         (with-syntax ([clause-num #`'#,(+ 1 (length (syntax->list #'(label-key ...))))]
                       [(body-expr ...) body-exprs])
           (tell-defn
            server
            #'(define-values (label-cond label-key ...)
                (apply
                 values
                 (for/list ([i (in-range clause-num)])
                   (fresh-label)))))
           (syntax/loc stx
             (a$conds
              label-cond
              (list
               (a$clause key type label-key body-expr) ...)))))]))

  (define (embed-as-a$ server env stx type-stx)
    (syntax-parse stx
      #:literals (λ let _ make-list :)
      [(: expr new-type)
       (embed-as-a$ server env #'expr #'new-type)]
      [n:nat ;; nat: de Bruijn index to local variable
       (define var-orig-stx (bound-value (env-ref env (syntax-e #'n))))
       (define var-stx
         (datum->syntax var-orig-stx
                        (syntax-e var-orig-stx)
                        stx
                        var-orig-stx))
       (with-syntax ([var var-stx]
                     [var-ast (syntax/loc stx (a$x n))])
         (syntax/loc stx (if #t var-ast var)))]
      [[X:id (~or* value:exact-integer value:boolean)]
       (define refined-type-stx
         (refine-type/non-#f #'value type-stx))
       (with-syntax ([type refined-type-stx]
                     [X.var (format-id #'X "~a.var" #'X #:source #'X #:subs? #t)]
                     [X.type (format-id #'X "~a.type" #'X #:source #'X #:subs? #t)])
         (unless (free-identifier=? #'X #'_)
           (tell-defn
             server
             #'(define-values (X X.var X.type) (make-a$X-internal type))))
         (tell-model
           server
           #'(make-a$X-model X value)))
       #'X]
      [(λ ((~and _ binding-stx)) conds:expr)
       (define/syntax-parse (_ dom-type range-type)
         (refine-type/non-#f stx type-stx))
       (define var-stx (fresh-var-stx #'binding-stx))
       (define conds-stx
         (embed-as-a$conds server var-stx env #'conds #'range-type))
       (with-syntax* ([conds-expr conds-stx]
                      [var var-stx]
                      [body (syntax/loc stx (a$λ conds-expr))])
         #'(let ([var #f]) body))]
      [(make-list form ...)
       (define refined-type-stx
         (refine-type/non-#f stx type-stx))
       (embed-as-list server env stx refined-type-stx)]
      [(let ([(~and _ binding-stx) rhs:expr]) conds:expr)
       (define var-stx (fresh-var-stx #'binding-stx))
       (define rhs-stx
         (syntax-parse #'rhs
           #:literals (car cdr)
           [((~and (~or* car cdr) list-selector)
             arg:nat)
            (define arg-type-stx
              (bound-type (env-ref env (syntax-e #'arg))))
            (define sel-stx
              (match (syntax-e #'list-selector)
                ['car #'a$car]
                ['cdr #'a$cdr]))
            (define arg-stx (embed-as-a$ server env #'arg arg-type-stx))
            (with-syntax ([sel sel-stx]
                          [arg arg-stx])
              (syntax/loc #'rhs (sel arg)))]
           [(f:nat arg:expr)
            (define/syntax-parse (~and f-type-stx (c-->s dom-type range-type))
              (bound-type (env-ref env (syntax-e #'f))))
            (define fun-stx (embed-as-a$ server env #'f #'f-type-stx))
            (define arg-stx (embed-as-a$ server env #'arg #'dom-type))
            (with-syntax ([fun fun-stx]
                          [arg-expr arg-stx])
              (syntax/loc #'rhs (a$%app fun arg-expr)))]))
       (define conds-stx
         (embed-as-a$conds server var-stx env #'conds type-stx))
       (with-syntax* ([rhs-expr rhs-stx]
                      [conds-expr conds-stx]
                      [var var-stx]
                      [body (syntax/loc stx (a$let rhs-expr conds-expr))])
         #'(let ([var #f]) body))]))

  (define (embed-as-list server env stx type-stx)
    (syntax-parse stx
      [(_ (~optional (~seq #:unless [guard:id guard-value:boolean])))
       #:with (guard-temp-id) (generate-temporaries (list stx))
       (define guard-var-stx
         (embed-as-a$ server env
                      #'[(~? guard guard-temp-id) (~? guard-value #t)]
                      #'c-boolean))
       (with-syntax ([guard-var guard-var-stx])
         (syntax/loc stx
           (a$empty guard-var)))]
      [(form:id
        (~optional (~seq #:unless [guard:id guard-value:boolean]))
        value-expr:expr
        rest-form ...)
       #:with (guard-temp-id) (generate-temporaries #'(value-expr))
       (define guard-var-stx
         (embed-as-a$ server env
                      #'[(~? guard guard-temp-id) (~? guard-value #f)]
                      #'c-boolean))
       (syntax-parse (refine-type/non-#f stx type-stx)
         #:literals (c-list/s c-list-of)
         [(c-list-of elem-type)
          (define elem-stx
            (embed-as-a$ server env #'value-expr #'elem-type))
          (define rest-stx
            (embed-as-list server env
                           #'(form rest-form ...)
                           #'(c-list-of elem-type)))
          (with-syntax ([guard-var guard-var-stx]
                        [elem elem-stx]
                        [rest rest-stx])
            (syntax/loc #'value-expr
              (a$cons guard-var elem rest)))]
         [(c-list/s car-type . cdr-type)
          (define elem-stx
            (embed-as-a$ server env #'value-expr #'car-type))
          (define rest-stx
            (embed-as-list server env
                           #'(form rest-form ...)
                           #'(c-list/s . cdr-type)))
          (with-syntax ([guard-var guard-var-stx]
                        [elem elem-stx]
                        [rest rest-stx])
            (syntax/loc #'value-expr
              (a$cons guard-var elem rest)))])]))
  )

(define-syntax (define-input stx)
  (when (eq? 'expression (syntax-local-context))
    (raise-syntax-error 'define-input "not allowed in an expression context" stx))
  (syntax-parse stx
    #:literals (make-list)
    [(form:id match-pattern:expr
              .
              (~and ([X:id type:expr value:expr] ...) inputs))
     (define inputs-stx (syntax->list #'inputs))
     (match-define (list (cons value-exprs-stx
                               (struct* input-env ([defns defns-stx]
                                                   [models models-stx]))))
       (call-with-server
        (input-env '() '())
        (λ (server)
          (define value-exprs-stx
            (for/list ([an-input-stx (in-list inputs-stx)])
              (define/syntax-parse [X:id type:expr value-expr:expr]
                an-input-stx)
              (define is-base-type?
                (syntax-parse #'type
                  #:literals (c-integer c-boolean c-integer-range
                                        c-list-of c-list/s
                                        c-->s
                                        c-or/s)
                  [(~or* c-integer c-boolean (c-integer-range _ _))
                   #t]
                  [(~or* (c-list-of _) (c-list/s . _)
                         (c-->s _ _)
                         (c-or/s . _))
                   #f]
                  [(~or* t:id (t:id . _) _)
                   (raise-syntax-error
                    'define-input
                    (string-append "unrecognized input specification"
                                   (cond
                                     [(not (attribute t)) ""]
                                     [else
                                      (format " (binding information: ~a)"
                                              (identifier-binding #'t))]))
                    an-input-stx
                    #'type)]))
              (define value-stx
                (embed-as-a$ server (empty-env)
                             (cond [is-base-type? #'[X value-expr]]
                                   [else          #'value-expr])
                             #'type))
              (cond
                [is-base-type?
                 value-stx]
                [else
                 (tell-defn
                  server
                  (with-syntax ([orig-stx stx]
                                [value value-stx])
                    #'(define X
                        (with-rosette () #:scope orig-stx
                          value))))
                 #'X])))
          (cons value-exprs-stx (get-local-state server)))))
     (with-syntax ([orig-stx stx]
                   [(defn ...) (reverse defns-stx)]
                   [(model ...) (reverse models-stx)]
                   [(value-expr ...) value-exprs-stx])
       (syntax/loc stx
         (begin
           defn ...
           (define input-types   (hash (~@ 'X type) ...))
           (define the-input-map (hash (~@ 'X X) ...))
           (define the-new-model
             (foldr model-union-prefer-right
                    (rosette:sat)
                    (list model ...)))
           (match-define match-pattern
             (input input-types
                    the-input-map
                    the-new-model)))))]))

(module* test racket/base
  (require racket/contract/base
           racket/match
           rackunit
           concolic-hop/data
           concolic-hop/store
           concolic-hop/lib
           concolic-hop/rosette
           (prefix-in rosette:
                      (only-in rosette/safe
                               define-symbolic
                               integer?
                               if))
           (submod ".."))

  (rosette:define-symbolic S rosette:integer?)
  (check-not-exn
   (λ ()
     (with-rosette ()
       (+ S 5))))

  (test-begin
   (define-input (struct* input ([type input-types]
                                 [map the-input-map]
                                 [model model]))
     [X integer 1]
     [Y integer 2]
     [B boolean #t]
     [I (integer-range 5 10) 7])

   (check-pred a$X? X)
   (check-equal? (hash-ref the-input-map 'X) X)
   (check-equal? (model X.var) 1)
   (check-equal? X.type integer)

   (check-pred a$X? Y)
   (check-equal? (hash-ref the-input-map 'Y) Y)
   (check-equal? (model Y.var) 2)
   (check-equal? Y.type integer)

   (check-pred a$X? B)
   (check-equal? (hash-ref the-input-map 'B) B)
   (check-equal? (model B.var) #t)
   (check-equal? B.type boolean)

   (check-pred a$X? I)
   (check-equal? (hash-ref the-input-map 'I) I)
   (check-equal? (model I.var) 7)
   (check-equal? I.type (integer-range 5 10))
   )

  (test-begin
   (define-input (struct* input ([type input-types]
                                 [map the-input-map]
                                 [model model]))
     [L0 (list-of integer)
         (make-list)]
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

   (check-pred (and/c a$list? a$empty?) L0)
   (check-pred (and/c a$list? a$cons?) L1)
   (check-pred (and/c a$list? a$cons?) L2)
   (check-pred (and/c a$list? a$cons?) L3)
   (check-equal? b2.type boolean)
   (check-equal? (model b2.var)
                 #f)
   (check-equal? b4.type boolean)
   (check-equal? (model b4.var)
                 #t)
   (check-equal? bnull.type boolean)
   (check-equal? (model bnull.var)
                 #f)
   )

  (test-begin
   (define-input (struct* input ([type input-types]
                                 [map the-input-map]
                                 [model model]))
     [Y integer 2]
     [F (->s integer boolean)
        (λ (_)
          (cond @ lbl0
                [1 : integer [B1 #f]]
                [(+ Y.var 1) : integer [B2 #t]] @ lbl1
                [(* Y.var 3) : integer [B3 #f]]))]
     [G (->s (->s integer boolean)
             (or/s (integer-range 2 5) (integer-range -1 2)))
        (λ (_)
          (cond
            [a$proc : (->s integer boolean)
                    (let ([_ (0 [X 1])]) ;; 0 -> de Bruijn index
                      (cond
                        [B1.var : boolean [Z 3]] @ lbl2
                        [#t : boolean [W 0]]))]))]
     [H (->s (list-of integer) integer)
        (λ (_)
          (cond
            [a$null : (list-of integer) [UU 1]]
            [a$pair : (list-of integer)
                    (let ([_ (cdr 0)])
                      (cond
                        [a$null : (list-of integer) [VV 2]]
                        [a$pair : (list-of integer)
                                (let ([_ (car 1)])
                                  (cond
                                    [-1 : integer 0]
                                    [1 : integer [K 7]]))]))]))])

   (check-pred a$X? X)
   (check-equal? (a$X X.var X.type) X)
   (check-equal? (model X.var)
                 1)
   (check-equal? (hash-ref the-input-map 'Y) Y)
   (check-equal? (model (a$X-variable (hash-ref the-input-map 'Y)))
                 2)
   (check-equal? (hash-ref the-input-map 'F) F)
   (check-match
    F
    (a$λ
     (struct* a$conds
              ([table
                `(,(struct* a$clause ([body
                                       (struct a$X _)]))
                  ...)]))))
   (check-equal? (hash-ref the-input-map 'G) G)
   (check-match
    G
    (a$λ
     (struct* a$conds
              ([table
                (list
                 (struct* a$clause
                          ([key (? a$proc?)]
                           [body
                            (struct* a$let
                                     ([elim (struct a$%app _)]
                                      [body (struct a$conds _)]))])))]))))
   (check-equal? (hash-ref the-input-map 'H) H)
   (check-match
    H
    (a$λ
     (struct*
      a$conds
      ([table
        (list
         (struct*
          a$clause
          ([key (? a$null?)]
           [body (== UU)]))
         (struct*
          a$clause
          ([key (? a$pair?)]
           [body (struct*
                  a$let
                  ([elim (struct a$cdr ((a$x 0)))]
                   [body (struct*
                          a$conds
                          ([table
                            (list
                             (struct* a$clause ([key (? a$null?)]
                                                [body (== VV)]))
                             (struct*
                              a$clause
                              ([key (? a$pair?)]
                               [body (struct*
                                      a$let
                                      ([elim (struct a$car ((a$x 1)))]
                                       [body (struct a$conds _)]))])))]))]))])))]))))
   (check-equal? (model Z.var)
                 3)
   (check-equal? (model B1.var)
                 #f)
   (check-equal? (model B2.var)
                 #t)
   (check-equal? (model B3.var)
                 #f)
   (check-pred label? lbl0)
   (check-pred label? lbl1)
   (check-pred label? lbl2)
   )

  (test-begin
   (define-input (struct* input ([type input-types]
                                 [map the-input-map]
                                 [model the-model]))
     [L1 (list-of (->s integer integer))
         (make-list (λ (_)
                      (cond
                        [0 : integer [X 33]]
                        [1 : integer [Y 1]])))])

   (check-pred (and/c a$list? a$cons?) L1)
   (check-match
    (a$cons-car L1)
    (a$λ
     (struct* a$conds ([table
                        (list
                         (struct* a$clause ([key 0] [body (== X)]))
                         (struct* a$clause ([key 1] [body (== Y)])))])))))

  (test-begin
   (define-input (struct* input ([type input-types]
                                 [map the-input-map]
                                 [model the-model]))
     [X integer 3]
     [F (->s integer (or/s integer (list-of integer)))
        (λ (_)
          (cond
            [X.var : integer
                   [Y 5]]
            [(* X.var 2) : integer
                         (make-list [E1 -1]
                                    0
                                    [E3 -3])]))])

   (check-match
    F
    (a$λ
     (struct*
      a$conds
      ([table
        (list
         (struct* a$clause ([key (== X.var)] [body (== Y)]))
         (struct* a$clause
                  ([key (== (with-rosette () (* X.var 2)))]
                   [body
                    (a$cons _ (== E1)
                            (a$cons _ (a$x 0)
                                    (a$cons _ (== E3)
                                              (a$empty _))))])))])))))
  )
