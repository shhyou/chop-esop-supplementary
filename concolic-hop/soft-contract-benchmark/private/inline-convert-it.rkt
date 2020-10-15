#lang racket
(require (except-in syntax/parse integer boolean)
         syntax/id-table
         concolic-hop/convert-it
         (submod concolic-hop/convert-it help-inline-conver-it)
         (only-in concolic-hop/lang ->s or/s list-of list/s integer boolean)
         (for-syntax syntax/parse)
         racket/runtime-path
         "inline-lib.rkt"
         "inline-simplifications.rkt")
(module+ test (require rackunit))

(provide inline-convert-it remove-#%apps
         (contract-out
          [get-external-dependencies
           (-> any/c (listof any/c))]))

(define-namespace-anchor anchor)
(define ns #f)

(define (inline-convert-it expression type
                           #:lumps [lumps '()]
                           #:structs [structs '()]
                           #:contract [contract #f]
                           #:needs-exposed-arithmetic?
                           [needs-exposed-arithmetic? #f])
  (unless ns (set! ns (namespace-anchor->namespace anchor)))
  (define expr
    (parameterize ([current-namespace ns])
      (eval `(define-lump L ,@(for/list ([lump (in-list lumps)]
                                         [i (in-naturals)])
                                `(,i ,lump))))

      ;; this sets up the transformer environment in a way to
      ;; fake what `struct` does, telling convert-it the
      ;; names of the constructor, predicate, and selectors
      ;; based on what we know they will have to be
      ;; For dumb technical reasons, constructors end up expanding
      ;; into identifiers that start with "CONSTRUCTOR:" and thus
      ;; need to be stripped off in an extra pass afterwards
      (namespace-require '(for-syntax racket/struct-info))
      (eval '(begin-for-syntax
               (define ((fake-struct-info-transformer name) stx)
                 (syntax-case stx ()
                   [(_ a ...) #`(#,name a ...)]
                   [x (identifier? #'x name)]))
               (struct fake-struct-info (proc info)
                 #:property prop:procedure 0
                 #:property prop:struct-info (λ (m) (fake-struct-info-info m)))))
      (for ([struct (in-list structs)])
        (match struct
          [`(struct ,s (,flds ...))
           (define constructor-name (string->symbol (format "CONSTRUCTOR:~a" s)))
           (eval `(define ,constructor-name ,(symbol->string constructor-name)))
           (eval `(define-syntax
                    ,s
                    (fake-struct-info
                     (fake-struct-info-transformer ',constructor-name)
                     (list #f
                           #',s
                           #',(string->symbol (format "~a?" s))
                           (list ,@(for/list ([fld (in-list (reverse flds))])
                                     `#',(string->symbol (format "~a-~a" s fld))))
                           (list ,@(for/list ([fld (in-list flds)])
                                     `#f))
                           #f))))]))
      (expand #`(convert-it #,expression #,type
                            L
                            #,@(if needs-exposed-arithmetic?
                                   (list '#:arithmetic-coercion-inside)
                                   (list))))))
  (check-for-prefix expr)
  (define result-with-possibly-large-numbers-in-the-names
    (strip-CONSTRUCTOR
     (with-freshening
         (simplify (to-plain expr) contract))))

  ;; normalize the names in the final result
  (with-freshening
      (freshen result-with-possibly-large-numbers-in-the-names)))

(define (strip-CONSTRUCTOR exp)
  (let loop ([exp exp])
    (cond
      [(and (symbol? exp)
            (regexp-match #rx"^CONSTRUCTOR:(.*)$" (symbol->string exp)))
       =>
       (λ (m)
         (string->symbol (list-ref m 1)))]
      [(pair? exp) (cons (loop (car exp))
                         (loop (cdr exp)))]
      [else exp])))

(define (remove-#%apps expr)
  (let loop ([expr expr])
    (match expr
      [`(#%app ,f ,xs ...)
       `(,(loop f) ,@(for/list ([x (in-list xs)])
                       (loop x)))]
      [(? list?) (map loop expr)]
      [_ expr])))

(define (to-plain expr)
  (let loop ([expr expr]
             [env (make-immutable-free-id-table)])
    (syntax-parse expr
      #:literals (let let-values λ #%plain-lambda #%plain-app if #%top quote)
      [(let ([x e1]) e2)
       (define nx (next-var))
       `(let ([,nx ,(loop #'e1 env)])
          ,(loop #'e2 (free-id-table-set env #'x nx)))]
      [(let-values ([(x) e1]) e2)
       (loop #`(let ([x e1]) e2) env)]
      [(let-values () e)
       (loop #'e env)]
      [(λ (xs ...) e)
       (define nxs
         (for/list ([x (in-list (syntax->list #'(xs ...)))])
           (next-var)))
       (define new-env
         (for/fold ([env env])
                   ([x (in-list (syntax->list #'(xs ...)))]
                    [nx (in-list nxs)])
           (free-id-table-set env x nx)))
       `(λ (,@nxs) ,(loop #'e new-env))]
      [(#%plain-lambda (xs ...) e) (loop #`(λ (xs ...) e) env)]
      [x:id
       (define remapped (free-id-table-ref env #'x #f))
       (cond
         [remapped remapped]
         [else (syntax-e #'x)])]
      [(#%plain-app f-e x-es ...)
       `(#%app ,(loop #'f-e env)
               ,@(for/list ([x-e (in-list (syntax->list #'(x-es ...)))])
                   (loop x-e env)))]
      [(if tst thn els)
       `(if ,(loop #'tst env)
            ,(loop #'thn env)
            ,(loop #'els env))]
      [n:number (syntax-e #'n)]
      ['n:number (syntax-e #'n)]
      [b #:when (boolean? (syntax-e #'b)) (syntax-e #'b)]
      ['b #:when (boolean? (syntax-e #'b)) (syntax-e #'b)]
      [s:string (syntax-e #'s)]
      ['s:string (syntax-e #'s)]
      ['(anything ...) (syntax->datum expr)]
      ['x:id (syntax->datum expr)]
      [(#%top . s:id) (syntax-e #'s)]
      [x (error 'to-plain
                "cannot convert ~s\n~a"
                expr
                (let ([sp (open-output-string)])
                  (parameterize ([current-output-port sp])
                    (pretty-write (syntax->datum expr) sp))
                  (get-output-string sp)))])))

(module+ test
  (check-equal? (with-freshening (to-plain #`(#%plain-app + x y))) `(#%app + x y))
  (check-equal? (with-freshening (to-plain #`(λ (x) (#%plain-app + x y)))) `(λ (✌0) (#%app + ✌0 y)))
  (check-equal? (with-freshening (to-plain #`(let ([x x]) x))) `(let ([✌0 x]) ✌0))
  (check-equal? (with-freshening (to-plain #`(let-values ([(x) x]) x))) `(let ([✌0 x]) ✌0))
  (check-equal? (with-freshening (to-plain #`(let ([x x]) (let ([x x]) x))))
                `(let ([✌0 x]) (let ([✌1 ✌0]) ✌1)))
  (check-equal? (with-freshening (to-plain #`(#%plain-app msg-send-error msg '(a b c))))
                `(#%app msg-send-error msg '(a b c))))

(define (simplify expr contract)
  (define all-simplifier-procs
    (list (λ (expr) (fixed-point-with-simplifications shrinking-simplifications expr contract))
          (λ (expr) (do-substitutions expr #:contract contract))
          (λ (expr) (simplify-everywhere-once expanding-simpifications expr #:contract contract))
          (λ (expr) (simplify-everywhere-once assert-simplifications-1 expr #:contract contract))
          (λ (expr) (simplify-everywhere-once assert-simplifications-2 expr #:contract contract))
          ))
  (assert-unique-binders expr)
  (let loop ([expr expr]
             [simplifier-procs all-simplifier-procs])
    (cond
      [(null? simplifier-procs) expr]
      [else
       (define next ((car simplifier-procs) expr))
       (cond
         [(equal? next expr)
          (loop next (cdr simplifier-procs))]
         [else
          (assert-unique-binders expr)
          (loop next all-simplifier-procs)])])))

(define (fixed-point-with-simplifications some-simplifications expr contract)
  (assert-unique-binders expr)
  (let loop ([expr expr])
    (define new (simplify-everywhere-once some-simplifications expr #:contract contract))
    (assert-unique-binders new)
    (cond
      [(equal? new expr) expr]
      [else (loop new)])))

(define (assert-unique-binders expr)
  (define binders (make-hash))
  (define (unique-var x)
    (cond
      [(hash-ref binders x #f)
       (define sp (open-output-string))
       (pretty-write expr sp)
       (error 'assert-unique-binders "found more than one ~s in\n~a"
              x
              (get-output-string sp))]
      [else
       (hash-set! binders x #t)]))
  (let loop ([expr expr])
    (match expr
      [`(let ([,xs ,es] ...) ,body)
       (for ([x (in-list xs)])
         (unique-var x))
       (for ([e (in-list es)])
         (loop e))
       (loop body)]
      [`(λ (,xs ...) ,body)
       (for ([x (in-list xs)])
         (unique-var x))
       (loop body)]
      [`(#%app ,f-e ,x-es ...)
       (loop f-e)
       (for ([x-e (in-list x-es)])
         (loop x-e))]
      [`(if ,tst-e ,thn-e ,els-e)
       (loop tst-e)
       (loop thn-e)
       (loop els-e)]
      [(? symbol? s) (void)]
      [(? boolean? b) (void)]
      [(? number? n) (void)]
      [(? string? s) (void)]
      [`',quoted-thing (void)])))

(define (do-substitutions expr #:contract [contract #f])
  (let loop ([expr expr]
             [simplification-env (build-initial-environment expr contract)])
    (match expr
      [`(let ([,xs ,(? (λ (x) (valuable? simplification-env x #:for-subst? #t)) vs)] ...) ,body)
       (substs xs vs body)]
      [`(let ([,xs ,es] ...) ,body)
       `(let (,@(for/list ([x (in-list xs)]
                           [e (in-list es)])
                  `[,x ,(loop e simplification-env)]))
          ,(loop body simplification-env))]
      [`(λ (,xs ...) ,body)
       `(λ (,@xs) ,(loop body simplification-env))]
      [`(#%app ,f-e ,x-es ...)
       `(#%app ,(loop f-e simplification-env)
               ,@(for/list ([x-e (in-list x-es)])
                   (loop x-e simplification-env)))]
      [`(if ,tst-e ,thn-e ,els-e)
       (define-values (thn-env els-env)
         (cond
           [(fact? tst-e)
            (values (add-fact simplification-env tst-e #t)
                    (add-fact simplification-env tst-e #f))]
           [else (values simplification-env simplification-env)]))
       `(if ,(loop tst-e simplification-env)
            ,(loop thn-e thn-env)
            ,(loop els-e els-env))]
      [(? symbol? s) s]
      [(? boolean? b) b]
      [(? number? n) n]
      [(? string? s) s]
      [`',quoted-thing expr])))

(module+ test
  (check-equal?
   (with-freshening
       (do-substitutions
        (freshen
         '(let ((x0 (λ (x1) (λ (x2) (#%app + x1 x2)))))
            (λ (x3 x4)
              (let ((x5 (#%app (#%app x0 x3) x4)))
                x5))))))
   '(λ (✌3 ✌4)
      (let ((✌5 (#%app (#%app (λ (✌6) (λ (✌7) (#%app + ✌6 ✌7))) ✌3) ✌4)))
        ✌5)))

  (check-equal?
   (with-freshening
       (do-substitutions
        (freshen
         '(λ (✌9 ✌10 ✌11 ✌12)
            (let ((✌52 (#%app procedure? ✌9)))
              (let ((✌51 (#%app null? ✌9)))
                (let ((✌50 (#%app pair? ✌9)))
                  (λ (✌24)
                    (#%app error "ASSERT_UNREACHABLE")))))))))
   '(λ (✌0 ✌1 ✌2 ✌3)
      (let ((✌5 (#%app null? ✌0)))
        (let ((✌6 (#%app pair? ✌0)))
          (λ (✌7)
            (#%app error "ASSERT_UNREACHABLE")))))))

(define (substs to-replace-xs to-replace-vs body)
  (let loop ([expr body]
             [replacements
              (for/hash ([x (in-list to-replace-xs)]
                         [v (in-list to-replace-vs)])
                (values x v))])
    (match expr
      [`(let ([,xs ,es] ...) ,body)
       `(let (,@(for/list ([x (in-list xs)]
                           [e (in-list es)])
                  `[,x ,(loop e replacements)]))
          ,(loop body
                 (for/fold ([replacements replacements])
                           ([x (in-list xs)])
                   (hash-remove replacements x))))]
      [`(#%app ,f-e ,x-es ...)
       `(#%app ,(loop f-e replacements)
               ,@(for/list ([x-e (in-list x-es)])
                   (loop x-e replacements)))]
      [`(if ,tst-e ,thn-e ,els-e)
       `(if ,(loop tst-e replacements)
            ,(loop thn-e replacements)
            ,(loop els-e replacements))]
      [`(λ (,xs ...) ,body)
       `(λ (,@xs) ,(loop body (for/fold ([replacements replacements])
                                        ([x (in-list xs)])
                                (hash-remove replacements x))))]
      [(? symbol? s)
       (cond
         [(hash-has-key? replacements s)
          (freshen (hash-ref replacements s))]
         [else s])]
      [(? boolean? b) b]
      [(? number? n) n]
      [(? string? s) s]
      [`',quoted-thing expr])))

(module+ test
  (check-equal? (with-freshening (substs '(x y) '(1 2) '(#%app + x y 3)))
                '(#%app + 1 2 3)))

(define (get-external-dependencies exp)
  (define dependents-that-need-data/enumerate
    '(string-or-integer-out
      string-or-integer-in
      string-out
      string-in))
  (define dependents
    (append dependents-that-need-data/enumerate
            '(to-integer
              improper-list->proper-list
              proper-list->improper-list)))
  (define data/enumerate? #f)
  (define dep-fns
    (filter
     values
     (for/list ([dependent (in-list dependents)])
       (cond
         [(has? dependent exp)
          (when (member dependent dependents-that-need-data/enumerate)
            (set! data/enumerate? #t))
          (fetch-dependent dependent)]
         [else #f]))))
  (cond
    [data/enumerate? (cons `(require data/enumerate/lib) dep-fns)]
    [else dep-fns]))

(define-runtime-path convert-it.rkt '(lib "convert-it.rkt" "concolic-hop"))
(define (fetch-dependent which-one)
  (call-with-input-file convert-it.rkt
    (λ (port)
      (let loop ()
        (define l (read-line port))
        (when (eof-object? l) (error 'fetch-dependent "didn't find lang line"))
        (unless (regexp-match? #rx"#lang" l) (loop)))
      (let loop ()
        (define exp (read port))
        (match exp
          [`(define (,(? symbol? s) ,x ...) ,body ...)
           #:when (equal? s which-one)
           (let loop ([exp exp])
             (match exp
               [`(get-current-concrete-value ,e) (loop e)]
               [(? list?) (map loop exp)]
               [_ exp]))]
          [(? eof-object?) (error 'fetch-dependent "didn't find definition of ~s" which-one)]
          [_ (loop)])))))
  
(module+ test
  (check-equal? (with-freshening
                    (inline-convert-it `(λ (x) (λ (y) (+ x y)))
                                       #`(->s integer integer integer)))
                '(λ (✌0 ✌1) (#%app + ✌0 ✌1)))

  (check-equal? (with-freshening
                    (inline-convert-it `(cons 1 (cons 2 null))
                                       #`(cons/s integer integer)))
                '(#%app cons 1 2))

  (check-equal? (with-freshening
                    (inline-convert-it `(λ (x45) (error "ASSERT_UNREACHABLE"))
                                       #'(or/s (->s integer integer)
                                               (list-of integer)
                                               integer
                                               boolean)))
                `(λ (✌0) (#%app error "ASSERT_UNREACHABLE")))
  
  (check-equal? (with-freshening
                    (inline-convert-it
                     `X
                     #'(list-of
                        (->s integer integer))))
                 '(#%app map (λ (✌0) (λ (✌1) (#%app ✌0 ✌1))) X))

  (check-equal? (with-freshening
                    (inline-convert-it
                     `(cons 0 (cons #f null))
                     #'(->si
                        ((msg (one-of/c "hd" "tl")))
                        (res
                         (msg)
                         (cond
                           ((equal? msg "hd") integer)
                           (else boolean))))))

                '(λ (✌0)
                   (if (#%app equal? ✌0 "hd")
                       0
                       (if (#%app equal? ✌0 "tl") #f
                           (#%app error "unknown message: ~s" ✌0)))))

  (check-equal? (with-freshening
                    (inline-convert-it
                     `(λ (x) 42)
                     #'(->s integer)))
                `(λ () 42))

  (check-equal? (with-freshening
                    (inline-convert-it
                     `(λ (x) x)
                     #'(->s (or/s (->s integer integer)
                                  (list-of integer)
                                  integer
                                  boolean)
                            (or/s (->s integer integer)
                                  (list-of integer)
                                  integer
                                  boolean))))
                 '(λ (✌0) ✌0))

  (check-equal? (with-freshening
                    (inline-convert-it
                     `(λ (x) x)
                     #'(->s string/s string/s)))
                 '(λ (✌0) ✌0))

  (check-equal? (with-freshening
                    (inline-convert-it
                     `(λ (x) x)
                     #'(->s string-or-integer/s string-or-integer/s)))
                 '(λ (✌0) ✌0))

  (check-equal? (with-freshening
                    (inline-convert-it
                     `0
                     #'string-or-integer/s))
                "a")

  (check-equal? (with-freshening
                    (inline-convert-it
                     `0
                     #'lump/s
                     #:lumps (list "x")))
                "x")

  (check-equal? (with-freshening
                    (inline-convert-it
                     `1
                     #'lump/s
                     #:lumps (list "x" "y")))
                "y")

  (check-equal? (with-freshening
                    (inline-convert-it
                     `1
                     #'lump/s
                     #:lumps (list ''p ''q)))
                ''q)

  (check-equal? (with-freshening
                    (inline-convert-it
                     '(cons 0 (cons 1 (cons 1 (cons 1 null))))
                     '(or/s (->s (list/s integer integer integer integer)
                                 (list/s integer integer integer integer))
                            (list/s integer integer integer integer)
                            boolean)
                     #:needs-exposed-arithmetic? #t))
                (sqrt -1))

  (check-equal? (with-freshening
                    (inline-convert-it
                     '(λ (x0) (error "ASSERT_UNREACHABLE"))
                     '(->s string/s string/s string/s)))
                '(λ (✌0 ✌1) (#%app error "ASSERT_UNREACHABLE")))

  (check-equal? (with-freshening
                    (inline-convert-it
                     `(λ (✌0)
                        (let ((✌1 (✌0 0)))
                          (error "ASSERT_UNREACHABLE")))
                     '(->s (->s integer integer) integer)))
                '(λ (✌0) (#%app ✌0 0)))

  (check-equal?
   (with-freshening
       (inline-convert-it
        `(λ (x)
           (let ((✌1 (car x)))
             (let ((✌2 (cdr x)))
               (if (equal? 0 (error "ASSERT_UNREACHABLE"))
                   'x
                   (if (equal? 1 (error "ASSERT_UNREACHABLE"))
                       'y
                       (if (equal? 2 (error "ASSERT_UNREACHABLE"))
                           'z
                           (error 'lump "out: ~s" (error "ASSERT_UNREACHABLE"))))))))
        `(->s (cons/s integer integer) lump/s)
        #:contract `(-> pair? any)))
   `(λ (✌0)
      (#%app error "ASSERT_UNREACHABLE")))

  )
