#lang racket
(require "env.rkt" "emit.rkt" "misc.rkt" "type.rkt")
(module+ test (require rackunit))

(provide
 (contract-out
  [convert-expression (-> sexp/c env/c (or/c #f sexp/c) sexp/c)]
  [emit-tl (-> sexp/c env/c void?)]))

(define (emit-tl tl env)
  (match tl
    [`(provide/contract ,clauses ...)
     (define (emit-a-define-id-with-ctc env name)
       (define contract (env-lookup-has-ctc env name))
       (define concolic-input? (not (env-is-tl-name? env name)))
       (tl-emit
        `(define-id-with-ctc
           ,contract
           ,(add-underscore-prefix env name)
           ,name
           ,(if concolic-input? 'bad-input 'bug) ;; positive
           bug   ;; negative
           )))
     (for ([clause (in-list clauses)])
       (match clause
         [`[,name ,ctc]
          (unless (env-lookup-is-ctc env name)
            ;; when the name is a contract, it is already defined without the
            ;; underscore so we don't emit a second definition here
            (emit-a-define-id-with-ctc env name))]
         [`(struct ,struct ([,fld-names ,_] ...))
          (define constructor
            (cond
              [(env-is-tl-name? env (string->symbol (~a "make-" struct)))
               (string->symbol (~a "make-" struct))]
              [else
               struct]))
          (emit-a-define-id-with-ctc env constructor)
          (emit-a-define-id-with-ctc env (string->symbol (~a struct "?")))
          (for ([fld-name (in-list fld-names)])
            (emit-a-define-id-with-ctc env (string->symbol (~a struct "-" fld-name))))]))]
    [`(provide ,names ...)
     (emit-tl `(provide/contract ,@(for/list ([name (in-list names)])
                                     `[,name any/c]))
              env)]
    [`(define ,header ,bodies ...)
     (define converted-bodies (add-underscores-everywhere env bodies))
     (define res-ctc
       ;; this assumes that the contract matches the definition
       ;; which is okay here because, if it isn't, this will
       ;; be a bug, which gets caught elsewhere
       ;; this gets used only to determine the input type
       (match (env-lookup-has-ctc env (header->tl-name header))
         [`(-> ,dom ... ,rng) rng]
         [`(->i ([,x1 ,dom])
                (res (,x2) ,rng)) rng]
         [ctc
          ;; if there is no contract then we
          ;; allow a dot in the body to be anything
          `any/c]))
     (define last (- (length bodies) 1))
     (tl-emit
      `(define ,(add-underscores-everywhere env header)
         ,@(for/list ([body (in-list converted-bodies)]
                      [i (in-naturals)])
             (convert-expression body
                                 env
                                 (and (= i last) res-ctc)))))]
    [`(define-ctc ,header ,bodies ...)
     (define converted-bodies (add-underscores-everywhere env bodies))
     (tl-emit
      `(define-ctc ,header
         ,@(for/list ([body (in-list converted-bodies)]
                      [i (in-naturals)])
             (convert-expression body
                                 env
                                 #f))))]
    [`(require ,mods ...)
     (define (local-mod? mod)
       (match mod
         [`',_ #t]
         [`(submod ".." ,_) #t]
         [_ #f]))
     (define non-local-mods
       (for/list ([mod (in-list mods)]
                  #:unless (local-mod? mod))
         mod))
     (unless (null? non-local-mods)
       (require-emit `(require ,@non-local-mods)))]
    [`(,(and ds (or 'define-struct 'struct)) ,s (,flds ...))
     (tl-emit `(,ds ,(add-underscore-prefix env s) (,@flds)))]
    [`(struct . ,_) (error 'tl-emit "cannot handle struct: ~s" tl)]
    [_
     (tl-emit (convert-expression tl env 'dont-care/c))]))

(module+ test
  (let ()
    (define tl-emits (box '()))
    (define tl-inputs (box '()))
    (define tl-requires (box '()))
    (define tl-lumps (box '()))
    (with-containers (tl-emits tl-inputs tl-requires tl-lumps)
      (emit-tl `(define (f x) (f x))
               (env-extend-tl-definition (new-env) 'f '(define f (λ (x) x))))
      (check-equal?
       (unbox tl-emits)
       (list `(define (_f x) (_f x))))))

  (let ()
    (define tl-emits (box '()))
    (define tl-inputs (box '()))
    (define tl-requires (box '()))
    (define tl-lumps (box '()))
    (with-containers (tl-emits tl-inputs tl-requires tl-lumps)
      (emit-tl `(define (f x) (f x)) (new-env))
      (check-equal?
       (unbox tl-emits)
       (list `(define (f x) (f x))))))

  (let ()
    (define tl-emits (box '()))
    (define tl-inputs (box '()))
    (define tl-requires (box '()))
    (define tl-lumps (box '()))
    (with-containers (tl-emits tl-inputs tl-requires tl-lumps)
      (emit-tl `(require 2htdp/image) (new-env))
      (check-equal?
       (unbox tl-requires)
       (list `(require 2htdp/image)))))

  (let ()
    (define tl-emits (box '()))
    (define tl-inputs (box '()))
    (define tl-requires (box '()))
    (define tl-lumps (box '()))
    (with-containers (tl-emits tl-inputs tl-requires tl-lumps)
      (emit-tl `(require 'x 2htdp/image 'y) (new-env))
      (emit-tl `(require 'x 'y (submod ".." math)) (new-env))
      (check-equal?
       (unbox tl-requires)
       (list `(require 2htdp/image)))))

  (let ()
    (define tl-emits (box '()))
    (define tl-inputs (box '()))
    (define tl-requires (box '()))
    (define tl-lumps (box '()))
    (with-containers (tl-emits tl-inputs tl-requires tl-lumps)
      (emit-tl `(provide/contract [x integer?])
               (extend-has-ctc (new-env) 'x #f 'integer?))
      (check-equal?
       (unbox tl-emits)
       (list `(define-id-with-ctc integer? _x x bad-input bug)))))

  (let ()
    (define tl-emits (box '()))
    (define tl-inputs (box '()))
    (define tl-requires (box '()))
    (define tl-lumps (box '()))
    (with-containers (tl-emits tl-inputs tl-requires tl-lumps)
      (emit-tl `(provide/contract [x integer?])
               (env-extend-tl-definition
                (extend-has-ctc (new-env) 'x #f 'integer?)
                'x
                '(define x 1)))
      (check-equal?
       (unbox tl-emits)
       (list `(define-id-with-ctc integer? _x x bug bug))))))

(define (add-underscores-everywhere env exp)
  (let loop ([exp exp])
    (cond
      [(pair? exp)
       (cons (loop (car exp)) (loop (cdr exp)))]
      [(and (symbol? exp)
            (env-is-tl-name? env exp))
       (add-underscore-prefix env exp)]
      [else exp])))

;; required-type : (or/c #f T/c)
(define/contract (convert-expression exp env required-type)
  (-> sexp/c env/c (or/c #f sexp/c) sexp/c)
  (let loop ([exp exp]
             [required-type required-type]
             [function-we-are-calling #f]
             [amb-context #f])
    (match exp
      [`(• ,(? symbol? id))
       (define ctc (env-lookup-has-ctc env id))
       (unless ctc
         (error 'emit-expression
                (string-append
                 '"found • in the function position of an"
                 " application but don't know the type of the argument")))
       (unless required-type
         (error 'convert-expression "found • but don't know the type.3"))
       (define dot-type `(-> ,ctc ,required-type))
       (define T/s (convert-contract-to-s env dot-type))
       (define complex-T/s (adjust-for-complex T/s))
       (define modname (env-lookup-has-ctc-moname env id))
       (define input-exp
         (string->symbol
          (if amb-context
              (~a "B" (~s (list amb-context id modname complex-T/s dot-type)))
              (let ([dot-index (next-dot)]) ;; need to call this only if we generate a dot variable
                (~a '• (~s (list dot-index complex-T/s dot-type)))))))
       `(,(ctc+convert-wrappers input-exp dot-type T/s complex-T/s
                                (string->symbol (~a "wrap " id)))
         ,id)]
      [`(amb) (error 'convert-expression "nullary amb is not okay")]
      [`(amb ,e1 ,es ...)
       (when amb-context (error 'exp.rkt "cannot handle nested `amb`s"))
       (input-emit 'integer 'Amb)
       `(cond
          ,@(let amb-loop ([e1 e1]
                           [es es]
                           [i 0])
              (cond
                [(null? es) (list `[else ,(loop e1 required-type function-we-are-calling i)])]
                [else (cons `[(= Amb ,i) ,(loop e1 required-type function-we-are-calling i)]
                            (amb-loop (car es) (cdr es) (+ i 1)))])))]
      [`(,(? symbol? s) ,arg-exps ...)
       (cond
         [(equal? s `•) (error 'emit-expression "found • but don't know the type.1")]
         [(or (env-lookup-has-ctc env s)
              (something-whose-type-we-know s))
          =>
          (λ (function-position-type)
            (define function-position-expression s)
            (generate-call function-position-type
                           function-position-expression
                           arg-exps
                           loop
                           amb-context))]
         [else `(,(loop s #f #f amb-context)
                 ,@(for/list ([exp (in-list arg-exps)])
                     (loop exp #f #f amb-context)))])]
      [`((,(? symbol? f) ,(? symbol? arg)) •)
       (cond
         [(or (equal? f `•) (equal? arg `•))
          (error 'emit-expression "found • but don't know the type.2")]
         [(or (env-lookup-has-ctc env f)
              (something-whose-type-we-know f))
          =>
          (λ (fs-type)
            (define function-position-expression `(,f ,arg))
            (define function-position-type
              (match fs-type
                [`(-> ,dom1 (-> ,dom2 ,rng)) `(-> ,dom2 ,rng)]
                [_
                 (error 'convert-expression
                        "could not deal with fs-type: ~s"
                        function-position-type)]))
            (generate-call
             function-position-type
             function-position-expression
             (list `•)
             loop
             amb-context))]
         [else
          (error 'emit-expression "found • but do not know the type.3")])]
      [(? list?)
       (for/list ([exp (in-list exp)])
         (loop exp #f #f amb-context))]
      [`•
       (unless required-type
         (error 'emit-expression "found • but don't know the type.4"))
       (when amb-context (error 'exp.rkt "cannot handle amb context in this situation"))
       (define T/s (convert-contract-to-s env required-type))
       (define complex-T/s (adjust-for-complex T/s))
       (define dot-index (next-dot))
       (define input-exp (string->symbol (~a '• (~s (list dot-index complex-T/s required-type)))))
       (ctc+convert-wrappers input-exp required-type T/s complex-T/s
                             (if function-we-are-calling
                                 (string->symbol (~a "argument of " function-we-are-calling))
                                 '<<unknown>>))]
      [(? symbol?) exp]
      [(? number?) exp]
      [(? boolean?) exp]
      [(? string?) exp]
      [(? keyword?) exp])))

(define (generate-call function-position-type
                       function-position-expression
                       arg-exps
                       loop
                       amb-context)
  (define doms
    (match function-position-type
      [`(-> ,doms ... ,rng) doms]
      [`(->i ([,ids ,doms] ...) ,rng) doms]
      [_
       (error 'convert-expression
              "found a call to ~s with the contract ~s"
              function-position-expression function-position-type)]))
  (define arg-exps-count (length arg-exps))
  (unless (equal? (length doms) arg-exps-count)
    (error 'convert-expression
           "found a call to ~s with ~s arg~a but the contract doesn't match\n  ctc: ~s~a"
           function-position-expression
           arg-exps-count
           (if (= 1 arg-exps-count) "" "s")
           function-position-type
           (if (= arg-exps-count 0)
               ""
               (for/fold ([s "\n  args:"])
                         ([arg-exp (in-list arg-exps)])
                 (string-append s (format "\n   ~s" arg-exp))))
           ))
  `(,function-position-expression
    ,@(for/list ([exp (in-list arg-exps)]
                 [dom (in-list doms)])
        (loop exp dom function-position-expression amb-context))))

(define (ctc+convert-wrappers input-exp type T/s complex-T/s name)
  (input-emit T/s input-exp)
  `(apply-ctc ,type
              (convert-it ,input-exp ,complex-T/s L
                          ,@(if (use-exposed-arithmetic?)
                                (list '#:arithmetic-coercion-both)
                                (list)))
              bad-input
              no-blame
              ,name))

(module+ test
  (check-equal? (convert-expression `(+ 1 2) (new-env) #f)
                `(+ 1 2))

  (let ()
    (define tl-emits (box '()))
    (define tl-inputs (box '()))
    (define tl-requires (box '()))
    (define tl-lumps (box '()))
    (with-containers (tl-emits tl-inputs tl-requires tl-lumps)
      (define first-X '|•(0 integer integer?)|)
      (check-equal? (convert-expression `• (new-env) 'integer?)
                    `(apply-ctc integer? (convert-it ,first-X integer L)
                                bad-input no-blame
                                <<unknown>>))
      (check-equal? (unbox tl-inputs)
                    `((,first-X integer)))))

  (let ()
    (define tl-emits (box '()))
    (define tl-inputs (box '()))
    (define tl-requires (box '()))
    (define tl-lumps (box '()))
    (with-containers (tl-emits tl-inputs tl-requires tl-lumps)
      (define first-X '|•(0 integer integer?)|)
      (define an-env (extend-has-ctc (new-env) 'f #f `(-> integer? integer?)))
      (check-equal? (convert-expression `(f •) an-env #f)
                    `(f (apply-ctc integer? (convert-it ,first-X integer L)
                                   bad-input no-blame
                                   |argument of f|)))
      (check-equal? (unbox tl-inputs)
                    `((,first-X integer)))))

  (let ()
    (define tl-emits (box '()))
    (define tl-inputs (box '()))
    (define tl-requires (box '()))
    (define tl-lumps (box '()))
    (with-containers (tl-emits tl-inputs tl-requires tl-lumps)
      (define first-X '|•(0 integer integer?)|)
      (define second-X '|•(1 (->s integer integer) (-> integer? integer?))|)
      (define an-env (extend-has-ctc (new-env) 'f #f `(->i ([x integer?] [y (-> integer? integer?)]) integer?)))
      (check-equal? (convert-expression `(f • •) an-env #f)
                    `(f (apply-ctc integer? (convert-it ,first-X integer L)
                                   bad-input no-blame
                                   |argument of f|)
                        (apply-ctc (-> integer? integer?)
                                   (convert-it ,second-X (->s integer integer) L)
                                   bad-input no-blame
                                   |argument of f|)))
      (check-equal? (unbox tl-inputs)
                    `((,second-X (->s integer integer))
                      (,first-X integer)))))

  (let ()
    (define tl-emits (box '()))
    (define tl-inputs (box '()))
    (define tl-requires (box '()))
    (define tl-lumps (box '()))
    (with-containers (tl-emits tl-inputs tl-requires tl-lumps)
      (define first-X '|•(0 (->s (->s integer integer) integer) (-> (-> integer? integer?) integer?))|)
      (define an-env (extend-has-ctc (new-env) 'f #f `(-> integer? integer?)))
      (check-equal? (convert-expression `(• f) an-env 'integer?)
                    `((apply-ctc (-> (-> integer? integer?) integer?)
                                 (convert-it ,first-X (->s (->s integer integer) integer) L)
                                 bad-input no-blame
                                 |wrap f|)
                      f))
      (check-equal? (unbox tl-inputs)
                    `((,first-X (->s (->s integer integer) integer))))))

  (let ()
    (define tl-emits (box '()))
    (define tl-inputs (box '()))
    (define tl-requires (box '()))
    (define tl-lumps (box '()))
    (with-containers (tl-emits tl-inputs tl-requires tl-lumps)
      (define first-X '|•(0 (->s (->s integer integer integer integer) integer) (-> (-> integer? integer? integer? integer?) integer?))|)
      (define an-env (extend-has-ctc (new-env) 'f #f `(-> integer? integer? integer? integer?)))
      (check-equal? (convert-expression `(• f) an-env 'integer?)
                    `((apply-ctc (-> (-> integer? integer? integer? integer?) integer?)
                                 (convert-it ,first-X (->s (->s integer integer integer integer) integer) L)
                                 bad-input
                                 no-blame
                                 |wrap f|)
                      f))
      (check-equal? (unbox tl-inputs)
                    `((,first-X (->s (->s integer (->s integer (->s integer integer))) integer))))))

  (let ()
    (define tl-emits (box '()))
    (define tl-inputs (box '()))
    (define tl-requires (box '()))
    (define tl-lumps (box '()))
    (with-containers (tl-emits tl-inputs tl-requires tl-lumps)
      (define fst-X '•)
      (define an-env (extend-has-ctc
                      (new-env)
                      'f #f
                      `(-> integer? integer?)))
      (check-true
       (match (convert-expression `(amb (• f)) an-env 'integer?)
         [`(cond
             [else
              ((apply-ctc (-> (-> integer? integer?) integer?)
                          (convert-it ,_
                                      (->s (->s integer integer) integer)
                                      L)
                          bad-input
                          no-blame
                          |wrap f|)
               f)])
          #t]
         [wrong-answer
          (eprintf "failed:\n")
          (pretty-write wrong-answer (current-error-port))
          #f]))
      (check-equal? (map cadr (unbox tl-inputs))
                    (list `(->s (->s integer integer) integer)
                          `integer))))

  (let ()
    (define tl-emits (box '()))
    (define tl-inputs (box '()))
    (define tl-requires (box '()))
    (define tl-lumps (box '()))
    (with-containers (tl-emits tl-inputs tl-requires tl-lumps)
      (define an-env (extend-has-ctc
                      (extend-has-ctc
                       (new-env)
                       'g #f `(-> integer? integer?))
                      'f #f `(-> (-> integer? integer?) integer?)))
      (check-equal? (convert-expression `(amb (f 1) (g 2)) an-env 'integer?)
                    `(cond
                       [(= Amb 0) (f 1)]
                       [else (g 2)]))
      (check-equal? (unbox tl-inputs)
                    `((Amb integer)))))

  (let ()
    (define tl-emits (box '()))
    (define tl-inputs (box '()))
    (define tl-requires (box '()))
    (define tl-lumps (box '()))
    (with-containers (tl-emits tl-inputs tl-requires tl-lumps)
      (define an-env (extend-has-ctc
                      (extend-has-ctc
                       (extend-has-ctc
                        (new-env)
                        'h #f `(-> integer? integer?))
                       'g #f `(-> integer? integer?))
                      'f #f `(-> (-> integer? integer?) integer?)))
      (check-equal? (convert-expression `(amb (f 4) (g 5) (h 6)) an-env 'integer?)
                    `(cond
                       [(= Amb 0)
                        (f 4)]
                       [(= Amb 1)
                        (g 5)]
                       [else
                        (h 6)]))
      (check-equal? (unbox tl-inputs)
                    `((Amb integer))))))

(define (add-underscore-prefix env name)
  (define str (~a name))
  (cond
    [(and (env-is-constructor-name? env name)
          (regexp-match? #rx"^make-" str))
     (string->symbol
      (regexp-replace #rx"^make-" name "make-_"))]
    [else
     (string->symbol (string-append "_" str))]))

(define (op-to-convert-to-complex? id)
  (member id '(+ * / reciprocal abs min max sqrt <= >= zero? real? number?
                 from-concolic-number)))

(define (something-whose-type-we-know s)
  (case s
    [(cons) `(-> any/c any/c (cons/c any/c any/c))]
    [else #f]))
