#lang racket
(require "env.rkt" "emit.rkt" "exp.rkt" "misc.rkt" "type.rkt")
(module+ test (require rackunit))

(provide
 (contract-out
  [only-modules? (-> (listof sexp/c) boolean?)]
  [convert-mod (-> sexp/c env/c env/c)]))


(define (only-modules? inputs)
  (for/and ([input (in-list inputs)])
    (match input
      [`(module ,_ ...) #t]
      [_ #f])))

(define (convert-mod mod env)
  (define env-with-ctc-references (add-contract-references mod env))
  (define-values (no-ctc-mod env-with-ctc) (extract-contract-definitions mod env-with-ctc-references))
  (match no-ctc-mod
    [`(module ,modname racket
        ,full-tl ...)
     (define tl (normalize-provides full-tl))
     (define extended-env (extend-with-provides tl env-with-ctc modname))
     (define this-modules-env (extend-with-tl tl extended-env))

     ;; treat functions that have contracts but no definition
     ;; as inputs that the concolic tester can supply
     (define provided-names (get-provided-names tl))
     (for ([name (in-list provided-names)]
           #:unless (env-is-tl-name? this-modules-env name)
           #:unless (env-is-contract-name? this-modules-env name))
       (define the-contract (env-lookup-has-ctc this-modules-env name))
       (define T/s (convert-contract-to-s this-modules-env the-contract))
       (define complex-T/s (adjust-for-complex T/s))
       (define input-exp (string->symbol (~a "M" (~s (list modname name complex-T/s the-contract)))))
       (input-emit T/s input-exp)
       (tl-emit `(define ,(string->symbol (~a "_" name))
                   (convert-it ,input-exp ,complex-T/s L
                               ,@(if (use-exposed-arithmetic?)
                                     (list '#:arithmetic-coercion-both)
                                     (list))))))

     (for ([tl (in-list (move-provides-to-the-end tl))])
       (emit-tl tl this-modules-env))

     ;; carry forward the definitions of names that are provided
     ;; and the structs
     (for/fold ([env (env-transfer-struct-names this-modules-env extended-env)])
               ([provided-name (in-list provided-names)])
       (define definition (env-lookup-defn this-modules-env provided-name))
       (cond
         [definition
           (env-extend-provided-definition
            env
            provided-name
            definition)]
         [else env]))]
    [_ (emit-tl mod env-with-ctc)
       env-with-ctc]))

(module+ test
  (let ()
    (define tl-emits (box '()))
    (define tl-inputs (box '()))
    (define tl-requires (box '()))
    (define tl-lumps (box '()))
    (with-containers (tl-emits tl-inputs tl-requires tl-lumps)
      (define e0 (new-env))
      (define e1
        (convert-mod `(module m racket
                        (provide c)
                        (define c (-> integer? integer?)))
                     e0))
      (define e2
        (convert-mod `(module n racket
                        (require (submod ".." m))
                        (provide/contract [f (-> c c)])
                        (define (f x) x))
                     e1))

      (check-equal? e2
                    (env-extend-contract-reference
                     (env-extend-provided-definition
                      (extend-has-ctc
                       (extend-is-ctc
                        (new-env)
                        'c '(-> integer? integer?))
                       'f 'n '(-> c c))
                      'f '(define (f x) x))
                     'c))
      (check-equal? (apply set (unbox tl-emits))
                    (set '(define-id-with-ctc (-> c c) _f f bug bug)
                         '(define (_f x) x)
                         '(define-ctc c (-> integer? integer?)))))))

(define (add-contract-references mod env)
  (match mod
    [`(module ,module-name ,module-lang ,mod-bodies ...)
     (for/fold ([env env])
               ;; we end up normalizing the provides twice :(
               ([body (in-list (normalize-provides mod-bodies))])
       (match body
         [`(provide/contract [,(? symbol?) ,ctc])
          (extend-env-with-contract-references env ctc)]
         [`(provide/contract (struct ,s ((,(? symbol?) ,ctcs) ...)))
          (for/fold ([env env])
                    ([ctc (in-list ctcs)])
            (extend-env-with-contract-references env ctc))]
         [`(provide/contract . ,_)
          (error 'add-contract-references "unexpected provide/contract form\n  ~s" body)]
         [_ env]))]
    [_ env]))

;; this is definitely an overapproximation ....
(define (extend-env-with-contract-references env ctc)
  (let loop ([ctc ctc])
    (match ctc
      [`(-> ,args ...)
       (for ([arg (in-list args)])
         (loop arg))]
      [`(and/c ,args ...)
       (for ([arg (in-list args)])
         (loop arg))]
      [`(or/c ,args ...)
       (for ([arg (in-list args)])
         (loop arg))]
      [`(>/c ,x) (void)]
      [`(>=/c ,x) (void)]
      [`(</c ,x) (void)]
      [`(<=/c ,x) (void)]
      [`(=/c ,x) (void)]
      [`(listof ,x) (loop x)]
      [`(non-empty-listof ,x) (loop x)]
      [`(->i ((,(? symbol?) ,arg-ctcs) ...)
             (,(? symbol?) (,(? symbol?) ...)
                           ,rng-ctc))
       (for ([arg-ctc (in-list arg-ctcs)]) (loop arg-ctc))
       (loop rng-ctc)]
      [`(λ (,x) ,e ...) (void)]
      [`(one-of/c ,stuff ...) (void)]
      [`(not/c ,ctc) (loop ctc)]
      [`(cons/c ,x ,y) (loop x) (loop y)]
      [(? symbol?)
       (set! env (env-extend-contract-reference env ctc))]))
  env)


(define (extract-contract-definitions mod initial-env)
  (match mod
    [`(module ,module-name ,module-lang ,mod-bodies ...)
     (define-values (is-ctc-env reversed-new-bodies provides-to-remove)
       (for/fold ([env initial-env]
                  [reversed-bodies '()]
                  [provides-to-remove (set)])
                 ([body (in-list mod-bodies)])
         (match body
           [`(define ,header ,ctc)
            #:when (or (looks-like-contract? ctc)
                       (env-is-contract-reference? env (header->tl-name header)))
            (match (header-expand-lambda body)
              [`(define ,x ,ctc)
               (values (extend-is-ctc env x ctc)
                       (cons `(define-ctc ,x ,ctc) reversed-bodies)
                       (set-add provides-to-remove x))])]
           [_ (values env
                      (cons body reversed-bodies)
                      provides-to-remove)])))
     (values `(module ,module-name ,module-lang
                ,@(remove-provides provides-to-remove
                                   (reverse reversed-new-bodies)))
             is-ctc-env)]
    [_ (values mod initial-env)]))

(module+ test
  (check-equal?
   (call-with-values
    (λ ()
      (extract-contract-definitions
       `(module m racket
          (define x (-> integer? integer?)))
       (new-env)))
    list)
   (list `(module m racket (define-ctc x (-> integer? integer?)))
         (extend-is-ctc (new-env) 'x '(-> integer? integer?))))

  (check-equal?
   (call-with-values
    (λ ()
      (extract-contract-definitions
       `(module m racket
          (define x (-> integer? x)))
       (new-env)))
    list)
   (list `(module m racket (define-ctc x (-> integer? x)))
         (extend-is-ctc (new-env) 'x '(-> integer? x)))))

(define (looks-like-contract? sexp)
  (match sexp
    [`(-> ,_ ...) #t]
    [`(->i ,_ ...) #t]
    [`(and/c ,_ ...) #t]
    [`integer? #t]
    [`(one-of/c ,_ ...) #t]
    [`(or/c ,_ ...) #t]
    [`(struct/c ,_ ...) #t]
    [_ #f]))

(define (remove-provides provides-to-remove bodies)
  (for/list ([body (in-list bodies)])
    (match body
      [`(provide ,ids ...)
       `(provide ,@(for/list ([id (in-list ids)]
                              #:unless (set-member? provides-to-remove id))
                     id))]
      [`(provide/contract [,ids ,ctcs] ...)
       `(provide/contract ,@(for/list ([id (in-list ids)]
                                       [ctc (in-list ctcs)]
                                       #:unless (set-member? provides-to-remove id))
                              `[,id ,ctc]))]
      [_ body])))

(define (extend-with-tl tls env)
  (for ([tl (in-list tls)])
    (match tl
      [`(provide/contract ,_ ...) '()]
      [`(provide ,_ ...) '()]
      [`(require ,_ ...) '()]

      ;; we don't count contracts as `tl` names
      ;; because this way we just leave them alone
      ;; (no underscores get added)
      [`(define-ctc ,x ,ctc)
       '()]
      [`(,(or 'struct 'define-struct) ,s (,flds ...))
       (set! env (env-extend-struct-names env tl))]
      [`(define ,header ,_ ...)
       (set! env (env-extend-tl-definition env (header->tl-name header) tl))]))
  env)

(define (move-provides-to-the-end tls)
  (define-values (provides others) (partition provide? tls))
  (append others provides))

(define/contract (extend-with-provides tls env modname)
  (-> sexp/c env/c symbol? env/c)
  (define-values (provides others) (partition provide? tls))
  (for/fold ([env env])
            ([provide (in-list provides)])
    (match provide
      [`(provide/contract ,provide)
       (match provide
         [`(,(? symbol? name) ,ctc)
          (extend-has-ctc env name modname ctc)]
         [`(struct ,name ((,(? symbol? flds) ,fld-ctcs) ...))
          ;; only add the parts of the contracts that
          ;; can signal blame outside the module
          (define predicate (string->symbol (~a name "?")))
          (define env-with-predicate-and-constructor
            (extend-has-ctc
             (extend-has-ctc
              env
              predicate modname `any/c)
             name
             modname
             `(-> ,@fld-ctcs any/c)))
          (for/fold ([env env-with-predicate-and-constructor])
                    ([fld (in-list flds)]
                     [fld-ctc (in-list fld-ctcs)])
            (extend-has-ctc
             env
             (string->symbol (~a name "-" fld))
             modname
             `(-> ,predicate any/c)))])]
      [`(provide ,(? symbol? name))
       (extend-has-ctc env name modname 'any/c)])))

(define (provide? tl)
  (match tl
    [`(provide/contract ,_ ...) #t]
    [`(provide ,_ ...) #t]
    [_ #f]))

(define (normalize-provides provides)
  (let loop ([provides provides])
    (match provides
      [`() `()]
      [(cons `(provide/contract ,first-thing ,more-inside ...) more-outside)
       (cons `(provide/contract ,first-thing)
             (loop (cons `(provide/contract ,@more-inside) more-outside)))]
      [(cons `(provide/contract) more-outside)
       (loop more-outside)]
      [(cons `(provide (contract-out ,first-thing ,more1 ...) ,more2 ...) more3)
       (cons `(provide/contract ,first-thing)
             (loop (cons `(provide (contract-out ,@more1) ,@more2) more3)))]
      [(cons `(provide (contract-out) ,more1 ...) more2)
       (loop (cons `(provide ,@more1) more2))]
      [(cons `(provide ,(? symbol? s) ,more1 ...) more2)
       (cons `(provide ,s) (loop (cons `(provide ,@more1) more2)))]
      [(cons `(provide) more)
       (loop more)]
      [(cons something-else more)
       (cons something-else (loop more))])))
(module+ test
  (check-equal?
   (normalize-provides
    (list `(provide (contract-out [f (-> integer? integer?)]
                                  [x integer?])
                    p
                    q)
          `(provide/contract [g (-> integer? integer?)] [y integer?])))
   (list `(provide/contract [f (-> integer? integer?)])
         `(provide/contract [x integer?])
         `(provide p)
         `(provide q)
         `(provide/contract [g (-> integer? integer?)])
         `(provide/contract [y integer?])))
  (check-equal?
   (normalize-provides
    (list `(define x 1)
          `(provide x)))
   (list `(define x 1)
         `(provide x))))

(define (get-provided-names tls)
  (apply
   append
   (for/list ([tl (in-list tls)])
     (match tl
       [`(provide/contract [,names ,_] ...) names]
       [`(provide ,names ...) names]
       [_ '()]))))
