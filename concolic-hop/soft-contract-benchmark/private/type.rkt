#lang racket
(require "env.rkt" "emit.rkt" "misc.rkt")
(module+ test (require rackunit))

(provide
 (contract-out
  [convert-contract-to-s
   (-> env/c sexp/c T/c)]))

(define (convert-contract-to-s env ctc)
  (define (recursive-contract-name? name)
    (and (symbol? name)
         (env-in-is-domain? env name)))
  (define (predicates-definition-is-visible? name)
    (cond
      [(symbol? name)
       (match (env-lookup-defn env name)
         [`(define (,(? symbol?) ,arg) ,body) #t]
         [_ #f])]
      [else #f]))
  (define (struct-predicate? name)
    (and (symbol? name)
         (env-is-predicate-name? env name)))
  (tidy-nested-or/s
  (let loop ([ctc ctc]
             ;; one to look up things and then
             ;; `number-of-times-to-unroll` more to unroll
             [depth (+ number-of-times-to-unroll 1)])
    (match ctc
      [(? recursive-contract-name?)
       ;; unroll contract lookups
       (if (= depth 0)
           `none/s
           (loop (env-lookup-is-ctc env ctc) (- depth 1)))]
      [`any/c `any/s]
      [`dont-care/c `dont-care/s]
      [`(recursive-contract ,(? symbol? s) #:chaperone) (loop s depth)]
      [`(not/c false?) (loop `any/c depth)]
      [`integer? `integer]
      [`real? `integer]
      [`positive? `integer]
      [`number? `integer]
      [`zero? `integer]
      [`prime? `integer]
      [`(λ (,x) (,(? predicate-name? p?) ,x))
       (loop p? depth)]
      [(? predicates-definition-is-visible?)
       (=> fail)
       (or (predicate->contract env ctc) (fail))]
      [(? struct-predicate?)
       (define selectors (env-predicate-name->selectors env ctc))
       ;; we put an underscore at the start of the struct name as
       ;; the use of the predicate seems like it should count as
       ;; the struct is "inside" the module
       (loop `(struct/c ,(string->symbol (~a "_" (regexp-replace #rx"[?]$" (~s ctc) "")))
                        ,@(for/list ([_ (in-list selectors)])
                            `any/c))
             depth)]
      [`(and/c integer? (=/c ,_)) `integer]
      [`(one-of/c ,(? number?) ...) `integer]
      [`(one-of/c ',(? symbol? ss) ...)
       (for ([s (in-list ss)])
         (lump-emit `',s))
       `lump/s]
      [`(one-of/c ,(? string? ss) ...)
       (for ([s (in-list ss)])
         (lump-emit s))
       `lump/s]
      [`(or/c ,(? string? ss) ...)
       (for ([s (in-list ss)])
         (lump-emit s))
       `lump/s]
      [`(or/c empty? (and/c (non-empty-listof ,t) ,_))
       `(list-of ,(loop t depth))]
      [`(or/c string? integer?) `string-or-integer/s]
      [`(or/c integer? string?) `string-or-integer/s]

      [`(or/c ,ts ...)
       (define without-zero-unrolls
         (cond
           ;; when we are at the last depth, we
           ;; drop any recursive references in the or/c,
           ;; thereby forcing other choices
           [(zero? depth)
            (for/list ([t (in-list ts)]
                       #:unless (recursive-contract-name? t))
              t)]
           [else ts]))
       (cond
         [(null? without-zero-unrolls)
          ;; but if there are no other choices, then
          ;; go back to none
          `none/s]
         [else
          `(or/s ,@(for/list ([t (in-list without-zero-unrolls)])
                     (loop t depth)))])]

      ;; approximate symbols with just 'x 'y and 'z
      [`symbol?
       (loop `(one-of/c 'x 'y 'z) depth)]
      [`string? `string/s]
      [`false? `boolean]
      [`boolean? `boolean]
      [`(struct/c ,struct-name ,Ts ...)
       `(struct/s ,struct-name
                  ,@(for/list ([T (in-list Ts)])
                      (loop T depth)))]
      [`(-> ,doms ... ,rng)
       `(->s ,@(for/list ([dom (in-list doms)])
                 (loop dom depth))
             ,(loop rng depth))]

      ;; this case is special handling for the object
      ;; encoding that zombie.sch and get-path.sch
      [`(->i ([,x1s (,(or `one-of/c `or/c) ,doms ...)])
             (res (,x2)
                  (cond
                    [(equal? ,x3s ,msgs) ,rngs] ...
                    [else ,ctc])))

       ;; emit the method names as lumps, just in case
       ;; the concolic tester ends up needing to call
       ;; methods at some point
       (for ([dom (in-list doms)])
         (match dom
           [`',(? symbol? s) (lump-emit `',s)]
           [(? string? s) (lump-emit s)]))

       `(->si ([,x1s (one-of/c ,@doms)])
              (res (,x2)
                   (cond
                     ,@(for/list ([x3 (in-list x3s)]
                                  [msg (in-list msgs)]
                                  [rng (in-list rngs)])
                         `[(equal? ,x3 ,msg) ,(loop rng depth)])
                     [else ,(if (equal? ctc "error")
                                "error"
                                (loop ctc depth))])))]

      ;; this looks like a one-method object so
      ;; add the `cond` in and try again
      [`(->i ([,x1s (,(or `one-of/c `or/c) ,dom)])
             (res (,x2)
                  ,rng))
       (loop `(->i ([,x1s (or/c ,dom)])
                   (res (,x2)
                        (cond [else ,rng])))
             depth)]

      ;; here we just drop the dependent information in dependent contracts
      [`(->i ([,x1s ,doms] ...) (res (,x2s ...) ,rng))
       (loop `(-> ,@doms ,rng) depth)]
      [`(and/c (-> ,doms ... ,rng)
               (λ (,y) ,stuff-we-ignore))
       (loop `(-> ,@doms ,rng) depth)]
      [`(and/c (non-empty-listof ,t) ,(? predicate-name? p))
       (loop `(non-empty-listof ,t) depth)]

      [`(listof ,t) `(list-of ,(loop t depth))]
      [`(non-empty-listof ,t) `(list-of ,(loop t depth))]
      [`empty? (loop `(listof any/c) depth)]
      [`cons? (loop `(cons/c any/c any/c) depth)]
      [`(cons/c ,t1 ,t2) `(cons/s ,(loop t1 depth) ,(loop t2 depth))]

      [`p? (loop 'any/c depth)]
      
      ;; if we get to any of these at runtime the attempt
      ;; case will just fail and we'll retry....
      [`image? `integer]
      [`image/c `integer]
      ["error" `integer]
      [`(λ (_) #f) `integer] ;; (retrying here is legit)
      ))))
(define number-of-times-to-unroll 2)

(define (predicate-name? x)
  (and (symbol? x) (regexp-match? #rx"[?]$" (symbol->string x))))
(module+ test
  (check-true (predicate-name? 'int?))
  (check-false (predicate-name? 'int?y)))

(define (tidy-nested-or/s t)
  (let loop ([t t])
    (match t
      [`(or/s ,args ...)
       (cond
         [(ormap is-or/s? args)
          (loop `(or/s ,@(flatten-one-layer-or/s args)))]
         [else
          (define adjusted-args
            (for/list ([arg (in-list args)])
              (loop arg)))
          (define w/out-dups (remove-duplicates adjusted-args))
          (cond
            [(null? (cdr w/out-dups))
             (car w/out-dups)]
            [else
             `(or/s ,@w/out-dups)])])]
      [`(,constructor ,args ...)
       `(,constructor ,@(for/list ([arg (in-list args)])
                          (loop arg)))]
      [_ t])))

(define (is-or/s? t)
  (match t
    [`(or/s ,x ...) #t]
    [_ #f]))

(define (flatten-one-layer-or/s ts)
  (let loop ([ts ts])
    (cond
      [(null? ts) '()]
      [else
       (match (car ts)
         [`(or/s ,args ...) (append args (loop (cdr ts)))]
         [_ (cons (car ts) (loop (cdr ts)))])])))

(module+ test

  (check-equal? (tidy-nested-or/s `(-> integer integer)) `(-> integer integer))
  (check-equal? (tidy-nested-or/s `(or/s integer boolean)) `(or/s integer boolean))
  (check-equal? (tidy-nested-or/s `(or/s integer (or/s (list/s integer integer) boolean)))
                `(or/s integer (list/s integer integer) boolean))
  (check-equal? (tidy-nested-or/s `(or/s boolean (or/s (list/s integer integer) boolean)))
                `(or/s boolean (list/s integer integer)))
  (check-equal? (tidy-nested-or/s `(or/s boolean (or/s boolean boolean)))
                `boolean)

  (check-equal?
   (convert-contract-to-s (new-env) `(-> integer? (-> integer? integer?)))
   `(->s integer (->s integer integer)))

  (let ()
    (define tl-emits (box '()))
    (define tl-inputs (box '()))
    (define tl-requires (box '()))
    (define tl-lumps (box '()))
    (with-containers (tl-emits tl-inputs tl-requires tl-lumps)

      (check-equal?
       (convert-contract-to-s (new-env) `(->i ([x (one-of/c 'x 'y)])
                                              (res (x)
                                                   (cond
                                                     [(equal? x 'x) (-> integer? integer?)]
                                                     [(equal? x 'y) (-> integer? integer? integer?)]
                                                     [else "error"]))))
       `(->si ([x (one-of/c 'x 'y)])
              (res (x)
                   (cond
                     [(equal? x 'x) (->s integer integer)]
                     [(equal? x 'y) (->s integer integer integer)]
                     [else "error"]))))

      (check-equal? (unbox tl-lumps) '('y 'x))))

  (check-equal?
   (convert-contract-to-s
    (extend-is-ctc (new-env) 'c `(-> integer? c))
    'c)
   ;; bottom out with none/s
   '(->s integer (->s integer (->s integer none/s))))

  (let ()
    (define tl-emits (box '()))
    (define tl-inputs (box '()))
    (define tl-requires (box '()))
    (define tl-lumps (box '()))
    (with-containers (tl-emits tl-inputs tl-requires tl-lumps)
      (check-equal? (convert-contract-to-s (new-env) `(one-of/c "get-child"))
                    `lump/s)
      (check-equal?
       (reverse (unbox tl-lumps))
       (list "get-child"))))

  (let ()
    (define tl-emits (box '()))
    (define tl-inputs (box '()))
    (define tl-requires (box '()))
    (define tl-lumps (box '()))
    (with-containers (tl-emits tl-inputs tl-requires tl-lumps)
      (check-equal? (convert-contract-to-s (new-env) `(-> (one-of/c 'x 'y 'z) (one-of/c 'a 'b 'c)))
                    `(->s lump/s lump/s))
      (check-equal?
       (reverse (unbox tl-lumps))
       (list `'x `'y `'z `'a `'b `'c))))

  (let ()
    (define tl-emits (box '()))
    (define tl-inputs (box '()))
    (define tl-requires (box '()))
    (define tl-lumps (box '()))
    (with-containers (tl-emits tl-inputs tl-requires tl-lumps)
      (check-equal? (convert-contract-to-s
                     (extend-is-ctc
                      (new-env)
                      `dom/c
                      `(->i ([msg (or/c "get-child")])
                            (res (msg) (integer? . -> . integer?))))
                     `dom/c)
                    `(->si
                      ((msg (one-of/c "get-child")))
                      (res
                       (msg)
                       (cond
                         (else
                          (->s
                           integer
                           integer))))))
      (check-equal? (unbox tl-lumps) '("get-child"))))

  (let ()
    (define tl-emits (box '()))
    (define tl-inputs (box '()))
    (define tl-requires (box '()))
    (define tl-lumps (box '()))
    (with-containers (tl-emits tl-inputs tl-requires tl-lumps)
      (check-equal?
       (convert-contract-to-s
        (extend-is-ctc
         (new-env)
         `T
         `(-> integer? (or/c integer? T)))
        `T)
       '(->s integer
             (or/s integer
                   (->s integer
                        (or/s integer
                              (->s integer
                                   integer))))))))

  (let ()
    (define tl-emits (box '()))
    (define tl-inputs (box '()))
    (define tl-requires (box '()))
    (define tl-lumps (box '()))
    (with-containers (tl-emits tl-inputs tl-requires tl-lumps)
      (check-equal?
       (convert-contract-to-s
        (extend-is-ctc
         (new-env)
         `T
         `(-> integer? (or/c T)))
        `T)
       '(->s integer (->s integer (->s integer none/s))))))

  )

(define (predicate->contract env ctc)
  (let/ec escape
    (match (env-lookup-defn env ctc)
      [`(define (,(? symbol? main-p?) ,main-arg) ,main-body)
       (let loop ([body main-body]
                  [depth (- number-of-times-to-unroll 1)])
         (match body
           [`(or ,ctcs ...)
            `(or/s ,@(for/list ([ctc (in-list ctcs)])
                       (loop ctc depth)))]
           [`(false? ,arg) #:when (equal? main-arg arg) `boolean]
           [`(and (,p? ,arg2)
                  ,other-things ...)
            #:when (env-predicate-name->selectors env p?)
            ;; the selectors come out in the same order as the struct/c would need to be
            (define selectors (env-predicate-name->selectors env p?))
            (define substructs
              (for/list ([selector (in-list selectors)])
                (define computed-contract
                  (for/or ([other-thing (in-list other-things)])
                    (match other-thing
                      [`(,(? symbol? recursive-call) (,(? symbol? maybe-selector) ,(? symbol? arg)))
                       #:when (and (equal? recursive-call main-p?)
                                   (equal? selector maybe-selector)
                                   (equal? arg main-arg))
                       (cond
                         [(= depth 0) `none/s]
                         [else (loop main-body (- depth 1))])]
                      [else #f])))
                (or computed-contract `any/s)))
            `(struct/s ,(string->symbol (regexp-replace #rx"[?]$" (symbol->string p?) ""))
                       ,@substructs)]
           [_
            (escape #f)]))])))
