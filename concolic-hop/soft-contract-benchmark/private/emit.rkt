#lang racket
(require "env.rkt" "misc.rkt"
         (for-syntax syntax/parse))
(module+ test (require rackunit))

(provide
 (contract-out
  [next-dot (-> natural?)]
  [tl-emit (-> sexp/c void?)]
  [input-emit (-> T/c symbol? void?)]
  [require-emit (-> (cons/c 'require sexp/c) void?)]
  [lump-emit (-> sexp/c void?)]
  [use-exposed-arithmetic? (parameter/c boolean?)]
  [adjust-for-complex (-> T/c T/c)])
 with-containers)

(define-syntax (with-containers stx)
  (syntax-parse stx
    [(_ (tl-emits:id tl-inputs:id tl-requires:id tl-lumps:id) e ...)
     #'(parameterize ([tl-emit-container tl-emits]
                      [input-emit-container tl-inputs]
                      [require-emit-container tl-requires]
                      [lump-emit-container tl-lumps]
                      [dot-container (box 0)])
         e ...)]))

(define tl-emit-container (make-parameter #f))
(define input-emit-container (make-parameter #f))
(define require-emit-container (make-parameter #f))
(define lump-emit-container (make-parameter #f))
(define dot-container (make-parameter #f))

(define (tl-emit exp)
  (define b (tl-emit-container))
  (unless b (error 'tl-emit "the emit container isn't set"))
  (set-box! b (cons exp (unbox b))))
(define (input-emit type variable-name)
  (define b (input-emit-container))
  (unless b (error 'input-emit "the emit container isn't set"))
  (for ([prs (in-list (unbox b))])
    (when (equal? (list-ref prs 0) variable-name)
      (error 'input-emit "emitted two variables with the same name\n  name: ~s" variable-name)))
  (set-box! b (cons `[,variable-name ,(convert-s type)] (unbox b))))
(define (require-emit exp)
  (define b (require-emit-container))
  (unless b (error 'require-emit "the emit container isn't set"))
  (set-box! b (cons exp (unbox b))))
(define (lump-emit exp)
  (define b (lump-emit-container))
  (unless b (error 'lump-emit "the emit container isn't set"))
  (set-box! b (set-add (unbox b) exp)))
(define (next-dot)
  (define b (dot-container))
  (unless b (error 'next-dot "the emit container isn't set"))
  (define n (unbox b))
  (begin0 n
          (set-box! b (+ n 1))))

;; This needs to match up with how `convert-it` works
;; in the sense that the concolic tester will generate
;; something of the type `convert-s` returns but the program
;; under test will expect something of the type that `convert-s`
;; consumes.
;; `convert-s` also adjusts the generated types to support
;; using complex numbers
(define (convert-s s)
  (define any/s-expansion-types
    (if (use-exposed-arithmetic?)
        ;; when we are in complex mode we get only three
        ;; branches for any, because the complexification of
        ;; (listof integer) will cause trouble with just
        ;; what integer itself turns into, and also convert-it
        ;; does not try to convert integers that are inside things
        (list `(->s (list/s integer integer integer integer)
                    (list/s integer integer integer integer))
              `(list/s integer integer integer integer)
              `boolean)
        (list `(->s integer integer)
              `(list/s boolean (list-of integer)) ;; boolean indicates if it a dotted list of not
              `integer
              `boolean)))
  (let loop ([s s])
    (match s
      [`(->s ,rng) `(->s integer ,(loop rng))]
      [`(->s ,dom ,rng) `(->s ,(loop dom) ,(loop rng))]
      [`(->s ,dom1 ,dom2s ... ,rng)
       `(->s ,(loop dom1) ,(loop `(->s ,@dom2s ,rng)))]
      [`(list/s ,Ts ...)
       `(list/s ,@(for/list ([T (in-list Ts)])
                    (loop T)))]
      [`(or/s ,Ts ...)
       #:when (for/or ([T (in-list Ts)]) (equal? T 'any/s))
       ;; when an `or/s` contains `any/s` there is a danger
       ;; that we are going to introduce nested `or/s`s.
       ;; so we insert the `or/s` here and remove any
       ;; duplicates and then try again to do the translation
       (loop `(or/s ,@(remove-duplicates
                       (append any/s-expansion-types
                               (for/list ([T (in-list Ts)]
                                          #:unless (equal? T 'any/s))
                                 T)))))]
      [`(or/s ,Ts ...)
       `(or/s ,@(for/list ([T (in-list Ts)])
                  (loop T)))]
      [`(list-of ,T) `(list-of ,(loop T))]
      [`(cons/s ,T1 ,T2) `(list/s ,(loop T1) ,(loop T2))]
      [`lump/s `integer]
      [`integer (if (use-exposed-arithmetic?)
                    `(list/s integer integer integer integer)
                    `integer)]
      [`any/s `(or/s ,@any/s-expansion-types)]
      [`dont-care/s `boolean]
      [`none/s `boolean] ;; this is guaranteed to fail (which is what we want)
      [`boolean `boolean]
      [`string/s `integer]
      [`string-or-integer/s `integer]
      [`(struct/s ,struct-name ,Ts ...)
       `(list/s integer ,@(for/list ([T (in-list Ts)])
                            (loop T)))]
      [`(->si ([,x1s (one-of/c ,doms ...)])
              (res (,x2)
                   (cond
                     ,clauses ...)))
       (define keys
         (for/set ([dom (in-list doms)])
           (match dom
             [`',(? symbol? s) s]
             [(? string? s) (string->symbol s)])))
       (define t (make-hash))
       (for ([clause (in-list clauses)])
         (match clause
           [`[(equal? ,(? symbol?) ',(? symbol? s)) ,rng]
            (hash-set! t s rng)
            (set! keys (set-remove keys s))]
           [`[(equal? ,(? symbol?) ,(? string? str)) ,rng]
            (define s (string->symbol str))
            (hash-set! t s rng)
            (set! keys (set-remove keys s))]
           [`[else "error"]
            (void)]
           [`[else ,rng]
            (unless (= (set-count keys) 1)
              (error 'emit.rkt "got confused while parsing ->si"))
            (hash-set! t (set-first keys) rng)
            (set! keys (set-remove keys s))]))
       `(list/s ,@(for/list ([msg (in-list (sort (hash-keys t) symbol<?))])
                    (loop (hash-ref t msg))))])))

;; this function needs to be called before any `T/s` is saved in a variable
;; name to communicate with the script that writes counterexamples
(define (adjust-for-complex s)
  (let loop ([s s])
     (match s
       [`(->s ,doms ... ,rng)
        `(->s ,@(for/list ([dom (in-list doms)])
                  (loop dom))
              ,(loop rng))]
       [`(list/s ,Ts ...)
        `(list/s ,@(for/list ([T (in-list Ts)])
                     (loop T)))]
       [`(or/s ,Ts ...)
        `(or/s ,@(for/list ([T (in-list Ts)])
                   (loop T)))]
       [`(list-of ,T) `(list-of ,(loop T))]
       [`(cons/s ,T1 ,T2) `(cons/s ,(loop T1) ,(loop T2))]
       [`integer (if (use-exposed-arithmetic?)
                     `(list/s integer integer integer integer)
                     `integer)]
       [`(->si ([,x1s ,d])
               (res (,x2)
                    (cond
                      [,qs ,ts] ...)))
        `(->si ([,x1s ,d])
               (res (,x2)
                    (cond
                      ,@(for/list ([q (in-list qs)]
                                   [t (in-list ts)])
                          (if (equal? t "error")
                              `[,q ,t]
                              `[,q ,(loop t)])))))]
       [`boolean `boolean]
       [`string/s `string/s]
       [`lump/s `lump/s]
       [`string-or-integer/s `string-or-integer/s]
       [`any/s `any/s]
       [`dont-care/s `dont-care/s]
       [`none/s `none/s]
       [`(struct/s ,struct-name ,Ts ...)
        `(struct/s ,struct-name ,@(for/list ([T (in-list Ts)])
                                    (loop T)))])))

(define use-exposed-arithmetic? (make-parameter #f))

(module+ test
  (check-equal? (convert-s `(->s integer integer))
                `(->s integer integer))
  (check-equal? (convert-s `(->s integer integer integer))
                `(->s integer (->s integer integer)))
  (check-equal? (convert-s `(->s integer integer integer integer))
                `(->s integer (->s integer (->s integer integer))))
  (check-equal? (convert-s `(->s (->s integer integer integer)
                               (->s integer integer integer)
                               (->s integer integer integer)))
                `(->s (->s integer (->s integer integer))
                      (->s (->s integer (->s integer integer))
                           (->s integer (->s integer integer)))))

  (check-equal? (convert-s `(or/s (->s integer integer integer)
                                integer))
                `(or/s (->s integer (->s integer integer))
                       integer))
  (check-equal? (convert-s `(list-of (->s integer integer integer)))
                `(list-of (->s integer (->s integer integer))))
  (check-equal? (convert-s `(list/s integer (->s integer integer integer)))
                `(list/s integer (->s integer (->s integer integer))))
  (check-equal? (convert-s `(->s (->s integer integer integer)))
                `(->s integer (->s integer (->s integer integer))))
  (check-equal? (convert-s `(->s (->s integer integer integer)))
                `(->s integer (->s integer (->s integer integer))))
  (check-equal? (convert-s `(->si ([x (one-of/c 'x 'y)])
                                (res (x)
                                     (cond
                                       [(equal? x 'x) (->s integer integer)]
                                       [(equal? x 'y) (->s integer integer integer)]
                                       [else "error"]))))
                `(list/s (->s integer integer)
                         (->s integer (->s integer integer))))
  (check-equal? (convert-s `(->si ([x (one-of/c 'x 'y)])
                                (res (x)
                                     (cond
                                       [(equal? x 'y) (->s integer integer integer)]
                                       [(equal? x 'x) (->s integer integer)]
                                       [else "error"]))))
                `(list/s (->s integer integer)
                         (->s integer (->s integer integer))))
  (check-equal? (convert-s `(->si ([x (one-of/c "x" "y")])
                                (res (x)
                                     (cond
                                       [(equal? x "x") (->s integer integer)]
                                       [else (->s integer integer integer)]))))
                `(list/s (->s integer integer)
                         (->s integer (->s integer integer))))
  (check-equal? (convert-s `(->si ([x (one-of/c "x" "y")])
                                (res (x)
                                     (cond
                                       [(equal? x "y") (->s integer integer)]
                                       [else (->s integer integer integer)]))))
                `(list/s (->s integer (->s integer integer))
                         (->s integer integer)))
  (parameterize ([use-exposed-arithmetic? #t])
    (check-equal? (convert-s `(->s integer lump/s))
                  `(->s (list/s integer integer integer integer) integer))))
