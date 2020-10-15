#lang racket
(require "misc.rkt")

(provide
 (contract-out
  [env/c contract?]
  [new-env (-> env/c)]
  [extend-has-ctc
   (->i ([e env/c]
         [s (e) (and/c symbol? (not-in-has-domain-of? e))]
         [mod (or/c symbol? #f)]
         [ctc sexp/c])
        [result env/c])]
  [extend-is-ctc
   (->i ([e env/c] [s (e) (and/c symbol? (not-in-is-domain-of? e))] [ctc sexp/c])
        [result env/c])]
  [replace-is-ctc
   (->i ([e env/c] [s (e) (and/c symbol? (in-is-domain-of? e))] [ctc sexp/c])
        [result env/c])]
  [env-extend-struct-names (-> env? sexp/c env?)]
  [env-extend-tl-definition (-> env? symbol? sexp/c env?)]
  [env-extend-provided-definition (-> env? symbol? sexp/c env?)]
  [env-extend-contract-reference (-> env? symbol? env?)]
  [env-lookup-has-ctc
   (-> env/c symbol? (or/c sexp/c #f))]
  [env-lookup-has-ctc-moname
   (-> env/c symbol? (or/c symbol? #f))]
  [env-lookup-is-ctc
   (-> env/c symbol? (or/c sexp/c #f))] ;; what if the contract is #f?
  [env-lookup-defn
   (-> env/c symbol? (or/c sexp/c #f))]
  [env-is-ctc-domain
   (-> env/c (listof symbol?))]
  [env-in-has-domain?
   (-> env/c symbol? boolean?)]
  [env-in-is-domain?
   (-> env/c symbol? boolean?)]
  [env-has-domain (-> env/c (listof symbol?))]
  [env-is-tl-name? (-> env/c symbol? boolean?)]
  [env-is-contract-name? (-> env/c symbol? boolean?)]
  [env-is-contract-reference? (-> env/c symbol? boolean?)]
  [env-is-constructor-name? (-> env/c symbol? boolean?)]
  [env-is-predicate-name? (-> env/c symbol? boolean?)]
  [env-predicate-name->selectors (-> env/c symbol? (or/c (listof symbol?) #f))]
  [env-transfer-struct-names (-> env/c env/c env/c)]))

(struct env (is-ctc           ;; definitions in a file that look like contract (e.g. "(-> ...)")
             has-ctc          ;; the contracts on definitions in a file (from provides)
             mods             ;; tells which module certain contract definitions came from
             tl-defs          ;; the top-level definitions in the module we're working on
             provided-defs    ;; the top-level definitions from earlier modules
             struct-names     ;; the struct definitions in the module we're working on
             contract-refs)   ;; variables that seem to be references to contracts defined elsewhere in the program
  #:transparent)
(define env/c
  (struct/c env
            (hash/c symbol? sexp/c)
            (hash/c symbol? sexp/c)
            (hash/c symbol? (or/c symbol? #f))
            (hash/c symbol? sexp/c)
            (hash/c symbol? sexp/c)
            (set/c (λ (x) (struct-names? x)))
            (set/c symbol?)))

(define (new-env) (env (hash) (hash) (hash)  (hash) (hash) (set) (set)))
(define (extend-has-ctc an-env name modname ctc)
  (struct-copy env an-env
               [has-ctc (hash-set (env-has-ctc an-env) name ctc)]
               [mods (hash-set (env-mods an-env) name modname)]))
(define (extend-is-ctc an-env name ctc)
  (struct-copy env an-env
               [is-ctc (hash-set (env-is-ctc an-env) name ctc)]))
(define (replace-is-ctc an-env name ctc)
  (struct-copy env an-env
               [is-ctc (hash-set (env-is-ctc an-env) name ctc)]))
(define (env-extend-tl-definition an-env name defn)
  (struct-copy env an-env
               [tl-defs (hash-set (env-tl-defs an-env) name defn)]))
(define (env-extend-provided-definition an-env name defn)
  (struct-copy env an-env
               [provided-defs (hash-set (env-provided-defs an-env) name defn)]))
(define (env-extend-struct-names an-env struct-decl)
  (struct-copy env an-env
               [struct-names (set-add (env-struct-names an-env)
                                      (struct->names struct-decl))]))

(define (env-transfer-struct-names from-env to-env)
  (struct-copy env to-env
               [struct-names
                (set-union (env-struct-names from-env)
                           (env-struct-names to-env))]))

(define (env-extend-contract-reference an-env name)
  (struct-copy env an-env
               [contract-refs (set-add (env-contract-refs an-env)
                                       name)]))

(define (env-lookup-has-ctc env name)
  (hash-ref (env-has-ctc env) name #f))
(define (env-lookup-has-ctc-moname env name)
  (hash-ref (env-mods env) name #f))
(define (env-lookup-is-ctc env name)
  (hash-ref (env-is-ctc env) name #f))
(define (env-lookup-defn env name)
  ;; here we're looking for the definition of a function
  ;; that is in the current module (hence `tl-defs`) or
  ;; in a earlier moulde (hence `provided-defs`)
  (or (hash-ref (env-tl-defs env) name #f)
      (hash-ref (env-provided-defs env) name #f)))
(define (env-is-ctc-domain env)
  (hash-keys (env-is-ctc env)))

(define (env-is-tl-name? env name)
  ;; here we want only names that are defined in the
  ;; current module (hence only `tl-defs` and structs)
  (or (hash-has-key? (env-tl-defs env) name)
      (env-is-struct-name? env name)))
(define (env-is-struct-name? env name)
  (for/or ([a-struct-names (in-set (env-struct-names env))])
    (match-define (struct-names constructor predicate selectors) a-struct-names)
    (or (equal? constructor name)
        (equal? predicate name)
        (for/or ([selector (in-list selectors)])
          (equal? selector name)))))
(define (env-is-contract-name? env name)
  (hash-has-key? (env-is-ctc env) name))
(define (env-is-predicate-name? env name)
  (for/or ([a-struct-names (in-set (env-struct-names env))])
    (match-define (struct-names constructor predicate selectors) a-struct-names)
    (equal? predicate name)))
(define (env-is-constructor-name? env name)
  (for/or ([a-struct-names (in-set (env-struct-names env))])
    (match-define (struct-names constructor predicate selectors) a-struct-names)
    (equal? constructor name)))
(define (env-predicate-name->selectors env name)
  (for/or ([a-struct-names (in-set (env-struct-names env))])
    (match-define (struct-names constructor predicate selectors) a-struct-names)
    (and (equal? predicate name)
         selectors)))
(define (env-is-contract-reference? env name)
  (set-member? (env-contract-refs env) name))

(define (not-in-has-domain-of? e)
  (define (not-in-has-domain-of? s)
    (not (hash-ref (env-has-ctc e) s #f)))
  not-in-has-domain-of?)

(define (not-in-is-domain-of? e)
  (define (not-in-is-domain-of? s)
    (not (hash-ref (env-is-ctc e) s #f)))
  not-in-is-domain-of?)
(define (in-is-domain-of? e)
  (define (in-is-domain-of? s)
    (and (hash-ref (env-is-ctc e) s #f) #t))
  in-is-domain-of?)

(define (env-in-has-domain? env name)
  (and (hash-ref (env-has-ctc env) name #f)
       #t))
(define (env-in-is-domain? env name)
  (and (hash-ref (env-is-ctc env) name #f)
       #t))

(define (env-has-domain env)
  (sort (hash-keys (env-has-ctc env)) symbol<?))
