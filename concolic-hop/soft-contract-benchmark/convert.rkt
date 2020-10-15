#lang racket
(require racket/runtime-path
         "private/env.rkt"
         "private/mod.rkt"
         "private/emit.rkt"
         "private/exp.rkt"
         "private/misc.rkt"
         "private/paths.rkt"
         "private/top-sort.rkt"
         (submod concolic-hop/complex ops-to-convert-to-complex))
(module+ test (require rackunit))

#|

This script converts the soft contract benchmark files to
use #lang concolic-hop/lang. Specifically, it:
- adjusts the contract checking to use concolic-hop/ctc instead of racket/contract
- uses the contracts to extract ->s types for the functions
  (unrolling recursive contracts a fixed amount and generally simplifying them
   see convert-it for what it is doing)
- replaces • with variables that count as inputs to the concolic tester
- removes the modules (replacing them with just a series of top-level definitions)

According to https://github.com/philnguyen/soft-contract/blob/jfp/soft-contract/main.rkt#L35,
in the case when there are no top-level non-module expressions, we should
treat every module's exported functions as things we can call.

TODO:
- adjust container setup so that it isn't banging away on boxes that are initialized externally
- treat structs as fixed-length lists with integers as tags in the first position
- need to ensure that the variables for the generated inputs don't conflict with the program's variables
  (they have strange names so probably they won't, which seems good enough for now)

- struct counterexamples:

fail-ce/others:
Contract violation: 'tree' violates its own contract.
Value
 (node 0 (node 0 (node 0 #f #f) #f) #f)
violates predicate
 (λ (x)
  (or (false? x)
      (and (node? x)
           (braun-tree? (node-l x))
           (braun-tree? (node-r x))
           (let ((x₁ (size (node-l x))) (y (size (node-r x))))
             (or (= x₁ y) (= x₁ (+ y 1)))))))
An example module that breaks it:
 (module user racket
  (require (submod ".." tree))
  (insert (node 0 (node 0 #f #f) #f) 0))
  braun-tree & 21 & 44 & 1 & 14468 \\
Contract violation: 'tree-depth' violates its own contract.
Value
 0
violates predicate
 (λ (x) (and (real? x) (> x 0)))
An example module that breaks it:
 (module user racket (require (submod ".." tree-depth)) (depth (leaf)))
  tree-depth & 12 & 21 & 1 & 100.8 \\

fail-ce/games:

------------------------------------------------------------

Contract violation: 'collide' violates '<='.
Value
 0+1i
violates predicate
 real?
An example module that breaks it:
 (module user racket
  (require (submod ".." collide))
  (snake-wall-collide? (snake "up" (cons (posn 0+1i 0) empty))))

------------------------------------------------------------

Contract violation: 'bset' violates '<='.
Value
 0+1i
violates predicate
 real?
An example module that breaks it:
 (module user racket (require (submod ".." bset)) (blocks-overflow? empty))

------------------------------------------------------------

Contract violation: 'zombie' violates '<='.
Value
 0+1i
violates predicate
 real?
An example module that breaks it:
 (module user racket
  (require (submod ".." zombie))
  (((new-zombie (λ (x) (λ (x) 0+1i))) 'touching?) any/c))


---------

To see Phil's counterexamples, run main.rkt in the benchmark-verification repository

Raco test this file
https://github.com/philnguyen/soft-contract/blob/jfp/soft-contract/benchmark-verification/main.rkt#L108
soft-contract/benchmark-verification/main.rkt:108
  (test-dir "fail-ce" (λ (s) (check-verify-fail s #t)))

and changed L108 to verbose:
(test-dir "fail-ce" (λ (s) (check-verify-fail s #t #:verbose? #t)))

---------

run with:

   racket -W "info@concolic:status info@concolic:inputs" -t THEFILE.rkt

do this to get more timing information

   racket -W "debug@concolic:status info@concolic:inputs" -t THEFILE.rkt

 to see what the concolic tester is doing.

|#

(define (convert-file in out)
  (define exposed-arithmetic? (needs-exposed-arithmetic? in))
  (define path-limit (get-path-limit in))
  (define time-limit (get-time-limit in))
  (define inputs
    (call-with-input-file in
      (λ (port)
        (let loop ()
          (define e (read port))
          (cond
            [(eof-object? e) '()]
            [else (cons e (loop))])))))
  (assert-no-leading-underscores inputs)

  (define tl-emits (box '()))
  (define tl-inputs (box '()))
  (define tl-requires (box '()))
  (define tl-lumps (box (set)))
  (parameterize ([use-exposed-arithmetic? exposed-arithmetic?])
    (with-containers (tl-emits tl-inputs tl-requires tl-lumps)
      (define final-env
        (for/fold ([env (new-env)])
                  ([mod (in-list inputs)])
          (convert-mod mod env)))
      (maybe-emit-call-to-main final-env inputs)))

  (define prop-name
    (string->symbol
     (regexp-replace #rx"[.].*$"
                     (~a (file-name-from-path out))
                     "")))

  (call-with-output-file out
    (λ (out-port)
      (displayln "#lang concolic-hop/lang" out-port)
      (fprintf
       out-port
       ";; this file generated by convert-soft-contract.rkt using ~a as input\n"
       (file-name-from-path in))
      (writeln `(require concolic-hop/ctc
                         concolic-hop/lib
                         concolic-hop/convert-it
                         ,@(if exposed-arithmetic?
                               (list 'concolic-hop/complex)
                               (list)))
               out-port)

      (for ([tl-require (in-list (reverse (unbox tl-requires)))])
        (writeln tl-require out-port))

      (define lumps (sort (set->list (unbox tl-lumps)) string<? #:key ~s))

      (pretty-write
       `(define-lump L
          ,@(for/list ([l (in-list lumps)]
                       [i (in-naturals)])
              `(,i ,l)))
       out-port)

      (define sorted-tl-emits
        (do-the-top-sort
         (reverse (unbox tl-emits))))

      (pretty-write
       `(define-concolic-test ,prop-name
          #:inputs
          ,@(reverse (unbox tl-inputs))
          #:prop
          (prop-not-exn
           (λ ()
             ,@(rewrite-for-complex sorted-tl-emits
                                    exposed-arithmetic?))))
       out-port)
      (pretty-write
       `(define (counterexample)
          (define test-result
            (concolic-test ,prop-name #:all? #f
                           ,@(if path-limit
                                 (list '#:path-limit path-limit)
                                 (list))
                           ,@(if time-limit
                                 (list '#:timeout time-limit)
                                 (list))
                           #:statistics? #t))
          (define witness (list-ref test-result 0))
          (define stats (list-ref test-result 1))
          (vector
           (concretize-input
            ,prop-name
            witness)
           '(,@lumps)
           `#hash((solve-count
                   . ,(concolic-statistics-solve-count stats))
                  (solve-real-nongc-time
                   . ,(concolic-statistics-solve-real-nongc-time stats))
                  (eval-real-nongc-time
                   . ,(concolic-statistics-eval-real-nongc-time stats))
                  (test-count
                   . ,(concolic-statistics-test-count stats)))))
       out-port)
      (writeln `(provide counterexample
                         (rename-out [,prop-name test-property]))
               out-port)
      (writeln `(module+ main (counterexample)) out-port))
    #:exists 'truncate))

(define (rewrite-for-complex sexp exposed-arithmetic?)
  (if exposed-arithmetic?
      (let loop ([sexp sexp])
        (match sexp
          [(cons fst rst) (cons (loop fst) (loop rst))]
          [(? number?)
           `(c:racket-number->c ,sexp)]
          [(? op-to-convert-to-complex?)
           (string->symbol (~a "c:" sexp))]
          [_ sexp]))
      sexp))

(define (op-to-convert-to-complex? c)
  (member c ops-to-convert-to-complex))

(define (assert-no-leading-underscores inputs)
  (let loop ([inputs inputs])
    (cond
      [(pair? inputs)
       (loop (car inputs))
       (loop (cdr inputs))]
      [(symbol? inputs)
       (unless (equal? inputs '_)
         (when (regexp-match #rx"^_" (symbol->string inputs))
           (error 'assert-no-leading-underscores
                  "found a leading underscore ~a" inputs)))])))

(define/contract (maybe-emit-call-to-main final-env inputs)
  (-> env/c sexp/c void?)
  (when (only-modules? inputs)
    (define calls
      (for/list ([id (in-list (env-has-domain final-env))]
                 #:unless (equal? 'any/c (env-lookup-has-ctc final-env id)))
        `(• ,id)))
    (unless (null? calls)
      (emit-tl
       `(amb ,@calls)
       final-env))))

(define/contract (function-contract-arity sexp)
  (-> sexp/c (or/c natural? #f))
  (match sexp
    [`(-> ,doms ... ,rng) (length doms)]
    [`(->i (,doms ...) ,rng) (length doms)]
    [_ #f]))

(module+ main
  (for ([file.sch (in-list sch-files)]
        #:when (known-to-work? file.sch)
        )
    (define file.rkt (file.sch->file.rkt file.sch))
    (printf "processing ~a\n" (file.sch->string file.sch))
    (convert-file file.sch file.rkt)))
