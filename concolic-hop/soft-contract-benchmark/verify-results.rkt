#lang racket

#|

Running this file verifies that the generated counterexamples do, in fact,
produce results that indiciate a counterexample. Specifically, it contains
strings that are prefixes of error messages that the benchmark programs raise
when they have bug-triggering inputs. The error messages have been carefully
audited by hand.

|#

(define expected-results
  (hash

   "hors/ack.sch"
   "ack: broke its own contract\n  promised: a number strictly greater than 1"

   "hors/fhnhn.sch"
   "g: broke its own contract"

   "hors/fold-div.sch"
   "/: division by zero"

   "hors/fold-fun-list.sch"
   "main: broke its own contract"

   "hors/hors.sch"
   "a: contract violation"

   "hors/hrec.sch"
   "main: broke its own contract\n  promised: (>=/c 0)"

   "hors/intro1.sch"
   "h: contract violation\n  expected: a number strictly greater than 1"

   "hors/intro2.sch"
   "h: contract violation\n  expected: a number strictly greater than 1"

   "hors/intro3.sch"
   "h: contract violation\n  expected: a number strictly greater than 1"

   "hors/isnil.sch"
   "mk-list: broke its own contract"

   "hors/l-zipmap.sch"
   "zip: broke its own contract\n  promised: integer?\n  produced: 'fail"

   "hors/r-file.sch"
   "readit: broke its own contract\n  promised: (quote opened)\n  produced: 'ignore"

   "hors/max.sch"
   "main: broke its own contract"

   "hors/mc91.sch"
   "mc91: broke its own contract\n  promised: (=/c 91)"

   "hors/mem.sch"
   "mk-list: broke its own contract"

   "hors/mult.sch"
   "sqr: broke its own contract\n  promised: (and/c integer? (>=/c 1))"

   "hors/neg.sch"
   "main: broke its own contract\n  promised: a number strictly greater than 0"

   "hors/nth0.sch"
   "cdr: contract violation"

   "hors/r-lock.sch"
   "unlock: contract violation\n  expected: 1"

   "hors/repeat.sch"
   "main: broke its own contract"

   "hors/reverse.sch"
   "car: contract violation"

   "hors/sum.sch"
   "sum: broke its own contract"

   "hors/zip.sch"
   "main: broke its own contract"
   
   "mochi-new/a-max.sch"
   "main: broke its own contract"

   "mochi-new/fold_fun_list.sch"
   "main: broke its own contract"

   "mochi-new/fold_left.sch"
   "main: broke its own contract"

   "mochi-new/fold_right.sch"
   "main: broke its own contract"

   "mochi-new/forall_leq.sch"
   "main: broke its own contract"

   "mochi-new/harmonic.sch"
   "/: division by zero"

   "mochi-new/length.sch"
   "main: broke its own contract"

   "mochi-new/map_filter.sch"
   "car: contract violation"

   "mochi-new/risers.sch"
   "car: contract violation"

   "mochi-new/search.sch"
   "main: broke its own contract"

   "mochi-new/zip_unzip.sch"
   "add1: contract violation"

   "octy/ex-01.sch"
   "add1: contract violation"

   "octy/ex-02.sch"
   "string-length: contract violation"

   "octy/ex-03.sch"
   "f: broke its own contract\n  promised: false?"

   "octy/ex-04.sch"
   "f: contract violation\n  expected: (or/c string? number?)"

   "octy/ex-05.sch"
   "string-length: contract violation"

   "octy/ex-07.sch"
   "string-length: contract violation"

   "octy/ex-08.sch"
   "strnum?: broke its own contract"

   "octy/ex-09.sch"
   "f: contract violation\n  expected: (or/c string? number?)"

   "octy/ex-10.sch"
   "add1: contract violation"

   "octy/ex-11.sch"
   "g: contract violation\n  expected: number?"

   "octy/ex-12.sch"
   "car: contract violation"

   "octy/ex-13.sch"
   "f: broke its own contract\n  promised: (not/c false?)"

   "octy/ex-14.sch"
   "string-length: contract violation"

   "others/ack.sch"
   "ack: broke its own contract\n  promised: integer?\n"

   "others/argmin.sch"
   "<: contract violation\n  expected: real?"
   
   "others/get-path.sch"
   "application: not a procedure;\n expected a procedure that can be applied to arguments"

   "others/all.sch"
   "all: broke its own contract\n  promised: boolean?"

   "others/even-odd.sch"
   ">: contract violation\n  expected: real?"

   "others/factorial-acc.sch"
   "factorial: broke its own contract\n  promised: (and/c integer? (>/c 1))\n  produced: 1"

   "others/factorial.sch"
   "factorial: broke its own contract\n  promised: (and/c integer? (>/c 1))\n  produced: 1"

   "others/filter.sch"
   #rx"^filter: broke its own contract\n  promised: [^\n]*\n  produced: '[(][)]"

   "others/foldl.sch"
   "foldl: broke its own contract"

   "others/foldl1.sch"
   "car: contract violation"

   "others/foldr.sch"
   "foldr: broke its own contract\n  promised: number?"

   "others/foldr1.sch"
   "car: contract violation"

   "others/ho-opaque.sch"
   "db1: contract violation\n  expected: zero?"

   "others/id-dependent.sch"
   "=/c: contract violation\n  expected: real?"

   "others/inc-or-greet.sch"
   "inc-or-greet: broke its own contract\n  promised: (or/c integer? string?)\n  produced: #f"

   "others/insertion-sort.sch"
   "insert: contract violation\n  expected: integer?"

   "others/map-foldr.sch"
   "car: contract violation"

   "others/map.sch"
   "car: contract violation"

   "others/mappend.sch"
   "car: contract violation"

   "others/mem.sch"
   "mk-list: broke its own contract"

   "others/recip-contract.sch"
   "/: division by zero"

   "others/sum-filter.sch"
   "+: contract violation\n  expected: number?"

   "others/sat-7.sch"
   "sat-solve-7: broke its own contract\n  promised: boolean?"

   "others/tree-depth.sch"
   "depth: broke its own contract\n"

   "others/rsa.sch"
   "rsa: contract violation\n  expected: number?"
   
   "softy/append.sch"
   "append: broke its own contract\n  promised: pair?\n  produced: '()"

   "softy/cpstak.sch"
   "<: contract violation\n  expected: real?"

   "softy/flatten.sch"
   "append: contract violation\n  expected: list?"

   "softy/last-pair.sch"
   "lastpair: broke its own contract\n  promised: pair?"

   "softy/last.sch"
   "cdr: contract violation\n  expected: pair?"

   "softy/length-acc.sch"
   "len: broke its own contract\n  promised: (and/c integer? (>/c 0))\n  produced: 0"

   "softy/length.sch"
   "len: broke its own contract\n  promised: (and/c integer? (>/c 0))\n  produced: 0"

   "softy/member.sch"
   "member: broke its own contract\n  promised: boolean?"

   "softy/recursive-div2.sch"
   "cdr: contract violation\n  expected: pair?"

   "softy/subst*.sch"
   "subst*: broke its own contract\n  promised: pair?"

   "softy/tak.sch"
   "<: contract violation\n  expected: real?"

   "softy/taut.sch"
   "taut: broke its own contract\n  promised: boolean?"

   "terauchi/boolflip-e.sch"
   "assert: contract violation\n  expected: (not/c false?)"

   "terauchi/mult-all-e.sch"
   "assert: contract violation\n  expected: (not/c false?)\n  given: #f"

   "terauchi/mult-cps-e.sch"
   "assert: contract violation\n  expected: (not/c false?)\n  given: #f"

   "terauchi/mult-e.sch"
   "assert: contract violation\n  expected: (not/c false?)\n  given: #f"

   "terauchi/sum-acm-e.sch"
   "assert: contract violation\n  expected: (not/c false?)\n  given: #f"

   "terauchi/sum-all-e.sch"
   "assert: contract violation\n  expected: (not/c false?)\n  given: #f"

   "terauchi/sum-e.sch"
   "assert: contract violation\n  expected: (not/c false?)\n  given: #f"

   ))

(require "private/paths.rkt")
(define (verify-counterexamples)
  (define number-that-worked 0)
  (define number-that-should-work 0)
  (define no-expected-result? #f)
  (for ([file.sch (in-list sch-files)])
    (define short-name (file.sch->string file.sch))
    (define expected-result (hash-ref expected-results short-name #f))
    (when (known-to-work? file.sch)
      (set! number-that-should-work (+ number-that-should-work 1)))
    (cond
      [(and expected-result (known-to-work? file.sch))
       (define counterexample-file (file.sch->counterexample-file.rkt file.sch))
       (define result
         (cond
           [(file-exists? counterexample-file)
            (with-handlers ([exn:fail? exn-message])
              (dynamic-require counterexample-file #f)
              #f)]
           [else 'dne]))
       (cond
         [(not result) (eprintf "~a: no error raised\n" short-name)]
         [(equal? result 'dne) (eprintf "~a: no counterexample file\n" short-name)]
         [(regexp-match? (if (regexp? expected-result)
                             expected-result
                             (regexp (~a "^" (regexp-quote expected-result))))
                         result)
          (set! number-that-worked (+ number-that-worked 1))]
         [else
          (define shortened
            (substring result
                       0
                       (min (if (string? expected-result)
                                (string-length expected-result)
                                70)
                            (string-length result))))
          (eprintf "~a: error did not match\n       got ~s\n  expected ~s\n"
                   short-name
                   shortened
                   expected-result)])]
      [(and (known-to-work? file.sch) (not expected-result))
       (set! no-expected-result? #t)
       (eprintf "~a: known to work but no expected result\n" short-name)]))
  (printf "~a worked (out of ~a)\n" number-that-worked (length sch-files))
  (and (not no-expected-result?)
       (= number-that-worked number-that-should-work)))

(module+ main
  (define succeeded?
    (verify-counterexamples))
  (unless succeeded?
    (exit 1)))
