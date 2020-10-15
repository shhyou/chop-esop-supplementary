#lang racket
(provide
 sch-files
 (contract-out
  [file.sch->file.rkt
   (-> path-string? path-string?)]
  [file.sch->counterexample-file.rkt
   (-> path-string? path-string?)]
  [file.sch->string (-> path-string? string?)]
  [needs-exposed-arithmetic? (-> path-string? boolean?)]
  [get-path-limit (-> path-string? (or/c natural? #f))]
  [get-time-limit (-> path-string? (or/c (and/c real? positive?) #f))]
  [known-to-work? (-> path-string? boolean?)]
  [reason-it-fails (-> path-string? (or/c "search"
                                          "complex features"
                                          #f))]
  [file.sch->benchmark-set+file (-> path-string? (values string? string?))]))
(module+ test (require rackunit))

(require racket/runtime-path)
(define-runtime-path benchmarks/concolic-hop/funs-erl.rkt '(lib "funs-erl.rkt" "benchmarks" "concolic-hop"))
(define soft-contract-jfp
  (let-values ([(base name dir?) (split-path benchmarks/concolic-hop/funs-erl.rkt)])
    (build-path base "soft-contract-jfp")))

(define soft-contract-jfp-converted
  (let-values ([(base name dir?) (split-path benchmarks/concolic-hop/funs-erl.rkt)])
    (build-path base "soft-contract-jfp-converted")))

(define soft-contract-jfp-counterexamples
  (let-values ([(base name dir?) (split-path benchmarks/concolic-hop/funs-erl.rkt)])
    (build-path base "soft-contract-jfp-counterexamples")))
(make-directory* soft-contract-jfp-counterexamples)

(define sch-files
  (for/list ([file.sch (in-directory soft-contract-jfp)]
             #:unless (regexp-match? #rx"web/[^/]*[.]sch$" file.sch)
             #:when (regexp-match? #rx#"[.]sch$" (path->bytes file.sch))
             #:unless (regexp-match? #rx"ORIGINAL[.]sch$" (path->bytes file.sch)))
    file.sch))

(define (file.sch->file.rkt file.sch)
  (define rel-path.sch (find-relative-path (simplify-path soft-contract-jfp) (simplify-path file.sch)))
  (ensure-containing-dir-exists (build-path soft-contract-jfp-converted (sch->rkt rel-path.sch))))

(define (file.sch->counterexample-file.rkt file.sch)
  (define rel-path.sch (find-relative-path (simplify-path soft-contract-jfp) (simplify-path file.sch)))
  (ensure-containing-dir-exists (build-path soft-contract-jfp-counterexamples (sch->rkt rel-path.sch))))

(define (ensure-containing-dir-exists path)
  (define-values (base name dir?) (split-path path))
  (make-directory* base)
  path)

(define (sch->rkt sch)
  (bytes->path (regexp-replace #rx#"[.]sch$" (path->bytes sch) #".rkt")))

(define (file.sch->string file.sch)
  (apply ~a (add-between (reverse (take (reverse (explode-path file.sch)) 2)) "/")))

(define (needs-exposed-arithmetic? file.sch)
  (match-define (cons file (cons dir _)) (reverse (map path->bytes (explode-path file.sch))))
  (match* (dir file)
    [(#"games" _) #t]
    [(_ #"ex-08.sch") #t]
    [(_ #"tak.sch") #t]
    [(_ #"cpstak.sch") #t]
    [(_ #"argmin.sch") #t]
    [(_ #"even-odd.sch") #t]
    [(_ #"id-dependent.sch") #t]
    [(#"others" #"ack.sch") #t]
    [(_ _) #f]))

(define (get-path-limit file.sch)
  (match (path->bytes (file-name-from-path file.sch))
    [#"hrec.sch" 1000]
    [#"l-zipmap.sch" 500]
    [else #f]))

(define (get-time-limit file.sch)
  (match (path->bytes (file-name-from-path file.sch))
    [#"l-zipmap.sch" 5]
    [#"r-file.sch" 5]
    [else #f]))

(define (known-to-work? sch) (not (reason-it-fails sch)))

(define (reason-it-fails sch)
  (match-define (cons file (cons dir _)) (reverse (map path->string (explode-path sch))))
  (match dir
    ["hors" #f]
    ["mochi-new" #f]
    ["octy" #f]
    ["softy" #f]
    ["others"
     (case file
       [("braun-tree.sch") "search"]
       [else #f])]
    ["games"
     (case file
       [("zombie.sch") "search"]
       [("snake.sch" "tetris.sch") "complex features"])]
    ["terauchi" #f]))

(define (file.sch->benchmark-set+file file.sch)
  (define-values (base1 name dir?1) (split-path file.sch))
  (define-values (base2 benchmark-set dir?2) (split-path base1))
  (values (path->string benchmark-set)
          (regexp-replace #rx"[.]sch" (path->string name) "")))
(module+ test
  (let ()
    (define-values (benchmark-set file)
      (file.sch->benchmark-set+file
       (for/or ([file.sch (in-list sch-files)])
         (and (regexp-match? #rx"games/zombie[.]sch" (path->string file.sch))
              file.sch))))
    (check-equal? benchmark-set "games")
    (check-equal? file "zombie")))

(module+ main
  (printf "~a total examples, ~a (probably) work\n"
          (length sch-files)
          (length (filter known-to-work? sch-files))))
