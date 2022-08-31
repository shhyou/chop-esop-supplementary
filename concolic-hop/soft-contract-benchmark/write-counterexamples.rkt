#lang racket
(require "private/paths.rkt"
         "private/misc.rkt"
         "private/inline-convert-it.rkt"
         concolic-hop/private/complex-core
         syntax/parse
         racket/gui/base)
(module+ test (require rackunit))

#|

This script runs the concolic-hop/lang programs (see `convert-soft-contract.rkt`)
and uses the results to construct modified versions of the original programs where
the bug-trigger inputs are replace the input specs in the counterexamples (the `•`s
and the missing definitions). Running this can take a little while, as two of the
counterexamples take 10 or 15 minutes to find (on a new, nice laptop).

The variables in the counterexample have specific meaning, based on the first letter:

- A --> this will be Amb and will be an integer (unless the program is in complex mode,
  in which case it is an encoded variable)

- B --> the name's content will be (list/c integer? symbol? symbol? T/c sexp/c-or-#f)
  that tells us which branch of the amb this was in (so we match it up with the value
  of the amb), and the name of the provided identifier (so we can generate the call),
  the module it was in (so we can require it into the top-level), the type to use with
  convert-it, and the contract (if one is known)

- M --> these are the variables that correspond to identifiers that have no
  definition in the original program (so the concolic tester has to define all
  of them or else the program won't run). The name's content is
  (list/c symbol? symbol? T/c sexp/c), giving the module name, the function name,
  the T/c that we need to pass to `convert-it` to wrap the value that
  the concolic tester generates, and the contract (or #f if there isn't one)
  on the export

- • --> this will be a • that was in the original program. The name's content (the
  part following the first character) will be (list/c integer? T/c sexp/c) that tells
  us which number • this is (in depth-first, left-to-right order) and what T/c to
  use with `convert-it` and what the contract is that in force on the dot
|#

(define (build-rewrites file.sch counterexample)
  (match-define (vector variable-table lumps stats) counterexample)
  (define stx
    (call-with-input-file file.sch
      (λ (port)
        (port-count-lines! port)
        (let loop ()
          (define p (peek-char port))
          (cond
            [(eof-object? p) '()]
            [else
             (cons (parameterize ([read-accept-reader #t])
                     (read-syntax file.sch port))
                   (loop))])))))
  (define rewrites '())
  (define (add-replace-rewrite stx str)
    (define start (- (syntax-position stx) 1))
    (set! rewrites
          ;; positions in syntax start at `1`, we want 0-indexed positions
          (list* (delete start (+ start (syntax-span stx)))
                 (insert start str)
                 rewrites)))
  (define (add-insert-after-rewrite stx str)
    (define start (- (syntax-position stx) 1))
    (define end (+ start (syntax-span stx)))
    (set! rewrites
          ;; positions in syntax start at `1`, we want 0-indexed positions
          (list* (insert end str)
                 rewrites)))
  
  (define module-names-to-insert (make-hash))
  (for ([k (in-list (sort (hash-keys variable-table) string<? #:key ~s))]
        #:when (regexp-match? #rx"^M" (symbol->string k)))
    (define sexp (hash-ref variable-table k))
    (define str (symbol->string k))
    (match-define (list mod name T/s contract)
      (read (open-input-string (substring str 1 (string-length str)))))
    (define definitions (hash-ref module-names-to-insert mod '()))
    (define inlined-convert-it-expression
      (get-inlined-convert-it-expression file.sch sexp T/s lumps contract))
    (hash-set! module-names-to-insert mod
               (cons `(define ,name
                        ,inlined-convert-it-expression)
                     definitions)))

  (define (fetch-T/s-and-code •-counter)
    (for/or ([(k sexp) (in-hash variable-table)])
      (define str (symbol->string k))
      (cond
        [(regexp-match? #rx"^•" str)
         (match-define (list index T/s the-contract)
           (read (open-input-string (substring str 1 (string-length str)))))
         (cond
           [(equal? index •-counter)
            (list T/s sexp the-contract)]
           [else #f])]
        [else #f])))
  
  (define •-counter 0)
  (define thing-inserted-at-top-level
    (let loop ([stx stx]
               [module-we-are-inside #f])
      (syntax-parse stx
        #:datum-literals (• module)
        [•
         (match-define (list T/s sexp contract) (fetch-T/s-and-code •-counter))
         (set! •-counter (+ •-counter 1))
         (define inlined-convert-it-expression
           (get-inlined-convert-it-expression file.sch sexp T/s lumps contract))
         (add-replace-rewrite stx (pretty-write->str
                                   inlined-convert-it-expression 
                                   #:remove-last-newline? #t
                                   #:start-column (+ 1 (syntax-column stx))))
         inlined-convert-it-expression]
        [(module modname:id language bodies ...)
         (define modname-sym (syntax-e #'modname))
         (define additions (hash-ref module-names-to-insert modname-sym #f))
         (define thing-inserted (loop #'(bodies ...) (syntax-e #'modname)))
         (define top-level-insertions (module-top-level-additions (list additions thing-inserted) #t))
         (when (or top-level-insertions (pair? additions))
           (define indent-string "  ")
           (define to-insert
             (~a (or top-level-insertions "")
                 (apply
                  string-append
                  (for/list ([addition (in-list additions)])
                    (~a "\n"
                        indent-string
                        (pretty-write->str addition
                                           #:remove-last-newline? #t
                                           #:start-column
                                           (string-length indent-string)))))))
           (add-insert-after-rewrite #'language to-insert))
         #f]
        [(a . b)
         (define ar (loop #'a module-we-are-inside))
         (define br (loop #'b module-we-are-inside))
         (cond
           [(and ar br) (list ar br)]
           [else (or ar br)])]
        [_ #f])))

  (define amb-insertion (get-amb-insertion file.sch variable-table lumps))

  (define insertion-at-start-of-file
    (cond
      [(and thing-inserted-at-top-level
            (module-top-level-additions thing-inserted-at-top-level #f))
       =>
       (λ (insertion)
         (string-append
          "#lang racket"
          insertion
          "\n"))]
      [else "#lang racket\n"]))
  
  ;; we always add a #lang racket to the top, not sure why these aren't in the original files
  (append (list (insert 0 insertion-at-start-of-file))
          rewrites
          (if amb-insertion (list amb-insertion) '())))

(define/contract (module-top-level-additions expression-with-dependencies indent?)
  (-> any/c boolean? (or/c string? #f))
  (define indent-string (if indent? "  " ""))
  (define deps (get-external-dependencies expression-with-dependencies))
  (cond
    [(null? deps) #f]
    [else
     (apply string-append
            (for/list ([dep (in-list deps)])
              (~a "\n" indent-string (~s dep))))]))

(define (get-amb-insertion file.sch variable-table lumps)
  (-> path-string? hash? (listof any/c) (or/c #f edit?))
  (cond
    [(hash-ref variable-table 'Amb #f)
     =>
     (λ (amb-val)
       (for/or ([(k sexp) (in-hash variable-table)])
         (define str (symbol->string k))
         (define m (regexp-match #rx"^B" str))
         (define amb-val-as-racket-number
           (cond
             [(needs-exposed-arithmetic? file.sch)
              (match amb-val
                [`(cons ,a (cons ,b (cons ,c (cons ,d null))))
                 (c:from-concolic-number (list a b c d))])]
             [else amb-val]))
         (cond
           [m
            (match-define (list amb-branch function-name modname T/s contract)
              (read (open-input-string (substring str 1 (string-length str)))))
            (cond
              [(= amb-branch amb-val-as-racket-number)
               (define inlined-convert-it-expression
                 (get-inlined-convert-it-expression file.sch sexp T/s lumps contract))
               (define top-level-insertion (module-top-level-additions inlined-convert-it-expression #f))
               (define prog
                 (pretty-write->str
                  `(,inlined-convert-it-expression ,function-name)))
               (insert +inf.0 (~a
                               (if top-level-insertion (~a "\n" top-level-insertion) "")
                               (if modname (~a "\n" (pretty-write->str `(require ',modname))) "")
                               "\n"
                               prog
                               "\n"))]
              [else #f])]
           [else #f])))]
    [else #f]))

(define (get-inlined-convert-it-expression file.sch sexp T/s lumps contract)
  (define structs (find-structs file.sch))
  (remove-#%apps
   (inline-convert-it sexp
                      (rewrite-_-structs T/s)
                      #:needs-exposed-arithmetic?
                      (needs-exposed-arithmetic? file.sch)
                      #:lumps lumps
                      #:contract contract
                      #:structs structs)))

(define (rewrite-_-structs sexp)
  (let loop ([sexp sexp])
    (match sexp
      [`(struct/s ,s ,more ...)
       #:when (regexp-match #rx"^_" (symbol->string s))
       (define str (symbol->string s))
       `(struct/s ,(string->symbol (substring str 1 (string-length str)))
                  ,@more)]
      [(? pair?) (cons (loop (car sexp))
                       (loop (cdr sexp)))]
      [_ sexp])))

;; find-structs : file.sch -> (listof sexp/c)
;; this is a low-tech way to pull out all of the
;; structs that are in file.sch which get used to
;; make sure we can expand the call to inline-it
(define (find-structs file.sch)
  (define structs '())
  (call-with-input-file file.sch
    (λ (port)
      (let loop ()
        (define exp (read port))
        (unless (eof-object? exp)
          (let loop ([exp exp])
            (match exp
              [`(struct ,(? symbol? struct-name) (,(? symbol? fld) ...))
               (set! structs (cons exp structs))]
              [(? list?)
               (for ([e (in-list exp)])
                 (loop e))]
              [_ (void)]))
          (loop)))))
  structs)

(define (pretty-write->str sexp
                           #:start-column [start-column 0]
                           #:remove-last-newline? [remove-last-newline? #f])
  (define sp (open-output-string))
  (parameterize ([pretty-print-print-line
                  (let ([old-pretty-print-print-line (pretty-print-print-line)])
                    (λ (new-line-number op line-length dest)
                      (cond
                        [(and (not (equal? new-line-number 0))
                              new-line-number)
                         (display "\n" op)
                         (display (make-string start-column #\space) op)
                         start-column]
                        [else (old-pretty-print-print-line
                               new-line-number op line-length dest)])))])
    (pretty-write sexp sp))
  (cond
    [remove-last-newline?
     (define str (get-output-string sp))
     (regexp-replace #rx"\n$" str "")]
    [else (get-output-string sp)]))


(struct edit () #:transparent)
(struct delete edit (start end) #:transparent)
(struct insert edit (pos text) #:transparent)

(define (edit-start-pos>? a b)
  (> (edit->start-pos a) (edit->start-pos b)))
(define (edit->start-pos edit)
  (match edit
    [(delete a-start a-end) a-start]
    [(insert a-start a-str) a-start]))

(define/contract (apply-rewrites/file original-file counterexample-file rewrites)
  (-> path-string? path-string? (listof edit?) void?)
  (define t (new text%))
  (send t load-file original-file)
  (send t set-filename #f)
  (for ([rewrite (in-list (sort rewrites edit-start-pos>?))])
    (apply-edit-to-text rewrite t))
  (send t save-file counterexample-file)
  (void))

(define (apply-edit-to-text edit t)
  (match edit
    [(delete start end) (send t delete start end)]
    [(insert pos/inf str)
     (define pos
       (if (= pos/inf +inf.0)
           (send t last-position)
           pos/inf))
     (send t insert str pos pos)]))

(define (get-counterexample-and-rewrite file.sch write-first-part-of-line)
  (define-values (results cpu real gc)
    (run-with-monitoring file.sch write-first-part-of-line))
  (define counterexample (list-ref results 0))
  (define rewrites (build-rewrites file.sch counterexample))
  (apply-rewrites/file file.sch
                       (file.sch->counterexample-file.rkt file.sch)
                       rewrites)
  (values (- real gc)
          (vector-ref counterexample 2)))

(define-values (get-current-namespace make-new-namespace)
  (let ()
    (define ns #f)
    (define (get-current-namespace) (make-new-namespace) ns)
    (define (make-new-namespace)
      (set! ns (make-base-namespace))
      (parameterize ([current-namespace ns])
        (for ([mod (in-list '(concolic-hop/lang
                              concolic-hop/ctc
                              concolic-hop/lib
                              concolic-hop/convert-it))])
          (dynamic-require mod '#f))))
    (make-new-namespace)
    (values get-current-namespace make-new-namespace)))

(define (run-with-monitoring file.sch write-first-part-of-line)
  (define response-chan (make-channel))
  (define (start-computing-thread)
    (define namespace-to-use (get-current-namespace))
    (thread
     (λ ()
       (with-handlers ([exn:fail?
                        (λ (exn)
                          (channel-put response-chan exn))])
         (define-values (results cpu real gc)
           (time-apply
            (λ ()
              (parameterize ([current-namespace namespace-to-use]
                             [current-output-port (open-output-nowhere)])
                (define do-search
                  (dynamic-require (file.sch->file.rkt file.sch) 'counterexample))
                (do-search)))
            '()))
         (channel-put response-chan (list results cpu real gc))))))
  (let loop ([computing-thread (start-computing-thread)]
             [number-of-possibly-stuck-stacks 0])
    (sync
     (handle-evt
      (alarm-evt (+ (current-inexact-milliseconds) 500))
      (λ (_)
        (cond
          [(possibly-stuck-stack? computing-thread)
           (cond
             [(= number-of-possibly-stuck-stacks 5)
              ;; looks like it has been three seconds
              ;; (6 checks in a row, 500 msec apart)
              ;; where we are stuck at the mysterious
              ;; deadlocked stack, so let's restart
              (kill-thread computing-thread)
              (printf "stopped progressing, restarting\n")
              (make-new-namespace)
              (write-first-part-of-line)
              (loop (start-computing-thread) 0)]
             [else
              (loop computing-thread (+ number-of-possibly-stuck-stacks 1))])]
          [else
           (loop computing-thread 0)])))
     (handle-evt
      response-chan
      (λ (vals)
        (cond
          [(exn? vals)
           (printf "\n")
           (raise vals)]
          [else
           (apply values vals)]))))))

(define (possibly-stuck-stack? t)
  (define stack
    (continuation-mark-set->context
     (continuation-marks t)))
  (match stack
    [(cons (cons 'make-expr (srcloc path line col pos span)) _)
     (equal? (simplify-path (collection-file-path "term.rkt" "rosette" "base" "core"))
             (simplify-path path))]
    [_ #f]))

(module+ main
  (require racket/cmdline)

  (define stat-filename/#f #f)
  (command-line
   #:once-each
   ["--stat" filename "Append statistics record to the specified file"
             (set! stat-filename/#f filename)])

  (define (slowish? file.sch)
    ;; these are the files that take more than about two seconds (for me)
    (define s (path->string file.sch))
    (or (regexp-match? #rx"hors/fhnhn[.]sch" s)
        (regexp-match? #rx"hors/hrec[.]sch" s)
        (regexp-match? #rx"hors/l-zipmap[.]sch" s)
        (regexp-match? #rx"hors/mc91[.]sch" s)
        (regexp-match? #rx"hors/r-file[.]sch" s)
        (regexp-match? #rx"octy/ex-03[.]sch" s)
        (regexp-match? #rx"others/ack[.]sch" s)
        (regexp-match? #rx"others/argmin[.]sch" s)))
  (define widest
    (apply
     max
     (for/list ([file.sch (in-list sch-files)])
       (string-length (file.sch->string file.sch)))))
  (define (pad-it s) (string-append s (make-string (- widest (string-length s)) #\space)))

  (define stats
    (for/hash ([file.sch (in-list sch-files)]
               ;#:unless (slowish? file.sch) ;; uncomment this line to skip the slower files
               #:when (known-to-work? file.sch)
               )
      (define (write-first-part-of-line)
        (printf "generating ~a" (pad-it (file.sch->string file.sch)))
        (flush-output))
      (write-first-part-of-line)
      (define-values (msec stats)
        (get-counterexample-and-rewrite file.sch write-first-part-of-line))
      (printf " real ~as; ~a test~a solving ~as; ~a quer~a\n"
              (~r #:min-width 5 #:precision '(= 1) (/ msec 1000))
              (~a #:min-width 3 #:align 'right (hash-ref stats 'test-count))
              (if (= (hash-ref stats 'test-count) 1) "; " "s;")
              (~r #:min-width 5 #:precision '(= 1) (/ (hash-ref stats 'solve-real-nongc-time) 1000))
              (hash-ref stats 'solve-count)
              (if (= (hash-ref stats 'solve-count) 1) "y" "ies"))
      (values (file.sch->string file.sch)
              (if (hash-has-key? stats 'msec)
                  (error 'write-counterexample "hash has key msec in: ~a: ~a"
                         file.sch
                         stats)
                  (hash-set stats 'msec msec)))))
  (when stat-filename/#f
    (with-output-to-file stat-filename/#f #:exists 'append
      (λ () (pretty-write stats))))
  )

