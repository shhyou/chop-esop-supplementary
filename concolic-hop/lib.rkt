#lang racket/base

(require racket/match
         racket/string
         racket/set
         racket/class
         racket/port racket/pretty racket/format
         racket/contract

         (for-syntax racket/base
                     syntax/parse)

         (only-in rosette/safe
                  for/all

                  evaluate
                  complete-solution

                  define-symbolic*
                  constant? term?

                  sat sat? unsat? unknown?
                  assert distinct?
                  &&)
         (prefix-in rosette:
                    (only-in rosette/safe
                             equal?
                             procedure?
                             integer? <=
                             if not boolean?
                             list? null? pair? car cdr append cons

                             union? union-contents))

         "rosette.rkt"
         "loggers.rkt"
         "run-bounded.rkt"
         "state-passing.rkt"

         "data.rkt"
         "strategy-queue.rkt"
         "store.rkt"
         "type-spec-impl.rkt"
         "path.rkt"
         "conds.rkt"
         "funast.rkt"
         "track.rkt"
         )

(provide
 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

 (struct-out branch)
 (struct-out dispatch)
 (struct-out list-access)
 record-branch-point
 record-list-access
 concolic-null?
 concolic-pair?

 (struct-out test-info)
 (struct-out input-info)
 (struct-out concolic-statistics)

 integer
 boolean
 integer-range
 list-of
 ;; Some shorthand wrappers
 ->s
 or/s
 list/s

 (contract-out
  [concolic-test-timeout
   (parameter/c (or/c #f (and/c real? positive?)))]
  [concolic-test-memory
   (parameter/c (or/c #f (and/c exact-nonnegative-integer? positive?)))]
  [concolic-test-path-limit
   (parameter/c (or/c #f (and/c exact-nonnegative-integer? positive?)))]
  [concolic-test-enable-provenance?
   (parameter/c boolean?)])
 (recontract-out
  concolic-test-heartbeat-path-step
  concolic-test-heartbeat-pending-step
  concolic-test-heartbeat-new-clause-step)
 define-concolic-test

 abort-concolic-execution
 error-bug
 reraise-as-error-bug
 call-with-error-bug-rerouting
 prop-not-false
 prop-not-error-bug
 exn:fail:error-bug?
 prop-not-exn
 exn:fail?
 abort-data?

 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

 empty-provenance
 extend-provenance

 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

 (contract-out
  [all-initial-inputs ((listof input-info?) . -> . (listof input?))]
  [concretize-input ((or/c test-info? (listof symbol?))
                     input?
                     . -> . (hash/c symbol? any/c))])

 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

 (contract-out
  [interpret (input? type/c a$? . -> . input-arg/c)])

 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

 (contract-out
  [compile-smt (input? type/c a$? set? . -> . any)]
  [compile-path-constraint (input? path-constraint/c . -> . any)]
  [solve-for-inputs
   (;; argument
    (pending?)
    ;; optional instance argument for collecting statistics
    (concolic-state?)
    . ->* .
    (or/c (listof input?) unsat? unknown?))]
  [adjacent-pending (pending? path-constraint/c . -> . (listof pending?))]
  [run-with-concolic-inputs
   (;; arguments
    (test-info?
     input?)
    ;; optional configuration arguments
    (#:timeout (or/c #f (and/c real? positive?))
     #:memory (or/c #f (and/c exact-nonnegative-integer? positive?))
     #:path-limit (or/c #f (and/c exact-nonnegative-integer? positive?)))
    . ->* .
    test-record?)]
  [run-with-concrete-inputs
   (;; arguments
    (test-info?
     (hash/c symbol? any/c))
    ;; optional arguments
    (#:timeout (or/c #f (and/c real? positive?))
     #:memory (or/c #f (and/c exact-nonnegative-integer? positive?))
     #:path-limit (or/c #f (and/c exact-nonnegative-integer? positive?)))
    . ->* .
    test-record?)]
  [empty-concolic-instance ((-> concolic-queue?) test-info? . -> . concolic-state?)]
  [concolic-test
   (;; arguments
    ([test test-info?])
    ;; optional arguments
    (#:strategy [strategy (-> concolic-queue?)]
     #:all? [all? (or/c boolean? real?)]
     #:timeout [timeout (or/c #f (and/c real? positive?))]
     #:memory [memory (or/c #f (and/c exact-nonnegative-integer? positive?))]
     #:path-limit [path-limit (or/c #f (and/c exact-nonnegative-integer? positive?))]
     #:statistics? [statistics? any/c])
    . ->i .
    [_ (test statistics?)
       (cond [(and statistics? (not (unsupplied-arg? statistics?)))
              (list/c (or/c #f input?) concolic-statistics?)]
             [else
              (or/c #f input?)])])]))

(struct exn:fail:not-implemented exn:fail ()
  #:transparent)

;; Default to 30s and 256MB. Numbers chosen arbitrarily.
(define concolic-test-timeout (make-parameter 30))
(define concolic-test-memory (make-parameter (* 256 1024 1024)))
(define concolic-test-path-limit (make-parameter 10000))
(define concolic-test-enable-provenance? (make-parameter #f))

(define-syntax (define-concolic-test stx)
  (syntax-parse stx
    [(_ test-id:id
        #:inputs
        [X:id spec:expr] ...
        #:prop
        body:expr ...+)
     (syntax/loc stx
       (begin
         (define test-id
           (test-info
            (list
             (input-info
              'X spec)
             ...)
            (let ([test-id (λ (args)
                             (match-define (list X ...) args)
                             body ...)])
              test-id)))))]))

(define (record-branch-point rosette-value)
  (define concrete-value
    (get-current-concrete-value rosette-value))
  (if concrete-value
      (log-trace "branch: then"
                 (branch 'then rosette-value))
      (log-trace "branch: else"
                 (branch 'else rosette-value)))
  concrete-value)

(define (record-list-access rosette-value)
  (define is-null?
    (rosette:null? rosette-value))
  (define is-null?-concrete
    (get-current-concrete-value is-null?))
  (log-trace "list-access" (list-access is-null?-concrete is-null?))
  rosette-value)

(define concolic-null?
  (let ([null? (λ (value)
                 (rosette:null? (record-list-access value)))])
    null?))

(define concolic-pair?
  (let ([pair? (λ (value)
                 (rosette:pair? (record-list-access value)))])
    pair?))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(struct abort-data exn ()
  #:transparent)

(define (abort-concolic-execution message . args)
  (raise (abort-data (apply format message args)
                     (current-continuation-marks))))

(struct exn:fail:error-bug exn:fail ()
  #:transparent)
(define (error-bug [message #f])
  (cond
    [message
     (raise (exn:fail:error-bug (format "bug: ~a" message)
                                (current-continuation-marks)))]
    [else
     (raise (exn:fail:error-bug "bug" (current-continuation-marks)))]))

(define (reraise-as-error-bug exn)
  (raise (exn:fail:error-bug (exn-message exn)
                             (exn-continuation-marks exn))))

(define (call-with-error-bug-rerouting thunk #:exn? [exn? exn:fail?])
  (with-handlers ([exn? reraise-as-error-bug])
    (thunk)))

(define (prop-not-false rosette-value)
  (define val
    (record-branch-point (rosette:not rosette-value)))
  (cond
   [val  (cons 'fail val)]
   [else 'pass]))

(define (prop-not-error-bug thunk)
  (with-handlers ([exn:fail:error-bug? (λ (e) (cons 'fail e))])
    (thunk)
    'pass))

(define (prop-not-exn #:exns [exns? (list exn:fail?)]
                      thunk)
  (define (is-exns? e)
    (for/or ([the-exn? (in-list exns?)])
      (the-exn? e)))
  (with-handlers ([is-exns? (λ (e) (cons 'fail e))])
    (thunk)
    'pass))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (remove-ending-newline message)
  (define last-pos (sub1 (string-length message)))
  (cond
    [(and (not (negative? last-pos))
          (char=? #\newline (string-ref message last-pos)))
     (substring message 0 last-pos)]
    [else message]))
;
;
;
;
;
;
;     ;;;  ;;; ;;;;     ;;;      ;;;;     ;;;;  
;   ;;  ;;  ;;;   ;;   ;   ;    ;;  ;;   ;;  ;
;   ;;  ;   ;;     ;; ;;   ;;   ;   ;;   ;   ;;
;   ;;;     ;;     ;;      ;;  ;;       ;;;;;;;
;     ;;;   ;;     ;;   ;;;;;  ;;       ;;
;      ;;;  ;;     ;;  ;   ;;  ;;       ;;
;   ;   ;;  ;;     ;  ;;   ;;  ;;       ;;
;   ;;  ;;  ;;    ;   ;;  ;;;   ;;   ;   ;;   ;
;   ;;;;    ;;;;;;     ;;; ;;;;  ;;;;     ;;;;
;           ;;
;           ;;
;           ;;
;           ;;
;          ;;;;;


(define (empty-concolic-instance strategy test)
  (concolic-state
   test
   (strategy)
   (empty-path-status-record)
   '()
   (concolic-statistics 0 0 0 0)))

(define (empty-path-status-record)
  (make-hash))

;; TODO fix time complexity
(define (update-path-status! instance inputs path-constraint status
                             #:all-prefix? [all-prefix? #f])
  (define key
    (reverse
     (vector->list
      (path-constraint->key inputs path-constraint))))
  (hash-set! (concolic-state-path-status instance)
             key
             status)
  (when (and all-prefix? (not (null? key)))
    (let stash ([key (cdr key)])
      (when (not (null? key))
        (hash-set! (concolic-state-path-status instance)
                   key
                   status)
        (stash (cdr key))))))

;; query-path-status-prefix : concolic-state? path-constraint/c -> #f or symbol?
(define (query-path-status instance inputs path-constraint)
  (define key
    (reverse
     (vector->list
      (path-constraint->key inputs path-constraint))))
  (hash-ref (concolic-state-path-status instance)
            key
            (λ () #f)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;
;
;    ;;
;    ;;              ;;                                              ;;
;                    ;;                                              ;;
;                    ;;                                              ;;
;     ;  ;;; ;;;    ;;;;;;  ;;;;   ;;; ;;;;; ;;;;   ;;; ;;;  ;;;;   ;;;;;
;   ;;;   ;;;  ;;    ;;    ;;  ;    ;;; ; ;;;   ;;   ;;; ;  ;;  ;    ;;
;    ;;   ;;   ;;    ;;    ;   ;;   ;;    ;;     ;;  ;;     ;   ;;   ;;
;    ;;   ;;   ;;    ;;   ;;;;;;;   ;;    ;;     ;;  ;;    ;;;;;;;   ;;
;    ;;   ;;   ;;    ;;   ;;        ;;    ;;     ;;  ;;    ;;        ;;
;    ;;   ;;   ;;    ;;   ;;        ;;    ;;     ;;  ;;    ;;        ;;
;    ;;   ;;   ;;    ;;   ;;        ;;    ;;     ;   ;;    ;;        ;;
;    ;;   ;;   ;;    ;;  ; ;;   ;   ;;    ;;    ;    ;;     ;;   ;   ;;
;  ;;;;;;;;;; ;;;;    ;;;   ;;;;  ;;;;;;  ;;;;;;   ;;;;;;    ;;;;     ;;;
;                                         ;;
;                                         ;;
;                                         ;;
;                                         ;;
;                                        ;;;;;


(define interpret%
  (class object%
    (init inputs type ast)

    (define full-type type)
    (define full-ast ast)
    (define current-env (make-parameter 'no-current-environment))
    (match-define (struct* input ([type input-types]
                                  [map the-input-map]
                                  [model the-model]))
      inputs)

    (define/private (env-ref/report-with-ast index var-ast
                                             #:sub-ast [referred-ast #f])
      (define env (current-env))
      (define (report-out-of-bound)
        (define referred-ast-message
          (cond
            [referred-ast
             (display-a$-to-stringln referred-ast #:indent "  in: ")]
            [else
             ""]))
        (error 'interpret
               (string-append
                "variable index out bound\n"
                "  environment: ~a\n"
                "  variable: ~a\n"
                "~a"
                "~a")
               env
               var-ast
               referred-ast-message
               (display-a$-to-string var-ast #:indent "  in: ")))
      (env-ref env index report-out-of-bound))

    (define/private (refine-type-by-value/report-with-ast type-expected
                                                          value
                                                          referred-ast
                                                          #:referred-part
                                                          [referred-part #f])
      (define concrete-value
        (get-current-concrete-value value))
      (define tag
        (infer-value-tag concrete-value))
      (define refined-type
        (refine-tag≼_/#f tag type-expected))
      (define check-tuple-length
        (match refined-type
          [(struct* list-c ([types types]))
           (and (= (length types) (length concrete-value))
                (for/and ([type (in-list types)]
                          [elem (in-list concrete-value)])
                  (refine-tag≼_/#f (infer-value-tag elem) type)))]
          [_ #t]))
      (unless (and refined-type check-tuple-length)
        (parameterize ([display-a$-model (get-current-model)])
          (error 'interpret
                 (string-append
                  "contract violation: type mismatch\n"
                  "  expected: ~a\n"
                  "  given: ~a\n"
                  "  symbolic value: ~e\n"
                  "~a\n"
                  "~a")
                 (type/c-name type-expected)
                 (get-current-concrete-value value)
                 value
                 (display-a$-to-string referred-ast
                                       #:indent
                                       (cond
                                         [referred-part
                                          (format "  in: ~a\n      " referred-part)]
                                         [else
                                          "  in: "]))
                 (display-a$-to-string full-ast #:indent "  in: "))))
      (values tag refined-type))

    (define/private (refine-type-by-tag/report-with-ast type-expected
                                                        tag
                                                        #:sub-ast [referred-ast #f])
      (define refined-type
        (refine-tag≼_/#f tag type-expected))
      (unless refined-type
        (parameterize ([display-a$-model (get-current-model)])
          (error 'interpret
                 (string-append
                  "contract violation: type mismatch\n"
                  "  expected: ~a\n"
                  "  actual tag: ~a\n"
                  "~a"
                  "~a")
                 (type/c-name type-expected)
                 tag
                 (cond
                   [referred-ast
                    (display-a$-to-stringln referred-ast #:indent "  in: ")]
                   [else ""])
                 (display-a$-to-string full-ast #:indent "  in: "))))
      refined-type)

    (define/private (refine-type-by-ast/report-with-ast type-expected
                                                        referred-ast)
      (define refined-type
        (refine-ast≼_/#f (current-env) referred-ast type-expected))
      (unless refined-type
        (parameterize ([display-a$-model (get-current-model)])
          (error 'interpret
                 (string-append
                  "contract violation: type mismatch\n"
                  "  expected: ~a\n"
                  "~a"
                  "~a")
                 (type/c-name type-expected)
                 (display-a$-to-stringln referred-ast #:indent "  in: ")
                 (display-a$-to-string full-ast #:indent "  in: "))))
      refined-type)

    (define/private (eval-conds new-value new-type-expected conds-ast type
                                #:sub-ast [sub-ast #f]
                                #:sub-ast-message [sub-ast-message #f])
      ;; TODO 1: use first-ordre checks
      (define-values (new-value-tag refined-new-type)
        (refine-type-by-value/report-with-ast new-type-expected new-value
                                              (or sub-ast full-ast)
                                              #:referred-part sub-ast-message))
      (match-define (struct* a$conds ([label cond-label]))
        conds-ast)

      (define-values (clause-key clause-type target-label body-ast)
        (conds-table-ref-by-value conds-ast new-value))
      (cond
        [target-label
         (log-trace (format "dispatch ~a ~a" cond-label target-label)
                    (dispatch cond-label target-label new-value-tag new-value))
         (parameterize ([current-env (extend-env (current-env)
                                                 refined-new-type
                                                 new-value)])
           (eval-expr body-ast type))]
        [else
         (log-trace (format "dispatch ~a else" cond-label)
                    (dispatch cond-label #f new-value-tag new-value))
         (abort-concolic-execution "interpret: dispatch ~a else" cond-label)]))

    (define/private (eval-list/untyped list-ast type)
      (define branch-var
        (eval-expr (a$list-guard list-ast) boolean))
      (match list-ast
        [(a$empty _)
         (unless (or (list-of? type)
                     (equal? type (list-c '())))
           (error 'interpret "contract violation: type mismatch in eval-list"))
         (match type
           [(struct list-of _)
            (rosette:if branch-var
                        '()
                        (list list-of-magic-ending-value))]
           [(struct list-c _)
            '()])]
        [(a$cons _ car-ast cdr-ast)
         (define list-value
           (match type
             [(struct list-of (elem-type))
              (rosette:cons (eval-expr car-ast elem-type)
                            (eval-list/untyped cdr-ast type))]
             [(struct list-c ((cons car-type cdr-type)))
              (rosette:cons (eval-expr car-ast car-type)
                            (eval-list/untyped cdr-ast (list-c cdr-type)))]
             [_ (error 'interpret "contract violation: type mismatch in eval-list")]))
         list-value]))

    (define/private (eval-expr expr-ast type)
      (match expr-ast
        [(and local-ast (struct* a$x ([index index])))
         (match-define (struct* bound ([type local-var-type]
                                       [value local-var-value]))
           (env-ref/report-with-ast index local-ast))
         ;; TODO change this to check type directly agains local-var-type
         (refine-type-by-value/report-with-ast type local-var-value local-ast)
         local-var-value]
        [(and var-ast (struct* a$X ([variable var-value]
                                    [type var-type])))
         (refine-type-by-ast/report-with-ast type var-ast)
         var-value]
        [(and xs-ast (struct a$list _))
         (define refined-type
           (refine-type-by-ast/report-with-ast type xs-ast))
         (eval-list/untyped xs-ast refined-type)]
        [(and lambda-ast (struct* a$λ ([body conds-ast])))
         (match-define (struct arr ((list dom) range))
           (refine-type-by-ast/report-with-ast type lambda-ast))
         (define env (current-env))
         (fun (λ (arg)
                (parameterize ([current-env env])
                  (eval-conds arg dom conds-ast range
                              #:sub-ast lambda-ast
                              #:sub-ast-message "the argument of"))))]
        [(and let-ast (struct* a$let ([elim elim-ast]
                                      [body conds-ast])))
         (match elim-ast
           [(struct* a$%app ([fun (and fun-ast (struct a$x (fun-index)))]
                             [arg arg-ast]))
            (match-define (struct* bound ([type fun-type]
                                          [value f]))
              (env-ref/report-with-ast fun-index
                                       fun-ast
                                       #:sub-ast let-ast))
            (match-define (struct arr ((list fun-dom) fun-range))
              (refine-type-by-tag/report-with-ast fun-type 'arrow
                                                  #:sub-ast let-ast))
            (define reply-of-call
              (f (eval-expr arg-ast fun-dom)))
            (eval-conds reply-of-call fun-range conds-ast type
                        #:sub-ast let-ast
                        #:sub-ast-message "the value bound to define")]
           [(struct* a$car ([xs (and xs-ast (struct a$x (xs-index)))]))
            (match-define (struct* bound ([type xs-type]
                                          [value xs]))
              (env-ref/report-with-ast xs-index
                                       xs-ast
                                       #:sub-ast let-ast))
            (match (refine-type-by-tag/report-with-ast xs-type 'list
                                                       #:sub-ast let-ast)
              [(struct* list-of ([type elem-type]))
               (eval-conds (rosette:car xs) elem-type conds-ast type
                           #:sub-ast let-ast
                           #:sub-ast-message "the value bound to define")]
              [(struct* list-c ([types (cons elem-type _)]))
               (eval-conds (rosette:car xs) elem-type conds-ast type
                           #:sub-ast let-ast
                           #:sub-ast-message "the value bound to define")])]
           [(struct* a$cdr ([xs (and xs-ast (struct a$x (xs-index)))]))
            (match-define (struct* bound ([type xs-type]
                                          [value xs]))
              (env-ref/report-with-ast xs-index
                                       xs-ast
                                       #:sub-ast let-ast))
            (match (refine-type-by-tag/report-with-ast xs-type 'list
                                                       #:sub-ast let-ast)
              [(and rest-type (struct list-of _))
               (eval-conds (rosette:cdr xs) rest-type conds-ast type
                           #:sub-ast let-ast
                           #:sub-ast-message "the value bound to define")]
              [(struct* list-c ([types (cons _ rest-type)]))
               (eval-conds (rosette:cdr xs) (list-c rest-type) conds-ast type
                           #:sub-ast let-ast
                           #:sub-ast-message "the value bound to define")])])]))

    (define/public (evaluate)
      (parameterize ([current-env (empty-env)])
        (eval-expr full-ast full-type)))

    (super-new)
    ))

(define (interpret inputs type ast)
  (send (new interpret%
             [inputs inputs]
             [type type]
             [ast ast])
        evaluate))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;                                                                                    
;
;                                                                ;;
;                                          ;;                    ;;              ;;
;                                          ;;                                    ;;
;                                          ;;                                    ;;
;     ;;;;      ;;;    ;;; ;;;      ;;;   ;;;;;;;;; ;;;  ;;;      ;  ;;; ;;;    ;;;;;
;    ;;  ;;   ;;  ;;    ;;;  ;;   ;;  ;;   ;;    ;;; ;  ;   ;   ;;;   ;;;  ;;    ;;
;    ;   ;;   ;    ;    ;;   ;;   ;;  ;    ;;    ;;    ;;   ;;   ;;   ;;   ;;    ;;
;   ;;       ;;    ;;   ;;   ;;   ;;;      ;;    ;;         ;;   ;;   ;;   ;;    ;;
;   ;;       ;;    ;;   ;;   ;;     ;;;    ;;    ;;      ;;;;;   ;;   ;;   ;;    ;;
;   ;;       ;;    ;;   ;;   ;;      ;;;   ;;    ;;     ;   ;;   ;;   ;;   ;;    ;;
;   ;;       ;;    ;    ;;   ;;   ;   ;;   ;;    ;;    ;;   ;;   ;;   ;;   ;;    ;;
;    ;;   ;   ;;  ;;    ;;   ;;   ;;  ;;   ;;  ; ;;    ;;  ;;;   ;;   ;;   ;;    ;;
;     ;;;;     ;;;     ;;;; ;;;;  ;;;;      ;;;;;;;;;   ;;; ;;;;;;;;;;;;; ;;;;    ;;;
;
;


(define (format-solution sol)
  (with-output-to-string
    (λ ()
      (pretty-write sol))))



(define compile-smt%
  (class traverse-ast%
    (inherit traverse)
    (init-field list-access-vars)

    (define/private (compile-base-type var-value type)
      (match type
        [(? primitive-solvable?)
         (void)]
        [(struct* integer-range ([lower lower] [upper upper]))
         (define type-constraint
           (rosette:<= lower var-value upper))
         (log-concolic:constraint-debug "  ~a: ~a"
                                        var-value
                                        type-constraint)
         (assert type-constraint)]))

    (define/private (compile-conds conds-ast type)
      (define keys-for-primitive-types (make-hash))
      (for ([(clause-key clause-type target-label body-ast)
             (in-conds-table conds-ast)]
            #:when (or (primitive-solvable? clause-type)
                       (integer-range? clause-type)))
        (define type
          (match clause-type
            [(struct* primitive-solvable ([type type]))
             type]
            [(struct integer-range _)
             rosette:integer?]))
        (hash-update! keys-for-primitive-types
                      type
                      (λ (keys) (cons clause-key keys))
                      (λ () '())))
      (define distinct-constraint
        (apply &&
               (for/list ([(type keys) (in-hash keys-for-primitive-types)])
                 (apply distinct? keys))))
      (log-concolic:constraint-debug "  ~a: ~a"
                                     (a$conds-label conds-ast)
                                     distinct-constraint)
      (assert distinct-constraint))

    (define/private (compile-list list-ast type)
      (match list-ast
        [(a$empty (a$X branch-var-value (== boolean)))
         (match type
           [(struct* list-of ([type elem-type]))
            (when (not (set-member? list-access-vars branch-var-value))
              (log-concolic:constraint-debug "  #t = ~a : (list-of _)"
                                             branch-var-value)
              (assert branch-var-value))]
           [(struct* list-c ([types '()]))
            (log-concolic:constraint-debug "  #t = ~a : (list/s)"
                                           branch-var-value)
            (assert branch-var-value)])]
        [(a$cons (a$X branch-var-value (== boolean))
                 car-ast cdr-ast)
         (match type
           [(struct* list-of ([type elem-type]))
            ;; disallow list truncation
            (log-concolic:constraint-debug "  #f = ~a" branch-var-value)
            (assert (rosette:not branch-var-value))]
           [(struct* list-c ([types (cons car-type cdr-type)]))
            (log-concolic:constraint-debug "  #f = ~a : (list/s ~a _ ...)"
                                           branch-var-value
                                           car-type)
            (assert (rosette:not branch-var-value))])]))

    (define/private (compile-expr expr-ast type)
      (match expr-ast
        [(and var-ast (struct* a$X ([variable var-value]
                                    [type var-type])))
         (compile-base-type var-value var-type)]
        [_ (void)]))

    (define/augment (update-list list-ast type)
      (compile-list list-ast type)
      list-ast)

    (define/augment (update-conds new-value-type conds-ast type)
      (compile-conds conds-ast type)
      conds-ast)

    (define/augment (visit-expr expr-ast type)
      (compile-expr expr-ast type))

    (define/public (compile)
      (traverse))

    (super-new)
    ))

(define (compile-smt inputs type ast vars)
  (call-with-server
   (input-model inputs)
   (λ (server)
     (send (new compile-smt%
                [server server]
                [type type]
                [ast ast]
                [list-access-vars vars])
           compile))))

(define (compile-path-constraint inputs path-constraint)
  (define size (path-constraint-length path-constraint))
  (for ([i (in-naturals)]
        [condition (in-reversed-path-constraint path-constraint)])
    (log-concolic:constraint-debug "[~a/~a]  ~a"
                                   (~r i #:min-width 3)
                                   (~r size #:min-width 3)
                                   condition)
    (match condition
      [(branch 'then rosette-value)
       (assert (rosette:not (rosette:not rosette-value)))]
      [(branch 'else rosette-value)
       (assert (rosette:not rosette-value))]
      [(list-access is-null? rosette-value-is-null?)
       (when (constant? rosette-value-is-null?)
         (cond [is-null? (assert rosette-value-is-null?)]
               [else     (assert (rosette:not rosette-value-is-null?))]))]
      ;; TODO: tests
      [(dispatch label target-label value-tag rosette-value)
       (define-values (var-name conds-ast)
         (let/ec return!
           (store-for-each
            inputs
            (λ (var-name var-value type)
              (search-expr
               var-value
               (λ (conds-ast)
                 (when (equal? label (a$conds-label conds-ast))
                   (return! var-name conds-ast))))))))
       (cond
         [target-label
          (define-values (clause-key clause-type _target-label _body-ast)
            (conds-table-ref-by-label conds-ast target-label))
          (define dispatch-constraint
            (cond
              [(a$proc? clause-key)
               (rosette:procedure? rosette-value)]
              [(a$null? clause-key)
               (rosette:null? rosette-value)]
              [(a$pair? clause-key)
               (rosette:pair? rosette-value)]
              [else
               (rosette:equal? rosette-value clause-key)]))
          (log-concolic:constraint-debug "      ~a" dispatch-constraint)
          (assert dispatch-constraint)]
         [else
          ;; TODO: tests needed for this case
          (define keys-with-rosette-value
            (cons rosette-value
                  (for/list ([(clause-key clause-type target-label body-ast)
                              (in-conds-table conds-ast)]
                             #:when (or (primitive-solvable? clause-type)
                                        (integer-range? clause-type)))
                    clause-key)))
          (unless (or (andmap rosette:integer? keys-with-rosette-value)
                      (andmap rosette:boolean? keys-with-rosette-value))
            (log-concolic:constraint-warning
             (string-append "non-uniform path constraint\n"
                            " in: ~a"
                            " in variable ~a: ~a")
             conds-ast
             var-name
             (hash-ref (input-map inputs) var-name)))
          (define distinct-constraint
            (apply distinct? keys-with-rosette-value))
          (log-concolic:constraint-debug "      ~a" distinct-constraint)
          (assert distinct-constraint)])])))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO in update-list
(define update-ast%
  (class traverse-ast%
    (inherit get-model-value traverse-expr traverse-list)
    (inherit-field server
                   current-local-server
                   [full-ast ast]
                   [full-type type])

    (define/augment (update-list list-ast type)
      (match list-ast
        [(a$empty (and branch-var (struct* a$X ([variable var-value]
                                                [type (== boolean)]))))
         (match (get-model-value var-value)
           [#t (a$empty branch-var)]
           [#f
            (define elem-type
              (match type
                [(struct* list-of ([type elem-type]))
                 elem-type]
                [(struct* list-c ([types '()]))
                 (local-abort! server)]))
            (match-define (struct* decomp-ctxt ([locals locals]
                                                [locals-known locals-known]))
              (get-local-state (current-local-server)))
            (define new-var-value
              (fresh-symbolic-variable rosette:boolean?))
            (update-local-state! server
                                 (λ (the-old-model)
                                   (model-set the-old-model
                                              new-var-value
                                              #t)))
            (define new-car-ast
              (all-new-a$values server elem-type locals locals-known))
            (a$cons branch-var
                    new-car-ast
                    (a$empty (a$X new-var-value boolean)))])]
        [(a$cons (and branch-var (struct* a$X ([variable var-value]
                                               [type (== boolean)])))
                 car-ast
                 cdr-ast)
         ;; TODO: a correct update-list should _NOT_ truncate
         ;; lists as done here.
         ;; The extension of complete search theorem to lists
         ;; should only increase the length of lists during
         ;; the search process.
         (match (get-model-value var-value)
           [#t
            (log-concolic:constraint-error "Truncating lists with branch var ~a in ~a"
                                           var-value
                                           full-ast)
            (a$empty branch-var)]
           [#f
            (a$cons branch-var car-ast cdr-ast)])]))

    (super-new)))

;; note: the local state is a model (sat?) containing updated base values
(define (update-ast-top server type ast)
  (send (new update-ast%
             [server server]
             [type type]
             [ast ast])
        traverse))

(define (solve-for-inputs new-pending [instance/#f #f])
  (let/ec return!
    (match-define (struct* pending ([partial-inputs
                                     (and inputs
                                          (struct* input ([type input-types]
                                                          [map the-input-map]
                                                          [model old-model])))]
                                    [prediction predicted-path]))
      new-pending)
    (log-concolic:constraint-info "solving constraints")
    (when (path-constraint-empty? predicted-path)
      (log-concolic:constraint-debug "path constraint is empty; use the provided model")
      (return! inputs))
    (log-concolic:constraint-debug "  in:")
    (parameterize ([display-a$-model old-model])
      (for ([(var-name var-value) (in-hash the-input-map)]
            #:when (and (a$? var-value) (not (a$X? var-value))))
        (log-concolic:constraint-debug "    ~a:\n~a"
                                       var-name
                                       (display-a$-to-string
                                        var-value
                                        #:indent
                                        (+ 6 (string-length "concolic:constraint: "))))))
    (define-values (solve-results cpu real gc)
      (time-apply
       (λ ()
         (solve/allow-exception
          (λ ()
            (define vars
              (for/set ([condition (in-reversed-path-constraint predicted-path)]
                        #:when
                        (or (and (list-access? condition)
                             (constant? (list-access-value condition)))
                            (and (dispatch? condition)
                                 (dispatch-clause condition)
                                 (constant? (rosette:null? (dispatch-value condition))))))
                (match condition
                  [(struct* list-access ([value rosette-value-is-null?]))
                   rosette-value-is-null?]
                  [(struct* dispatch ([value rosette-value]))
                   (rosette:null? rosette-value)])))
            (for ([(var-name var-value) (in-hash the-input-map)])
              (compile-smt inputs (hash-ref input-types var-name) var-value vars))
            (compile-path-constraint inputs predicted-path))))
       '()))
    (match-define (list partial-model) solve-results)
    (when instance/#f
      (define stats (concolic-state-statistics instance/#f))
      (set-concolic-statistics-solve-count!
       stats
       (+ 1 (concolic-statistics-solve-count stats)))
      (set-concolic-statistics-solve-real-nongc-time!
       stats
       (+ (- real gc)
          (concolic-statistics-solve-real-nongc-time stats))))
    (when (or (unsat? partial-model) (unknown? partial-model))
      (log-concolic:constraint-info "constraints are unsatisfiable")
      (log-concolic:constraint-debug "  ~a" partial-model)
      (return! partial-model))
    (unless (sat? partial-model)
      (log-concolic:constraint-error "IMPOSSIBLE: not one of sat?, unsat? or unknown?: ~a"
                                     partial-model)
      (error 'solve-for-inputs "IMPOSSIBLE"))
    (log-concolic:constraint-info "constraints have a model")
    (for ([line (in-list (string-split (format-solution partial-model) "\n"))])
      (log-concolic:constraint-debug "  ~a" line))
    (define model-with-all-constants
      (model-union-prefer-right old-model partial-model))
    (define all-new-inputs
      (call-with-server
       model-with-all-constants
       (λ (server)
         (define new-input-map
           (for/hash ([(var-name var-ast) (in-hash the-input-map)])
             (define new-var-ast
               (update-ast-top server
                               (hash-ref input-types var-name)
                               var-ast))
             (values var-name new-var-ast)))
         (define new-model
           (get-local-state server))
         (input input-types
                new-input-map
                new-model))))
    all-new-inputs))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;
;
;                                      ;;;       ;;;
;                        ;;             ;;        ;;
;                        ;;             ;;        ;;
;                                       ;;        ;;
;                                       ;;        ;;
;   ;;; ;;;      ;;;;     ;    ;;; ;;;  ;; ;;;    ;; ;;;       ;;;    ;;;  ;;;   ;;; ;;
;    ;;;  ;;    ;;  ;   ;;;   ;  ;;     ;;;  ;;   ;;;  ;;    ;;  ;;    ;;   ;;    ;;; ;
;    ;;   ;;    ;   ;;   ;;  ;;   ;;    ;;   ;;   ;;    ;;   ;    ;    ;;   ;;    ;;
;    ;;   ;;   ;;;;;;;   ;;  ;;   ;;    ;;   ;;   ;;    ;;  ;;    ;;   ;;   ;;    ;;
;    ;;   ;;   ;;        ;;   ;   ;     ;;   ;;   ;;    ;;  ;;    ;;   ;;   ;;    ;;
;    ;;   ;;   ;;        ;;   ;;;;      ;;   ;;   ;;    ;;  ;;    ;;   ;;   ;;    ;;
;    ;;   ;;   ;;        ;;  ;          ;;   ;;   ;;   ;;   ;;    ;    ;;   ;;    ;;
;    ;;   ;;    ;;   ;   ;;  ;          ;;   ;;   ;;   ;     ;;  ;;    ;;  ;;;;;  ;;
;   ;;;; ;;;;    ;;;;  ;;;;;;;;;;;;;   ;;;; ;;;;  ; ;;;       ;;;       ;;; ;;  ;;;;;;
;                            ;     ;;;
;                           ;;      ;;
;                           ;;      ;
;                           ;;;   ;;
;                             ;;;;


(define (all-initial-inputs input-info-list)
  (define final-inputs
    (call-with-server
     #:name 'all-initial-inputs
     (sat)
     (λ (server)
       (define the-input-map
         (for/hash ([an-input (in-list input-info-list)])
           (match-define (struct* input-info ([name var-name]
                                              [type type]))
             an-input)
           (define var-value
             (all-new-a$values server
                               type
                               (empty-env)
                               (hash)))
           (values var-name var-value)))
       (define input-types
         (for/hash ([an-input (in-list input-info-list)])
           (match-define (struct* input-info ([name var-name]
                                              [type type]))
             an-input)
           (define refined-input-type
             (refine-ast≼_/#f (empty-env)
                              (hash-ref the-input-map var-name)
                              type))
           (values var-name refined-input-type)))
       (input input-types
              the-input-map
              (get-local-state server)))))
  final-inputs)

(define (concretize-input test-info-or-vars inputs)
  (reset-a$-local-variable-count!)
  (define var-names
    (cond
      [(test-info? test-info-or-vars)
       (for/list ([an-input (in-list (test-info-inputs test-info-or-vars))])
         (input-info-name an-input))]
      [else test-info-or-vars]))
  (for/hash ([var-name (in-list var-names)])
    (define var-datum
      (a$->datum inputs (hash-ref (input-map inputs) var-name)))
    (values var-name var-datum)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; checks if target-clause-label from a dispatch does not
;; appear in other dispatches in remaining-path-constraint
(define (does-not-appear-in? target-clause-label remaining-path-constraint)
  (for/and ([pc (in-reversed-path-constraint remaining-path-constraint)])
    (match pc
      [(struct branch _) #t]
      [(struct list-access _) #t]
      [(struct* dispatch ([clause other-target-label]))
       (not (and other-target-label
                 (equal? target-clause-label other-target-label)))])))

(define (find-cond-ast inputs label)
  (let/ec return!
    (store-for-each
     inputs
     (λ (var-name var-value type)
       (search-expr
        var-value
        (λ (conds-ast)
          (when (equal? label (a$conds-label conds-ast))
            (return! (list var-name var-value conds-ast)))))))
    'conds-ast-not-found))

(define augment-ast%
  (class traverse-ast%
    (inherit traverse
             bind-new-local-var!)

    (inherit-field server
                   [full-ast ast]
                   current-local-server)

    (init-field target-conds-label
                clause-key-tag
                clause-key)

    (define/private (refine-tag≼_/report-with-ast type-expected tag)
      (define refined-type
        (refine-tag≼_/#f tag type-expected))
      (unless refined-type
        (error 'augment-ast%:refine-tag≼_/report-with-ast
               "internal error: no refinement for ~a with ~a\n~a"
               type-expected
               tag
               (display-a$-to-string full-ast #:indent "  in: ")))
      refined-type)

    (define current-augment-result-server
      (make-parameter 'no-augment-server))

    (define/augment (update-conds new-value-type conds-ast type)
      (let/ec return!
        (match-define (struct* a$conds ([label this-conds-label]
                                        [table table]))
          conds-ast)
        (unless (equal? target-conds-label this-conds-label)
          (return! conds-ast))
        (define refined-new-value-type
          (refine-tag≼_/report-with-ast new-value-type clause-key-tag))
        (define body-ast
          (call-with-local-state
           (current-local-server)
           (get-local-state (current-local-server))
           (λ ()
             (bind-new-local-var! clause-key refined-new-value-type (a$x 0))
             (match-define (struct* decomp-ctxt ([locals locals]
                                                 [locals-known locals-known]))
               (get-local-state (current-local-server)))
             (all-new-a$exprs server
                              type
                              locals
                              locals-known))))
        (define-values (new-conds-ast new-clause)
          (conds-table-extend conds-ast
                              refined-new-value-type
                              clause-key
                              body-ast))
        (when (get-local-state (current-augment-result-server))
          (log-concolic:adjacent-warning
           "augment-ast%: augment answer is not #f: ~a\n~a\n~a"
           (get-local-state (current-augment-result-server))
           (display-a$-to-string conds-ast
                                 #:indent "               in: ")
           (display-a$-to-string full-ast
                                 #:indent "               in: ")))
        (set-local-state! (current-augment-result-server) new-clause)
        new-conds-ast))

    (define/public (augment-ast)
      (match-define (list (list new-full-ast new-clause))
        (call-with-server
         #f
         (λ (new-local-server)
           (parameterize ([current-augment-result-server new-local-server])
             (define new-full-ast (traverse))
             (list new-full-ast
                   (get-local-state (current-augment-result-server)))))))
      (values new-full-ast new-clause))

    (super-new)))

(define (adjacent-dispatch-targets server progress-count-server negate-index
                                   old-pending disp remaining-path-constraint)
  (match-define (struct* dispatch ([label label]
                                   [clause target-clause-label]
                                   [tag value-tag]
                                   [value rosette-value]))
    disp)
  (define inputs (pending-partial-inputs old-pending))
  (match-define (struct* input ([map old-input-map]
                                [type input-types]
                                [model the-old-model]))
    inputs)
  (match-define (list var-name full-ast (and conds-ast (struct a$conds _)))
    (find-cond-ast inputs label))

  (define rule (choose*! server '(m-new m-change)))
  (match rule
    ['m-new
     (define available-new-clause-keys
       (match value-tag
         [(? base-tags/c)
          (list rosette-value)]
         ['arrow
          (cond [target-clause-label '()]
                [else (list a$proc)])]
         ['list
          (define avail-tags
            (apply append
                   (for/list ([tag (in-list (list a$pair a$null))])
                     (define tag-exists?
                       (for/or ([(clause-key clause-type target-label body-ast)
                                 (in-conds-table conds-ast)])
                         (equal? tag clause-key)))
                     (if tag-exists? '() (list tag)))))
          (define is-pair?
            (call-with-model
             the-old-model
             (λ () (get-current-concrete-value (rosette:pair? rosette-value)))))
          (cond
            [(and (member a$null avail-tags)  (not is-pair?)) (list a$null)]
            [(and (member a$pair avail-tags)   is-pair?)      (list a$pair)]
            [(and (member a$null avail-tags))                 (list a$null)]
            [(and (member a$pair avail-tags))                 (list a$pair)]
            [else '()])]))
     (define new-clause-key
       (choose*! server available-new-clause-keys))
     (call-with-local-state
      server
      the-old-model
      (λ ()
        ;; TODO 2: use first-order checks to obtain clause-type
        ;; instead of value-tag
        (define-values (new-full-ast new-clause)
          (send (new augment-ast%
                     [server server]
                     [type (hash-ref input-types var-name)]
                     [ast full-ast]
                     [target-conds-label label]
                     [clause-key-tag value-tag]
                     [clause-key new-clause-key])
                augment-ast))
        (update-local-state! progress-count-server add1)
        (define progress-count (get-local-state progress-count-server))
        (when (= 0 (modulo progress-count (concolic-test-heartbeat-new-clause-step)))
          (log-concolic:heartbeat-debug "new clause: ~a expressions expanded"
                                        progress-count))
        (make-pending
         old-pending
         (input input-types
                (hash-set old-input-map var-name new-full-ast)
                (get-local-state server))
         (extend-path-constraint
          remaining-path-constraint
          (dispatch label
                    (a$clause-label new-clause)
                    value-tag
                    rosette-value))
         (list 'm-new negate-index))))]
    ['m-change
     (match-define (struct* a$conds ([label (== label)]
                                     [table table]))
       conds-ast)

     ;; for the [M-Change] rule to be applicable when
     ;; the current clause appears for the first time in the
     ;; path constraint, the cond-ast should not already
     ;; have a corresponding clause (target-clause-label = #f)
     (when (and target-clause-label
                (target-clause-label . does-not-appear-in? . remaining-path-constraint))
       (local-abort! server))

     ;; choose any existing clause as the new target, if
     (match-define (and new-target-clause
                        (struct* a$clause ([type clause-type]
                                           [label new-target-clause-label])))
       (choose*! server table))

     (when (union? clause-type)
       (log-concolic:constraint-error
        "union type should not appear in clause type in ~a in ~a"
        new-target-clause
        full-ast))
     ;; the new target clause dispatches on the same kind of value
     (unless (equal? value-tag (infer-type-tag clause-type))
       (local-abort! server))
     ;; and avoid choosing the old clause itself
     (when (equal? new-target-clause-label target-clause-label)
       (local-abort! server))

     (make-pending
      old-pending
      inputs
      (extend-path-constraint
       remaining-path-constraint
       (dispatch label new-target-clause-label value-tag rosette-value))
      (list 'm-change negate-index))]))

(define (adjacent-branches server negate-index
                           old-pending br remaining-path-constraint)
  (when (and (not (term? (branch-value br)))
             (not (constant? (branch-value br))))
    (local-abort! server))
  (match br
    [(branch 'then rosette-value)
     (make-pending
      old-pending
      (pending-partial-inputs old-pending)
      (extend-path-constraint
       remaining-path-constraint
       (branch 'else rosette-value))
      (list 'm-false negate-index))]
    [(branch 'else rosette-value)
     (make-pending
      old-pending
      (pending-partial-inputs old-pending)
      (extend-path-constraint
       remaining-path-constraint
       (branch 'then rosette-value))
      (list 'm-true negate-index))]))

(define (adjacent-list-accesses server negate-index
                                old-pending acc remaining-path-constraint)
  (match acc
    [(list-access #f _) ;; not null?; could be pair or non-list
     (local-abort! server)]
    [(list-access #t rosette-value-is-null?)
     #:when (not (constant? rosette-value-is-null?))
     (local-abort! server)]
    [(list-access #t rosette-value-is-null?)
     (make-pending
      old-pending
      (pending-partial-inputs old-pending)
      (extend-path-constraint
       remaining-path-constraint
       (list-access #f rosette-value-is-null?))
      (list 'm-list negate-index))]))

(define (adjacent-pending old-pending path-constraint)
  (define total-length (path-constraint-length path-constraint))
  (log-concolic:adjacent-info "computing adjacent nodes; total: ~a" total-length)
  (for ([condition (in-path-constraint path-constraint)])
    (log-concolic:adjacent-debug "    ~a" condition))
  (match-define (list new-pending-inputs)
    (call-with-server
     0
     (λ (progress-count-server)
       (call-with-server
        #f
        (λ (server)
          (do-adjacent-pending server progress-count-server
                               old-pending path-constraint
                               (- total-length 1) total-length))))))
  new-pending-inputs)

(define (do-adjacent-pending server progress-count-server
                             old-pending path-constraint negate-index total-length)
  (when (path-constraint-empty? path-constraint)
    (local-abort! server))
  (define c
    (last-path-condition path-constraint))
  (define remaining-path-constraint
    (path-constraint-initial path-constraint))

  (define rule (choose! server 'm-prefix 'other))
  (match rule
    ['m-prefix
     ;; if the current dispatch path condition is the one that
     ;; inserts a new clause in a cond expression, abort.
     (match c
       [(struct branch _)
        (void)]
       [(struct list-access _)
        (void)]
       [(struct* dispatch ([label label]
                           [clause target-clause-label]))
        (when (and target-clause-label
                   (target-clause-label . does-not-appear-in? . remaining-path-constraint))
          (local-abort! server))])
     (do-adjacent-pending server progress-count-server
                          old-pending (path-constraint-initial path-constraint)
                          (- negate-index 1) total-length)]
    ['other
     (when (= 0 (modulo (+ 1 negate-index) (concolic-test-heartbeat-path-step)))
       (log-concolic:heartbeat-debug "adjacent path constraint length: ~a/~a"
                                     (+ 1 negate-index) total-length))
     (match c
       [(struct branch _)
        (adjacent-branches server negate-index
                           old-pending c remaining-path-constraint)]
       [(struct list-access _)
        (adjacent-list-accesses server negate-index
                                old-pending c remaining-path-constraint)]
       [(struct dispatch _)
        (adjacent-dispatch-targets server progress-count-server negate-index
                                   old-pending c remaining-path-constraint)])]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;                                                                              
;                                                                              
;                                                                              
;                                                                              
;                                                                              
;                                    ;                           ;;            
;                                    ;                           ;;            
;                                   ;                                          
;                                   ;                                          
;   ;;; ;;;;;;  ;;;   ;;; ;;;      ;   ;;; ;;;  ;;;      ;;;      ;  ;;; ;;;   
;    ;;; ;  ;;   ;;    ;;;  ;;     ;    ;;;  ;;;  ;;    ;   ;   ;;;   ;;;  ;;  
;    ;;     ;;   ;;    ;;   ;;     ;    ;;   ;;   ;;   ;;   ;;   ;;   ;;   ;;  
;    ;;     ;;   ;;    ;;   ;;    ;     ;;   ;;   ;;        ;;   ;;   ;;   ;;  
;    ;;     ;;   ;;    ;;   ;;    ;     ;;   ;;   ;;     ;;;;;   ;;   ;;   ;;  
;    ;;     ;;   ;;    ;;   ;;    ;     ;;   ;;   ;;    ;   ;;   ;;   ;;   ;;  
;    ;;     ;;   ;;    ;;   ;;   ;      ;;   ;;   ;;   ;;   ;;   ;;   ;;   ;;  
;    ;;     ;;  ;;;;;  ;;   ;;   ;      ;;   ;;   ;;   ;;  ;;;   ;;   ;;   ;;  
;  ;;;;;;    ;;; ;;   ;;;; ;;;;  ;     ;;;; ;;;; ;;;;   ;;; ;;;;;;;;;;;;; ;;;; 
;                               ;                                              
;                                                                              
;                                                                              
;                                                                              
;                                                                              

(define (run-with-concolic-inputs the-test-info new-inputs
                                  [new-inputs-provenance #f]
                                  #:timeout [timeout (concolic-test-timeout)]
                                  #:memory [memory-limit (concolic-test-memory)]
                                  #:path-limit [path-limit (concolic-test-path-limit)])
  (match-define (struct* test-info ([inputs input-info-list]))
    the-test-info)
  (match-define (struct* input ([type input-types]
                                [map the-input-map]
                                [model new-model]))
    new-inputs)
  (define concolic-inputs
    (call-with-model
     new-model
     (λ ()
       (define concolic-inputs
         (for/list ([an-input (in-list input-info-list)])
           (define var-name (input-info-name an-input))
           (define var-type (hash-ref input-types var-name))
           (define ast (hash-ref the-input-map var-name))
           (log-concolic:inputs-info
            "  ~a is:\n~a"
            (~a var-name #:max-width 60 #:limit-marker "...")
            (parameterize ([display-a$-model (get-current-model)])
              (display-a$-to-string
               ast
               #:indent
               (+ 4 (string-length "concolic:status: ")))))
           (log-concolic:inputs-debug
            "    : ~a"
            (type/c-name var-type))
           (unless (equal? var-type (input-info-type an-input))
             (log-concolic:inputs-warning
              "  ~a: type mismatch: expected ~a but got ~a"
              (~a var-name #:max-width 60 #:limit-marker "...")
              (type/c-name (input-info-type an-input))
              (type/c-name var-type)))
           (interpret new-inputs
                      (hash-ref input-types var-name)
                      ast)))
       concolic-inputs)))
  (do-run-a-test
   'run-with-concolic-inputs
   the-test-info
   new-model
   concolic-inputs
   new-inputs-provenance
   timeout
   memory-limit
   path-limit))

(define (run-with-concrete-inputs the-test-info new-inputs
                                  #:timeout [timeout (concolic-test-timeout)]
                                  #:memory [memory-limit (concolic-test-memory)]
                                  #:path-limit [path-limit (concolic-test-path-limit)])
  (match-define (struct* test-info ([inputs input-info-list]))
    the-test-info)
  (define concrete-inputs
    (for/list ([an-input (in-list input-info-list)])
      (define var-name (input-info-name an-input))
      (define var-type (input-info-type an-input))
      (hash-ref new-inputs var-name)))
  (do-run-a-test
   'run-with-concrete-inputs
   the-test-info
   (sat) ;; new-model
   concrete-inputs
   #f ;; new-inputs-provenance
   timeout
   memory-limit
   path-limit))

(define (do-run-a-test who
                       the-test-info
                       new-model
                       concolic-inputs
                       new-inputs-provenance
                       timeout
                       memory-limit
                       path-limit)
  (match-define (struct* test-info ([inputs input-info-list]
                                    [action action]))
    the-test-info)

  (log-concolic:status-info "running with new inputs")
  (when new-inputs-provenance
    (log-concolic:inputs-debug "from ~a"
                               new-inputs-provenance))
  (define-values (path-constraint test-result)
    (call-with-model
     new-model
     (λ ()
       (call-with-tracing
        #:path-limit path-limit
        (λ ()
          (run-with-limit
           (λ ()
             (with-handlers ([abort-data?
                              (λ (data)
                                (cons 'abort data))])
               (action concolic-inputs)))
           #:timeout timeout
           #:memory memory-limit))))))
  (match test-result
    [(struct run:terminated:out-of-memory _)
     (log-concolic:status-info
      "execution result: out of memory in time {cpu: ~a, real: ~a, gc: ~a}"
      (run:terminated-cpu test-result)
      (run:terminated-real test-result)
      (run:terminated-gc test-result))

     (test-record
      new-model
      concolic-inputs
      path-constraint
      'out-of-memory
      (run:terminated-cpu test-result)
      (run:terminated-real test-result)
      (run:terminated-gc test-result))]
    [(struct run:terminated:killed _)
     (log-concolic:status-info
      "execution result: killed in time {cpu: ~a, real: ~a, gc: ~a}"
      (run:terminated-cpu test-result)
      (run:terminated-real test-result)
      (run:terminated-gc test-result))

     (test-record
      new-model
      concolic-inputs
      path-constraint
      'killed
      (run:terminated-cpu test-result)
      (run:terminated-real test-result)
      (run:terminated-gc test-result))]
    [(struct* run:timed:exn ([exception e]))
     (log-concolic:status-info
      "execution result: exception raised in time {cpu: ~a, real: ~a, gc: ~a}: ~a"
      (run:timed-cpu test-result)
      (run:timed-real test-result)
      (run:timed-gc test-result)
      (let ()
        (define message
          (with-output-to-string
            (λ ()
              (parameterize ([current-error-port (current-output-port)])
                ((error-display-handler) (exn-message e) e)))))
        (remove-ending-newline message)))

     (test-record
      new-model
      concolic-inputs
      path-constraint
      'exception
      (run:timed-cpu test-result)
      (run:timed-real test-result)
      (run:timed-gc test-result))]
    [(struct* run:timed:normal ([results results]))
     (log-concolic:status-info "terminated in time {cpu: ~a, real: ~a, gc: ~a} with ~a"
                               (run:timed-cpu test-result)
                               (run:timed-real test-result)
                               (run:timed-gc test-result)
                               results)

     (test-record
      new-model
      concolic-inputs
      path-constraint
      (car results)
      (run:timed-cpu test-result)
      (run:timed-real test-result)
      (run:timed-gc test-result))]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (main-test-loop! instance
                         #:all? all?/fuel
                         #:timeout timeout
                         #:memory memory-limit
                         #:path-limit path-limit)
  (define a-counter-example/#f
    #f)

  (let/ec break!
    (let while⟨1⟩ ()
      (let/ec continue!
        (when (concolic-queue-empty? (concolic-state-queue instance))
          (log-concolic:status-debug "queue is empty")
          (break!))

        (define new-pending-input
          (concolic-queue-extract! (concolic-state-queue instance)))
        (define inputs (pending-partial-inputs new-pending-input))
        (update-path-status! instance
                             inputs
                             (pending-prediction new-pending-input)
                             'tried
                             #:all-prefix? #t)

        (define record
          (run-with-concolic-inputs
           (concolic-state-test instance)
           inputs
           (and (concolic-test-enable-provenance?)
                (pending-provenance new-pending-input))
           #:timeout timeout
           #:memory memory-limit
           #:path-limit path-limit))

        (log-concolic:status-debug
         "updating path constraint record; length: ~a"
         (path-constraint-length
          (test-record-path-constraint record)))

        (define stats (concolic-state-statistics instance))
        (set-concolic-statistics-test-count!
         stats
         (+ 1 (concolic-statistics-test-count stats)))
        (set-concolic-statistics-eval-real-nongc-time!
         stats
         (+ (concolic-statistics-eval-real-nongc-time stats)
            (- (test-record-real record) (test-record-gc record))))
        (let ()
          (define-values (_unused_update-results cpu real gc)
            (time-apply
             (λ ()
               (update-path-status! instance
                                    inputs
                                    (test-record-path-constraint record)
                                    'explored
                                    #:all-prefix? #t))
             '()))
          (log-concolic:status-debug
           "search record updated; cpu: ~a, real: ~a, gc: ~a"
           cpu real gc))

        (when (test-failed? (test-record-result record))
          (define test-return-value
            (cdr (test-record-result record)))
          (set! a-counter-example/#f inputs)

          (printf "~a failed with "
                  (object-name (test-info-action (concolic-state-test instance))))
          (cond
            [(exn:fail? test-return-value)
             (printf "exception: ")
             (parameterize ([current-error-port (current-output-port)])
               ((error-display-handler) (exn-message test-return-value)
                                        test-return-value))]
            [else
             (printf "result: ~a\n" test-return-value)])
          (printf "Inputs:\n")
          (define bad-inputs
            (call-with-model
             (input-model inputs)
             (λ ()
               (for/hash ([an-input (in-list
                                     (test-info-inputs
                                      (concolic-state-test instance)))])
                 (define var-name (input-info-name an-input))
                 (define var-type (hash-ref (input-type inputs) var-name))
                 (define ast (hash-ref (input-map inputs) var-name))
                 (define ast-datum (a$->datum inputs ast))
                 (parameterize ([display-a$-model (input-model inputs)])
                   (printf "  ~a is:\n~a"
                           var-name
                           (with-output-to-string
                             (λ ()
                               (port-count-lines! (current-output-port))
                               (printf "    ")
                               (pretty-write ast-datum)))))
                 (values var-name ast)))))
          (set-concolic-state-bad-inputs!
           instance
           (append (concolic-state-bad-inputs instance)
                   (list bad-inputs)))
          (when (or (not all?/fuel)
                    (and (real? all?/fuel)
                         (>= (length (concolic-state-bad-inputs instance))
                             all?/fuel)))
            (break!)))

        (log-concolic:status-debug "computing new pending nodes")
        (define-values (adjacent-pending-inputs pending-input-count)
          (let ()
            (match-define-values ((list adjacent-pending-inputs)
                                  cpu real gc)
              (time-apply
               (λ ()
                 (adjacent-pending
                  new-pending-input
                  (test-record-path-constraint record)))
               '()))
            (define pending-input-count
              (length adjacent-pending-inputs))
            (log-concolic:status-debug
             "~a adjcent inputs; cpu: ~a, real: ~a, gc: ~a"
             (~a (length adjacent-pending-inputs) #:min-width 6 #:align 'right)
             cpu real gc)
            (values adjacent-pending-inputs pending-input-count)))
        ;; TODO: fix time complexity
        (let ()
          (define-values (_unused_void_result cpu real gc)
            (time-apply
             (λ ()
               (for ([i (in-naturals)]
                     [next-pending-input (in-list adjacent-pending-inputs)])
                 (define predicted-path-constraint
                   (pending-prediction next-pending-input))
                 (when (= 0 (modulo i (concolic-test-heartbeat-pending-step)))
                   (collect-garbage)
                   (log-concolic:heartbeat-debug "pending inputs: ~a/~a"
                                                 i pending-input-count))
                 (when (not (query-path-status instance
                                               (pending-partial-inputs next-pending-input)
                                               predicted-path-constraint))
                   (define new-inputss
                     (solve-for-inputs next-pending-input instance))
                   (when (list? new-inputss)
                     (for ([new-inputs (in-list new-inputss)])
                       (update-path-status! instance
                                            new-inputs
                                            predicted-path-constraint
                                            'queued)
                       (concolic-queue-insert!
                        (concolic-state-queue instance)
                        (pending new-inputs
                                 predicted-path-constraint
                                 (pending-provenance next-pending-input))))))))
             '()))
          (log-concolic:status-debug
           "pending inputs queued; cpu: ~a, real: ~a, gc: ~a"
           cpu real gc)))

      (while⟨1⟩)))

  a-counter-example/#f)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (empty-provenance) '())
(define (extend-provenance provenance new-provenance-info)
  (cons new-provenance-info provenance))

(define (make-pending old-pending partial-inputs prediction new-provenance-info)
  (cond
    [(concolic-test-enable-provenance?)
     (pending partial-inputs prediction
              (extend-provenance (pending-provenance old-pending)
                                 new-provenance-info))]
    [else
     (pending partial-inputs prediction (empty-provenance))]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (concolic-test test
                       #:all? [all?/fuel #t]
                       #:strategy [strategy
                                   (ignore-locals-adapter
                                    breadth-first-search-strategy)]
                       #:timeout [timeout (concolic-test-timeout)]
                       #:memory [memory-limit (concolic-test-memory)]
                       #:path-limit [path-limit (concolic-test-path-limit)]
                       #:statistics? [statistics? #f])
  (define instance
    (empty-concolic-instance strategy test))

  (log-concolic:status-debug "computing initial store(s)")
  (define new-inputss
    (all-initial-inputs (test-info-inputs test)))

  (log-concolic:status-debug "setting up the queue")
  (for ([new-inputs (in-list new-inputss)])
    (concolic-queue-insert!
     (concolic-state-queue instance)
     (pending
      new-inputs
      (empty-path-constraint)
      (empty-provenance))))

  (log-concolic:status-info "starting main test loop")
  (define result
    (main-test-loop! instance
                     #:all? all?/fuel
                     #:timeout timeout
                     #:memory memory-limit
                     #:path-limit path-limit))

  (cond
    [statistics?
     (list result
           (concolic-state-statistics instance))]
    [else
     result]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(module* internals #f
  (provide (all-from-out (submod ".."))))
