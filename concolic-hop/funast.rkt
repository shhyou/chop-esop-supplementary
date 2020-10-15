#lang racket/base

(require racket/match
         racket/port
         racket/sequence ;; for sequence/c
         racket/contract/base
         racket/class
         racket/dict

         (prefix-in rosette:
                    (only-in rosette/safe
                             integer?
                             boolean?
                             car
                             cdr
                             if))
         (only-in rosette/safe
                  evaluate
                  complete-solution
                  sat
                  define-symbolic*)
         "rosette.rkt"
         "state-passing.rkt"

         "data.rkt"
         "conds.rkt"
         "store.rkt"
         "type-spec-impl.rkt")

(provide
 reset-a$-local-variable-count!
 display-a$-model
 display-a$-to-string
 display-a$-to-stringln
 display-a$
 display-a$ln
 (contract-out
  [a$->datum (input? a$? . -> . any/c)]
  [type/c-name (type/c . -> . any/c)])

 search-expr
 traverse-ast%
 (struct-out decomp-ctxt)

 (contract-out
  [all-new-a$values (server?
                     type/c
                     (env/c (bound/c a$x?))
                     (hash/c a$tags/c (env/c (bound/c (cons/c real? a$x?))))
                     . -> .
                     a$value?)]
  [all-new-a$exprs (server?
                    type/c
                    (env/c (bound/c a$x?))
                    (hash/c a$tags/c (env/c (bound/c (cons/c real? a$x?))))
                    . -> .
                    a$expr?)]))

(define local-var-counter 0)
(define (reset-a$-local-variable-count!)
  (set! local-var-counter 0))
(define (fresh-a$-local-variable basename)
  (define old-counter local-var-counter)
  (set! local-var-counter (add1 local-var-counter))
  (string->uninterned-symbol (format "~a~a" basename old-counter)))


;
;
;                                                          ;;;
;                         ;;                        ;;    ;  ;;
;            ;;           ;;                        ;;   ;;
;            ;;                                          ;;
;            ;;                                          ;;
;     ;;;   ;;;;;;;;; ;;;  ;  ;;; ;;;      ;;; ;;;   ;  ;;;;;;;;;   ;;;
;   ;;  ;;   ;;    ;;; ; ;;;   ;;;  ;;    ;  ;;    ;;;   ;;   ;;     ;
;   ;;  ;    ;;    ;;     ;;   ;;   ;;   ;;   ;;    ;;   ;;    ;;   ;
;   ;;;      ;;    ;;     ;;   ;;   ;;   ;;   ;;    ;;   ;;    ;;   ;
;     ;;;    ;;    ;;     ;;   ;;   ;;    ;   ;     ;;   ;;     ;   ;
;      ;;;   ;;    ;;     ;;   ;;   ;;    ;;;;      ;;   ;;     ;; ;
;   ;   ;;   ;;    ;;     ;;   ;;   ;;   ;          ;;   ;;      ; ;
;   ;;  ;;   ;;  ; ;;     ;;   ;;   ;;   ;          ;;   ;;      ;;
;   ;;;;      ;;;;;;;;; ;;;;;;;;;; ;;;;  ;;;;;;;  ;;;;;;;;;;     ;;
;                                        ;     ;;;               ;
;                                       ;;      ;;               ;
;                                       ;;      ;                ;
;                                       ;;;   ;;              ;;;
;                                         ;;;;                ;;


(define display-a$-model (make-parameter #f))
(define display-a$-indent (make-parameter ""))
(define display-a$-env (make-parameter '()))

(define (display-a$-nest action #:indent [indent "  "])
  (parameterize ([display-a$-indent
                  (string-append (cond [(string? indent) indent]
                                       [(exact-nonnegative-integer? indent)
                                        (make-string indent #\space)]
                                       [else ""])
                                 (display-a$-indent))])
    (action)))

(define (do-a$-env-ref n)
  (with-handlers ([exn:fail? (λ (_) (format "_uu:~a" n))])
    (format "~a" (list-ref (display-a$-env) n))))

(define (do-display-a$conds conds-ast)
  (cond
    [(conds-table-empty? conds-ast)
     (printf "(case@~a ~a)"
             (a$conds-label conds-ast)
             (do-a$-env-ref 0))]
    [else
     (define (format-key key)
       (cond
         [(display-a$-model)
          => (λ (model)
               (format "~a:~a" key (evaluate key model)))]
         [else
          (format "~a" key)]))
     (display-a$-nest
      (λ ()
        (printf "(case@~a ~a"
                (a$conds-label conds-ast)
                (do-a$-env-ref 0))
        (for ([(clause-key clause-type label body-ast) (in-conds-table conds-ast)])
          (define key-str (format-key clause-key))
          (define label-str (format "~a" label))
          (define display-clause-in-new-line?
            (match body-ast
              [(or (struct a$x _) (struct a$X _)) #f]
              [(or (struct a$λ _) (struct a$list _) (struct a$let _)) #t]))
          (printf "\n~a~a:[~a" (display-a$-indent) label-str key-str)
          (display-a$-nest
           #:indent (+ (string-length label-str)
                       2
                       (if display-clause-in-new-line?
                           0
                           (+ 1 (string-length key-str))))
           (λ ()
             (if display-clause-in-new-line?
                 (printf "\n~a" (display-a$-indent))
                 (write-char #\space))
             (do-display-a$ body-ast)))
          (printf "]"))
        (printf ")")))]))

(define (do-display-a$list ast)
  (match ast
    [(a$empty (struct* a$X ([variable var-value])))
     (printf "empty@~a" var-value)]
    [(a$cons (struct* a$X ([variable var-value]))
             car-ast cdr-ast)
     (display-a$-nest
      (λ ()
        (printf "(cons@~a\n~a" var-value (display-a$-indent))
        (do-display-a$ car-ast)
        (printf "\n~a" (display-a$-indent))
        (do-display-a$ cdr-ast)
        (printf ")")))]))

;; TODO
(define (do-display-a$ ast)
  (match ast
    [(struct a$x (index))
     (printf "~a" (do-a$-env-ref index))]
    [(struct* a$X ([variable var-value]
                   [type var-type]))
     (printf "~a" var-value)
     (when (display-a$-model)
       (printf ":~a"
               (call-with-model
                (display-a$-model)
                (λ () (get-current-concrete-value var-value)))))]
    [(and xs-ast (struct a$list _))
     (do-display-a$list xs-ast)]
    [(struct a$λ (body))
     (display-a$-nest
      (λ ()
        (define new-name (fresh-a$-local-variable 'x))
        (printf "(λ (~a)\n~a" new-name (display-a$-indent))
        (parameterize ([display-a$-env (cons new-name (display-a$-env))])
          (do-display-a$conds body))
        (printf ")")))]
    [(struct a$let (elim-ast body))
     (define new-name (fresh-a$-local-variable 'x))
     (printf "(define ~a" new-name)
     (match elim-ast
       [(struct a$%app ((struct a$x (fun-index)) arg))
        (define fun-str (do-a$-env-ref fun-index))
        (display-a$-nest
         (λ ()
           (printf "\n~a(~a " (display-a$-indent) fun-str)
           (display-a$-nest
            #:indent (+ 2 (string-length fun-str))
            (λ () (do-display-a$ arg)))
           (printf ")")))]
       [(struct a$car ((struct a$x (xs-index))))
        (define xs-str (do-a$-env-ref xs-index))
        (printf " (car ~a)" xs-str)]
       [(struct a$cdr ((struct a$x (xs-index))))
        (define xs-str (do-a$-env-ref xs-index))
        (printf " (cdr ~a)" xs-str)])
     (printf ")\n~a" (display-a$-indent))
     (parameterize ([display-a$-env (cons new-name (display-a$-env))])
       (do-display-a$conds body))]
    [(struct a$conds _)
     (do-display-a$conds ast)]))

(define (display-a$ ast)
  (define-values (next-line next-col next-pos)
    (port-next-location (current-output-port)))
  (parameterize ([display-a$-env '()])
    (display-a$-nest
     #:indent (or next-col "")
     (λ () (do-display-a$ ast)))))

(define (display-a$ln ast)
  (display-a$ ast)
  (newline))

(define (display-a$-to-string ast
                              #:indent [indent ""]
                              #:format [display-a$ display-a$])
  (with-output-to-string
    (λ ()
      (port-count-lines! (current-output-port))
      (write-string
       (cond
         [(string? indent) indent]
         [(exact-nonnegative-integer? indent)
          (make-string indent #\space)]
         [else ""]))
      (display-a$ ast))))

(define (display-a$-to-stringln ast
                                #:indent [indent ""])
  (display-a$-to-string ast #:indent indent #:format display-a$ln))


(define a$->datum-inputs (make-parameter 'a$->datum-inputs))
(define a$->datum-env (make-parameter 'a$->datum-env))

(define dead-end
  '(error "ASSERT_UNREACHABLE"))

(define (do-a$conds->datum new-name conds-ast)
  (cond
    [(conds-table-empty? conds-ast) dead-end]
    [else
     (define clauses-datum
       (for/list ([(clause-key clause-type target-label body-ast)
                   (in-conds-table conds-ast)])
         (define body-datum
           (parameterize ([a$->datum-env (cons new-name (a$->datum-env))])
             (do-a$->datum body-ast)))
         (cond
           [(a$proc? clause-key)
            (cons clause-key `[(procedure? ,new-name) ,body-datum])]
           [(a$null? clause-key)
            (cons clause-key `[(null? ,new-name) ,body-datum])]
           [(a$pair? clause-key)
            (cons clause-key `[(pair? ,new-name) ,body-datum])]
           [else
            (define key-datum
              (call-with-model
               (input-model (a$->datum-inputs))
               (λ () (get-current-concrete-value clause-key))))
            (cons key-datum `[(equal? ,new-name ,key-datum) ,body-datum])])))
     `(cond
        ,(dict-ref clauses-datum a$proc (λ () `[(procedure? ,new-name) ,dead-end]))
        ,(dict-ref clauses-datum a$null (λ () `[(null? ,new-name) ,dead-end]))
        ,(dict-ref clauses-datum a$pair (λ () `[(pair? ,new-name) ,dead-end]))
        ,@(for/list ([(clause-key clause-datum) (in-dict clauses-datum)]
                     #:when (not (a$tags? clause-key)))
            clause-datum)
        [else ,dead-end])]))

(define (do-a$list->datum xs-ast)
  (match xs-ast
    [(a$empty _)
     'null]
    [(a$cons _ car-ast cdr-ast)
     `(cons ,(do-a$->datum car-ast)
            ,(do-a$list->datum cdr-ast))]))

(define (do-a$->datum expr-ast)
  (match expr-ast
    [(struct a$x (index))
     (list-ref (a$->datum-env) index)]
    [(struct* a$X ([variable var-value]
                   [type var-type]))
     (call-with-model
      (input-model (a$->datum-inputs))
      (λ () (get-current-concrete-value var-value)))]
    [(and xs-ast (struct a$list _))
     (do-a$list->datum xs-ast)]
    [(struct a$λ (body))
     (define new-name (fresh-a$-local-variable 'x))
     (define body-datum (do-a$conds->datum new-name body))
     `(λ (,new-name) ,body-datum)]
    [(struct a$let (elim-ast body))
     (define new-name (fresh-a$-local-variable 'x))
     (define rhs
       (match elim-ast
         [(struct a$%app ((struct a$x (fun-index)) arg))
          (list (list-ref (a$->datum-env) fun-index)
                (do-a$->datum arg))]
         [(struct a$car ((struct a$x (xs-index))))
          (list 'car (list-ref (a$->datum-env) xs-index))]
         [(struct a$cdr ((struct a$x (xs-index))))
          (list 'cdr (list-ref (a$->datum-env) xs-index))]))
     (define body-datum
       (do-a$conds->datum new-name body))
     `(let ([,new-name ,rhs])
        ,body-datum)]))

(define (a$->datum inputs ast)
  (parameterize ([a$->datum-inputs inputs]
                 [a$->datum-env '()])
    (do-a$->datum ast)))

(define (type/c-name type)
  (match type
    [(== boolean) 'boolean]
    [(== integer) 'integer]
    [(integer-range low high)
     (list 'integer-range low high)]
    [(struct arr ((list dom-type) range-type))
     (list '->s (type/c-name dom-type) (type/c-name range-type))]
    [(struct* list-of ([type elem-type]))
     (list 'list-of (type/c-name elem-type))]
    [(struct* list-c ([types types]))
     (cons 'list/s (map type/c-name types))]
    [(struct* union ([types types]))
     (cons 'or/s (map type/c-name types))]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;
;
;                                                                    ;;;
;                                                                     ;;
;    ;;                                                               ;;
;    ;;                                                               ;;
;    ;;                                                               ;;
;   ;;;;;;;;; ;;;  ;;;   ;;;;  ;;;;   ;;;;   ;;; ;;;  ;;;     ;;;     ;;
;    ;;    ;;; ;  ;   ;   ;;    ;;   ;;  ;    ;;; ; ;;  ;;   ;   ;    ;;
;    ;;    ;;    ;;   ;;   ;;   ;    ;   ;;   ;;    ;;  ;   ;;   ;;   ;;
;    ;;    ;;         ;;   ;;   ;   ;;;;;;;   ;;    ;;;          ;;   ;;
;    ;;    ;;      ;;;;;    ;  ;    ;;        ;;      ;;;     ;;;;;   ;;
;    ;;    ;;     ;   ;;    ;; ;    ;;        ;;       ;;;   ;   ;;   ;;
;    ;;    ;;    ;;   ;;     ;;     ;;        ;;    ;   ;;  ;;   ;;   ;;
;    ;;  ; ;;    ;;  ;;;     ;;      ;;   ;   ;;    ;;  ;;  ;;  ;;;   ;;
;     ;;;;;;;;;   ;;; ;;;;   ;        ;;;;  ;;;;;;  ;;;;     ;;; ;;;;;;;;
;
;


(define (search-conds conds-ast action)
  (action conds-ast)
  (for ([(clause-key clause-type target-label ast)
         (in-conds-table conds-ast)])
    (search-expr ast action)))

(define (search-list list-ast action)
  (match list-ast
    [(struct a$empty _)
     (void)]
    [(struct a$cons (_ car-ast cdr-ast))
     (search-expr car-ast action)
     (search-list cdr-ast action)]))

(define (search-expr ast action)
  (match ast
    [(or (struct a$x _)
         (struct a$X _))
     (void)]
    [(and list-ast (struct a$list _))
     (search-list list-ast action)]
    [(struct a$λ (body-ast))
     (search-conds body-ast action)]
    [(struct a$let (elim-ast body-ast))
     (match elim-ast
       [(struct a$%app (fun-ast arg-ast))
        (search-expr arg-ast action)]
       [(or (struct a$car _)
            (struct a$cdr _))
        (void)])
     (search-conds body-ast action)]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define (hash-map/as-hash h f)
  (for/hash ([(key value) (in-hash h)])
    (values key (f value))))

(struct decomp-ctxt (locals locals-known)
  #:guard (struct-guard/c (env/c (bound/c a$x?))
                          (hash/c a$tags/c (env/c (bound/c (cons/c real? a$x?)))))
  #:transparent)

(define traverse-ast%
  (class object%
    [init-field
     server
     [(full-type type)]
     [(full-ast ast)]]

    (field
     [current-local-server (make-parameter 'no-local-server)])

    (define/private (refine-ast≼_/report-with-ast ast type)
      (define refined-type
        (refine-ast≼_/#f (decomp-ctxt-locals
                          (get-local-state
                           (current-local-server)))
                         ast
                         type))
      (unless refined-type
        (error 'update-ast%:refine-ast≼_/report-with-ast
               "internal error: no refinement for ~a with ~a\n~a"
               type
               ast
               (display-a$-to-string full-ast #:indent "  in: ")))
      refined-type)

    (define/private (refine-type≼_/report-with-ast type-expected type)
      (define refined-type
        (refine-type≼_/#f type type-expected))
      (unless refined-type
        (error 'update-ast%:refine-type≼_/report-with-ast
               "internal error: no refinement for ~a with ~a\n~a"
               type-expected
               type
               (display-a$-to-string full-ast #:indent "  in: ")))
      refined-type)

    (define/public (get-model-value var-value)
      ((get-local-state server) var-value))

    (define/match (shift-+1 x)
      [((struct bound (type (struct a$x (index)))))
       (bound type (a$x (+ 1 index)))])

    (define/match (shift-cdr-+1 x)
      [((struct bound (type (cons fuel (struct a$x (index))))))
       (bound type (cons fuel (a$x (+ 1 index))))])

    (define/public (bind-new-local-var! clause-key
                                        refined-new-value-type
                                        new-var-ast)
      (update-local-state!
       (current-local-server)
       (match-lambda
         [(struct* decomp-ctxt ([locals locals]
                                [locals-known locals-known]))
          (define shifted-known-locals
            (hash-map/as-hash
             locals-known
             (λ (env-tagged)
               (env-map shift-cdr-+1 env-tagged))))
          (decomp-ctxt
           (extend-env (env-map shift-+1 locals)
                       refined-new-value-type
                       new-var-ast)
           (cond
             [(not (a$tags? clause-key))
              shifted-known-locals]
             [else
              (hash-update
               shifted-known-locals
               clause-key
               (λ (env-tagged)
                 (extend-env env-tagged refined-new-value-type
                             (cons (hash-ref a$tag-fuel clause-key)
                                   new-var-ast)))
               (λ () ;; failure thunk: no env for the current clause-key
                 (empty-env)))]))])))

    (define/private (decrement-var-fuel tag var)
      (update-local-state!
       (current-local-server)
       (match-lambda
         [(struct* decomp-ctxt ([locals locals]
                                [locals-known locals-known]))
          (decomp-ctxt
           locals
           (hash-update
            locals-known
            tag
            (λ (env-tagged)
              (env-map
               (match-lambda
                 [(struct* bound ([type  var-type]
                                  [value (cons fuel var-ast)]))
                  (bound var-type
                         (cons (if (equal? var-ast var) (sub1 fuel) fuel)
                               var-ast))])
               env-tagged))))])))

    (define/public (traverse-conds new-value-type conds-ast type)
      (define new-conds-ast
        (update-conds new-value-type conds-ast type))
      (traverse-conds-recur new-value-type new-conds-ast type))

    (define/pubment (update-conds new-value-type conds-ast type)
      (inner conds-ast update-conds new-value-type conds-ast type))

    (define/private (traverse-conds-recur new-value-type conds-ast type)
      (match-define (struct* a$conds ([label label]
                                      [table table]))
        conds-ast)
      (define new-table
        (for/list ([(clause-key clause-type target-label body-ast)
                    (in-conds-table conds-ast)])
          (define refined-new-value-type
            (refine-type≼_/report-with-ast new-value-type clause-type))
          (define dead?
            (match refined-new-value-type
              [(struct* list-c ([types '()]))
               (equal? clause-key a$pair)]
              [(struct* list-c ([types (cons _ _)]))
               (equal? clause-key a$null)]
              [_ #f]))
          (cond
            [dead?
             (a$clause clause-key clause-type target-label body-ast)]
            [else
             (define new-body-ast
               (call-with-local-state
                (current-local-server)
                (get-local-state (current-local-server))
                (λ ()
                  (bind-new-local-var! clause-key refined-new-value-type (a$x 0))
                  (traverse-expr body-ast type))))
             (a$clause clause-key clause-type target-label new-body-ast)])))
      (a$conds label new-table))

    (define/public (traverse-list list-ast type)
      (define new-list-ast
        (update-list list-ast type))
      (match new-list-ast
        [(and empty-ast (a$empty _))
         empty-ast]
        [(a$cons branch-var
                 car-ast
                 cdr-ast)
         (define-values (car-type cdr-type)
           (match type
             [(struct* list-of ([type elem-type]))
              (values elem-type
                      (list-of elem-type))]
             [(struct* list-c ([types (cons first-type rest-types)]))
              (values first-type
                      (list-c rest-types))]))
         (a$cons branch-var
                 (traverse-expr car-ast car-type)
                 (traverse-list cdr-ast cdr-type))]))

    (define/pubment (update-list list-ast type)
      (inner
       (match list-ast
         [(a$empty (and branch-var (struct* a$X ([variable var-value]
                                                 [type (== boolean)]))))
          (match (get-model-value var-value)
            [#t (a$empty branch-var)])]
         [(a$cons (and branch-var (struct* a$X ([variable var-value]
                                                [type (== boolean)])))
                  car-ast
                  cdr-ast)
          (match (get-model-value var-value)
            [#f
             (a$cons branch-var car-ast cdr-ast)])])
       update-list list-ast type))

    (define/public (traverse-expr ast type)
      (visit-expr ast type)
      (match ast
        [(and local-ast (struct a$x _))
         local-ast]
        [(and var-ast (struct a$X _))
         var-ast]
        [(and xs-ast (struct a$list _))
         (define xs-type
           (refine-ast≼_/report-with-ast xs-ast type))
         (traverse-list xs-ast xs-type)]
        [(and lambda-ast (struct* a$λ ([body body-ast])))
         (match-define (arr (list dom-type) range-type)
           (refine-ast≼_/report-with-ast lambda-ast type))
         (define new-body-ast
           (traverse-conds dom-type body-ast range-type))
         (a$λ new-body-ast)]
        [(and let-ast (struct* a$let ([elim elim-ast]
                                      [body body-ast])))
         (match-define (and decomp (struct* decomp-ctxt ([locals locals])))
           (get-local-state (current-local-server)))
         (call-with-local-state
          (current-local-server)
          decomp
          (λ ()
            (match elim-ast
              [(struct* a$%app ([fun (and fun-ast (struct a$x (fun-index)))]
                                [arg arg-ast]))
               (match-define (arr (list dom-type) range-type)
                 (bound-type (env-ref locals fun-index)))
               (decrement-var-fuel a$proc fun-ast)
               (a$let (a$%app fun-ast (traverse-expr arg-ast dom-type))
                      (traverse-conds range-type body-ast type))]
              [(and car-elim-ast (struct* a$car ([xs (struct a$x (xs-index))])))
               (define car-type
                 (match (bound-type (env-ref locals xs-index))
                   [(struct* list-of ([type elem-type]))
                    elem-type]
                   [(struct* list-c ([types (cons car-type _)]))
                    car-type]))
               (decrement-var-fuel a$pair (a$x xs-index))
               (a$let car-elim-ast
                      (traverse-conds car-type body-ast type))]
              [(and cdr-elim-ast (struct* a$cdr ([xs (struct a$x (xs-index))])))
               (define cdr-type
                 (match (bound-type (env-ref locals xs-index))
                   [(and xs-type (struct list-of _))
                    xs-type]
                   [(struct* list-c ([types (cons _ cdr-type)]))
                    (list-c cdr-type)]))
               (decrement-var-fuel a$pair (a$x xs-index))
               (a$let cdr-elim-ast
                      (traverse-conds cdr-type body-ast type))])))]))

    (define/pubment (visit-expr ast type)
      (inner (void) visit-expr ast type))

    (define/public (traverse)
      (match-define (list new-full-ast)
        (call-with-server
         (decomp-ctxt (empty-env) (hash))
         (λ (local-server)
           (parameterize ([current-local-server local-server])
             (traverse-expr full-ast full-type)))))
      new-full-ast)

    (super-new)
    ))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;
;
;                                                        ;
;                                                        ;
;                                                      ;;;;
;                                                     ;; ;;;
;                                                    ;;  ; ;
;   ;;; ;;;      ;;;;  ;;;; ;;;;  ;;;;        ;;;    ;;  ;
;    ;;;  ;;    ;;  ;   ;;   ;;    ;;        ;   ;   ;;;;
;    ;;   ;;    ;   ;;   ;;   ;;   ;        ;;   ;;    ;;;
;    ;;   ;;   ;;;;;;;   ;;   ;;   ;             ;;      ;;;
;    ;;   ;;   ;;         ;  ; ;  ;           ;;;;;     ; ;;;
;    ;;   ;;   ;;         ;; ; ;; ;          ;   ;;     ;  ;;
;    ;;   ;;   ;;          ;;   ;;          ;;   ;;  ;  ;  ;;
;    ;;   ;;    ;;   ;     ;;   ;;          ;;  ;;;  ;; ; ;;
;   ;;;; ;;;;    ;;;;      ;    ;            ;;; ;;;; ;;;;
;                                                       ;
;                                                       ;
;
;

(define (fresh-list-branch-var server concrete-value)
  (define boolean (primitive-solvable rosette:boolean?))
  (define var-value (fresh-symbolic-variable (primitive-solvable-type boolean)))
  (update-local-state!
   server
   (λ (the-old-model)
     (model-set the-old-model var-value concrete-value)))
  (a$X var-value boolean))

(define (all-new-a$values server type locals locals-known)
  (define rule (choose! server 'local 'new))
  (match rule
    ['local
     (define local-var (choose*! server locals))
     (define local-var-type (bound-type local-var))
     ;; ad-hoc subtyping
     (unless (or (equal? type local-var-type)
                 (and (union? type) (member local-var-type (union-types type))))
       (local-abort! server))
     (bound-value local-var)]
    ['new
     (match type
       [(or (struct primitive-solvable _)
            (struct integer-range _))
        (define var-value
          (match type
            [(struct* primitive-solvable ([type ty]))
             (fresh-symbolic-variable ty)]
            [(struct integer-range _)
             (fresh-symbolic-variable rosette:integer?)]))
        (update-local-state!
         server
         (λ (the-old-model)
           (model-set the-old-model var-value (default-value-of (empty-env) type))))
        (a$X var-value type)]
       [(struct arr _)
        (empty-canonical-function)]
       [(struct list-of _)
        (a$empty (fresh-list-branch-var server #t))]
       [(struct list-c (elem-types))
        (define elem-values
          (for/list ([elem-type (in-list elem-types)])
            (all-new-a$values server elem-type locals locals-known)))
        ;; build list AST
        (define xs
          (let loop ([elem-values elem-values])
            (define branch-var
              (fresh-list-branch-var server (null? elem-values)))
            (cond
              [(null? elem-values)
               (a$empty branch-var)]
              [else
               (define xs-rest
                 (loop (cdr elem-values)))
               (a$cons branch-var (car elem-values) xs-rest)])))
        xs]
       [(struct union (types))
        (define sub-type (choose*! server types))
        (all-new-a$values server sub-type locals locals-known)])]))

(define (all-new-a$exprs server type locals locals-known)
  (define rule (choose! server 'value 'havoc 'car 'cdr))
  (match rule
    ['value
     (all-new-a$values server type locals locals-known)]
    ['havoc
     (define local-f ;; locally bound procedures
       (choose*! server
                 (hash-ref locals-known a$proc
                           (λ () (empty-env)))))
     (define arg
       (all-new-a$values server
                         (car (arr-domains (bound-type local-f)))
                         locals
                         locals-known))
     (empty-let-expression
      (a$%app (cdr (bound-value local-f)) arg))]
    [(and rule (or 'car 'cdr))
     (define list-selector
       (match rule
         ['car a$car]
         ['cdr a$cdr]))
     (define all-local-xs ;; locally bound lists
       (for/list ([local-xs (in-env (hash-ref locals-known a$pair
                                              (λ () (empty-env))))]
                  #:when (> (car (bound-value local-xs)) 0)) ;; fuel
         local-xs))
     (define local-xs (choose*! server all-local-xs))
     (match (bound-type local-xs)
       [(struct* list-c ([types '()]))
        (local-abort! server)]
       [_ (void)])
     (empty-let-expression
      (list-selector
       (cdr (bound-value local-xs))))]))
