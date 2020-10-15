#lang racket/base

(require racket/match
         racket/hash
         racket/sequence ;; for sequence/c
         racket/pretty
         racket/port
         racket/contract

         (for-syntax racket/base
                     syntax/parse)

         (only-in rosette/safe
                  constant constant?
                  expression
                  [union-contents rosette:union-contents])

         "state-passing.rkt"

         "data.rkt"
         "store.rkt"
         "conds.rkt"
         "funast.rkt"
         )

(provide
 ;; match expander; (-> path-constraint/c)
 empty-path-constraint

 ;; match expander; (path-constraint/c path-condition/c . -> . path-constraint/c)
 extend-path-constraint

 (contract-out
  [path-constraint-empty? (path-constraint/c . -> . boolean?)]
  [path-constraint-length (path-constraint/c . -> . exact-nonnegative-integer?)]
  [in-path-constraint (path-constraint/c . -> . (sequence/c path-condition/c))]
  [in-reversed-path-constraint (path-constraint/c . -> . (sequence/c path-condition/c))]
  [last-path-condition (path-constraint/c . -> . path-condition/c)]
  [path-constraint-initial (path-constraint/c . -> . path-constraint/c)]
  [path-constraint->key (input? path-constraint/c
                                . -> . (vectorof path-condition-key/c))]))

(define-logger concolic:pathkey)

;
;
;
;
;
;
;
;
;    ;;;;;;;;;;;
;   ;  ;   ;
;  ;   ;   ;
;      ;   ;
;      ;   ;
;      ;   ;
;      ;    ;
;      ;    ;
;     ;;    ;
;     ;;     ;
;     ;      ;
;
;
;
;
;

(define-match-expander empty-path-constraint
  (syntax-parser
    [(_)              (syntax/loc this-syntax '())])
  (syntax-parser
    [_:id             (syntax/loc this-syntax empty-path-constraint-proc)]
    [(_ arg:expr ...) (syntax/loc this-syntax (empty-path-constraint-proc arg ...))]))
(define/contract (empty-path-constraint-proc)
  (-> path-constraint/c)
  '())
(define (path-constraint-empty? pcs) (null? pcs))
(define (path-constraint-length pcs) (length pcs))
;; in-path-constraint
;; iterates the given path constraint from the front
;; (first path condition first)
(define (in-path-constraint pcs)
  (in-list (reverse pcs)))
;; in-reversed-path-constraint
;; iterates the given path constraint from the rear
;; (last path condition first)
(define in-reversed-path-constraint in-list)
;; extend-path-constraint
;; adds a path condition to the end of the given path constraint
(define-match-expander extend-path-constraint
  (syntax-parser
    [(_ initial-pattern:expr last-path-condition-pattern:expr)
     (syntax/loc this-syntax
       (cons last-path-condition-pattern initial-pattern))])
  (syntax-parser
    [_:id             (syntax/loc this-syntax extend-path-constraint-proc)]
    [(_ arg:expr ...) (syntax/loc this-syntax (extend-path-constraint-proc arg ...))]))
(define/contract (extend-path-constraint-proc pcs pc)
  (path-constraint/c path-condition/c . -> . path-constraint/c)
  (cons pc pcs))
;; last-path-condition
;; returns the last path condition in the given path constraint
(define (last-path-condition pcs)
  (car pcs))
;; path-constraint-initial
;; computes the initial segment of the given path constraint
(define (path-constraint-initial pcs)
  (cdr pcs))

(define (rosette-term->key symbolic-variable-map term)
  (match term
    [(constant _ ty)
     (hash-ref symbolic-variable-map term)]
    [(expression rator rands ...)
     (cons rator
           (for/list ([rand (in-list rands)])
             (rosette-term->key symbolic-variable-map rand)))]
    [(or (? a$proc?) (? a$null?) (? a$pair?) (? boolean?) (? number?)) term]))

(struct renaming (inputs var-count var-map) #:transparent)

(define (map-variable! server X)
  (unless (hash-has-key? (renaming-var-map (get-local-state server))
                         (a$X-variable X))
    (match-define (struct* renaming ([inputs inputs]
                                     [var-count var-count]
                                     [var-map var-map]))
      (get-local-state server))
    (set-local-state! server
                      (renaming inputs
                                (+ 1 var-count)
                                (hash-set var-map
                                          (a$X-variable X)
                                          (a$X≡ var-count (a$X-type X))))))
  (define new-var (hash-ref (renaming-var-map (get-local-state server))
                            (a$X-variable X)))
  new-var)

(define (a$list->a$list≡ server list-ast)
  (match list-ast
    [(struct a$empty (branch-var))
     (define new-var (map-variable! server branch-var))
     (a$empty≡ new-var)]
    [(struct a$cons (branch-var car-ast cdr-ast))
     (define new-var (map-variable! server branch-var))
     (define car≡ (a$expr->a$expr≡ server car-ast))
     (define cdr≡ (a$list->a$list≡ server cdr-ast))
     (a$cons≡ new-var car≡ cdr≡)]))

(define (a$expr->a$expr≡ server ast)
  (match ast
    [(struct a$x (index))
     (a$x≡ index)]
    [(and X (struct a$X _))
     (define new-var (map-variable! server X))
     new-var]
    [(struct a$λ (conds-ast))
     (a$λ≡)]
    [(and list-ast (struct a$list _))
     (a$list->a$list≡ server list-ast)]
    [(struct* a$let ([elim elim-ast]
                     [body conds-ast]))
     (match elim-ast
       [(struct* a$%app ([fun (struct a$x (fun-index))]
                         [arg arg-ast]))
        (define arg≡ (a$expr->a$expr≡ server arg-ast))
        (a$let≡ (a$%app≡ (a$x≡ fun-index)
                         arg≡))]
       [(struct* a$car ([xs (struct a$x (xs-index))]))
        (a$let≡ (a$car≡ (a$x≡ xs-index)))]
       [(struct* a$cdr ([xs (struct a$x (xs-index))]))
        (a$let≡ (a$cdr≡ (a$x≡ xs-index)))])]))

;; path-constraint->key
;; produces a comparable representation of the given path constraint
;; *must be in forward order*
(define (path-constraint->key inputs path-constraint)
  (match-define (list global-symbolic-variable-map)
    (call-with-server
     (hash)
     (λ (server)
       (match-define (struct* input ([map the-input-map]))
         inputs)
       (for ([var-name (in-hash-keys the-input-map)])
         (define var-value (hash-ref the-input-map var-name))
         (match var-value
           [(and (struct a$X _) X)
            (update-local-state!
             server
             (λ (var-map)
               (hash-set var-map (a$X-variable X) (a$X≡ var-name (a$X-type X)))))]
           [(and (struct a$list _) list-ast)
            (define var-count 0)

            (define (declare-var! var-ast)
              (update-local-state!
               server
               (λ (var-map)
                 (hash-set var-map
                           (a$X-variable var-ast)
                           (a$X≡ (a$X-name-list var-name var-count)
                                 (a$X-type var-ast)))))
              (set! var-count (+ 1 var-count)))

            (define (declare-list! list-ast)
              (match list-ast
                [(a$empty branch-var)
                 (declare-var! branch-var)]
                [(a$cons branch-var car-ast cdr-ast)
                 (declare-var! branch-var)
                 (declare-expr! car-ast)
                 (declare-list! cdr-ast)]))

            (define (declare-expr! expr)
              (match expr
                [(and (struct a$X _) X)
                 (declare-var! X)]
                [(and (struct a$list _) list-ast)
                 (declare-list! list-ast)]
                [(struct a$λ _)
                 (void)]))

            (declare-list! list-ast)]
           [(struct a$λ _)
            (void)]))
       (get-local-state server))))
  (log-concolic:pathkey-debug
   "~a"
   (with-output-to-string
     (λ ()
       (port-count-lines! (current-output-port))
       (printf "path-constraint->key:\n")
       (printf "                    map:\n")
       (printf "                      ")
       (pretty-print global-symbolic-variable-map)
       (printf "                    path constraint:"))))
  (match-define (list path-keys)
    (call-with-server
     (renaming inputs 0 global-symbolic-variable-map)
     (λ (server)
       (define path-keys
         (for/list ([condition (in-path-constraint path-constraint)])
           (log-concolic:pathkey-debug "  ~a" condition)
           (match condition
             [(struct* branch ([target where]))
              (eq? where 'then)]
             [(struct* list-access ([target where]))
              (list-access≡ where)]
             [(struct* dispatch ([label label] [clause #f]))
              (dispatch-else≡ label)]
             [(struct* dispatch ([label label] [clause target-label]))
              (define symbolic-variable-map
                (renaming-var-map (get-local-state server)))
              (define conds-ast
                (let/ec return!
                  (store-for-each
                   (renaming-inputs (get-local-state server))
                   (λ (var-name var-value type)
                     (search-expr
                      var-value
                      (λ (conds-ast)
                        (when (equal? label (a$conds-label conds-ast))
                          (return! conds-ast))))))
                  'conds-ast-not-found))
              (define-values (clause-key clause-type _tagert-label body-ast)
                (conds-table-ref-by-label conds-ast target-label))
              (define body≡
                (a$expr->a$expr≡ server body-ast))
              (dispatch≡ label
                         (rosette-term->key symbolic-variable-map clause-key)
                         body≡)])))
       path-keys)))
  (apply vector-immutable path-keys))
