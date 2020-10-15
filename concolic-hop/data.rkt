#lang racket/base

(require racket/contract/base
         racket/list
         racket/math

         (only-in rosette/safe
                  sat? unsat? unknown?

                  function? solvable?
                  constant?
                  [union? rosette:union?])

         racket/generic
         )

(provide
 (except-out (all-defined-out)
             (struct-out type-decl))
 type-decl)

(struct bound (type value)
  #:transparent)

(define (bound/c value/c)
  (struct/c bound type/c value/c))

(define (env? val) (and (list? val) (andmap bound? val)))
(define env/c listof)
(define (empty-env) '())
(define (extend-env env type value)
  (cons (bound type value) env))
(define (env-rest env)
  (cdr env))
(define (env-ref env index
                 [failure (λ () (error 'env-ref "variable index out of bound"))])
  (unless (and (<= 0 index) (< index (length env)))
    (failure))
  (list-ref env index))
(define (env-set env index type value
                 [failure (λ () (error 'env-set "variable index out of bound"))])
  (unless (and (<= 0 index) (< index (length env)))
    (failure))
  (list-set env index (bound type value)))
(define (env-map f env)
  (map f env))
(define (in-env xs)
  (in-list xs))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(struct branch (target value)
  #:transparent)

;; clause : (or/c label? #f)
(struct dispatch (label clause tag value)
  #:transparent)

(struct list-access (target value)
  #:transparent)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; temporary -- as type/c is used in the type of a$clause
(struct type-decl ()
  #:constructor-name make-type
  #:transparent)

(define type/c
  (flat-named-contract 'type/c
                       type-decl?))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(struct label (name)
  #:guard (struct-guard/c natural?)
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc label port mode)
     (cond
       ;; write
       [(equal? #t mode)
        (write-string "#(struct:label " port)
        (write (label-name label) port)
        (write-char #\) port)]
       ;; display
       [(equal? #f mode)
        (write-char #\L port)
        (display (label-name label) port)]
       ;; print or display
       [else
        (write-char #\L port)
        (print (label-name label) port mode)]))])

(struct a$ ()
  #:transparent)

(struct a$expr a$ () #:transparent)
(struct a$value a$expr () #:transparent)
(struct a$elim a$ () #:transparent)

;; a$clause-type is the most precise (no union!) type
;; of a$clause-key resulting from tag checking
(struct a$clause (key type label body)
  #:guard (struct-guard/c any/c ;; a symbolic expression or one of a$tags/c
                          (and/c type/c (recursive-contract (not/c union?)))
                          label?
                          a$expr?)
  #:transparent)
(struct a$conds a$ (label table)
  #:guard (struct-guard/c label? (listof a$clause?))
  #:transparent)

(struct a$x a$value (index)
  #:guard (struct-guard/c natural?)
  #:transparent)
(struct a$X a$value (variable type)
  #:guard (struct-guard/c constant? type/c) ;; must be a base type
  #:transparent)
(struct a$λ a$value (body)
  #:guard (struct-guard/c a$conds?)
  #:transparent)

(struct a$list a$value (guard)
  #:guard (struct-guard/c a$X?)
  #:transparent)
(struct a$cons a$list (car cdr)
  #:guard (struct-guard/c a$X? a$value? a$list?)
  #:transparent)
(struct a$empty a$list ()
  #:guard (struct-guard/c a$X?)
  #:transparent)

(struct a$let a$expr (elim body)
  #:guard (struct-guard/c a$elim? a$conds?)
  #:transparent)

(struct a$%app a$elim (fun arg)
  #:guard (struct-guard/c a$x? a$value?)
  #:transparent)
(struct a$car a$elim (xs)
  #:guard (struct-guard/c a$x?)
  #:transparent)
(struct a$cdr a$elim (xs)
  #:guard (struct-guard/c a$x?)
  #:transparent)

(define a$proc (string->uninterned-symbol "proc?"))
(define (a$proc? v)
  (eq? v a$proc))

(define a$null (string->uninterned-symbol "null?"))
(define (a$null? v)
  (eq? v a$null))
(define a$pair (string->uninterned-symbol "pair?"))
(define (a$pair? v)
  (eq? v a$pair))

(define a$tags/c
  (or/c a$proc a$null a$pair))

(define (a$tags? key)
  (member key (list a$proc a$null a$pair)))

;; hack; should've limited repeated usage of a$car and a$cdr instead
(define a$tag-fuel
  (hash a$proc +inf.0
        a$null 0
        a$pair 2))

(define tag/c
  (flat-named-contract 'tag/c
                       (or/c 'integer 'boolean 'arrow 'list)))

(define base-tags/c
  (flat-named-contract 'base-tag/c
                       (or/c 'integer 'boolean)))

(struct fun (proc)
  #:guard (struct-guard/c procedure?)
  #:property prop:procedure (struct-field-index proc)
  #:transparent)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define path-condition/c
  (or/c branch? dispatch? list-access?))
(define path-constraint/c (listof path-condition/c))

(struct a$X-name-list (name count)
  #:guard (struct-guard/c symbol? natural?)
  #:transparent)
(define a$X-name/c
  (or/c natural?
        symbol?
        a$X-name-list?))

(struct a$x≡ (index)
  #:guard (struct-guard/c natural?)
  #:transparent)
(struct a$X≡ (count type)
  #:guard (struct-guard/c a$X-name/c type/c)
  #:transparent)
(struct a$λ≡ ()
  #:transparent)
(struct a$list≡ (guard)
  #:guard (struct-guard/c a$X≡?)
  #:transparent)

(define a$≡-value/c (or/c a$x≡? a$X≡? a$λ≡? a$list≡?))

(struct a$empty≡ a$list≡ ()
  #:guard (struct-guard/c a$X≡?)
  #:transparent)
(struct a$cons≡ a$list≡ (car cdr)
  #:guard (struct-guard/c a$X≡? a$≡-value/c a$list≡?)
  #:transparent)


(struct a$elim≡ ()
  #:transparent)
(struct a$let≡ (elim)
  #:guard (struct-guard/c a$elim≡?)
  #:transparent)

(struct a$%app≡ a$elim≡ (fun arg)
  #:guard (struct-guard/c a$x≡? a$≡-value/c)
  #:transparent)
(struct a$car≡ a$elim≡ (xs)
  #:guard (struct-guard/c a$x≡?)
  #:transparent)
(struct a$cdr≡ a$elim≡ (xs)
  #:guard (struct-guard/c a$x≡?)
  #:transparent)

(define a$≡-expr/c
  (or/c a$≡-value/c a$let≡?))

(struct dispatch-else≡ (label)
  #:transparent)
(struct dispatch≡ (label key kind)
  #:guard (struct-guard/c label? any/c a$≡-expr/c)
  #:transparent)

(struct list-access≡ (target)
  #:guard (struct-guard/c boolean?)
  #:transparent)

(define path-condition-key/c
  (or/c
   ;; branches
   #f #t
   ;; dispatches
   dispatch≡? dispatch-else≡?
   ;; list accesses
   list-access≡?))

(define test-result/c
  (or/c 'pass
        'killed
        'out-of-memory
        'exception
        (cons/c 'abort any/c)
        (cons/c 'fail any/c)))

(define (test-failed? test-result)
  (and (pair? test-result)
       (equal? (car test-result) 'fail)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(struct integer-range type-decl (lower upper)
  #:guard (let ()
            (define struct-guard-integer?-integer?
              (struct-guard/c integer? integer?))
            (define (integer-range-guard/c lower upper name)
              (struct-guard-integer?-integer? lower upper name)
              (unless (<= lower upper)
                (raise-arguments-error 'integer-range
                                       "lower ≤ upper"
                                       "lower" lower
                                       "upper" upper))
              (values lower upper))
            integer-range-guard/c)
  #:transparent)

(struct union type-decl (types)
  #:guard (let ()
            (define types-not-union/c
              (non-empty-listof (recursive-contract (and/c type/c (not/c union?)) #:flat)))
            (define (union/c types name)
              ;; TODO: check integer-range do not overlap
              (unless (types-not-union/c types)
                (raise-argument-error 'union
                                      "(listof (and/c type/c (not/c union?)))"
                                      types))
              (unless (<= (count arr? types) 1)
                (raise-argument-error 'union
                                      "at most one arr? type"
                                      types))
              types)
            union/c)
  #:transparent)

(struct list-of-magic () #:transparent)
(define list-of-magic-ending-value (list-of-magic))
(struct list-of type-decl (type)
  #:guard (struct-guard/c type/c)
  #:transparent)

(struct list-c type-decl (types)
  #:guard (struct-guard/c (listof type/c))
  #:transparent)

(struct primitive-solvable type-decl (type)
  #:guard (struct-guard/c (and/c solvable? (not/c function?)))
  #:transparent)

(struct arr type-decl (domains range)
  #:guard (struct-guard/c (listof type/c) type/c)
  #:transparent)

(define top-level-type/c
  (flat-named-contract 'top-level-type/c
                       (and/c type/c (not/c union?))))

(struct input-info (name type)
  #:guard (struct-guard/c symbol? type/c)
  #:transparent)

;; input-value/c should be *closed*
(define input-value/c a$value?)
(define input-arg/c
  (or/c
   ;; concolic values; rosette:union? for the encoded version of the list
   constant? rosette:union? fun?
   ;; concrete values; actually procedure? subsumes fun?
   boolean? number? (and/c procedure? (not/c fun?))
   (recursive-contract (listof input-arg/c))))

(struct test-info (inputs action)
  #:guard (struct-guard/c (listof input-info?)
                          ((listof input-arg/c) . -> . test-result/c))
  #:transparent)

(struct input (type map model)
  #:guard (struct-guard/c (and/c (hash/c symbol? top-level-type/c) immutable?)
                          (and/c (hash/c symbol? input-value/c) immutable?)
                          sat?)
  #:transparent)

(struct concolic-state (test queue path-status
                             [bad-inputs #:mutable]
                             statistics)
  #:transparent)

(struct concolic-statistics ([eval-real-nongc-time #:mutable]
                             [solve-count #:mutable]
                             [solve-real-nongc-time #:mutable]
                             [test-count #:mutable])
  #:transparent)

(struct pending
  (partial-inputs
   prediction
   provenance)
  #:guard (struct-guard/c input?
                          path-constraint/c
                          list?)
  #:transparent)

(struct test-record
  (model
   concolic-inputs
   path-constraint
   result
   cpu real gc)
  #:guard (struct-guard/c sat?
                          (listof input-arg/c)
                          path-constraint/c
                          test-result/c
                          real? real? real?)
  #:transparent)
