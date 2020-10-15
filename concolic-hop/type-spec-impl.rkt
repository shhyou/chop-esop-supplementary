#lang racket/base

(require racket/match
         racket/contract

         (prefix-in rosette:
                    (only-in rosette/safe
                             boolean?
                             integer?
                             procedure?
                             list?
                             pair?
                             null?))
         (only-in rosette/safe
                  complete-solution
                  sat
                  define-symbolic*)

         "data.rkt")

(provide
 integer
 boolean
 ->s
 or/s
 list/s
 (contract-out
  [default-value-of ((env/c any/c) type/c . -> . any/c)]
  [infer-value-tag  (-> (or/c integer? boolean? procedure? list?) tag/c)]
  [infer-type-tag   (-> (or/c primitive-solvable? integer-range? arr? list-of? list-c?)
                        tag/c)]
  [refine-ast≼_/#f  (-> (env/c (bound/c any/c))
                        (or/c a$x? a$X? a$value?)
                        type/c
                        (or/c #f type/c))]
  [refine-type≼_/#f (-> type/c type/c (or/c #f type/c))]
  [refine-tag≼_/#f  (-> tag/c type/c (or/c #f type/c))]))

(define integer (primitive-solvable rosette:integer?))
(define boolean (primitive-solvable rosette:boolean?))

(define (->s dom range)
  (arr (list dom) range))

(define (or/s . types) (union types))

(define (list/s . types) (list-c types))

;; TODO: use values in env
(define default-value-cache (make-hash))
(define (default-value-of env type)
  (cond
    [(primitive-solvable? type)
     (hash-ref! default-value-cache type
                (λ ()
                  (define-symbolic* DefaultConstantValue
                    (primitive-solvable-type type))
                  ((complete-solution (sat) (list DefaultConstantValue))
                   DefaultConstantValue)))]
    [(integer-range? type)
     (integer-range-lower type)]
    [(arr? type)
     (define result (default-value-of env (arr-range type)))
     (define (default-constant-function . args)
       result)
     (fun default-constant-function)]
    [(union? type)
     (default-value-of env (list-ref (union-types type) 0))]
    [(list-of? type)
     '()]
    [(list-c? type)
     (for/list ([elem-type (in-list (list-c-types type))])
       (default-value-of env elem-type))]
    [else
     (error 'default-value-of
            "cannot generate a default value of type ~a"
            type)]))


(define (infer-value-tag real-value)
  (cond
    [(integer? real-value) 'integer]
    [(boolean? real-value) 'boolean]
    [(procedure? real-value) 'arrow]
    [(list? real-value) 'list]
    [else #f]))

(define (infer-a$expr-tag ast)
  (match ast
    ;; another approach would be consulting a model
    [(struct* a$X ([type (== integer)])) 'integer]
    [(struct* a$X ([type (struct integer-range _)])) 'integer]
    [(struct* a$X ([type (== boolean)])) 'boolean]
    [(struct a$λ _) 'arrow]
    [(struct a$list _) 'list]))

(define (infer-type-tag type)
  (match type
    [(== integer) 'integer]
    [(== boolean) 'boolean]
    [(struct integer-range _) 'integer]
    [(struct arr _) 'arrow]
    [(struct list-of _) 'list]
    [(struct list-c _) 'list]))

(define/contract (check-ast-against-list-c-type env ast type)
  (-> (env/c (bound/c any/c)) any/c list-c? boolean?)
  (match* (ast type)
    [((a$empty _)
      (struct* list-c ([types '()])))
     #t]
    [((a$cons _ car-ast cdr-ast)
      (struct* list-c ([types (cons car-type cdr-type)])))
     (and (refine-ast≼_/#f env car-ast car-type)
          (check-ast-against-list-c-type env cdr-ast (list-c cdr-type)))]
    [(_ _) #f]))

(define/contract (check-ast-against-list-of-type env ast type)
  (-> (env/c (bound/c any/c)) any/c list-of? boolean?)
  (match ast
    [(a$empty _) #t]
    [(a$cons _ car-ast cdr-ast)
     (and (refine-ast≼_/#f env car-ast (list-of-type type))
          (check-ast-against-list-of-type env cdr-ast type))]
    [_ #f]))

(define (refine-ast≼_/#f env ast type)
  (match* (ast type)
    [((struct* a$X ([type var-type]))
      type)
     (refine-type≼_/#f var-type type)]
    [((struct* a$x ([index var-index]))
      type)
     (refine-type≼_/#f (bound-type (env-ref env var-index)) type)]
    [((struct a$λ _)
      (and arrow-type (struct arr _)))
     arrow-type]
    [((and xs-ast (struct a$list _))
      (and xs-type (struct* list-c ([types types]))))
     #:when (check-ast-against-list-c-type env xs-ast xs-type)
     xs-type]
    [((and xs-ast (struct a$list _))
      (and xs-type (struct* list-of ([type elem-type]))))
     #:when (check-ast-against-list-of-type env xs-ast xs-type)
     xs-type]
    [(ast
      (struct* union ([types types])))
     (for/or ([type (in-list types)])
       (refine-ast≼_/#f env ast type))]
    [(_ _) #f]))

;; Can have more normal subtyping
(define (refine-type≼_/#f type-sub type)
  (match* (type-sub type)
    [(_ (== type-sub)) type-sub]
    [(type-sub (struct* union ([types types])))
     (for/or ([type (in-list types)])
       (refine-type≼_/#f type-sub type))]
    [(_ _) #f]))

(define (refine-tag≼_/#f tag type)
  (match* (tag type)
    [('integer (== integer)) type]
    [('integer (struct integer-range _)) type]
    [('boolean (== boolean)) type]
    [('arrow (struct arr _)) type]
    [('list (struct list-of _)) type]
    [('list (struct list-c _)) type]
    [(tag (struct* union ([types types])))
     (for/or ([type (in-list types)])
       (refine-tag≼_/#f tag type))]
    [(_ _) #f]))
