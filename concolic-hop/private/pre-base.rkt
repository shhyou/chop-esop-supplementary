#lang rosette/safe

(require (for-syntax racket/base
                     racket/syntax
                     syntax/parse)
         (prefix-in racket: racket/base)
         (only-in racket/base
                  values)

         "../track.rkt"

         "../store.rkt"
         "../lib.rkt")

(provide
 values
 (except-out (all-from-out rosette/safe)
             cond
             if
             and
             or
             when
             unless
             /
             null?
             pair?

             car cdr
             caar cadr cdar cddr
             caaar caadr cadar caddr cdaar cdadr cddar cdddr
             caaaar caaadr caadar caaddr cadaar cadadr caddar cadddr
             cdaaar cdaadr cdadar cdaddr cddaar cddadr cdddar cddddr

             ~>
             forall
             exists

             apply
             case-lambda)
 (rename-out
  [apply rosette:apply]
  [case-lambda rosette:case-lambda]
  [concolic-if if]
  [concolic-cond cond]
  [concolic-and and]
  [concolic-or or]
  [concolic-when when]
  [concolic-unless unless]
  [concolic-/ /]
  [concolic-null? null?]
  [concolic-pair? pair?]
  [concolic-object-name object-name]
  [concolic-procedure-arity-includes? procedure-arity-includes?]
  [concolic-string? string?]
  [concolic-string-length string-length]
  [concolic-symbol? symbol?]
  )

 (struct-out test-info)
 (struct-out input-info)

 integer
 boolean
 integer-range
 list-of
 ;; Some shorthand wrappers
 ->s
 or/s
 list/s

 define-concolic-test

 abort-concolic-execution
 error-bug
 prop-not-false
 prop-not-error-bug
 exn:fail:error-bug?
 prop-not-exn
 exn:fail?

 cprintf)

(define-syntax concolic-if
  (syntax-parser
    [(_ expr-cond:expr expr-then:expr expr-else:expr)
     (syntax/loc this-syntax
       (racket:if
        (record-branch-point expr-cond)
        expr-then
        expr-else))]))

(define-syntax concolic-cond
  (syntax-parser
    #:literals (else)
    [(_
      [expr-cond:expr
       expr-body:expr ...+]
      ...
      [else expr-else:expr ...+])
     (syntax/loc this-syntax
       (racket:cond
        [(record-branch-point expr-cond)
         expr-body ...]
        ...
        [else expr-else ...]))]))

(define-syntax concolic-and
  (syntax-parser
    [(_ e1:expr ...)
     (syntax/loc this-syntax
       (racket:and (record-branch-point e1) ...))]))

(define-syntax concolic-or
  (syntax-parser
    [(_ e1:expr ...)
     (syntax/loc this-syntax
       (racket:or (record-branch-point e1) ...))]))

(define-syntax concolic-when
  (syntax-parser
    [(_ pred:expr body:expr ...+)
     (syntax/loc this-syntax
       (concolic-if pred (let () body ...) (void)))]))

(define-syntax concolic-unless
  (syntax-parser
    [(_ pred:expr body:expr ...+)
     (syntax/loc this-syntax
       (concolic-if pred (void) (let () body ...)))]))

(define (assert-not-zero n fail)
  (concolic-unless (number? n) (fail))
  (concolic-when   (zero? n)   (fail)))

(define (concolic-/-fail . args)
  (apply racket:/ (map get-current-concrete-value args)))

(define concolic-/
  (case-lambda
   [(divisor)
    (assert-not-zero divisor (λ () (concolic-/-fail divisor)))
    (/ divisor)]
   [(dividend divisor . divisors)
    (define (fail) (apply concolic-/-fail dividend divisor divisors))
    (racket:for ([divisor (racket:in-list (cons divisor divisors))])
                (assert-not-zero divisor fail))
    (apply / dividend divisor divisors)]))

(define-syntax define-provide-unary-function-with-concrete-evaluation
  (syntax-parser
    [(_ function:id ...+)
     #:with (racket-function-id ...+)
     (for/list ([f (in-list (syntax->list #'(function ...)))])
       (format-id f "racket:~a" f))
     #:with (local-function-id ...+)
     (for/list ([f (in-list (syntax->list #'(function ...)))])
       (format-id f "concolic-~a" f))
     (syntax/loc this-syntax
       (begin
         (provide (rename-out [local-function-id function] ...))
         (define (local-function-id p)
           (begin0
             (function p)
             ;; for error checking; inefficient
             (racket-function-id (get-current-concrete-value p))))
         ...))]))

(define-provide-unary-function-with-concrete-evaluation
  car cdr

  caar cadr cdar cddr

  caaar caadr cadar caddr cdaar cdadr cddar cdddr

  caaaar caaadr caadar caaddr cadaar cadadr caddar cadddr
  cdaaar cdaadr cdadar cdaddr cddaar cddadr cdddar cddddr)

(define (concolic-object-name maybe-union-val)
  (for/all ([val maybe-union-val])
    (racket:object-name val)))

(define (concolic-procedure-arity-includes? maybe-union-val maybe-symbolic-arity)
  (define arity (get-current-concrete-value maybe-symbolic-arity))
  (for/all ([val maybe-union-val])
    (racket:procedure-arity-includes? val arity)))

(define (concolic-string? maybe-union-val)
  (for/all ([val maybe-union-val])
    (racket:string? val)))

(define (concolic-string-length maybe-union-val)
  (concolic-unless (concolic-string? maybe-union-val)
                   (racket:error 'string-length
                                 "expected a string? but given ~e"
                                 maybe-union-val))
  (for/all ([val maybe-union-val])
    (racket:string-length val)))

(define (concolic-symbol? maybe-union-val)
  (for/all ([val maybe-union-val])
    (racket:symbol? val)))

(racket:struct C# (concrete symbolic) #:prefab)
(define (cprintf format . args)
  (racket:apply printf format
                (racket:for/list ([arg (racket:in-list args)])
                                 (C# (get-current-concrete-value arg)
                                     arg))))
