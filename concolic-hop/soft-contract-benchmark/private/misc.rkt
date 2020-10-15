#lang racket
(module+ test (require rackunit))

(provide
 (contract-out
  [sexp/c contract?]
  [T/c contract?]
  [header->tl-name (-> sexp/c symbol?)]
  [header-expand-lambda (-> sexp/c sexp/c)]
  [struct->names
   (-> sexp/c
       (struct/c struct-names symbol? symbol? (listof symbol?)))])
 (struct-out struct-names))

(define sexp/c (not/c #f))

;; this has to match what convert-it is doing.
(define T/c
  (flat-rec-contract
   T/c
   (cons/c '->s (listof T/c))
   (cons/c 'or/s (listof T/c))
   (cons/c 'list/s (listof T/c))
   (list/c 'list-of T/c)
   'lump/s
   'integer
   'boolean
   'string/s
   'string-or-integer/s
   'any/s

   ;; this is like any/s in that anything goes,
   ;; but unlike any/s in that no conversion happens
   ;; it is meant to be used in context where the
   ;; results are ignored (like the top-level of a module)
   'dont-care/s

   'none/s
   (cons/c 'struct/s (cons/c symbol? (listof T/c)))
   (list/c 'cons/s T/c T/c)
   (list/c '->si
           (list/c [list/c symbol? (cons/c 'one-of/c (listof (or/c (list/c 'quote symbol?)
                                                                   string?)))])
           (list/c symbol? (list/c symbol?)
                   (cons/c 'cond any/c))) ;; simplify to any/c here (less checking)
   ))

(define (header->tl-name header)
  (let loop ([header header])
    (match header
      [(? symbol?) header]
      [`(,f ,x ...) (loop f)])))

(define (header-expand-lambda defn)
  (let loop ([defn defn])
    (match defn
      [`(define ,(? symbol? s) ,body) `(define ,s ,body)]
      [`(define (,f ,x ...) ,body) (loop `(define ,f (λ (,@x) ,body)))])))
(module+ test
  (check-equal? (header-expand-lambda `(define x 1))
                `(define x 1))
  (check-equal? (header-expand-lambda `(define ((f x) y z) 1))
                `(define f (λ (x) (λ (y z) 1)))))

(struct struct-names (constructor predicate selectors)
  #:transparent)

(define (struct->names tl)
  (match tl
    [`(struct ,s (,flds ...))
     (struct-names s
                   (string->symbol (~a s "?"))
                   (for/list ([fld (in-list flds)])
                     (string->symbol (~a s "-" fld))))]
    [`(define-struct ,s (,flds ...))
     (struct-names
      (string->symbol (~a "make-" s))
      (string->symbol (~a s "?"))
      (for/list ([fld (in-list flds)])
        (string->symbol (~a s "-" fld))))]))