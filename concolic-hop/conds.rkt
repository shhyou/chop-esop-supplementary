#lang racket/base

(require racket/match
         racket/contract/base

         (prefix-in rosette:
                    (only-in rosette/safe
                             equal?
                             pair? null?))

         "data.rkt"
         "store.rkt")

(provide
 (contract-out
  [fresh-label (-> label?)]

  [empty-canonical-function (-> a$λ?)]
  [empty-let-expression (a$elim? . -> . a$let?)]
  [conds-table-empty? (a$conds? . -> . boolean?)]
  [in-conds-table (a$conds? . -> . sequence?)]
  [conds-table-ref-by-value (a$conds? any/c . -> . (values (or/c #f any/c)
                                                           (or/c #f type/c)
                                                           (or/c #f label?)
                                                           (or/c #f a$?)))]
  [conds-table-ref-by-label (a$conds? label? . -> . (values (or/c #f any/c)
                                                            (or/c #f type/c)
                                                            (or/c #f label?)
                                                            (or/c #f a$?)))]
  [conds-table-extend (a$conds? type/c any/c a$? . -> . (values a$conds? a$clause?))]))

(define label-counter 0)
(define (fresh-label)
  (define old-label-counter label-counter)
  (set! label-counter (add1 label-counter))
  (label old-label-counter))

(define (empty-canonical-function)
  (a$λ (a$conds (fresh-label) '())))

(define (empty-let-expression elim-ast)
  (a$let elim-ast (a$conds (fresh-label) '())))

(define (conds-table-empty? conds-ast)
  (null? (a$conds-table conds-ast)))

(define (in-conds-table conds-ast)
  (define table (a$conds-table conds-ast))
  (in-parallel
   (map a$clause-key table)
   (map a$clause-type table)
   (map a$clause-label table)
   (map a$clause-body table)))

(define (conds-table-ref-by-value conds-ast new-value)
  (define key-label-body
    (for/or ([(clause-key clause-type target-label body-ast) (in-conds-table conds-ast)])
      (define found
        (cond
          [(a$proc? clause-key)
           (procedure? new-value)]
          [(a$pair? clause-key)
           (get-current-concrete-value (rosette:pair? new-value))]
          [(a$null? clause-key)
           (get-current-concrete-value (rosette:null? new-value))]
          [else
           (get-current-concrete-value (rosette:equal? clause-key new-value))]))
      (and found
           (list clause-key clause-type target-label body-ast))))
  (cond
    [key-label-body (apply values key-label-body)]
    [else (values #f #f #f #f)]))

(define (conds-table-ref-by-label conds-ast label)
  (define key-label-body
    (for/first ([(clause-key clause-type target-label body-ast)
                 (in-conds-table conds-ast)]
                #:when (equal? label target-label))
      (list clause-key clause-type target-label body-ast)))
  (cond
    [key-label-body (apply values key-label-body)]
    [else (values #f #f #f #f)]))

(define (conds-table-extend conds-ast new-type new-value body)
  (match-define (struct* a$conds ([label label]
                                  [table table]))
    conds-ast)
  (define new-clause (a$clause new-value new-type (fresh-label) body))
  (define new-conds-ast
    (a$conds label
             (append table (list new-clause))))
  (values new-conds-ast new-clause))
