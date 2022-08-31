#lang racket/base

(require racket/contract/base
         racket/hash

         (for-syntax racket/base
                     syntax/parse)

         (only-in rosette/safe
                  define-symbolic*
                  solve
                  model sat unsat
                  with-vc vc-true failed? normal? result-value result-state
                  solvable? constant?
                  solution? sat?))

(provide
 (contract-out
  [solve/allow-exception ((-> any) . -> . solution?)]
  [fresh-symbolic-variable (solvable? . -> . constant?)]
  [model-set (sat? constant? any/c . -> . sat?)]
  [model-union-prefer-right (sat? sat? . -> . sat?)])
 with-rosette)

(define (shortcircuit-or-reraise e)
  (cond
    [(regexp-match? #rx"assert.*(failed|contradict)" (exn-message e))
     (unsat)]
    [else
     (raise e)]))

(define (solve/allow-exception thunk)
  (with-handlers ([exn:fail? shortcircuit-or-reraise])
    (define svm-result
      (with-vc vc-true
        (let ()
          (thunk)
          (solve (void)))))
    (cond
      [(failed? svm-result)
       (raise (result-value svm-result))]
      [else
       (result-value svm-result)])))

(define (fresh-symbolic-variable solvable-type)
  (define-symbolic* Z solvable-type)
  Z)

(define (model-set old-model name value)
  (sat
   (hash-set (model old-model)
             name value)))

(define (model-union-prefer-right old-model new-model)
  (define (discard-old-value old-value new-value)
    new-value)
  (sat
   (hash-union (model old-model)
               (model new-model)
               #:combine discard-old-value)))



(define-for-syntax rosette-default-require-ids
  '(+ - * > >= = < <= && ! not equal? distinct?))
(define-syntax (with-rosette stx)
  (syntax-parse stx
    [(form:id (require-id:id ...)
              (~optional (~seq #:scope scope-stx)
                         #:defaults ([scope-stx stx]))
              body ...+)
     (define require-ids-stx (syntax->list #'(require-id ...)))
     (define rosette-require-ids
       (cond [(null? require-ids-stx)
              rosette-default-require-ids]
             [else
              require-ids-stx]))
     (syntax-local-introduce
      (syntax-local-lift-require
       (datum->syntax (syntax-local-introduce #'scope-stx)
                      (list* 'only 'rosette/safe rosette-require-ids)
                      #'scope-stx)
       (syntax-local-introduce #'(let () body ...))))]))
