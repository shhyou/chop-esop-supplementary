#lang racket/base

(require racket/match
         racket/contract/base

         (only-in rosette/safe
                  evaluate
                  sat?
                  term?
                  constant?
                  [union? rosette:union?])

         "data.rkt"
         "rosette.rkt"
         "state-passing.rkt"
         )

(provide
 (contract-out
  [store-for-each (input? (symbol? a$? type/c . -> . any)
                          . -> . any)])

 (contract-out
  [call-with-model (sat? (-> any) . -> . any)]
  [get-current-concrete-value (any/c . -> . (not/c (or/c term? rosette:union?)))])
 get-current-model

 (contract-out
  [fresh-concolic-variable-name (-> symbol?)]))

(define concolic-var-counter 0)
(define (fresh-concolic-variable-name)
  (define old-counter concolic-var-counter)
  (set! concolic-var-counter (add1 concolic-var-counter))
  (string->uninterned-symbol (format "_X~a" old-counter)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;
;
;
;
;
;
;
;
;      ;;;;;;;;;
;     ;    ;
;    ;      ;
;    ;      ;
;   ;;      ;
;    ;      ;;
;    ;      ;
;    ;      ;
;     ;    ;;
;     ;;   ;
;       ;;;
;
;
;
;
;

(define (store-for-each inputs action)
  (match-define (struct* input ([type input-types]
                                [map the-input-map]
                                [model the-model]))
    inputs)
  (for ([var-name (in-hash-keys the-input-map)])
    (action var-name
            (hash-ref the-input-map var-name)
            (hash-ref input-types var-name))))

(define current-model (make-parameter 'no-model))

(define (get-current-model)
  (current-model))

(define (call-with-model new-model action)
  (parameterize ([current-model new-model])
    (action)))

(define (get-current-concrete-value rosette-value)
  (evaluate rosette-value (get-current-model)))
