#lang concolic-hop/lang
;; this file generated by convert-soft-contract.rkt using ex-12.sch as input
(require concolic-hop/ctc concolic-hop/lib concolic-hop/convert-it)
(define-lump L)
(define-concolic-test
 ex-12
 #:inputs
 (|•(0 any/s any/c)|
  (or/s
   (->s integer integer)
   (list/s boolean (list-of integer))
   integer
   boolean))
 #:prop
 (prop-not-exn
  (λ ()
    (define (_carnum? p) (number? (car p)))
    (define-id-with-ctc
     (->i
      ((p any/c))
      (res (p) (and/c boolean? (λ (a) (equal? a (number? (car p)))))))
     _carnum?
     carnum?
     bug
     bug)
    (carnum?
     (apply-ctc
      any/c
      (convert-it |•(0 any/s any/c)| any/s L)
      bad-input
      no-blame
      |argument of carnum?|)))))
(define (counterexample)
  (define test-result (concolic-test ex-12 #:all? #f #:statistics? #t))
  (define witness (list-ref test-result 0))
  (define stats (list-ref test-result 1))
  (vector
   (concretize-input ex-12 witness)
   '()
   `#hash((solve-count . ,(concolic-statistics-solve-count stats))
          (solve-real-nongc-time
           .
           ,(concolic-statistics-solve-real-nongc-time stats))
          (test-count . ,(concolic-statistics-test-count stats)))))
(provide counterexample (rename-out (ex-12 test-property)))
(module+ main (counterexample))