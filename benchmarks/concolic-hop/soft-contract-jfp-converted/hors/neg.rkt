#lang concolic-hop/lang
;; this file generated by convert-soft-contract.rkt using neg.sch as input
(require concolic-hop/ctc concolic-hop/lib concolic-hop/convert-it)
(define-lump L)
(define-concolic-test
 neg
 #:inputs
 (|•(0 integer integer?)| integer)
 #:prop
 (prop-not-exn
  (λ ()
    (define (_g x) (λ (_) x))
    (define-id-with-ctc (-> integer? (-> any/c integer?)) _g g bug bug)
    (define (_twice f x y) ((f (f x)) y))
    (define-id-with-ctc
     (->
      (-> (-> any/c integer?) (-> any/c integer?))
      (-> any/c integer?)
      any/c
      integer?)
     _twice
     twice
     bug
     bug)
    (define (_neg x) (λ (_) (- 0 (x #f))))
    (define-id-with-ctc
     (-> (-> any/c integer?) (-> any/c integer?))
     _neg
     neg
     bug
     bug)
    (define (_main n) (if (>= n 0) (twice neg (g n) 'unit) 42))
    (define-id-with-ctc
     (-> integer? (and/c integer? (>/c 0)))
     _main
     main
     bug
     bug)
    (main
     (apply-ctc
      integer?
      (convert-it |•(0 integer integer?)| integer L)
      bad-input
      no-blame
      |argument of main|)))))
(define (counterexample)
  (define test-result (concolic-test neg #:all? #f #:statistics? #t))
  (define witness (list-ref test-result 0))
  (define stats (list-ref test-result 1))
  (vector
   (concretize-input neg witness)
   '()
   `#hash((solve-count . ,(concolic-statistics-solve-count stats))
          (solve-real-nongc-time
           .
           ,(concolic-statistics-solve-real-nongc-time stats))
          (test-count . ,(concolic-statistics-test-count stats)))))
(provide counterexample (rename-out (neg test-property)))
(module+ main (counterexample))