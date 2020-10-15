#lang concolic-hop/lang
;; this file generated by convert-soft-contract.rkt using sum.sch as input
(require concolic-hop/ctc concolic-hop/lib concolic-hop/convert-it)
(define-lump L)
(define-concolic-test
 sum
 #:inputs
 (|•(0 integer integer?)| integer)
 #:prop
 (prop-not-exn
  (λ ()
    (define (_sum n) (if (<= n 0) 0 (+ n (_sum (- n 1)))))
    (define-id-with-ctc
     (->i ((n integer?)) (res (n) (and/c integer? (>=/c (+ n 1)))))
     _sum
     sum
     bug
     bug)
    (sum
     (apply-ctc
      integer?
      (convert-it |•(0 integer integer?)| integer L)
      bad-input
      no-blame
      |argument of sum|)))))
(define (counterexample)
  (define test-result (concolic-test sum #:all? #f #:statistics? #t))
  (define witness (list-ref test-result 0))
  (define stats (list-ref test-result 1))
  (vector
   (concretize-input sum witness)
   '()
   `#hash((solve-count . ,(concolic-statistics-solve-count stats))
          (solve-real-nongc-time
           .
           ,(concolic-statistics-solve-real-nongc-time stats))
          (test-count . ,(concolic-statistics-test-count stats)))))
(provide counterexample (rename-out (sum test-property)))
(module+ main (counterexample))