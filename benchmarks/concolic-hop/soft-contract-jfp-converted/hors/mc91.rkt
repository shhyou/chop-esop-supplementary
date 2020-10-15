#lang concolic-hop/lang
;; this file generated by convert-soft-contract.rkt using mc91.sch as input
(require concolic-hop/ctc concolic-hop/lib concolic-hop/convert-it)
(define-lump L)
(define-concolic-test
 mc91
 #:inputs
 (|•(0 integer integer?)| integer)
 #:prop
 (prop-not-exn
  (λ ()
    (define (_mc91 x) (if (> x 100) (- x 10) (_mc91 (_mc91 (+ x 11)))))
    (define-id-with-ctc
     (-> integer? (and/c integer? (=/c 91)))
     _mc91
     mc91
     bug
     bug)
    (mc91
     (apply-ctc
      integer?
      (convert-it |•(0 integer integer?)| integer L)
      bad-input
      no-blame
      |argument of mc91|)))))
(define (counterexample)
  (define test-result (concolic-test mc91 #:all? #f #:statistics? #t))
  (define witness (list-ref test-result 0))
  (define stats (list-ref test-result 1))
  (vector
   (concretize-input mc91 witness)
   '()
   `#hash((solve-count . ,(concolic-statistics-solve-count stats))
          (solve-real-nongc-time
           .
           ,(concolic-statistics-solve-real-nongc-time stats))
          (test-count . ,(concolic-statistics-test-count stats)))))
(provide counterexample (rename-out (mc91 test-property)))
(module+ main (counterexample))