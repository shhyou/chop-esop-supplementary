#lang concolic-hop/lang
;; this file generated by convert-soft-contract.rkt using a-max.sch as input
(require concolic-hop/ctc concolic-hop/lib concolic-hop/convert-it)
(define-lump L)
(define-concolic-test
 a-max
 #:inputs
 (|•(0 integer integer?)| integer)
 (|•(1 integer integer?)| integer)
 #:prop
 (prop-not-exn
  (λ ()
    (define (_make_array n) (λ (i) (- n i)))
    (define (_array_max n i a m)
      (cond
       ((>= i n) m)
       (else
        (let* ((x (a i)) (z (if (< x m) x m))) (_array_max n (+ 1 i) a z)))))
    (define (_main n i)
      (cond
       ((and (> n 0) (>= i 0) (<= i 0))
        (let ((m (_array_max n i (_make_array n) -1))) (>= m n)))
       (else #t)))
    (define-id-with-ctc
     (-> integer? integer? (not/c false?))
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
      |argument of main|)
     (apply-ctc
      integer?
      (convert-it |•(1 integer integer?)| integer L)
      bad-input
      no-blame
      |argument of main|)))))
(define (counterexample)
  (define test-result (concolic-test a-max #:all? #f #:statistics? #t))
  (define witness (list-ref test-result 0))
  (define stats (list-ref test-result 1))
  (vector
   (concretize-input a-max witness)
   '()
   `#hash((solve-count . ,(concolic-statistics-solve-count stats))
          (solve-real-nongc-time
           .
           ,(concolic-statistics-solve-real-nongc-time stats))
          (test-count . ,(concolic-statistics-test-count stats)))))
(provide counterexample (rename-out (a-max test-property)))
(module+ main (counterexample))