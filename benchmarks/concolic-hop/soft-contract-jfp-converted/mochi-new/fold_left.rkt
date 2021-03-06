#lang concolic-hop/lang
;; this file generated by convert-soft-contract.rkt using fold_left.sch as input
(require concolic-hop/ctc concolic-hop/lib concolic-hop/convert-it)
(define-lump L)
(define-concolic-test
 fold_left
 #:inputs
 (|•(0 integer integer?)| integer)
 (|•(1 integer integer?)| integer)
 #:prop
 (prop-not-exn
  (λ ()
    (define (_fold_left f acc xs)
      (cond ((empty? xs) acc) (else (_fold_left f (f acc (car xs)) (cdr xs)))))
    (define (_make_list n) (if (< n 0) empty (cons n (_make_list (- n 1)))))
    (define (_add x y) (+ x y))
    (define (_main n m)
      (let ((xs (_make_list n))) (> (_fold_left _add m xs) m)))
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
  (define test-result (concolic-test fold_left #:all? #f #:statistics? #t))
  (define witness (list-ref test-result 0))
  (define stats (list-ref test-result 1))
  (vector
   (concretize-input fold_left witness)
   '()
   `#hash((solve-count . ,(concolic-statistics-solve-count stats))
          (solve-real-nongc-time
           .
           ,(concolic-statistics-solve-real-nongc-time stats))
          (test-count . ,(concolic-statistics-test-count stats)))))
(provide counterexample (rename-out (fold_left test-property)))
(module+ main (counterexample))
