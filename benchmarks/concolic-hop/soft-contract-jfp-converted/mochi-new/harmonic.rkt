#lang concolic-hop/lang
;; this file generated by convert-soft-contract.rkt using harmonic.sch as input
(require concolic-hop/ctc concolic-hop/lib concolic-hop/convert-it)
(define-lump L)
(define-concolic-test
 harmonic
 #:inputs
 (|•(0 integer integer?)| integer)
 #:prop
 (prop-not-exn
  (λ ()
    (define (_fold_left f acc xs)
      (cond ((empty? xs) acc) (else (_fold_left f (f acc (car xs)) (cdr xs)))))
    (define (_range i j)
      (cond ((> i j) empty) (else (cons i (_range (+ 1 i) j)))))
    (define (_harmonic n)
      (let ((ds (_range 0 n))) (_fold_left (λ (s k) (+ s (/ 10000 k))) 0 ds)))
    (define-id-with-ctc (-> integer? any/c) _harmonic harmonic bug bug)
    (harmonic
     (apply-ctc
      integer?
      (convert-it |•(0 integer integer?)| integer L)
      bad-input
      no-blame
      |argument of harmonic|)))))
(define (counterexample)
  (define test-result (concolic-test harmonic #:all? #f #:statistics? #t))
  (define witness (list-ref test-result 0))
  (define stats (list-ref test-result 1))
  (vector
   (concretize-input harmonic witness)
   '()
   `#hash((solve-count . ,(concolic-statistics-solve-count stats))
          (solve-real-nongc-time
           .
           ,(concolic-statistics-solve-real-nongc-time stats))
          (test-count . ,(concolic-statistics-test-count stats)))))
(provide counterexample (rename-out (harmonic test-property)))
(module+ main (counterexample))