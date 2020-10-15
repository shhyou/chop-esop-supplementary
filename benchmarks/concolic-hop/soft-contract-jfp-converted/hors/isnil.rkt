#lang concolic-hop/lang
;; this file generated by convert-soft-contract.rkt using isnil.sch as input
(require concolic-hop/ctc concolic-hop/lib concolic-hop/convert-it)
(define-lump L)
(define-concolic-test
 isnil
 #:inputs
 (|•(0 integer integer?)| integer)
 #:prop
 (prop-not-exn
  (λ ()
    (define (_mk-list n) (if (= n 0) empty (cons n (_mk-list (- n 1)))))
    (define-id-with-ctc
     (->i
      ((n integer?))
      (res
       (n)
       (and/c (listof integer?) (λ (l) (implies (>= n 0) (not (empty? l)))))))
     _mk-list
     mk-list
     bug
     bug)
    (mk-list
     (apply-ctc
      integer?
      (convert-it |•(0 integer integer?)| integer L)
      bad-input
      no-blame
      |argument of mk-list|)))))
(define (counterexample)
  (define test-result (concolic-test isnil #:all? #f #:statistics? #t))
  (define witness (list-ref test-result 0))
  (define stats (list-ref test-result 1))
  (vector
   (concretize-input isnil witness)
   '()
   `#hash((solve-count . ,(concolic-statistics-solve-count stats))
          (solve-real-nongc-time
           .
           ,(concolic-statistics-solve-real-nongc-time stats))
          (test-count . ,(concolic-statistics-test-count stats)))))
(provide counterexample (rename-out (isnil test-property)))
(module+ main (counterexample))