#lang concolic-hop/lang
;; this file generated by convert-soft-contract.rkt using ack.sch as input
(require concolic-hop/ctc concolic-hop/lib concolic-hop/convert-it concolic-hop/complex)
(define-lump L)
(define-concolic-test
 ack
 #:inputs
 (|•(0 (list/s integer integer integer integer) integer?)|
  (list/s integer integer integer integer))
 (|•(1 (list/s integer integer integer integer) real?)|
  (list/s integer integer integer integer))
 #:prop
 (prop-not-exn
  (λ ()
    (define (_ack m n)
      (cond
       ((c:= m (c:racket-number->c 0)) (c:+ n (c:racket-number->c 1)))
       ((c:= n (c:racket-number->c 0))
        (_ack (c:- m (c:racket-number->c 1)) (c:racket-number->c 1)))
       (else
        (_ack
         (c:- m (c:racket-number->c 1))
         (_ack m (c:- n (c:racket-number->c 1)))))))
    (define-id-with-ctc (-> c:integer? c:real? c:integer?) _ack ack bug bug)
    (ack
     (apply-ctc
      c:integer?
      (convert-it
       |•(0 (list/s integer integer integer integer) integer?)|
       (list/s integer integer integer integer)
       L
       #:arithmetic-coercion-both)
      bad-input
      no-blame
      |argument of ack|)
     (apply-ctc
      c:real?
      (convert-it
       |•(1 (list/s integer integer integer integer) real?)|
       (list/s integer integer integer integer)
       L
       #:arithmetic-coercion-both)
      bad-input
      no-blame
      |argument of ack|)))))
(define (counterexample)
  (define test-result (concolic-test ack #:all? #f #:statistics? #t))
  (define witness (list-ref test-result 0))
  (define stats (list-ref test-result 1))
  (vector
   (concretize-input ack witness)
   '()
   `#hash((solve-count . ,(concolic-statistics-solve-count stats))
          (solve-real-nongc-time
           .
           ,(concolic-statistics-solve-real-nongc-time stats))
          (test-count . ,(concolic-statistics-test-count stats)))))
(provide counterexample (rename-out (ack test-property)))
(module+ main (counterexample))