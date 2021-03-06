#lang concolic-hop/lang
;; this file generated by convert-soft-contract.rkt using foldr.sch as input
(require concolic-hop/ctc concolic-hop/lib concolic-hop/convert-it)
(define-lump L)
(define-concolic-test
 foldr
 #:inputs
 (|•(0 (->s integer boolean boolean) (-> number? boolean? boolean?))|
  (->s integer (->s boolean boolean)))
 (|•(1 boolean boolean?)| boolean)
 (|•(2 (list-of any/s) (listof any/c))|
  (list-of
   (or/s
    (->s integer integer)
    (list/s boolean (list-of integer))
    integer
    boolean)))
 #:prop
 (prop-not-exn
  (λ ()
    (define (_foldr f z xs)
      (if (empty? xs) z (f (_foldr f z (cdr xs)) (car xs))))
    (define-id-with-ctc
     (-> (-> number? boolean? boolean?) boolean? (listof any/c) boolean?)
     _foldr
     foldr
     bug
     bug)
    (foldr
     (apply-ctc
      (-> number? boolean? boolean?)
      (convert-it
       |•(0 (->s integer boolean boolean) (-> number? boolean? boolean?))|
       (->s integer boolean boolean)
       L)
      bad-input
      no-blame
      |argument of foldr|)
     (apply-ctc
      boolean?
      (convert-it |•(1 boolean boolean?)| boolean L)
      bad-input
      no-blame
      |argument of foldr|)
     (apply-ctc
      (listof any/c)
      (convert-it |•(2 (list-of any/s) (listof any/c))| (list-of any/s) L)
      bad-input
      no-blame
      |argument of foldr|)))))
(define (counterexample)
  (define test-result (concolic-test foldr #:all? #f #:statistics? #t))
  (define witness (list-ref test-result 0))
  (define stats (list-ref test-result 1))
  (vector
   (concretize-input foldr witness)
   '()
   `#hash((solve-count . ,(concolic-statistics-solve-count stats))
          (solve-real-nongc-time
           .
           ,(concolic-statistics-solve-real-nongc-time stats))
          (test-count . ,(concolic-statistics-test-count stats)))))
(provide counterexample (rename-out (foldr test-property)))
(module+ main (counterexample))
