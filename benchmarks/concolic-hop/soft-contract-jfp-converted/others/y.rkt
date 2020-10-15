#lang concolic-hop/lang
(require concolic-hop/ctc concolic-hop/lib)
(define-concolic-test
  argmin
  #:inputs
  (INPUT
   (->s
    (->s (->s boolean (list/s integer integer integer integer))
         (->s (list/s boolean (list-of boolean))
              boolean))
    boolean))
  #:prop
  (prop-not-exn
   (λ ()
     (define ((argmin f) xs) (f (car xs)))
     (INPUT
      argmin))))
(define counterexample
  (vector (concretize-input argmin (concolic-test argmin #:all? #f))
          '()))
(provide counterexample)
