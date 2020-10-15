#lang concolic-hop/lang
;; this file generated by convert-soft-contract.rkt using argmin.sch as input
(require concolic-hop/ctc concolic-hop/lib concolic-hop/convert-it concolic-hop/complex)
(define-lump L)
(require (only-in racket/base error))

(define (_argmin f xs) (_argmin/acc f (car xs) (f (car xs)) (cdr xs)))
(define (_argmin/acc f a b xs)
  (if (empty? xs)
      a
      (if (c:< b (f (car xs)))
          (_argmin/acc f a b (cdr xs))
          (_argmin/acc f (car xs) (f (car xs)) (cdr xs)))))
(define-id-with-ctc
  (-> (-> any/c c:number?) (cons/c any/c (listof any/c)) any/c)
  _argmin
  argmin
  bug
  bug)
((convert-it
  (λ (x8)
    (cond
      ((procedure? x8)
       (let ((x9 (x8 (λ (x10) (error "ASSERT_UNREACHABLE")))))
         (cond
           ((procedure? x9)
            (let ((x11
                   (x9
                    (cons
                     (cons 0 (cons 0 (cons 0 (cons 0 null))))
                     (cons null null)))))
              (error "ASSERT_UNREACHABLE")))
           ((null? x9) (error "ASSERT_UNREACHABLE"))
           ((pair? x9) (error "ASSERT_UNREACHABLE"))
           (else (error "ASSERT_UNREACHABLE")))))
      ((null? x8) (error "ASSERT_UNREACHABLE"))
      ((pair? x8) (error "ASSERT_UNREACHABLE"))
      (else (error "ASSERT_UNREACHABLE"))))

  (->s
   (->s
    (->s any/s (list/s integer integer integer integer))
    (cons/s any/s (list-of any/s))
    any/s)
   dont-care/s)
  L)
 argmin)