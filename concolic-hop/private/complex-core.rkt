#lang concolic-hop/lang
(require concolic-hop/store
         (prefix-in
          r:
          (only-in racket/base
                   real-part imag-part
                   make-rectangular /
                   numerator denominator)))

(provide c->rind rind->c c:number? c:real?
         c:racket-number->c c:from-concolic-number)

(define (c->rind c)
  ;; it should be an invariant of this representation
  ;; that the denominators aren't zero but the concolic
  ;; tester has only `integer` not `non-zero integer`
  ;; so we convert them here. (Negatives should be fine
  ;; with all the primitives I believe.)
  ;; (I'm not sure this is the right place to convert them)
  (values (list-ref c 0)
          (if (zero? (list-ref c 1)) 1 (list-ref c 1))
          (list-ref c 2)
          (if (zero? (list-ref c 3)) 1 (list-ref c 3))))

(define (rind->c rn rd in id)
  (list rn rd in id))

(define (c:racket-number->c n/c)
  (define n (get-current-concrete-value n/c))
  (define r (r:real-part n))
  (define i (r:imag-part n))
  (rind->c (r:numerator r) (r:denominator r)
           (r:numerator i) (r:denominator i)))

(define (c:from-concolic-number c)
  (define-values (rn rd in id) (c->rind c))
  (r:make-rectangular (r:/ rn rd) (r:/ in id)))

(define (c:real? n)
  (cond
    [(c:number? n)
     (define-values (rn rd in id) (c->rind n))
     (zero? in)]
    [else #f]))

(define (c:number? n)
  (and (list? n)
       (= 4 (length n))
       (real? (list-ref n 0))
       (real? (list-ref n 1))
       (real? (list-ref n 2))
       (real? (list-ref n 3))))
