#lang racket

(require concolic-hop/complex
         (only-in concolic-hop/private/complex-core
                  c->rind rind->c)
         concolic-hop/rosette
         concolic-hop/store
         concolic-hop/data
         rackunit
         (prefix-in cl: concolic-hop/lang)
         "../private/utils.rkt")
#|
(check-equal? (c:+ (c:racket-number->c 1)
                   (c:racket-number->c 2))
              (c:racket-number->c 3))

(check-equal? (c:+ (c:racket-number->c 1+3i)
                   (c:racket-number->c 2+5i))
              (c:racket-number->c 3+8i))

(check-equal? (c:add1 (c:racket-number->c 2))
              (c:racket-number->c 3))

(check-equal? (c:- (c:racket-number->c 1)
                   (c:racket-number->c 2))
              (c:racket-number->c -1))

(check-equal? (c:- (c:racket-number->c 1+3i)
                   (c:racket-number->c 2+5i))
              (c:racket-number->c -1-2i))

(check-equal? (c:sub1 (c:racket-number->c 2))
              (c:racket-number->c 1))

(check-equal? (c:* (c:racket-number->c 3)
                   (c:racket-number->c 2))
              (c:racket-number->c 6))

(check-equal? (c:* (c:racket-number->c 0+3i)
                   (c:racket-number->c 0+2i))
              (c:racket-number->c -6))

(check-equal? (c:* (c:racket-number->c 1+3i)
                   (c:racket-number->c 2+5i))
              (c:racket-number->c -13+11i))

(check-equal? (c:reciprocal (c:racket-number->c 2+3i))
              (c:racket-number->c 2/13-3/13i))

(define (normalize c)
  (define-values (rn rd in id) (c->rind c))
  (define r (/ rn rd))
  (define i (/ in id))
  (rind->c (numerator r) (denominator r)
           (numerator i) (denominator i)))

(check-equal? (normalize
               (c:/ (c:racket-number->c 2+3i)
                    (c:racket-number->c 5+7i)))
              (c:racket-number->c 31/74+1/74i))

(check-true (c:zero? (c:racket-number->c 0)))
(check-false (c:zero? (c:racket-number->c 0+1i)))
(check-false (c:zero? (c:racket-number->c 1)))
(check-false (c:zero? (c:racket-number->c 2+3i)))

(check-equal? (c:abs (c:racket-number->c -1))
              (c:racket-number->c 1))
(check-equal? (c:abs (c:racket-number->c 1))
              (c:racket-number->c 1))

(check-true (c:= (c:racket-number->c 1) (c:racket-number->c 1)))
(check-false (c:= (c:racket-number->c 2) (c:racket-number->c 1)))
(check-false (c:= (c:racket-number->c 0+2i) (c:racket-number->c 0+1i)))

(check-false (c:< (c:racket-number->c 1) (c:racket-number->c 1)))
(check-true (c:< (c:racket-number->c 1) (c:racket-number->c 2)))
(check-false (c:< (c:racket-number->c 2) (c:racket-number->c 1)))

(check-true (c:<= (c:racket-number->c 1) (c:racket-number->c 1)))
(check-true (c:<= (c:racket-number->c 1) (c:racket-number->c 2)))
(check-false (c:<= (c:racket-number->c 2) (c:racket-number->c 1)))

(check-true (c:>= (c:racket-number->c 1) (c:racket-number->c 1)))
(check-true (c:>= (c:racket-number->c 2) (c:racket-number->c 1)))
(check-false (c:>= (c:racket-number->c 1) (c:racket-number->c 2)))

(check-false (c:> (c:racket-number->c 1) (c:racket-number->c 1)))
(check-true (c:> (c:racket-number->c 2) (c:racket-number->c 1)))
(check-false (c:> (c:racket-number->c 1) (c:racket-number->c 2)))


(check-equal? (c:min (c:racket-number->c 1) (c:racket-number->c 1))
              (c:racket-number->c 1))
(check-equal? (c:min (c:racket-number->c 1) (c:racket-number->c 2))
              (c:racket-number->c 1))
(check-equal? (c:min (c:racket-number->c 2) (c:racket-number->c 1))
              (c:racket-number->c 1))

(check-equal? (c:max (c:racket-number->c 1) (c:racket-number->c 1))
              (c:racket-number->c 1))
(check-equal? (c:max (c:racket-number->c 1) (c:racket-number->c 2))
              (c:racket-number->c 2))
(check-equal? (c:max (c:racket-number->c 2) (c:racket-number->c 1))
              (c:racket-number->c 2))

(for ([i (in-range 20)])
  (check-equal? (c:sqrt (c:racket-number->c (* i i)))
                (c:racket-number->c i))
  (check-equal? (c:sqrt (c:racket-number->c (* -1 i i)))
                (c:racket-number->c (make-rectangular 0 i))))

(check-true (c:real? (c:racket-number->c 1)))
(check-false (c:real? (c:racket-number->c 1+1i)))
(check-false (c:real? "string"))

(check-true (c:integer? (c:racket-number->c 1)))
(check-false (c:integer? (c:racket-number->c 1.5)))
(check-false (c:integer? (c:racket-number->c #e1.5)))
(check-false (c:integer? (c:racket-number->c 1+1i)))
(check-false (c:integer? "string"))
|#
(let ()
  (define-input inputs
    ;; not likely to be a special case in the code
    [X cl:integer 197136]
    [Y cl:integer 0]
    [A cl:integer 17]
    [B cl:integer 19]
    [C cl:integer 23]
    [D cl:integer 27])

  #;
  (check-equal?
   (call-with-model
    (input-model inputs)
    (λ ()
      (get-current-concrete-value
       (c:sqrt (rind->c X.var 1 Y.var 1)))))
   '(444 1 0 1))

  #;
  (check-equal?
   (call-with-model
    (input-model inputs)
    (λ ()
      (get-current-concrete-value
       (c:sqrt (rind->c X.var 0 Y.var 0)))))
   '(444 1 0 1))

  #;
  (check-equal?
   (call-with-model
    (input-model inputs)
    (λ ()
      (get-current-concrete-value
       (c:sqrt (c:racket-number->c (with-rosette () (* 4 X.var)))))))
   (list (* 2 444) 1 0 1))

  (check-equal?
   (call-with-model
    (input-model inputs)
    (λ ()
      (get-current-concrete-value
       (c:* (list (with-rosette () (* 2 A.var))
                  (with-rosette () (* 2 B.var))
                  (with-rosette () (* 2 C.var))
                  (with-rosette () (* 2 D.var)))
            (list (with-rosette () (* 2 A.var))
                  (with-rosette () (* 2 B.var))
                  (with-rosette () (* 2 C.var))
                  (with-rosette () (* 2 D.var)))))))
   (call-with-model
    (input-model inputs)
    (λ ()
      (get-current-concrete-value
       (c:* (list (get-current-concrete-value (with-rosette () (* 2 A.var)))
                  (get-current-concrete-value (with-rosette () (* 2 B.var)))
                  (get-current-concrete-value (with-rosette () (* 2 C.var)))
                  (get-current-concrete-value (with-rosette () (* 2 D.var))))
            (list (get-current-concrete-value (with-rosette () (* 2 A.var)))
                  (get-current-concrete-value (with-rosette () (* 2 B.var)))
                  (get-current-concrete-value (with-rosette () (* 2 C.var)))
                  (get-current-concrete-value (with-rosette () (* 2 D.var))))))))))
