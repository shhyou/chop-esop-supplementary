#lang concolic-hop/lang

(require concolic-hop/ctc
         concolic-hop/store
         concolic-hop/data
         (prefix-in
          r:
          (only-in racket/base
                   sqrt make-rectangular
                   real-part imag-part error
                   + - / * numerator denominator))
         (for-syntax syntax/parse)
         "private/complex-core.rkt")

(define-ctc c:complex/c (list/c integer? integer? integer? integer?))
(define-ctc c:real/c (list/c integer? integer? (and/c integer? zero?) integer?))

(define (c:integer? n)
  (cond
    [(c:real? n)
     (define-values (rn rd in id) (c->rind n))
     (= 0 (modulo rn rd))]
    [else #f]))

(define (c:+ c1 c2)
  (define-values (c1rn c1rd c1in c1id) (c->rind c1))
  (define-values (c2rn c2rd c2in c2id) (c->rind c2))
  (define-values (c3rn c3rd) (pr:+ c1rn c1rd c2rn c2rd))
  (define-values (c3in c3id) (pr:+ c1in c1id c2in c2id))
  (rind->c c3rn c3rd c3in c3id))

(define (pr:+ n1 d1 n2 d2)
  (values (+ (* n1 d2) (* n2 d1))
          (* d1 d2)))

(define (c:add1 c) (c:+ c (c:racket-number->c 1)))
(define (c:sub1 c) (c:+ c (c:racket-number->c -1)))

(define (c:- c1 c2)
  (c:+ c1 (c:negate c2)))

(define (c:negate n)
  (define-values (rn rd in id) (c->rind n))
  (rind->c (- rn) rd (- in) id))

(define (c:* x+yi u+vi)
  ;; if the arguments are x+yi and u+vi, the result's
  ;; real part is (+ (* x u) (- (* y v))), and its
  ;; imag part is (+ (* x v) (* y u)))
  (define-values (xn xd yn yd) (c->rind x+yi))
  (define-values (un ud vn vd) (c->rind u+vi))
  (define-values (x*un x*ud) (pr:* xn xd un ud))
  (define-values (y*vn y*vd) (pr:* yn yd vn vd))
  (define-values (x*vn x*vd) (pr:* xn xd vn vd))
  (define-values (y*un y*ud) (pr:* yn yd un ud))
  (define-values (-y*vn -y*vd) (values (- y*vn) y*vd))
  (define-values (x*u-y*vn x*u-y*vd) (pr:+ x*un x*ud -y*vn -y*vd))
  (define-values (x*v+y*un x*v+y*ud) (pr:+ x*vn x*vd y*un y*ud))
  (rind->c x*u-y*vn x*u-y*vd x*v+y*un x*v+y*ud))

(define (pr:* n1 d1 n2 d2)
  (values (* n1 n2) (* d1 d2)))

(define (c:/ c1 c2) (c:* c1 (c:reciprocal c2)))

(define (c:reciprocal n)
  (define-values (rn rd in id) (c->rind n))
  (define x (get-current-concrete-value (/ rn rd)))
  (define y (get-current-concrete-value (/ in id)))
  (define d (+ (r:* x x) (r:* y y)))
  (define r (r:/ x d))
  (define i (r:- (r:/ y d)))
  (rind->c (r:numerator r) (r:denominator r)
           (r:numerator i) (r:denominator i)))

(define (c:zero? c)
  (define-values (rn rd in id) (c->rind c))
  (and (zero? rn) (zero? in)))

(define (c:= c1 c2)
  (define-values (c1rn c1rd c1in c1id) (c->rind c1))
  (define-values (c2rn c2rd c2in c2id) (c->rind c2))
  (and (pr:= c1rn c1rd c2rn c2rd)
       (pr:= c1in c1id c2in c2id)))

(define (pr:= n1 d1 n2 d2)
  (= (* n1 d2) (* n2 d1)))

(define (c:< c1 c2)
  (define-values (±n1 ±d1 _1 _2) (c->rind c1))
  (define-values (±n2 ±d2 _3 _4) (c->rind c2))
  (define-values (n1 d1) (normalize-signs ±n1 ±d1))
  (define-values (n2 d2) (normalize-signs ±n2 ±d2))
  ;; d1, d2 > 0 ->
  ;; n1/d1 < n2/d2   <->
  ;; n1 < n2*d1/d2   <->
  ;; n1*d2 < n2*d1
  (< (* n1 d2) (* n2 d1)))

(define (normalize-signs ±n1 ±d1)
  (cond
    [(< ±d1 0) (values (- ±n1) (- ±d1))]
    [else (values ±n1 ±d1)]))

(define (c:<= c1 c2)
  (or (c:= c1 c2) (c:< c1 c2)))

(define (c:>= c1 c2) (not (c:< c1 c2)))
(define (c:> c1 c2) (not (c:<= c1 c2)))

(define (c:abs c)
  (define-values (rn rd in id) (c->rind c))
  (rind->c (abs rn) (abs rd) 0 1))

(define (c:min a b) (if (c:<= a b) a b))
(define (c:max a b) (if (c:<= a b) b a))

(define (c:sqrt c)
  (define-values (rn rd in id) (c->rind c))
  (cond
    [(and (= rn -1) (= rd 1) (= in 0))
     (rind->c 0 1 1 1)]
    [(and (= rn -4) (= rd 1) (= in 0))
     (rind->c 0 1 2 1)]
    [(and (= rn -9) (= rd 1) (= in 0))
     (rind->c 0 1 3 1)]
    [(and (= rn 1)  (= rd 1) (= in 0))
     (rind->c 1 1 0 1)]
    [(and (= rn 4)  (= rd 1) (= in 0))
     (rind->c 2 1 0 1)]
    [(and (= rn 9)  (= rd 1) (= in 0))
     (rind->c 3 1 0 1)]
    [else
     (c:racket-number->c
       (r:sqrt
        (r:make-rectangular
         (/ (get-current-concrete-value rn)
            (get-current-concrete-value rd))
         (/ (get-current-concrete-value in)
            (get-current-concrete-value id)))))]))
(define (c:sqr c) (c:* c c))

(define-syntax (provide-contract-out/add-to-ops-to-convert-to-complex stx)
  (syntax-parse stx
    [(_ pos neg [x:id ctc] ...)
     (with-syntax ([(without-prefix-x ...)
                    (for/list ([x (in-syntax #'(x ...))])
                      (string->symbol
                       (regexp-replace #rx"^c:"
                                       (symbol->string (syntax-e x))
                                       "")))])
       #'(begin 
           (provide-contract-out pos neg [x ctc] ...)
           (module ops-to-convert-to-complex racket/base
             (provide ops-to-convert-to-complex)
             (define ops-to-convert-to-complex
               '(=/c ;; we add =/c -- it isn't defined here but want to rewrite it
                 without-prefix-x ...)))))]))

(provide-contract-out/add-to-ops-to-convert-to-complex
 ;; treat bad inputs to these functions as bugs in the programs under test
 exn:fail bug
 [c:+ (-> c:complex/c c:complex/c c:complex/c)]
 [c:add1 (-> c:complex/c c:complex/c)]
 [c:sub1 (-> c:complex/c c:complex/c)]
 [c:- (-> c:complex/c c:complex/c c:complex/c)]
 [c:* (-> c:complex/c c:complex/c c:complex/c)]
 [c:/ (-> c:complex/c (and/c c:complex/c (not/c c:zero?)) c:complex/c)]
 [c:reciprocal (-> (and/c c:complex/c (not/c c:zero?)) c:complex/c)]
 [c:abs (-> c:real/c c:real/c)]
 [c:min (-> c:real/c c:real/c c:real/c)]
 [c:max (-> c:real/c c:real/c c:real/c)]
 [c:sqrt (-> c:complex/c c:complex/c)]
 [c:<= (-> c:real/c c:real/c boolean?)]
 [c:>= (-> c:real/c c:real/c boolean?)]
 [c:< (-> c:real/c c:real/c boolean?)]
 [c:> (-> c:real/c c:real/c boolean?)]
 [c:= (-> c:complex/c c:complex/c boolean?)]
 [c:zero? (-> c:complex/c boolean?)]
 [c:number? (-> any/c boolean?)]
 [c:real? (-> any/c boolean?)]
 [c:integer? (-> any/c boolean?)]
 
 ;; the way to build constants
 [c:racket-number->c (-> number? c:complex/c)]

 ;; used to call code that's not inspected by the concolic tester
 [c:from-concolic-number (-> c:complex/c number?)])
